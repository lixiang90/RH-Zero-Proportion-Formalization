"""V3 scoped-cache Linux resource test. Prepared separately; old v1/v2 remain frozen."""
from pathlib import Path
import argparse, ctypes, errno, fcntl, hashlib, json, os, re, signal, subprocess, time

BASE = Path('/tmp/rh-proportion-memory-20261010')
CGNAME = 'rh-proportion-memory-20261010'
MEMORY = 8 * 1024**3
ALLOWED_EXE = {BASE/'lean-4.33.0-rc2-linux/bin/lean', BASE/'lean-4.33.0-rc2-linux/bin/lake', Path('/usr/bin/python3')}

RUNTIME=BASE/'lean-4.33.0-rc2-linux'
DEFAULT_EVICT_ROOTS=[BASE/'native-cache',RUNTIME/'lib']
PAGESIZE=os.sysconf('SC_PAGE_SIZE')
ARTIFACT_SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ir.sig')
LIBC=ctypes.CDLL(None,use_errno=True)
LIBC.mmap.argtypes=[ctypes.c_void_p,ctypes.c_size_t,ctypes.c_int,ctypes.c_int,ctypes.c_int,ctypes.c_longlong]
LIBC.mmap.restype=ctypes.c_void_p
LIBC.mincore.argtypes=[ctypes.c_void_p,ctypes.c_size_t,ctypes.POINTER(ctypes.c_ubyte)]
LIBC.mincore.restype=ctypes.c_int
LIBC.munmap.argtypes=[ctypes.c_void_p,ctypes.c_size_t]
LIBC.munmap.restype=ctypes.c_int

def idle_proof_guard():
    active=[]
    expected={x.resolve() for x in ALLOWED_EXE if x.name in {'lean','lake'}}
    for p in Path('/proc').iterdir():
        if not p.name.isdigit() or int(p.name)==os.getpid():continue
        try:
            exe=(p/'exe').resolve(strict=True)
            if exe in expected:
                active.append({'pid':int(p.name),'exe':str(exe)})
        except (FileNotFoundError,PermissionError,ProcessLookupError):pass
    parent=Path('/sys/fs/cgroup/memory')/CGNAME
    if parent.exists():
        for file in parent.glob('*/cgroup.procs'):
            for pid in file.read_text().split():
                if int(pid)!=os.getpid():
                    active.append({'pid':int(pid),'owned_cgroup':str(file.parent)})
    assert not active,'Concurrent proof process: scoped eviction refused '+json.dumps(active)

def selected_cache_file(p):
    return p.name.endswith(ARTIFACT_SUFFIXES) or p.name.endswith('.so') or '.so.' in p.name

def validate_evict_roots(extra):
    approved=[BASE.resolve(),Path('/mnt/e/codex-build/RH-Weil/tmp').resolve(),
              Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp').resolve()]
    roots=[]
    for value in [*DEFAULT_EVICT_ROOTS,*map(Path,extra)]:
        resolved=value.resolve(strict=True)
        assert resolved.is_dir()
        assert any(resolved.is_relative_to(x) and resolved!=x for x in approved), 'Eviction root outside owned private subdirectory'
        if resolved not in roots:roots.append(resolved)
    return roots

def mincore_fd(fd,size):
    if not size:return {'page_count':0,'resident_page_count':0,'resident_page_bytes':0}
    # PROT_NONE and MAP_PRIVATE do not fault file data into memory.
    address=LIBC.mmap(None,size,0,2,fd,0)
    if address==ctypes.c_void_p(-1).value:
        code=ctypes.get_errno();raise OSError(code,os.strerror(code))
    count=(size+PAGESIZE-1)//PAGESIZE
    vector=(ctypes.c_ubyte*count)()
    try:
        if LIBC.mincore(address,size,vector)!=0:
            code=ctypes.get_errno();raise OSError(code,os.strerror(code))
        resident=sum(bool(value&1) for value in vector)
        return {'page_count':count,'resident_page_count':resident,'resident_page_bytes':resident*PAGESIZE}
    finally:
        if LIBC.munmap(address,size)!=0:
            code=ctypes.get_errno();raise OSError(code,os.strerror(code))

def scoped_cache_evict(extra,recorddir):
    started=time.monotonic();idle_proof_guard()
    roots=validate_evict_roots(extra)
    files=[];seen=set()
    for root in roots:
        for p in sorted(root.rglob('*')):
            if not p.is_file() or not selected_cache_file(p):continue
            resolved=p.resolve(strict=True)
            assert resolved.is_relative_to(root),'Cache artifact symlink escapes selected root'
            st=resolved.stat();key=(st.st_dev,st.st_ino)
            if key not in seen:seen.add(key);files.append(resolved)
    # The exact executable is small but also belongs to this runtime.
    for p in [RUNTIME/'bin/lean',RUNTIME/'bin/lake']:
        resolved=p.resolve(strict=True);st=resolved.stat();key=(st.st_dev,st.st_ino)
        assert resolved.is_relative_to(RUNTIME.resolve())
        if key not in seen:seen.add(key);files.append(resolved)
    report={'status':'PREPARING','method':'Per-owned-file readonly-fd fsync then POSIX_FADV_DONTNEED; PROT_NONE mmap/mincore before and after; no global drop_caches',
            'roots':list(map(str,roots)),'page_size':PAGESIZE,'files':[],
            'scope':'Only selected artifact/shared-library files and exact Lean/Lake executables. Kernel, unrelated file cache and WSL VM size are unchanged.'}
    try:
        for i,p in enumerate(files):
            if i%128==0:idle_proof_guard()
            # O_RDONLY: neither file contents nor proof artifact bytes are changed.
            fd=os.open(p,os.O_RDONLY|os.O_CLOEXEC)
            try:
                st=os.fstat(fd)
                before=mincore_fd(fd,st.st_size)
                os.fsync(fd)  # Flush only this selected file, including fresh dirty overlays.
                os.posix_fadvise(fd,0,0,os.POSIX_FADV_DONTNEED)
                after=mincore_fd(fd,st.st_size)
                st2=os.fstat(fd)
                assert (st.st_size,st.st_mtime_ns,st.st_ino)==(st2.st_size,st2.st_mtime_ns,st2.st_ino),'Artifact changed during scoped eviction'
                report['files'].append({'path':str(p),'bytes':st.st_size,'device':st.st_dev,'inode':st.st_ino,
                                        'before':before,'after':after,'fsync_completed':True})
            finally:os.close(fd)
        idle_proof_guard()
        report['file_count']=len(report['files'])
        report['file_bytes']=sum(x['bytes'] for x in report['files'])
        report['before_resident_page_bytes']=sum(x['before']['resident_page_bytes'] for x in report['files'])
        report['after_resident_page_bytes']=sum(x['after']['resident_page_bytes'] for x in report['files'])
        report['all_selected_pages_nonresident']=report['after_resident_page_bytes']==0
        report['status']='PASS' if report['all_selected_pages_nonresident'] else 'RESIDUAL_RESIDENCY'
        report['elapsed_seconds']=round(time.monotonic()-started,3)
        (recorddir/'scoped-cache-eviction.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps({k:v for k,v in report.items() if k!='files'}),flush=True)
        # DONTNEED is advisory. A residual page invalidates a strict fresh-charge claim.
        assert report['all_selected_pages_nonresident'],'Scoped eviction left resident pages; proof launch refused'
        return report
    except BaseException as e:
        report['status']='REFUSED';report['error']=repr(e)
        report['elapsed_seconds']=round(time.monotonic()-started,3)
        (recorddir/'scoped-cache-eviction.json').write_text(json.dumps(report,indent=2)+'\n')
        raise

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(8*1024*1024),b''):h.update(b)
    return h.hexdigest()
def read(path):return Path(path).read_text().strip()
def write(path,value):Path(path).write_text(str(value))
def current(group):
    memory=group['memory']
    return {name:read(memory/name) for name in ['memory.usage_in_bytes','memory.max_usage_in_bytes','memory.memsw.usage_in_bytes','memory.memsw.max_usage_in_bytes','memory.failcnt','memory.oom_control','memory.stat']} | {'cpu.stat':read(group['cpu']/'cpu.stat'),'cpuacct.usage':read(group['cpuacct']/'cpuacct.usage')}
def members(group):
    return {int(x) for x in read(group['memory']/'cgroup.procs').split()}
def proc(pid):
    try:
        status=dict(line.split(':',1) for line in Path(f'/proc/{pid}/status').read_text().splitlines() if ':' in line)
        stat=Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()
        rollup=dict(line.split(':',1) for line in Path(f'/proc/{pid}/smaps_rollup').read_text().splitlines() if ':' in line)
        return {'pid':pid,'name':status['Name'].strip(),'uid':int(status['Uid'].split()[0]),'rss_bytes':int(status.get('VmRSS','0 kB').split()[0])*1024,'pss_bytes':int(rollup.get('Pss','0 kB').split()[0])*1024,'swap_bytes':int(rollup.get('Swap','0 kB').split()[0])*1024,'threads':int(status['Threads']),'starttime':int(stat[19]),'cpu_ticks':int(stat[11])+int(stat[12])}
    except (FileNotFoundError,ProcessLookupError):return None
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--run-id',required=True)
    parser.add_argument('--timeout',type=float,required=True)
    parser.add_argument('--cwd',required=True)
    parser.add_argument('--lean-path',default='')
    parser.add_argument('--bind',action='append',default=[])
    parser.add_argument('--evict-root',action='append',default=[])
    parser.add_argument('command',nargs=argparse.REMAINDER)
    args=parser.parse_args()
    assert os.geteuid()==0,'Only supervisor needs root; proof subprocess is demoted'
    lockfd=os.open(BASE/'resource-harness-v3.lock',os.O_CREAT|os.O_RDWR|os.O_CLOEXEC,0o600)
    fcntl.flock(lockfd,fcntl.LOCK_EX|fcntl.LOCK_NB)
    assert re.fullmatch(r'[a-z0-9][a-z0-9-]{0,60}',args.run_id)
    assert 0<args.timeout<=3400
    command=args.command[1:] if args.command[:1]==['--'] else args.command
    assert command and Path(command[0]).resolve() in {x.resolve() for x in ALLOWED_EXE}
    cwd=Path(args.cwd).resolve()
    assert cwd==BASE or cwd.is_relative_to(BASE) or cwd.is_relative_to(Path('/mnt/e/codex-build/RH-Weil/tmp')) or cwd.is_relative_to(Path('/mnt/e/codex-build/RH-Zero-Proportion-Formalization/tmp'))
    recorddir=BASE/'resource-runs'/args.run_id
    assert not recorddir.exists(),'Each experiment must be fresh'
    recorddir.mkdir(parents=True)
    os.chown(recorddir,1000,1000)
    before={str(Path(x).resolve()):sha(x) for x in args.bind}
    # Hash inputs first: hashing a cache artifact after eviction would warm it outside the proof cgroup.
    eviction=scoped_cache_evict(args.evict_root,recorddir)
    groups={}
    for controller in ['memory','cpu','cpuacct','cpuset']:
        base=Path('/sys/fs/cgroup')/controller/CGNAME
        base.mkdir(exist_ok=True)
        if controller=='cpuset':
            write(base/'cpuset.mems','0');write(base/'cpuset.cpus','0-3')
        group=base/args.run_id
        assert not group.exists(),'Never reuse old cgroup counters'
        group.mkdir();groups[controller]=group
    write(groups['memory']/'memory.limit_in_bytes',MEMORY)
    write(groups['memory']/'memory.memsw.limit_in_bytes',MEMORY)
    write(groups['memory']/'memory.swappiness',0)
    write(groups['cpu']/'cpu.cfs_period_us',100000)
    write(groups['cpu']/'cpu.cfs_quota_us',400000)
    write(groups['cpuset']/'cpuset.mems','0');write(groups['cpuset']/'cpuset.cpus','0-3')
    configuration={key:read(groups[controller]/key) for controller,key in [('memory','memory.limit_in_bytes'),('memory','memory.memsw.limit_in_bytes'),('memory','memory.swappiness'),('cpu','cpu.cfs_period_us'),('cpu','cpu.cfs_quota_us'),('cpuset','cpuset.mems'),('cpuset','cpuset.cpus')]}
    assert configuration['memory.limit_in_bytes']==str(MEMORY) and configuration['memory.memsw.limit_in_bytes']==str(MEMORY)
    env={'PATH':str(BASE/'lean-4.33.0-rc2-linux/bin')+':/usr/bin:/bin','HOME':'/home/xiaoai','USER':'xiaoai','LOGNAME':'xiaoai','LANG':'C.UTF-8','LEAN_ABORT_ON_PANIC':'1'}
    if args.lean_path:env['LEAN_PATH']=args.lean_path
    def preexec():
        os.setsid()
        for group in groups.values():write(group/'cgroup.procs',os.getpid())
        os.setgroups([]);os.setgid(1000);os.setuid(1000)
        assert os.getuid()==1000 and os.getgid()==1000
    samples=[];known={};begin=time.monotonic();timedout=False;last=begin
    initial=current(groups)
    with (recorddir/'process.log').open('wb') as log:
        p=subprocess.Popen(command,cwd=cwd,env=env,stdout=log,stderr=subprocess.STDOUT,preexec_fn=preexec)
        print(json.dumps({'started_pid':p.pid,'run_id':args.run_id,'configuration':configuration,'proof_uid':1000}),flush=True)
        while p.poll() is None:
            now=time.monotonic();records=[q for pid in members(groups) if (q:=proc(pid))]
            for q in records:
                key=f"{q['pid']}:{q['starttime']}"
                old=known.setdefault(key,{**q,'peak_rss_bytes':0,'peak_pss_bytes':0,'peak_swap_bytes':0})
                old['peak_rss_bytes']=max(old['peak_rss_bytes'],q['rss_bytes']);old['cpu_ticks']=max(old['cpu_ticks'],q['cpu_ticks'])
                old['peak_pss_bytes']=max(old['peak_pss_bytes'],q['pss_bytes']);old['peak_swap_bytes']=max(old['peak_swap_bytes'],q['swap_bytes'])
            sample={'elapsed_seconds':round(now-begin,3),'group':current(groups),'tree_rss_bytes':sum(q['rss_bytes'] for q in records),'tree_pss_bytes':sum(q['pss_bytes'] for q in records),'tree_swap_bytes':sum(q['swap_bytes'] for q in records),'processes':records}
            samples.append(sample)
            if now-last>15:
                print(json.dumps({'running':args.run_id,'seconds':round(now-begin,1),'memory_current_bytes':int(sample['group']['memory.usage_in_bytes']),'memory_peak_bytes':int(sample['group']['memory.max_usage_in_bytes']),'tree_rss_bytes':sample['tree_rss_bytes']}),flush=True);last=now
            if now-begin>args.timeout:
                timedout=True
                for pid in members(groups):
                    try:os.kill(pid,signal.SIGTERM)
                    except ProcessLookupError:pass
                try:p.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    for pid in members(groups):
                        try:os.kill(pid,signal.SIGKILL)
                        except ProcessLookupError:pass
                break
            time.sleep(.5)
        exitcode=p.wait()
    # Cgroup descendants must be accounted for even if the first process exits.
    residual=members(groups)
    if residual:
        for pid in residual:
            try:os.kill(pid,signal.SIGTERM)
            except ProcessLookupError:pass
        time.sleep(.2)
        for pid in members(groups):
            try:os.kill(pid,signal.SIGKILL)
            except ProcessLookupError:pass
    final=current(groups);after={name:sha(name) for name in before}
    oom=dict(line.split() for line in final['memory.oom_control'].splitlines())
    result={'run_id':args.run_id,'command':command,'cwd':str(cwd),'proof_uid':1000,'configuration':configuration,'actual_exit_code':exitcode,'timeout':timedout,'oom_kill_count':int(oom.get('oom_kill','0')),'memory_limit_hit':int(final['memory.failcnt'])>0,'elapsed_seconds':round(time.monotonic()-begin,3),'initial_cgroup':initial,'final_cgroup':final,'sampled_tree_peak_rss_bytes':max((s['tree_rss_bytes'] for s in samples),default=0),'sampled_tree_peak_pss_bytes':max((s['tree_pss_bytes'] for s in samples),default=0),'sampled_tree_peak_swap_bytes':max((s['tree_swap_bytes'] for s in samples),default=0),'per_process':known,'inputs_before':before,'inputs_after':after,'inputs_unchanged':before==after,'log_sha256':sha(recorddir/'process.log'),'samples':samples,'scope':'Private Linux cgroup-v1 component resource experiment: scoped imported-artifact cache pages were evicted and checked nonresident before launch, with no concurrent owned proof processes. Owned group capped at 4 CPUs and 8 GiB with no swap; enclosing WSL VM remains32GiB. Kernel, unrelated file cache, source filesystem and cross-group charge ownership still differ from a whole official8GiBVM. RSS/PSS, cache residency and cgroup counters are all reported. No exact official reproduction or website acceptance claim.'}
    result['harness_version']=3
    result['scoped_eviction']={k:v for k,v in eviction.items() if k!='files'}
    result['scoped_eviction_sha256']=sha(recorddir/'scoped-cache-eviction.json')
    result['sampled_pss_exceeds_memory_limit']=result['sampled_tree_peak_pss_bytes']>MEMORY
    result['cgroup_peak_bytes']=int(final['memory.max_usage_in_bytes'])
    result['cgroup_pss_peak_gap_bytes']=result['sampled_tree_peak_pss_bytes']-result['cgroup_peak_bytes']
    result['proof_succeeded']=exitcode==0 and not timedout and not result['oom_kill_count'] and before==after
    result['resource_fit']=result['proof_succeeded'] and eviction['all_selected_pages_nonresident'] and not result['sampled_pss_exceeds_memory_limit'] and not result['memory_limit_hit'] and result['sampled_tree_peak_swap_bytes']==0
    result['resource_fit_scope']='Observed component resource fit under this scoped-cache experiment, not full official VM fit; sampled PSS may miss between-sample peaks.'
    result['resource_status']='OBSERVED_COMPONENT_FIT' if result['resource_fit'] else 'NOT_ESTABLISHED'
    if result['sampled_pss_exceeds_memory_limit']:result['resource_status']='PSS_EXCEEDS_8GIB_DESPITE_CGROUP'
    (recorddir/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in {'samples','per_process','initial_cgroup','inputs_before','inputs_after'}}),flush=True)
    return 0 if result['proof_succeeded'] and result['resource_fit'] else 1
if __name__=='__main__':raise SystemExit(main())
