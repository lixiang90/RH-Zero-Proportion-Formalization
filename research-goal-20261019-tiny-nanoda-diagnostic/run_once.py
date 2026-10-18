"""Bounded complete nanoda timing diagnostic, never a full3200s acceptance."""
from pathlib import Path
import hashlib,json,os,re,signal,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
OLD=Path('/var/tmp/rh-zero-20261015/tiny-production-v0')
JOB=Path('/var/tmp/rh-zero-20261015/tiny-nanoda-diagnostic-v0')
MIRROR=ROOT/'tmp/current-s1r-tiny-20261018/nanoda-diagnostic-v0'
BIN=Path('/var/tmp/rh-zero-20261015/nanoda-target/release/nanoda_bin')
ALLOWED={'propext','Quot.sound','Classical.choice'}
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def write(p,o):
    with p.open('x',encoding='utf-8') as f:json.dump(o,f,indent=2);f.write('\n')
def main():
    assert ROOT==Path('/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization')
    failure=json.loads((OLD/'failure.json').read_bytes())
    assert failure['failed'] and failure['stage']=='nanoda' and failure['default_kernel_replay_passed']
    assert sha(BIN)=='0c8332aae13164943ebfed4f8f4ed969494d8e85edff9d774a70fd92ea9318c2'
    export=OLD/'solution.ndjson';expected=failure['exports']['solution']['output_sha256']
    assert sha(export)==expected
    config=OLD/'nanoda-config.json';c=json.loads(config.read_bytes())
    assert c['num_threads']==4 and set(c['permitted_axioms'])==ALLOWED
    assert not c['unsafe_permit_all_axioms'] and c['unpermitted_axiom_hard_error']
    active=subprocess.run(['/usr/bin/pgrep','-a','-x','nanoda_bin'],capture_output=True)
    assert active.returncode==1 and not active.stdout
    JOB.mkdir();MIRROR.mkdir(parents=True)
    cfg=JOB/'config.json';cfg.write_bytes(config.read_bytes())
    t0=time.monotonic();deadline=t0+1200
    command=['/usr/bin/time','-v','-o',str(JOB/'resources.txt'),str(BIN),str(cfg)]
    write(JOB/'started.json',dict(command=command,pid=os.getpid(),diagnostic_only=True,
        timeout_seconds=1200,num_threads=4,source_export_sha256=expected,
        previous_full3200s_attempt_passed=False,official_website_acceptance=False))
    print(json.dumps({'diagnostic_started':True,'threads':4,'timeout_seconds':1200}),flush=True)
    with export.open('rb') as inp,(JOB/'nanoda.log').open('xb') as out:
        child=subprocess.Popen(command,stdin=inp,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
        write(JOB/'child.json',dict(pid=child.pid))
        try:code=child.wait(timeout=max(.01,deadline-time.monotonic()))
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGTERM)
            try:child.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=5)
            code=124
    elapsed=time.monotonic()-t0
    log=(JOB/'nanoda.log').read_text(errors='replace')
    checked=re.search(r'Checked (\d+) declarations with no errors',log)
    observed={n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)',log,re.M)}
    unchanged=sha(export)==expected and sha(cfg)==sha(config)
    passed=code==0 and checked is not None and observed<=ALLOWED and unchanged
    result=dict(diagnostic_only=True,independent_complete_nanoda_passed=passed,
        exit_code=code,elapsed_seconds=elapsed,num_threads=4,
        checked_declarations=int(checked[1]) if checked else None,observed_axioms=sorted(observed),
        source_export_sha256=expected,inputs_unchanged=unchanged,
        log_sha256=sha(JOB/'nanoda.log'),resources_sha256=sha(JOB/'resources.txt'),
        previous_full3200s_attempt_passed=False,full_cold_submission_ready=False,
        official_website_acceptance=False)
    write(JOB/'terminal.json',result);write(MIRROR/'terminal.json',result)
    print(json.dumps(result),flush=True)
    return 0 if passed else 1
if __name__=='__main__':raise SystemExit(main())
