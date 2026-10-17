"""Independent read-only replay of a bottom-up original-witness W10 merge.

No producer import or search.  Bind every retained branch to the frozen
old tree and every numeric representative to its exact original FS/code.
Then reconstruct the NEW complete root geometry and verify all remaining
leaf PT domains, Pruefer dual proposals and final integer inequalities.
Default read-only; --write-receipt creates an absent receipt once.
Prepared without executing any merge or replay before the packet is stable.
"""
from pathlib import Path
import argparse,collections,gzip,hashlib,importlib.util,json,struct,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
AUDIT=HERE.parent/'w10-size-audit-20261017';OUT=HERE/'independent-merge-replay.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser();parser.add_argument('packet',type=Path);parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    packetpath=args.packet.resolve();raw=packetpath.read_bytes();decompressed=gzip.decompress(raw) if raw[:2]==b'\x1f\x8b' else raw;packet=json.loads(decompressed)
    paths=[Path(__file__),packetpath,AUDIT/'independent_codec_replay.py',AUDIT/'independent-codec-files.json',AUDIT/'semantics.json',
        AUDIT/'nodes.bin',AUDIT/'fs.bin',AUDIT/'treecodes.bin',ROOT/'research-20261016/spectral-w10-refined-rational.json',
        ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean',ROOT/'research-20261016-w10-cert/independent_integer_audit.py']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    frozen=json.loads((AUDIT/'independent-codec-files.json').read_bytes())
    for entry in frozen['package_files']+frozen['dependency_files']:assert sha(ROOT/entry['path'])==entry['sha256']
    semantics=json.loads((AUDIT/'semantics.json').read_bytes());params=json.loads(paths[8].read_bytes())
    assert packet['n']==86600000 and packet['target']=='433/50000'
    assert packet['semantics_sha256']==sha(AUDIT/'semantics.json')
    for entry in semantics['cache_files']:assert sha(AUDIT/entry['path'])==entry['sha256']
    spec=importlib.util.spec_from_file_location('frozen_independent_mathematical_checker',paths[2]);check=importlib.util.module_from_spec(spec);spec.loader.exec_module(check)
    tablespec=importlib.util.spec_from_file_location('frozen_independent_PT_reader',paths[10]);table=importlib.util.module_from_spec(tablespec);tablespec.loader.exec_module(table)
    terms=[tuple(t) for t in params['a_upper'] if t[2]];bs=params['b_numerators'];points,lower=table.load_analytic_library()
    assert packet['root']==check.root_of(bs)==semantics['root']
    assert not packet.get('unresolved') and not packet.get('frontier')
    branches={};leaves={};wanted={}
    for row in packet['branches']:
        path=row['path'];assert re_path(path) and path not in branches;branches[path]=row
        assert isinstance(row['axis'],int) and 0<=row['axis']<45 and isinstance(row['cut'],int) and row['cut']>=0
    for row in packet['leaves']:
        path=row['path'];assert re_path(path) and path not in leaves;leaves[path]=row
        assert row['kind'] in ['numeric','empty','reflection']
        if row['kind']=='numeric':
            origin=row['original_witness_path'];assert re_path(origin) and origin.startswith(path) and origin not in wanted
            fs=row['FS'];assert len(fs)==39 and all(len(t)==4 and all(isinstance(v,int) and v>=0 for v in t) for t in fs)
            assert isinstance(row['tree_code'],int) and 0<=row['tree_code']<10**8;wanted[origin]=row
    assert not set(branches)&set(leaves)
    # One linear scan of the immutable original semantic cache checks exact
    # provenance.  The new packet may not invent a new anchor/mix/topology.
    nodes=(AUDIT/'nodes.bin').read_bytes();fsbytes=(AUDIT/'fs.bin').read_bytes();codes=(AUDIT/'treecodes.bin').read_bytes()
    nodepos=fspos=codepos=0;oldstack=['r'];matched_origins=set();matched_branches=set();oldcounts=collections.Counter()
    while oldstack:
        path=oldstack.pop();assert nodepos<len(nodes);kind=nodes[nodepos];nodepos+=1;oldcounts['nodes']+=1
        if kind==1:
            assert nodepos+5<=len(nodes);axis,cut=struct.unpack_from('<BI',nodes,nodepos);nodepos+=5
            if path in branches:
                assert branches[path]['axis']==axis and branches[path]['cut']==cut;matched_branches.add(path)
            oldstack.extend([path+'1',path+'0']);oldcounts['branches']+=1
        elif kind==0:
            assert fspos+39*7<=len(fsbytes) and codepos+4<=len(codes)
            if path in wanted:
                original=[]
                for k in range(39):
                    kind2,m,p,r=struct.unpack_from('<BHHH',fsbytes,fspos+7*k);original.append([kind2,m,32*p,32*r])
                code=struct.unpack_from('<I',codes,codepos)[0]
                assert original==wanted[path]['FS'] and code==wanted[path]['tree_code'],('Altered original witness',path)
                matched_origins.add(path)
            fspos+=39*7;codepos+=4;oldcounts['numeric']+=1
            if path in leaves and leaves[path]['kind']!='numeric':raise AssertionError(('Changed old nonnumeric kind',path))
        elif kind==2:
            assert nodepos<len(nodes);axis=nodes[nodepos];nodepos+=1;oldcounts['empty']+=1
            if path in leaves:assert leaves[path]['kind']=='empty' and leaves[path]['violation_axis']==axis
        else:
            assert kind==3;oldcounts['reflection']+=1
            if path in leaves:assert leaves[path]['kind']=='reflection'
    assert nodepos==len(nodes) and fspos==len(fsbytes) and codepos==len(codes)
    assert matched_origins==set(wanted) and matched_branches==set(branches)
    assert oldcounts=={'nodes':191557,'branches':95778,'numeric':95615,'empty':163,'reflection':1}
    # New-tree checks: both children must appear; no disconnected, extra or
    # silently skipped record is allowed.  Each parent is normalized anew.
    stack=[('r',packet['root'])];seenbranches=set();seenleaves=set();counts=collections.Counter();states=hashlib.sha256();evidence=hashlib.sha256()
    minimum=None;minimum_path=None;collapsed=0
    while stack:
        path,rawstate=stack.pop();state=check.normal(rawstate);counts['nodes']+=1;states.update(struct.pack('<90I',*(state[0]+state[1])))
        if path in branches:
            row=branches[path];axis,cut=row['axis'],row['cut'];assert state[0][axis]<cut<state[1][axis]
            seenbranches.add(path);counts['branches']+=1
            stack.append((path+'1',check.child(state,axis,cut,False)));stack.append((path+'0',check.child(state,axis,cut,True)))
            record=[path,'branch',axis,cut]
        else:
            assert path in leaves,('Uncovered new prefix',path)
            row=leaves[path];seenleaves.add(path);kind=row['kind'];counts[kind]+=1
            if kind=='empty':
                axis=row['violation_axis'];assert isinstance(axis,int) and 0<=axis<45 and state[1][axis]<state[0][axis]
                record=[path,kind,axis]
            elif kind=='reflection':
                assert state[1][8]<state[0][0];record=[path,kind]
            else:
                fs=[tuple(t) for t in row['FS']]
                numerator,_=check.numeric_check(path,state,fs,row['tree_code'],terms,bs,points,lower)
                assert numerator>=check.TARGET
                if minimum is None or numerator<minimum:minimum=numerator;minimum_path=path
                collapsed+=row['original_witness_path']!=path
                record=[path,kind,row['original_witness_path'],row['FS'],row['tree_code'],str(numerator)]
                if counts['numeric']%10000==0:print(json.dumps({'new_numeric_checked':counts['numeric'],'seconds':time.monotonic()-began}),flush=True)
            if 'normalized_cell' in row:assert row['normalized_cell']==state
        encoded=json.dumps(record,separators=(',',':')).encode();evidence.update(len(encoded).to_bytes(4,'little'));evidence.update(encoded)
    assert seenbranches==set(branches) and seenleaves==set(leaves)
    assert len(branches)+1==len(leaves) and counts['nodes']==len(branches)+len(leaves)
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    out={'scope':__doc__,'status':'complete_merged_tree_original_witnesses_and_all_integer_leaf_checks_verified',
        'source_sha256_start':initial,'source_sha256_end':final,'all_sources_unchanged':True,
        'packet_uncompressed_sha256':hashlib.sha256(decompressed).hexdigest(),'packet_bytes':len(raw),'packet_uncompressed_bytes':len(decompressed),
        'counts':dict(counts),'numeric_provenance_checks':len(wanted),'retained_branch_identity_checks':len(branches),
        'strictly_merged_parent_leaves':collapsed,'all_new_prefix_records_reachable':True,'both_children_fully_consumed':True,
        'new_normalized_states_sha256':states.hexdigest(),'full_mathematical_evidence_sha256':evidence.hexdigest(),
        'minimum_leaf_numerator':str(minimum),'minimum_leaf_path':minimum_path,'target_numerator':str(check.TARGET),
        'minimum_exact_margin':str(minimum-check.TARGET),'pure_stdlib_replay':True,'search_calls':0,'optimizer_calls':0,'Lean_invocations':0,
        'new_Lean_cover_checked':False,'two_MB_source_checked':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','counts','numeric_provenance_checks','strictly_merged_parent_leaves','minimum_exact_margin','elapsed_milliseconds']}),flush=True)


def re_path(path):return isinstance(path,str) and path.startswith('r') and all(c in '01' for c in path[1:])
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
