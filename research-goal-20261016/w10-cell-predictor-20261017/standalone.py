"""Project/replay exactly the existing first1000-leaf W10 predictor pilot.

No tuning, optimizer, cover search or Lean. The small projection binds
the original full-cache hashes, but checks only this prefix. Default
replay needs the frozen analytic/geometry readers, not the large caches.
"""
from pathlib import Path
import argparse, base64, gzip, hashlib, importlib.util, json, struct, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];CACHE=HERE.parent/'w10-size-audit-20261017'


def sha(b):return hashlib.sha256(b).hexdigest()
def file_sha(p):return sha(p.read_bytes())
def load(name,p):
    s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def export():
    target=HERE/'sample-input.json.gz';assert not target.exists()
    r=json.loads((HERE/'result.json').read_bytes());meta=json.loads((CACHE/'semantics.json').read_bytes())
    for n,h in r['source_and_input_sha256'].items():assert file_sha(ROOT/n)==h
    with(CACHE/'nodes.bin').open('rb')as f:
        b=bytearray()
        for _ in range(r['preorder_nodes_consumed']):
            k=f.read(1);assert k;b.extend(k);b.extend(f.read(5 if k==b'\x01' else 1 if k==b'\x02' else 0))
    with(CACHE/'fs.bin').open('rb')as f:fs=f.read(1000*39*7)
    with(CACHE/'treecodes.bin').open('rb')as f:trees=f.read(4000)
    params=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_bytes())
    deps=['research-goal-20261016/w10-size-audit-20261017/independent_codec_replay.py',
      'research-20261016-w10-cert/independent_integer_audit.py','formal/upstream/ajp88-reweighted-nine-point.lean']
    p={'schema':'W10-fixed-first1000-projection-v1','source_full_cache_sha256':meta['cache_files'],
      'original_cache_prefixes':{n:{'base64':base64.b64encode(v).decode(),'bytes':len(v),'sha256':sha(v)}
        for n,v in [('nodes',bytes(b)),('FS',fs),('trees',trees)]},
      'root':meta['root'],'terms':meta['terms'],'bs':params['b_numerators'],
      'dependencies':{n:r['source_and_input_sha256'][n]for n in deps},
      'pilot_result_sha256':file_sha(HERE/'result.json'),'protocol_sha256':file_sha(HERE/'protocol.json'),
      'only_first1000_projection':True,'full_cover_or_new_record_proven':False}
    target.write_bytes(gzip.compress(json.dumps(p,sort_keys=True,separators=(',',':')).encode(),mtime=0))
    print(json.dumps({'projected_bytes':target.stat().st_size,'sha256':file_sha(target)}),flush=True)


def replay():
    started=time.monotonic();target=HERE/'standalone-replay.json';assert not target.exists()
    p=json.loads(gzip.decompress((HERE/'sample-input.json.gz').read_bytes()));assert p['schema']=='W10-fixed-first1000-projection-v1'
    r=json.loads((HERE/'result.json').read_bytes());protocol=json.loads((HERE/'protocol.json').read_bytes())
    assert p['pilot_result_sha256']==file_sha(HERE/'result.json') and p['protocol_sha256']==file_sha(HERE/'protocol.json')
    for n,h in p['dependencies'].items():assert file_sha(ROOT/n)==h
    old=load('independent_W10_replay',ROOT/'research-goal-20261016/w10-size-audit-20261017/independent_codec_replay.py')
    a=load('independent_W10_analytic',ROOT/'research-20261016-w10-cert/independent_integer_audit.py')
    points,lower=a.load_analytic_library();anchors=sorted(k for k in points if k%32==0);terms=p['terms'];bs=p['bs']
    assert old.root_of(bs)==p['root']
    decoded={}
    for name,row in p['original_cache_prefixes'].items():
        raw=base64.b64decode(row['base64'],validate=True);assert len(raw)==row['bytes'] and sha(raw)==row['sha256'];decoded[name]=raw
    exceptions=[]
    for i in range(3):
        q=HERE/f'rule{i}-exceptions.bin.gz';assert file_sha(q)==r['rules'][i]['gzip_sha256']
        raw=gzip.decompress(q.read_bytes());assert sha(raw)==r['rules'][i]['raw_sha256']
        assert raw[:5]==b'W10P\x01' and raw[5]==i and struct.unpack_from('<H',raw,6)[0]==1000
        exceptions.append(raw)
    positions=[8]*3;pred_pass=[0]*3;fixed_pass=[0]*4;portfolio=0;numeric=nodes=pos=0;geometry=hashlib.sha256();stack=[('r',p['root'])]
    def point_delta(raw,k):
        value=0
        for j in range(3):
            byte=raw[k];k+=1;value+=(byte&127)<<(7*j)
            if byte<128:return (value//2 if value%2==0 else -(value//2)-1),k
        raise AssertionError('bad delta')
    def check(path,state,fs,code):
        try:
            value,_=old.numeric_check(path,state,fs,code,terms,bs,points,lower)
            return True,value-old.TARGET
        except AssertionError as e:
            msg=e.args[0]
            if isinstance(msg,tuple)and msg[0]=='mcheckGX inequality failed':return False,msg[2]
            raise
    while numeric<1000:
        path,state=stack.pop();state=old.normal(state);geometry.update(struct.pack('<90I',*(state[0]+state[1])));nodes+=1
        kind=decoded['nodes'][pos];pos+=1
        if kind==1:
            axis,cut=struct.unpack_from('<BI',decoded['nodes'],pos);pos+=5;assert state[0][axis]<cut<state[1][axis]
            stack.extend([(path+'1',old.child(state,axis,cut,False)),(path+'0',old.child(state,axis,cut,True))]);continue
        if kind==2:
            axis=decoded['nodes'][pos];pos+=1;assert state[1][axis]<state[0][axis];continue
        if kind==3:assert state[1][8]<state[0][0];continue
        assert kind==0;original=[]
        for t in range(39):
            k,m,x,y=struct.unpack_from('<BHHH',decoded['FS'],7*(numeric*39+t));original.append((k,m,32*x,32*y))
        code=struct.unpack_from('<I',decoded['trees'],4*numeric)[0];assert check(path,state,original,code)[0]
        guesses=[[],[],[]]
        for i,j,_ in terms:
            z=old.SLOT[i,j];lo=max(state[0][z],sum(state[0][i:j]));hi=min(state[1][z],sum(state[1][i:j]))
            eligible=[x for x in anchors if lo<=x<=hi and points[x][2]>0 and points[x][1]<=lo and hi<=points[x][2]]
            for guess,aim in zip(guesses,[lo+hi,2*lo,2*hi]):
                x=min(eligible,key=lambda v:(abs(2*v-aim),v))if eligible else None
                guess.append((1,0,x,0)if x is not None else(0,0,0,0))
        for i,(raw,guess)in enumerate(zip(exceptions,guesses)):
            k=positions[i];mask=int.from_bytes(raw[k:k+5],'little');k+=5;assert mask<1<<39;fs=[]
            for t,new in enumerate(guess):
                if not(mask>>t)&1:fs.append(new);continue
                kind=raw[k];k+=1;m=x=y=0;assert kind<4
                if kind>=2:m=struct.unpack_from('<H',raw,k)[0];k+=2
                if kind:delta,k=point_delta(raw,k);x=new[2]+32*delta
                if kind==3:delta,k=point_delta(raw,k);y=x+32*delta
                fs.append((kind,m,x,y))
            assert fs==original and struct.unpack_from('<I',raw,k)[0]==code;positions[i]=k+4
            pred_pass[i]+=check(path,state,guess,code)[0]
        passes=[check(path,state,original,c)[0]for c in protocol['fixed_tree_codes']]
        for i,b in enumerate(passes):fixed_pass[i]+=b
        portfolio+=any(passes);numeric+=1
    assert pos==len(decoded['nodes']) and len(decoded['FS'])==273000 and len(decoded['trees'])==4000
    assert nodes==r['preorder_nodes_consumed'] and geometry.hexdigest()==r['sample_normalized_geometry_sha256']
    assert all(k==len(raw)for k,raw in zip(positions,exceptions))
    assert pred_pass==[x['predicted_FS_with_old_tree_pass']for x in r['rules']]
    assert fixed_pass==[x['original_FS_domain_valid_and_integer_check_passes']for x in r['fixed_tree_results']]
    assert portfolio==r['fixed_tree_portfolio_integer_check_passes']
    out={'scope':__doc__,'passed':True,'source_sha256':file_sha(Path(__file__)),'sample_input_sha256':file_sha(HERE/'sample-input.json.gz'),
      'numeric_leaves':numeric,'original_FS_checks_passed':1000,'exception_stream_exact_reconstructions':3000,
      'predicted_FS_with_old_Pruefer_recomputed_flow_and_scalar_guards_pass':pred_pass,
      'original_FS_with_fixed_tree_pass':fixed_pass,'original_FS_fixed_tree_portfolio_pass':portfolio,
      'all_analytic_domain_and_flow_conservation_guards_checked':True,'large_caches_required_for_this_replay':False,
      'original_cache_projection_membership_attested_by_export_hashes_not_full_file_replayed':True,
      'optimizer_calls':0,'Lean_invocations':0,'complete_source_under_two_MB':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-started}
    target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--export',action='store_true');args=ap.parse_args()
    assert __debug__
    export()if args.export else replay()
