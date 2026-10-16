"""Freeze at most 64 depth-24 branch parents from the located deep subtree."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,time
from cover_compact_checkpoint import Stream
import cover_compact_codec as codec
import window_lower_global_cover as w
from cover_correlated_replay import a
HERE=Path(__file__).parent;ROOT=HERE.parent;PREFIX='r00100000';DEPTH=24
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    start=time.monotonic();stream=Stream(HERE/'window-compact-obbt-cover.json');stream.token('{');meta={};branches=[];leaves=[]
    selected=[];needed=set();wanted=set();obbt={};newton={};work={}
    def tag(p):return p[:DEPTH+1] if len(p)>=DEPTH+1 and p[:DEPTH+1] in wanted else None
    def mapping(kind,out):
        stream.token('{')
        while stream.peek()!='}':
            p=stream.value();stream.token(':');value=stream.value()
            if p in needed:out[p]=value
            root=tag(p)
            if root:
                if kind=='OBBT':work[root]['OBBT_paths']+=1;work[root]['OBBT_bounds']+=len(value['b'])
                else:work[root]['Newton_paths']+=1;work[root]['Newton_steps']+=len(value)
            if stream.peek()!=',':break
            stream.token(',')
        stream.token('}')
    while stream.peek()!='}':
        key=stream.value();stream.token(':')
        if key=='accepted':stream.array(lambda r:leaves.append((r['path'],r['kind'])))
        elif key=='branches':
            stream.array(lambda r:branches.append(r))
            candidates=[r for r in branches if r['path'].startswith(PREFIX) and len(r['path'])==DEPTH+1]
            pool=candidates[-512:];n=min(64,len(pool));assert n>0
            selected=[pool[k*(len(pool)-1)//max(1,n-1)]['path'] for k in range(n)]
            wanted=set(selected);needed={p[:k] for p in selected for k in range(1,len(p)+1)}
            work={p:{'branches':0,'accepted_leaves':0,'OBBT_paths':0,'OBBT_bounds':0,'Newton_paths':0,'Newton_steps':0} for p in selected}
            for r in branches:
                root=tag(r['path'])
                if root:work[root]['branches']+=1
            for p,kind in leaves:
                root=tag(p)
                if root:work[root]['accepted_leaves']+=1
            meta['selection']={'prefix':PREFIX,'depth':DEPTH,'all_candidate_count':len(candidates),'latest_pool_count':len(pool),'sample_size':n,
              'rule':'Uniform discovery-order sample from latest at most 512 same-depth existing branch parents; no curvature-based selection.'}
        elif key=='contractions':mapping('Newton',newton)
        elif key=='sublevel_contractions':mapping('OBBT',obbt)
        elif key in ['tangent_data','unresolved']:stream.value()
        else:meta[key]=stream.value()
        if stream.peek()!=',':break
        stream.token(',')
    stream.token('}');assert stream.peek()=='';stream.file.close()
    assert meta['target']=='11/1250' and meta['root']==[list(v) for v in w.root()]
    for name,digest in meta['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    branchmap={r['path']:r for r in branches if r['path'] in needed};assert set(branchmap)==needed
    states={};todo=[('r',meta['root'])];before={};historical={}
    while todo:
        p,state=todo.pop()
        if p in wanted:before[p]=state
        if p in obbt:state=codec.unpack_obbt(state,obbt[p],w.g.TARGET,w)['new_cell']
        for row in newton.get(p,[]):state=codec.unpack_newton(state,row,w)['new_cell']
        assert state is not None
        if p in wanted:historical[p]=state;continue
        b=branchmap[p]
        for bit in ['0','1']:
            if p+bit in needed:
                child=a.child(state,b['axis'],b['cut'],bit=='0');assert child is not None;todo.append((p+bit,child))
    assert set(before)==wanted
    cases=[{'path':p,'before':before[p],'historical_refined':historical[p],'source_branch':branchmap[p],
      'recorded_old_work':work[p]} for p in selected]
    data={'scope':__doc__,'source_checkpoint_sha256':stream.sha.hexdigest(),'source_checkpoint_bytes':stream.size,
      'source_checkpoint_checked':meta['checked'],'input_sha256':meta['input_sha256'],'selection':meta['selection'],
      'target':meta['target'],'root':meta['root'],'branches':branchmap,'OBBT':obbt,'Newton':newton,'cases':cases,
      'source_descendant_branches':[r for r in branches if tag(r['path'])],
      'source_descendant_contractions_independently_replayed':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode();packed=gzip.compress(raw,compresslevel=9,mtime=0)
    target=HERE/'cover-curvature-parent64.input.json.gz';target.write_bytes(packed)
    header={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(packed),'uncompressed_sha256':sha(raw),
      'compressed_bytes':len(packed),'uncompressed_bytes':len(raw),'source_checked':meta['checked'],'selection':meta['selection'],
      'ancestor_and_parent_nodes':len(needed),'captured_OBBT_paths':len(obbt),'captured_Newton_paths':len(newton),
      'selected_recorded_descendant_totals':{key:sum(r['recorded_old_work'][key] for r in cases) for key in work[selected[0]]},
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-curvature-parent64-snapshot.json').write_text(json.dumps(header,indent=2)+'\n',encoding='utf8');print(json.dumps(header),flush=True)
if __name__=='__main__':main()
