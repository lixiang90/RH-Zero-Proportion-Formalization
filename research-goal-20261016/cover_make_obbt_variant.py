"""Reproducibly extend the frozen Newton runner with sublevel epigraph OBBT."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def replace(source,old,new):
    assert source.count(old)==1,(old[:100],source.count(old))
    return source.replace(old,new)

def main():
    base=HERE/'window_newton_gram_cover_cached.py';s=base.read_text(encoding='utf8')
    s=replace(s,'Complete-domain discovery with KKT-only Newton contraction and Gram basins.',
      'Complete-domain discovery with sublevel epigraph OBBT and KKT Newton contraction.')
    s=replace(s,'Contractions are stored in a separate per-path map.',
      'OBBT preserves only F<target points; Newton preserves their original KKT conditions.\nBoth operations have separate maps, applied in the fixed OBBT-before-Newton order.\nContractions are stored in a separate per-path map.')
    s=replace(s,'import cover_gram_basin_api as gram','import cover_gram_basin_api as gram\nimport cover_sublevel_obbt_api as obbt')
    s=replace(s,"default=HERE/'window-newton-gram-cover.json'","default=HERE/'window-obbt-newton-cover.json'")
    s=replace(s,'oracle=correlated.make_correlated_oracle(args.oracle);registry=gram.make_gram_registry()',
      'oracle=correlated.make_correlated_oracle(args.oracle);registry=gram.make_gram_registry();obbt_engine=obbt.make_engine(w)')
    s=replace(s,"HERE/'cover-newwindow-gram.json',ROOT/'research-20261016-w10-cert/generate.py',",
      "HERE/'cover-newwindow-gram.json',HERE/'cover_sublevel_obbt_api.py',HERE/'cover_sublevel_obbt.py',\n      HERE/'cover_sublevel_contractor.py',ROOT/'research-20261016-w10-cert/generate.py',")
    s=replace(s,'modules=[Path(__file__),Path(w.__file__),Path(direction.__file__)',
      'modules=[Path(__file__),Path(high.__file__),Path(low.__file__),Path(w.__file__),Path(direction.__file__)')
    s=replace(s,"'coercive global minimum and KKT/directional transfer','KKT contraction preservation','all 69 actual Gram basin transfers'",
      "'coercive global minimum and KKT/directional transfer','KKT contraction preservation',\n            'sublevel epigraph mixture and exact-flow Lagrange transfer','all 69 actual Gram basin transfers'")
    s=replace(s,"todo=[(w.root(),0,'r')];accepted=[];branches=[];contractions={};checked=0;depthmax=0;resumed=None;inherited_supports={}",
      "todo=[(w.root(),0,'r')];accepted=[];branches=[];contractions={};sublevel={};checked=0;depthmax=0;resumed=None;inherited_supports={}")
    s=replace(s,"contractions=old.get('contractions',{});checked=old['checked'];depthmax=old['maxdepth']",
      "contractions=old.get('contractions',{});sublevel=old.get('sublevel_contractions',{});checked=old['checked'];depthmax=old['maxdepth']")
    s=replace(s,"['value','stationary','reflection','Gram','stationary_empty']",
      "['value','stationary','reflection','Gram','stationary_empty','sublevel_empty']")
    s=replace(s,"'format':'KKT-only-Newton-Gram-v1'","'format':'RelevantBelow-KKT-OBBT-v1'")
    s=replace(s,"'contraction_semantics':'Only original global-minimum KKT points survive. NOT pointwise PCell coverage.',",
      "'sublevel_contraction_paths':len(sublevel),'sublevel_bounds':sum(len(v['certificates']) for v in sublevel.values()),\n          'obbt_inputs':obbt.source_hashes(),\n          'contraction_semantics':'Only F<target points with original global-minimum KKT conditions survive. NOT pointwise PCell coverage.',")
    s=replace(s,"'accepted':accepted,'branches':branches,'contractions':contractions,",
      "'accepted':accepted,'branches':branches,'contractions':contractions,'sublevel_contractions':sublevel,")
    needle='''            if kind is None:
                refined,steps,ex=newton.contract(state,args.max_rounds,oracle)'''
    addition='''            if kind is None:
                assert rec is not None
                axis,_=g.cut(state,rec)
                axes=sorted(set(list(range(9))+[axis]))
                refined,bounds=obbt.contract(state,g.TARGET,axes,obbt_engine)
                if bounds:
                    assert path not in sublevel
                    sublevel[path]={'old_cell':state,'new_cell':refined,'certificates':bounds}
                    state=refined
                    if state is None:kind,result='sublevel_empty',{'reason':'No F<target point survives epigraph OBBT'}
                    else:
                        kind,result=cheap(state)
                        if kind is None:
                            rec=w.certify(state)
                            if int(rec.get('floor_numerator','-1'))>=g.TARGET:kind,result='value',rec
            if kind is None:
                refined,steps,ex=newton.contract(state,args.max_rounds,oracle)'''
    s=replace(s,needle,addition)
    s=replace(s,"'contraction_paths':len(contractions),'seconds':time.monotonic()-start}),flush=True)",
      "'contraction_paths':len(contractions),'sublevel_paths':len(sublevel),'seconds':time.monotonic()-start}),flush=True)")
    s=replace(s,"['checked','accepted_count','counts','contraction_paths','contraction_steps','unresolved_count','maxdepth','seconds']",
      "['checked','accepted_count','counts','contraction_paths','contraction_steps','sublevel_contraction_paths','sublevel_bounds','unresolved_count','maxdepth','seconds']")
    target=HERE/'window_obbt_newton_cover.py';target.write_text(s,encoding='utf8')

    replay=HERE/'window_newton_gram_replay.py';r=replay.read_text(encoding='utf8')
    r=replace(r,'import cover_gram_basin_api as gram','import cover_gram_basin_api as gram\nimport cover_sublevel_obbt_verify_api as obbt')
    r=replace(r,"data['format']=='KKT-only-Newton-Gram-v1'","data['format']=='RelevantBelow-KKT-OBBT-v1'")
    r=replace(r,"contractions=data['contractions']","contractions=data['contractions'];sublevel=data['sublevel_contractions']")
    r=replace(r,"'contraction_steps':0}","'contraction_steps':0,'sublevel_paths':0,'sublevel_bounds':0,'sublevel_empty':0}")
    r=replace(r,"todo=[(w.root(),'r')];seen=set();usedcontractions=set();minimum=None",
      "todo=[(w.root(),'r')];seen=set();usedcontractions=set();usedsublevel=set();minimum=None")
    r=replace(r,'        if path in contractions:', '''        if path in sublevel:
            usedsublevel.add(path);counts['sublevel_paths']+=1;counts['sublevel_bounds']+=len(sublevel[path]['certificates'])
            state=obbt.verify_step(state,sublevel[path],g.TARGET)
            if state is None:
                assert path not in contractions and path in leaves and leaves[path]['kind']=='sublevel_empty'
                counts['sublevel_empty']+=1
                continue
        if path in contractions:''')
    r=replace(r,"usedcontractions==set(contractions)","usedcontractions==set(contractions) and usedsublevel==set(sublevel)")
    r=replace(r,"assert data['checked']==len(branches)+len(leaves)",
      "assert counts['sublevel_paths']==data['sublevel_contraction_paths'] and counts['sublevel_bounds']==data['sublevel_bounds']\n    assert data['checked']==len(branches)+len(leaves)")
    r=replace(r,"'KKT_only_contractions_replayed':True", "'sublevel_only_OBBT_replayed':True,'KKT_only_contractions_replayed':True")
    r=replace(r,"default=HERE/'window-newton-gram-replay.json'","default=HERE/'window-obbt-newton-replay.json'")
    r=replace(r,"independent_verifier_sources=newton.source_hashes()", "independent_verifier_sources={**newton.source_hashes(),**obbt.source_hashes()}")
    verifier=HERE/'window_obbt_newton_replay.py';verifier.write_text(r,encoding='utf8')
    receipt={'scope':__doc__,'base_runner_sha256':hashlib.sha256(base.read_bytes()).hexdigest(),'base_replayer_sha256':hashlib.sha256(replay.read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'new_runner_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
      'new_replayer_sha256':hashlib.sha256(verifier.read_bytes()).hexdigest(),'complete_global_cover':False,'ordinary_Lean_compiled':False}
    (HERE/'cover-obbt-runner-generated.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt))
if __name__=='__main__':main()
