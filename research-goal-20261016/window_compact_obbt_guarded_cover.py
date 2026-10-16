"""Complete-domain OBBT/Newton discovery with compact, lossless witnesses.

OBBT preserves only F<target points; Newton preserves their original KKT conditions.
Both operations have separate maps, applied in the fixed OBBT-before-Newton order.
Contractions are stored in a separate per-path map. A contraction preserves
only points satisfying the original global-minimum KKT conditions; it is
NOT a pointwise PCell cover. Every branch and leaf after contraction refers
to the refined cell. Complete finite discovery still requires all analytic,
minimizer and scalar-Taylor Lean bridges before any zeta-bound claim.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,os,time
import window_global_cover as high
import window_lower_global_cover as low
import window_direction_probe as direction
import cover_correlated_api as correlated
import cover_contractor_api as newton
import cover_gram_basin_api as gram
import cover_sublevel_obbt_api as obbt
import cover_compact_codec as codec
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--floor',choices=['11/1250','221/25000'],default='11/1250')
    ap.add_argument('--resume',type=Path);ap.add_argument('--max-nodes',type=int,default=2000000)
    ap.add_argument('--max-rounds',type=int,default=8);ap.add_argument('--oracle',type=Path,default=HERE/'cover_newjet.json')
    ap.add_argument('--output',type=Path,default=HERE/'window-compact-obbt-cover.json');args=ap.parse_args()
    args.output=args.output.resolve();args.oracle=args.oracle.resolve()
    if args.resume:args.resume=args.resume.resolve()
    w=low if args.floor=='11/1250' else high;g=w.g;oracle_sha=direction.install_grid(args.oracle)
    oracle=correlated.make_correlated_oracle(args.oracle);registry=gram.make_gram_registry();obbt_engine=obbt.make_engine(w)
    assert direction.g.TERMS==g.TERMS and direction.g.BS==g.BS and direction.g.SEP==g.SEP
    assert newton.core.g.TERMS==g.TERMS and newton.core.g.BS==g.BS and newton.core.g.SEP==g.SEP
    modules=[Path(__file__),Path(high.__file__),Path(low.__file__),Path(w.__file__),Path(direction.__file__),Path(w.ik.__file__),w.PARAM,args.oracle,
      HERE/'window_interval_kernel.json',HERE/'cover_correlated_api.py',HERE/'cover_correlated_direction.py',
      HERE/'cover_contractor_api.py',HERE/'cover_newton_contractor.py',HERE/'cover_gram_basin_api.py',
      HERE/'cover-newwindow-gram.json',HERE/'cover_sublevel_obbt_api.py',HERE/'cover_sublevel_obbt.py',
      HERE/'cover_sublevel_contractor.py',ROOT/'research-20261016-w10-cert/generate.py',
      ROOT/'research-20261016-followup/global_periodic_upper_bound.py',
      HERE/'cover_compact_codec.py',HERE/'cover_flow_basis.py',HERE/'cover_correlated_replay.py',HERE/'cover_contractor_verify.py']
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in modules}
    todo=[(w.root(),0,'r')];accepted=[];branches=[];contractions={};sublevel={};checked=0;depthmax=0;resumed=None;inherited_supports={}
    if args.resume:
        raw=args.resume.read_bytes();old=json.loads(raw)
        for name,digest in old['input_sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
        assert old['target']==args.floor and old['root']==[list(x) for x in w.root()]
        if old['format']=='RelevantBelow-KKT-OBBT-v1':old=codec.pack_document(old)
        assert old['format']=='RelevantBelow-KKT-OBBT-compact-v2'
        resumed={'path':str(args.resume.relative_to(ROOT)),'sha256':hashlib.sha256(raw).hexdigest(),'checked':old['checked']}
        todo=[(x['state'],x['depth'],x['path']) for x in old['unresolved']];accepted=old['accepted'];branches=old['branches']
        contractions=old.get('contractions',{});sublevel=old.get('sublevel_contractions',{});checked=old['checked'];depthmax=old['maxdepth']
        for p,*values in old.get('tangent_data',[]):
            w.USED_SUPPORTS.add(p);inherited_supports[p]=values
    start=time.monotonic();initial=checked
    def save():
        assert hashes=={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in modules}
        counts={kind:sum(row['kind']==kind for row in accepted) for kind in ['value','stationary','reflection','Gram','stationary_empty','sublevel_empty']}
        out={'scope':__doc__,'format':'RelevantBelow-KKT-OBBT-compact-v2','input_sha256':hashes,'resumed_from':resumed,'target':args.floor,
          'SC':g.SC,'denominator':str(g.DEN),'separation':'123/128','pid':os.getpid(),'root':w.root(),'checked':checked,
          'maxdepth':depthmax,'accepted_count':len(accepted),'counts':counts,'unresolved_count':len(todo),'seconds':time.monotonic()-start,
          'derivative_grid_sha256':oracle_sha,'correlated_api_inputs':correlated.api_sources(oracle),'contractor_api_inputs':newton.api_sources(oracle),
          'Gram_certificate_sha256':registry['sha256'],'contraction_paths':len(contractions),'contraction_steps':sum(len(v) for v in contractions.values()),
          'sublevel_contraction_paths':len(sublevel),'sublevel_bounds':sum(len(v['b']) for v in sublevel.values()),
          'obbt_inputs':obbt.source_hashes(),
          'contraction_semantics':'Only F<target points with original global-minimum KKT conditions survive. NOT pointwise PCell coverage.',
          'analytic_obligations':['actual profile and derivative Taylor grid','sixteen actual convex/positive-curvature core certificates',
            'actual scalar point Taylor value/derivative bridges','actual order24 global derivative bound',
            'coercive global minimum and KKT/directional transfer','KKT contraction preservation',
            'sublevel epigraph mixture and exact-flow Lagrange transfer','all 69 actual Gram basin transfers'],
          'analytic_obligations_Lean_proven':False,'global_floor_Lean_proven':False,'new_zero_proportion_proven':False,
          'accepted':accepted,'branches':branches,'contractions':contractions,'sublevel_contractions':sublevel,
          'unresolved':[{'state':s,'depth':d,'path':p} for s,d,p in todo],
          'tangent_data':[[p,*(inherited_supports[p] if p in inherited_supports else w.original_support(p))] for p in sorted(w.USED_SUPPORTS)]}
        temp=args.output.with_suffix('.partial');temp.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
        for attempt in range(80):
            try:temp.replace(args.output);break
            except PermissionError:
                if attempt==79:raise
                time.sleep(.25)
        return out
    def cheap(state):
        basin=gram.gram_basin(state,args.floor,registry)
        if basin:return 'Gram',basin
        ex=direction.exclusion(state,True)
        if ex is None:ex=correlated.correlated_exclusion(state,oracle)
        if ex:
            ex['derivative_grid_sha256']=oracle_sha
            return 'stationary',ex
        return None,None
    while todo and checked-initial<args.max_nodes:
        state,depth,path=todo.pop();state=(state[0],state[1]);checked+=1;depthmax=max(depthmax,depth)
        if state[1][8]<state[0][0]:accepted.append({'path':path,'depth':depth,'kind':'reflection'})
        else:
            kind,result=cheap(state);rec=None
            if kind is None:
                rec=w.certify(state)
                if int(rec.get('floor_numerator','-1'))>=g.TARGET:kind,result='value',rec
            if kind is None:
                assert rec is not None
                axis,_=g.cut(state,rec)
                axes=sorted(set(list(range(9))+[axis]))
                refined,bounds=obbt.contract(state,g.TARGET,axes,obbt_engine)
                if bounds:
                    assert path not in sublevel
                    sublevel[path]=codec.pack_obbt({'old_cell':state,'new_cell':refined,'certificates':bounds})
                    state=refined
                    if state is None:kind,result='sublevel_empty',{'reason':'No F<target point survives epigraph OBBT'}
                    else:
                        kind,result=cheap(state)
                        if kind is None:
                            rec=w.certify(state)
                            if int(rec.get('floor_numerator','-1'))>=g.TARGET:kind,result='value',rec
            if kind is None:
                refined,steps,ex=newton.contract(state,args.max_rounds,oracle)
                if steps:
                    contractions.setdefault(path,[]).extend(codec.pack_newton(step) for step in steps);state=refined
                    if state is None:kind,result='stationary_empty',{'reason':'KKT-only contraction closure is empty'}
                    else:
                        basin=gram.gram_basin(state,args.floor,registry)
                        if basin:kind,result='Gram',basin
                        elif ex:
                            ex['derivative_grid_sha256']=oracle_sha;kind,result='stationary',ex
                        else:
                            kind,result=cheap(state)
                            if kind is None:
                                rec=w.certify(state)
                                if int(rec.get('floor_numerator','-1'))>=g.TARGET:kind,result='value',rec
            if kind is not None:accepted.append(codec.pack_leaf({'path':path,'depth':depth,'kind':kind,'result':result}))
            else:
                assert state is not None and rec is not None
                ax,q=g.cut(state,rec);assert state[0][ax]<q<state[1][ax];branches.append({'path':path,'axis':ax,'cut':q})
                for suffix,upper in [('1',False),('0',True)]:
                    child=g.split(state,ax,q,upper)
                    if child is not None:todo.append((child,depth+1,path+suffix))
        if checked%100==0:
            print(json.dumps({'checked':checked,'accepted':len(accepted),'pending':len(todo),'contraction_paths':len(contractions),'sublevel_paths':len(sublevel),'seconds':time.monotonic()-start}),flush=True)
        if checked%500==0:save()
    out=save();print(json.dumps({k:out[k] for k in ['checked','accepted_count','counts','contraction_paths','contraction_steps','sublevel_contraction_paths','sublevel_bounds','unresolved_count','maxdepth','seconds']}),flush=True)
if __name__=='__main__':main()
