"""Paired pre-contraction curvature experiment on the frozen 64-parent cohort."""
from pathlib import Path
from functools import reduce
from math import gcd
import gzip,hashlib,json,time
import numpy as np
import cover_correlated_curvature as curvature
import cover_correlated_api as correlated
import cover_contractor_api as newton
import cover_sublevel_obbt_api as obbt
import cover_gram_basin_api as gram
import cover_compact_codec as codec
import window_lower_global_cover as w
import window_direction_probe as baseline
HERE=Path(__file__).parent;g=w.g;SC=g.SC;DS=curvature.DS
sha=lambda b:hashlib.sha256(b).hexdigest()

def center_hessian(state,oracle):
    # Midpoint of the two feasible DBM prefix potentials, hence an actual
    # feasible point of the closed cell rather than independent span centers.
    potentials=[0]+[state[0][g.LOOK[0,j]]+state[1][g.LOOK[0,j]] for j in range(1,10)]
    H=np.zeros((9,9))
    for i,j,aw in g.TERMS:
        P=potentials[j]-potentials[i];z=g.LOOK[i,j];assert 2*state[0][z]<=P<=2*state[1][z]
        v,_=oracle.point(P);H[i:j,i:j]+=(aw/g.D)*float((v.l+v.u)/2)
    return H

def curvature_exclusion(state,oracle,seeds):
    free=[i for i in range(9) if state[0][i]>g.SEP]
    if not free:return None,{'free':0,'negative_midpoint':False,'directions_tested':0}
    H=center_hessian(state,oracle);values,vectors=np.linalg.eigh(H[np.ix_(free,free)])
    stats={'free':len(free),'midpoint_min_eigenvalue_hint':float(values[0]),'negative_midpoint':bool(values[0]<-1e-10),'directions_tested':0}
    if not stats['negative_midpoint']:return None,stats
    choices=set()
    def add(d):
        d=[int(v) if i in free else 0 for i,v in enumerate(d)]
        if not any(d):return
        common=reduce(gcd,map(abs,d));d=[v//common for v in d]
        if next(v for v in d if v)<0:d=[-v for v in d]
        if float(np.array(d)@H@np.array(d))/sum(v*v for v in d)<-1e-10:choices.add(tuple(d))
    for d in seeds:add(d)
    for col,ev in enumerate(values):
        if ev>=-1e-10:break
        v=vectors[:,col]
        for den in [1,16,256,65536]:
            d=[0]*9
            for k,i in enumerate(free):d[i]=round(v[k]/max(abs(v))*den)
            add(d)
    for i in free:
        d=[0]*9;d[i]=1;add(d)
        for j in free:
            if j<=i:continue
            for sign in [-1,1]:d=[0]*9;d[i]=1;d[j]=sign;add(d)
    choices=sorted(choices,key=lambda d:float(np.array(d)@H@np.array(d))/sum(v*v for v in d))
    data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,aw in g.TERMS]
    for d in choices:
        stats['directions_tested']+=1;upper,flow=curvature.exact_upper(state,data,list(d))
        if upper<0:
            return {'kind':'correlated_negative_curvature','direction':list(d),'direction_scale':1,'upper_numerator':str(upper),
              'denominator':str(2*SC*g.D*DS),'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
              'exact_flow':flow,'affine_terms':sum(row[4]=='affine' for row in data)},stats
    return None,stats

def old_pipeline(state,oracle,engine,registry):
    state=(state[0],state[1]);sublevel=None;steps=[];rec=None
    def cheap(state):
        basin=gram.gram_basin(state,'11/1250',registry)
        if basin:return {'kind':'Gram','result':basin}
        ex=baseline.exclusion(state,True)
        if ex is None:ex=correlated.correlated_exclusion(state,oracle)
        if ex:ex['derivative_grid_sha256']=oracle.sha;return {'kind':'stationary','result':ex}
        return None
    result={'kind':'reflection'} if state[1][8]<state[0][0] else cheap(state)
    if result is None:
        rec=w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=g.TARGET:result={'kind':'value','result':rec}
    if result is None:
        axis,_=g.cut(state,rec);refined,bounds=obbt.contract(state,g.TARGET,sorted(set(list(range(9))+[axis])),engine)
        if bounds:
            sublevel=codec.pack_obbt({'old_cell':state,'new_cell':refined,'certificates':bounds});state=refined
            if state is None:result={'kind':'sublevel_empty'}
            else:
                result=cheap(state)
                if result is None:
                    rec=w.certify(state)
                    if int(rec.get('floor_numerator','-1'))>=g.TARGET:result={'kind':'value','result':rec}
    if result is None:
        refined,ns,ex=newton.contract(state,8,oracle)
        if ns:
            steps=[codec.pack_newton(s) for s in ns];state=refined
            if state is None:result={'kind':'stationary_empty'}
            else:
                basin=gram.gram_basin(state,'11/1250',registry)
                if basin:result={'kind':'Gram','result':basin}
                elif ex:ex['derivative_grid_sha256']=oracle.sha;result={'kind':'stationary','result':ex}
                else:
                    result=cheap(state)
                    if result is None:
                        rec=w.certify(state)
                        if int(rec.get('floor_numerator','-1'))>=g.TARGET:result={'kind':'value','result':rec}
    out={'OBBT':sublevel,'Newton':steps,'outcome':codec.pack_leaf(result) if result else None,'final_state_sha256':codec.digest(state)}
    if result is None:
        axis,cut=g.cut(state,rec);out['branch']={'axis':axis,'cut':cut}
    return out

def main():
    start=time.monotonic();inputpath=HERE/'cover-curvature-parent64.input.json.gz';raw=inputpath.read_bytes();doc=json.loads(gzip.decompress(raw))
    oracle=curvature.CurvatureOracle(curvature.first.TaylorOracle(HERE/'cover_newjet.json'));engine=obbt.make_engine(w);registry=gram.make_gram_registry()
    frozen=json.loads((HERE/'cover-curvature-actual-active.json').read_bytes());seeds=[r['d'] for r in frozen['leaves']]
    startup=time.monotonic()-start;rows=[];counts={'parents':0,'negative_midpoint':0,'curvature_closed':0,'old_pipeline_closed':0,'extra_curvature_closed':0,'directions_tested':0}
    curv_time=control_time=0.;savings={k:0 for k in doc['cases'][0]['recorded_old_work']}
    for case in doc['cases']:
        state=tuple(case['before']);t=time.monotonic();result,stats=curvature_exclusion(state,oracle,seeds);ct=time.monotonic()-t;curv_time+=ct
        t=time.monotonic();control=old_pipeline(state,oracle.taylor,engine,registry);ot=time.monotonic()-t;control_time+=ot
        counts['parents']+=1;counts['negative_midpoint']+=stats['negative_midpoint'];counts['curvature_closed']+=bool(result)
        closed=control['outcome'] is not None;counts['old_pipeline_closed']+=closed;extra=bool(result) and not closed;counts['extra_curvature_closed']+=extra;counts['directions_tested']+=stats['directions_tested']
        if extra:
            for k,v in case['recorded_old_work'].items():savings[k]+=v
        rows.append({'path':case['path'],'curvature':result,'curvature_statistics':stats,'control':control,'new_over_control':extra,'curvature_seconds':ct,'control_seconds':ot})
        if counts['parents']%8==0:print(json.dumps({**counts,'curvature_seconds':curv_time,'control_seconds':control_time,'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'target':'11/1250','startup_seconds':startup,'counts':counts,
      'curvature_seconds':curv_time,'old_control_seconds':control_time,'recorded_old_work_avoided_by_extra_curvature':savings,
      'source_descendant_contractions_independently_replayed':False,'independent_new_proof_replay_passed':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-curvature-parent64.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
