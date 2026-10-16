"""Stdlib independent replay of one exact outer-relaxation feasible point.

Rebuild every old row/box from frozen scalar graph data, redo the one-shot
adjacent KKT projection, check 43,306 Fraction inequalities, and verify all
41 exact normalized residual LDL witnesses. No producer or solver import.
This is not an actual-kernel sublevel point or a zero-proportion result.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys,time
import cover_cross_moment_old_rows_replay as old

HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    started=time.monotonic();proofpath=HERE/'cover-residual-psd-rational-projection.json';inputpath=HERE/'cover-residual-psd-rational-inputs.json'
    scspath=HERE/'cover-residual-psd-bregman-full-cone.json';slabpath=HERE/'cover-residual-psd-pilot.json';parampath=ROOT/'research-20261016-followup/window_reweight_rational.json';tablepath=HERE/'cover_newjet.json'
    watched=[proofpath,inputpath,scspath,slabpath,parampath,tablepath,Path(__file__)];initial={p.relative_to(ROOT).as_posix():sha(p) for p in watched}
    proof=json.loads(proofpath.read_text());inputs=json.loads(inputpath.read_text());scs=json.loads(scspath.read_text());slabs=json.loads(slabpath.read_text());params=json.loads(parampath.read_text())
    assert proof['status']=='strict_exact_feasible_relaxation_point' and proof['path']==inputs['path']==scs['path']==slabs['path']
    for p,h in inputs['input_sha256_start'].items():assert sha(ROOT/p)==h
    state=inputs['cell'];terms=[tuple(r) for r in params['a_upper'] if r[2]];bs=params['b_numerators'];assert len(terms)==41 and all(v>123*SC//128 for v in state[0][:9])
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])];radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    x=[F(str(v)) for v in scs['raw_primal'][:464]];ys=[(x[i]-center[i])/radius[i] for i in range(9)]
    adj={r:next(t for t,(i,j,a) in enumerate(terms) if i==r and j==r+1) for r in range(9)}
    for r,e in adj.items():x[9+e]=-(bs[r]+sum(a*x[9+t] for t,(i,j,a) in enumerate(terms) if i<=r<j and t!=e))/F(terms[e][2])
    for s in range(9):
        for r,e in adj.items():x[95+41*s+e]=-(bs[r]*ys[s]+sum(a*x[95+41*s+t] for t,(i,j,a) in enumerate(terms) if i<=r<j and t!=e))/F(terms[e][2])
    assert x==list(map(F,proof['projected_464_rational_moments'])) and ys==list(map(F,proof['normalized_y']))
    for r in range(9):
        assert bs[r]+sum(a*x[9+t] for t,(i,j,a) in enumerate(terms) if i<=r<j)==0
        for s in range(9):assert bs[r]*ys[s]+sum(a*x[95+41*s+t] for t,(i,j,a) in enumerate(terms) if i<=r<j)==0
    checker=old.graph.GraphReplay(json.loads(tablepath.read_text()))
    integer,ubounds,stats=old.rebuild_old_rows(state,inputs['old_meta'],inputs['scalar_affine_data'],params,checker)
    assert [[list(ag),list(au),str(B)] for ag,au,B in integer]==inputs['old_integer_rows']
    assert [[str(l),str(u)] for l,u in ubounds]==inputs['u_bounds']
    model=old.exact.inputs(state,integer,inputs['old_meta'],ubounds,inputs['energy_packets']);assert len(model['rows'])==43306
    digest=hashlib.sha256();minimum=None;energy_slacks=[]
    for k,row in enumerate(model['rows']):
        digest.update(json.dumps([sorted((i,str(v)) for i,v in row['coeff'].items()),str(row['bound']),row['meta']],separators=(',',':')).encode())
        slack=row['bound']-sum(a*x[i] for i,a in row['coeff'].items());assert slack>=0,(k,row['meta'],slack)
        minimum=slack if minimum is None else min(minimum,slack)
        if row['meta'][0]=='energy':energy_slacks.append(str(slack))
    assert digest.hexdigest()==proof['retained_row_serialization_sha256']==inputs['retained_row_serialization_sha256']
    assert [[str(l),str(u)] for l,u in model['bounds']]==inputs['all_464_box_bounds']
    for v,(l,u) in zip(x,model['bounds']):assert l<=v<=u
    # Direct entry reconstruction has no SCS packing or sqrt(2).
    pairs=[(r,s) for r in range(9) for s in range(r,9)];hidx={p:50+k for k,p in enumerate(pairs)}
    X=[[F(1) for j in range(10)] for i in range(10)]
    for r in range(9):X[0][r+1]=X[r+1][0]=ys[r]
    for (r,s),k in hidx.items():X[r+1][s+1]=X[s+1][r+1]=x[k]
    assert len(proof['rational_LDL_blocks'])==len(slabs['scalar_slabs'])==41
    for e,(witness,slab,raw) in enumerate(zip(proof['rational_LDL_blocks'],slabs['scalar_slabs'],inputs['scalar_affine_data'])):
        assert e==witness['term'];i,j,_=terms[e];P,m0,m1,err,kind=raw;m0,m1,err=map(int,[m0,m1,err])
        beta=[F(m0,10**15)+F(m1,10**15)*(sum(center[i:j])-F(P,2*SC))]
        beta+=[F(m1,10**15)*radius[r] if i<=r<j else F(0) for r in range(9)];eps=F(err,10**15)
        assert beta==list(map(F,slab['beta'])) and eps==F(slab['epsilon'])>0
        z=[x[9+e]]+[x[95+41*r+e] for r in range(9)]
        residual=[(z[r]-sum(X[r][s]*beta[s] for s in range(10)))/eps for r in range(10)]
        N=[row+[residual[r]] for r,row in enumerate(X)]+[residual+[F(1)]]
        L=[[F(v) for v in row] for row in witness['unit_lower']];D=list(map(F,witness['positive_diagonal']))
        assert len(L)==len(D)==11 and all(len(row)==11 for row in L) and all(d>0 for d in D)
        assert all(L[i][i]==1 for i in range(11)) and all(L[i][j]==0 for i in range(11) for j in range(i+1,11))
        assert all(N[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(11)) for i in range(11) for j in range(11))
    variances=[x[hidx[r,r]]-ys[r]**2 for r in range(9)];assert all(v>0 for v in variances)
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in watched};assert final==initial
    result={'scope':__doc__,'input_sha256_start':initial,'input_sha256_end':final,'inputs_unchanged':'yes',
        'status':'strict_exact_feasible_outer_relaxation_verified','cases':1,'path':proof['path'],
        'first_and_mixed_KKT_equalities':90,'rational_rows_checked':43306,'finite_boxes_checked':464,
        'strict_positive_LDL_blocks_checked':41,'LDL_block_size':11,'minimum_exact_linear_slack':str(minimum),
        'two_energy_slacks':energy_slacks,'positive_position_variances':list(map(str,variances)),
        'old_graph_and_slab_ingredient_checks':stats,'pure_stdlib_replay':'yes',
        'actual_Fw_sublevel_counterexample':'no; position variances are strictly nonzero',
        'new_cell_exclusion':'none','complete_global_cover':'not_proven','new_zero_proportion':'not_proven',
        'elapsed_milliseconds':int((time.monotonic()-started)*1000)}
    out=HERE/'cover-residual-psd-rational-replay.json';assert not out.exists();out.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['status','rational_rows_checked','finite_boxes_checked','strict_positive_LDL_blocks_checked','elapsed_milliseconds']}),flush=True)

if __name__=='__main__':main()
