"""Research-only concave-phase chord minorants on failed W10 parent cells.

Concavity is located numerically, NOT certified by interval arithmetic or
Lean. LP comparisons below are hypothetical and never enter the immutable
certificate. Existing endpoint values are lower bounds from the frozen
PT/PV-LB library; a second comparison uses floating true endpoint values.
"""
from pathlib import Path
import argparse,bisect,hashlib,json,math,time
import numpy as np
from scipy.optimize import brentq,linprog
import ordered_generate as o
import hessian_boxes as curvature
from reduce_proof_input import Stream,sha
g=o.g;HERE=Path(__file__).parent
INC=np.array([[int(i<=r<j) for r in range(9)] for i,j,a in g.TERMS],float)
OBJ=np.r_[np.array(g.BS)/g.D,[a/g.D for i,j,a in g.TERMS]]
POINT={p:(l,u,v) for p,l,u,v,*_ in g.PT}

def branches_only(path):
    source=Stream(path);source.eat('{');first=True
    while source.peek()!='}':
        if not first:source.eat(',')
        key=source.value();source.eat(':')
        if key=='branches':
            result={r['path']:r for r in source.array()};source.close();return result
        source.value();first=False
    raise AssertionError('No branch array')

def concavity_phases(upper):
    grid=np.linspace(0,upper,math.ceil(upper*2048)+1);values=curvature.w2(grid)
    roots=[]
    for k in np.flatnonzero(values[:-1]*values[1:]<0):
        roots.append(float(brentq(lambda x:float(curvature.w2(np.array([x]))[0]),grid[k],grid[k+1],xtol=1e-13)))
    edges=[0.]+roots+[upper]
    return [{'lower':l,'upper':u,'midpoint_w2':float(curvature.w2(np.array([(l+u)/2]))[0])}
            for l,u in zip(edges,edges[1:]) if curvature.w2(np.array([(l+u)/2]))[0]<0]

def endpoint(q):
    pv=g.f.lb(q,q+1);kind='frozen_PV_LB_on_endpoint_microinterval' if pv else 'nonnegative_zero'
    if q in POINT and POINT[q][2]>pv:pv=POINT[q][2];kind='frozen_PT_point_value'
    return pv/10**10,{'coordinate_SC':q,'numerator':pv,'denominator':10**10,'source':kind}

def model(state):
    lo,hi=state;rows=[];rhs=[]
    for t,(i,j,a) in enumerate(g.TERMS):
        z=g.LOOK[i,j]
        for const,slope,p in g.lines(lo[z],hi[z],sum(lo[i:j])):
            if p==-2:continue
            row=np.zeros(9+len(g.TERMS));row[i:j]=slope/10**10;row[9+t]=-1
            rows.append(row);rhs.append(-const/g.WD)
    for (i,j),l,u in zip(g.ALL,lo,hi):
        row=np.zeros(len(OBJ));row[i:j]=1;rows.extend([row,-row]);rhs.extend([u/g.SC,-l/g.SC])
    return rows,rhs

def solve(rows,rhs):
    fit=linprog(OBJ,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*9+[(0,None)]*len(g.TERMS),method='highs',
        options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
    assert fit.success,fit.message
    return float(fit.fun)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=100);args=ap.parse_args()
    source=HERE/'ordered-proof-input.json';source_sha=sha(source)
    frozen_names=['generate.py','relative_codec.py','compact_thin.py','tree_flow.py','ordered_generate.py','hessian_boxes.py']
    frozen={name:sha(HERE/name) for name in frozen_names};started=time.monotonic()
    branches=branches_only(source);all_paths=sorted(branches);paths=[p for p in all_paths if p not in ('r','r1')]
    picked={paths[k] for k in np.linspace(0,len(paths)-1,min(args.limit,len(paths)),dtype=int)}
    needed={p[:k] for p in picked for k in range(1,len(p)+1)};states={};todo=[('r',g.root())]
    while todo:
        path,state=todo.pop()
        if path not in needed:continue
        state,cuts=o.normalize(state)
        if path in picked:states[path]=state
        node=branches[path];axis=node['axis'];q=node['cut']
        for digit,upper in [('1',False),('0',True)]:
            if path+digit in needed:todo.append((path+digit,o.rawsplit(state,axis,q,upper)))
    phases=concavity_phases(max(g.root()[1])/g.SC+.01);results=[]
    for path,state in sorted(states.items()):
        old=g.certify(state,True);old_integer=int(old['mcheck_numerator'])>=g.TARGET
        rows,rhs=model(state);baseline=solve(rows,rhs);assert abs(baseline-old['lp_floor'])<1e-9
        table_rows=list(rows);table_rhs=list(rhs);true_rows=list(rows);true_rhs=list(rhs);chords=[]
        lo,hi=state
        for t,(i,j,a) in enumerate(g.TERMS):
            z=g.LOOK[i,j];l=lo[z]/g.SC;u=hi[z]/g.SC
            if u<=l:continue
            phase=next((p for p in phases if p['lower']+1e-8<=l and u<=p['upper']-1e-8),None)
            if phase is None:continue
            grid=np.linspace(l,u,max(65,math.ceil((u-l)*2048)+1));sample_max=float(max(curvature.w2(grid)))
            if sample_max>=-1e-9:continue
            vl,dl=endpoint(lo[z]);vu,du=endpoint(hi[z]);true=g.kernel(np.array([l,u]))
            for vals,out_rows,out_rhs in [((vl,vu),table_rows,table_rhs),(true,true_rows,true_rhs)]:
                slope=float((vals[1]-vals[0])/(u-l));intercept=float(vals[0]-slope*l)
                row=np.zeros(len(OBJ));row[i:j]=slope;row[9+t]=-1;out_rows.append(row);out_rhs.append(-intercept)
            chords.append({'term':t,'edge':[i,j],'cell_lower':l,'cell_upper':u,'assumed_concavity_phase':phase,
                'sampled_w2_maximum':sample_max,'left_endpoint':dl,'right_endpoint':du,
                'floating_true_endpoint_values':true.tolist(),
                'concavity_formally_verified':False,'floating_endpoint_values_formally_verified':False})
        table=solve(table_rows,table_rhs) if chords else baseline
        ideal=solve(true_rows,true_rhs) if chords else baseline
        results.append({'path':path,'old_integer_check_passed':old_integer,'baseline_lp_floor':baseline,
            'table_endpoint_chord_lp_floor':table,'true_endpoint_chord_lp_floor':ideal,
            'table_lp_gain':table-baseline,'ideal_lp_gain':ideal-baseline,'chord_count':len(chords),
            'baseline_float_closed':baseline>=.00866+1e-9,'table_chord_hypothetically_closed':table>=.00866+1e-9,
            'true_chord_hypothetically_closed':ideal>=.00866+1e-9,
            'old_subtree_leaf_count':bisect.bisect_left(all_paths,path+'2')-bisect.bisect_left(all_paths,path)+1,
            'chords':chords})
    failed=[r for r in results if not r['old_integer_check_passed']]
    stats={'scope':__doc__,'source_sha256':source_sha,'frozen_helper_sha256':frozen,'sampled_parents':len(results),
        'confirmed_failed_parents':len(failed),'baseline_float_closed':sum(r['baseline_float_closed'] for r in failed),
        'parents_with_concave_chords':sum(bool(r['chords']) for r in failed),
        'table_endpoint_hypothetical_closures':sum(r['table_chord_hypothetically_closed'] for r in failed),
        'true_endpoint_hypothetical_closures':sum(r['true_chord_hypothetically_closed'] for r in failed),
        'table_new_closures_over_baseline':sum(r['table_chord_hypothetically_closed'] and not r['baseline_float_closed'] for r in failed),
        'true_new_closures_over_baseline':sum(r['true_chord_hypothetically_closed'] and not r['baseline_float_closed'] for r in failed),
        'maximum_table_lp_gain':max(r['table_lp_gain'] for r in failed),'maximum_ideal_lp_gain':max(r['ideal_lp_gain'] for r in failed),
        'largest_hypothetically_replaced_subtree_leaves':max((r['old_subtree_leaf_count'] for r in failed if r['table_chord_hypothetically_closed']),default=0),
        'formalization_still_required':['Prove w second derivative is nonpositive throughout each selected exact cell interval.',
            'Prove the concave-function chord lower-bound lemma and instantiate the frozen endpoint lower values.',
            'Extend a sound affine leaf checker before treating any new chord-supported LP result as a certificate.'],
        'concavity_and_chords_formally_verified':False,'new_integer_or_lean_certificates_created':False,
        'probe_script_sha256':sha(Path(__file__)),'seconds':time.monotonic()-started}
    assert sha(source)==source_sha and frozen=={name:sha(HERE/name) for name in frozen_names}
    (HERE/'concave-chord-probe.json').write_text(json.dumps({'stats':stats,'numerical_concavity_phases':phases,'parents':results},indent=2)+'\n')
    print(json.dumps(stats),flush=True)
if __name__=='__main__':main()
