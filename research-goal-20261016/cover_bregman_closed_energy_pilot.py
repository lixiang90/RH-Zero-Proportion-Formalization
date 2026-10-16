"""One final fixed-cell LP using the analytically eliminated affine h row.

Original model and original midpoint energy, plus one closed Bregman
quadratic. No fixed-h sampled rows, reverse rows, residual PSD cuts, new
point or full cover. Exactly one HiGHS-IPM call, time limit 45 seconds.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time,traceback
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;V=base.V;SC=base.SC;OUT=HERE/'cover-bregman-closed-energy-pilot.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert not OUT.exists();started=time.monotonic();source=HERE/'cover-cross-moment-remaining-six.json';closed=HERE/'cover-bregman-closed-primal-check.json'
    prior=json.loads(source.read_bytes())['rows'][0];closed_data=json.loads(closed.read_bytes());state=tuple(prior['cell'])
    assert prior['path']==closed_data['path'] and closed_data['closed_row_strictly_cuts_latest_primal']
    assert all(v>123*SC//128 for v in state[0][:9]);packets=[prior['energy_packets'][0],closed_data['proposed_KKT_energy_packet']]
    table=HERE/'cover_newjet.json';watched=[source,closed,table,Path(__file__),Path(base.__file__),Path(base.old.__file__),Path(exact.__file__),base.g.PAR]
    initial={str(p.relative_to(HERE.parent)).replace('\\','/'):sha(p) for p in watched}
    out={'scope':__doc__,'path':prior['path'],'cell':prior['cell'],'target':'11/1250','input_sha256_start':initial,
        'energy_packets':packets,'all_nine_coordinates_strictly_free':True,'LP_method':'highs-ipm','LP_time_limit_seconds':45,
        'maximum_LP_calls':1,'fixed_h_rows':0,'reverse_rows':0,'PSD_cuts':0,'new_scalar_points':0,
        'strict_integer_certificate':None,'actual_closed_Bregman_bridge_formalized':False,'actual_Lean_exclusion_proven':False,
        'complete_global_cover':False,'new_zero_proportion_proven':False}
    def save():
        out['seconds']=time.monotonic()-started;out['input_sha256_end']={str(p.relative_to(HERE.parent)).replace('\\','/'):sha(p) for p in watched}
        assert out['input_sha256_end']==initial;out['all_inputs_unchanged']=True
        OUT.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    out['phase']='building_base';save();taylor=base.old.context.curvature.first.TaylorOracle(table);graph=base.old.GraphOracle(table)
    rr,bb,integer,meta,data,obj,stats=base.old.build(state,taylor,graph,True)
    original=base.linprog;last=None;base_nr=None
    def solver(c,**kw):
        nonlocal last,base_nr
        base_nr=kw['A_ub'].shape[0];erows=[];rhs=[];scales=[]
        for p in packets:
            row=np.zeros(V)
            for k,v in p['row']:row[k]=float(F(v))
            B=float(F(p['bound']));scale=max(1.,max(abs(row)),abs(B));erows.append(row/scale);rhs.append(B/scale);scales.append(scale)
        A=vstack([kw['A_ub'],csr_matrix(erows)],format='csr');B=np.r_[kw['b_ub'],rhs]
        column=np.r_[np.zeros(base_nr),[-1/scale for scale in scales]]
        out['phase']='LP_running';save();tick=time.monotonic()
        fit=linprog(np.r_[np.zeros(V),1.],A_ub=hstack([A,csr_matrix(column[:,None])],format='csr'),b_ub=B,
            bounds=kw['bounds']+[(0,None)],method='highs-ipm',
            options={'time_limit':45.,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-8})
        last=fit;out['LP']={'status':int(fit.status),'success':bool(fit.success),'message':str(fit.message),
            'LP_seconds':time.monotonic()-tick,'base_rows':base_nr,'energy_rows':2}
        if fit.success:
            out['LP'].update({'energy_slack_hint':float(fit.fun),'raw_primal_with_slack':fit.x.tolist(),
                'positive_row_dual_weights':[[i,float(-v)] for i,v in enumerate(fit.ineqlin.marginals) if -v>1e-14],
                'minimum_scaled_row_slack_hint':float(min(B-A@fit.x[:V]-column*fit.x[-1]))})
            fit.x=fit.x[:V]
        out['phase']='LP_completed';save();return fit
    base.linprog=solver
    try:
        out['base_result']=base.solve(state,taylor,graph,0)
        if last is not None and last.success and last.fun>1e-10:
            out['phase']='extracting_exact_Farkas';save();ubounds=[]
            for i,j,aw in base.g.TERMS:
                z=base.g.LOOK[i,j];ff,_=graph.facets(state[0][z],state[1][z])
                ubounds.append((max(F(C,SC*base.old.DS) for sign,S,C in ff if sign==-1 and S==0),
                    min(F(C,SC*base.old.DS) for sign,S,C in ff if sign==1 and S==0)))
            model=exact.inputs(state,integer,meta,ubounds,packets);assert len(model['rows'])==base_nr+2
            selected=[i for i,v in enumerate(last.ineqlin.marginals) if -v>1e-14]
            coeff=[-float(last.ineqlin.marginals[i])/float(model['rows'][i]['scale']) for i in selected];mx=max(coeff)
            irows=[exact.integerize(model['rows'][i],model['bounds'],10**30) for i in selected];attempts=[]
            for power in [32,48,64]:
                weights=[round(v/mx*2**power) for v in coeff];checked=exact.verify_aggregate(irows,[(i,w) for i,w in enumerate(weights) if w],model['bounds'])
                attempts.append({'power':power,'strict':checked['strict_exclusion'],'margin':str(checked['strict_margin'])})
                if checked['strict_exclusion']:
                    out['strict_integer_certificate']={'old_meta':meta,'old_integer_rows':[[list(ag),list(au),str(B)] for ag,au,B in integer],
                        'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
                        'u_bounds':[[str(l),str(u)] for l,u in ubounds],'selected_rows':[{'index':k,'weight':str(w),'meta':model['rows'][k]['meta'],
                        'integer_coefficients':[[j,str(v)] for j,v in sorted(row['coeff'].items())],
                        'integer_bound':str(row['bound']),'rounding_payment':str(row['rounding_payment'])}
                        for k,w,row in zip(selected,weights,irows) if w],
                        'strict_margin':str(checked['strict_margin']),'box_minimum':str(checked['box_minimum']),
                        'aggregate_bound':str(checked['bound']),'aggregate_coefficients':[[j,str(v)] for j,v in sorted(checked['coefficient'].items())],
                        'box_bounds':[[str(l),str(u)] for l,u in model['bounds']],'power':power,'integerization_denominator':str(10**30),
                        'actual_input_soundness_independently_verified':False};break
            out['integer_attempts']=attempts
        out['phase']='completed_bounded_pilot';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    finally:base.linprog=original
    print(json.dumps({'phase':out['phase'],'LP':{k:v for k,v in out.get('LP',{}).items() if k not in ['raw_primal_with_slack','positive_row_dual_weights']},
        'strict_integer':out['strict_integer_certificate'] is not None,'seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
