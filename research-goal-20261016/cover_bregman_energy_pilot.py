"""At most two IPMs for fixed-shared-h Bregman energy on one frozen cell.

Original scalar graph/KKT/RLT plus original midpoint energy. No residual
PSD or reverse row. First fixed h is already frozen; only if zero slack,
one further h is obtained by exact 9x9 elimination from that same LP primal.
Each IPM <=45s. No new scalar point, profile, cell, target or Lean job.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time,traceback
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact
import cover_bregman_primal_check as algebra

HERE=Path(__file__).parent;V=base.V;SC=base.SC;OUT=HERE/'cover-bregman-energy-pilot.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def from_primal(primal,prior,matrices):
    old=prior['energy_packets'][0];point=list(map(F,old['centre']));Hm=[[F(v) for v in row] for row in matrices['Hm']];HL=[[F(v) for v in row] for row in matrices['HL']]
    grad=[(F(l)+F(u))/2 for l,u in old['gradient_interval']];error=[(F(u)-F(l))/2 for l,u in old['gradient_interval']]
    delta=[F(str(x))-p for x,p in zip(primal[:9],point)];v=[a+b for a,b in zip(grad,algebra.matvec(Hm,delta))]
    inverse,pivots=algebra.solve(HL,v);D=2**20;h=[F(round(-x*D),D) for x in inverse]
    state=prior['cell'];lower=[F(x,SC) for x in state[0][:9]];upper=[F(x,SC) for x in state[1][:9]]
    payment=sum(e*max(abs(l-p-z),abs(u-p-z)) for e,l,u,p,z in zip(error,lower,upper,point,h))
    mh=algebra.matvec(Hm,h);row={i:F(c) for i,c in old['row']}
    for r in range(9):
        value=row.get(r,F(0))-mh[r]
        if value:row[r]=value
        else:row.pop(r,None)
    C=F(old['quadratic_constant'])-algebra.dot(grad,h)+algebra.dot(mh,point)-algebra.dot(h,algebra.matvec(HL,h))/2-(payment-F(old['uniform_gradient_error_payment']))
    return {'kind':'Bregman_fixed_shared_h_free_KKT','centre':old['centre'],'row':[[i,str(v)] for i,v in sorted(row.items())],
        'bound':str(F(11,1250)-C),'quadratic_constant':str(C),'fixed_h':list(map(str,h)),
        'uniform_gradient_error_payment':str(payment),'all_nine_free_KKT_required':True,
        'selection':'one exact HL solve at preceding LP mean, rounded to denominator 2^20'}

def main():
    assert not OUT.exists();started=time.monotonic();source=HERE/'cover-cross-moment-remaining-six.json';selection=HERE/'cover-bregman-primal-check.json'
    prior=json.loads(source.read_bytes())['rows'][0];matrices=json.loads(selection.read_bytes());state=tuple(prior['cell'])
    assert prior['path']==matrices['path'] and matrices['new_row_strictly_cuts_saved_decimal_primal']
    assert all(v>123*SC//128 for v in state[0][:9])
    table=HERE/'cover_newjet.json';watched=[source,selection,table,Path(__file__),Path(base.__file__),Path(base.old.__file__),Path(exact.__file__),Path(algebra.__file__),base.g.PAR]
    initial={str(p.relative_to(HERE.parent)).replace('\\','/'):sha(p) for p in watched}
    packets=[prior['energy_packets'][0],matrices['proposed_KKT_energy_packet']]
    out={'scope':__doc__,'path':prior['path'],'cell':prior['cell'],'target':'11/1250','input_sha256_start':initial,
        'energy_packets':packets,'rounds':[],'maximum_LP_calls':2,'LP_method':'highs-ipm','LP_time_limit_seconds':45,
        'all_nine_coordinates_strictly_free':True,'new_scalar_points':0,'PSD_rounds':0,'reverse_rows':0,
        'strict_integer_certificate':None,'actual_Bregman_bridge_formalized':False,'actual_Lean_exclusion_proven':False,
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
        base_nr=kw['A_ub'].shape[0]
        for iteration in range(2):
            erows=[];rhs=[];scales=[]
            for p in packets:
                row=np.zeros(V)
                for k,v in p['row']:row[k]=float(F(v))
                B=float(F(p['bound']));scale=max(1.,max(abs(row)),abs(B));erows.append(row/scale);rhs.append(B/scale);scales.append(scale)
            A=vstack([kw['A_ub'],csr_matrix(erows)],format='csr');B=np.r_[kw['b_ub'],rhs]
            column=np.r_[np.zeros(base_nr),[-1/scale for scale in scales]]
            out['phase']='LP_running';out['active_iteration']=iteration;save();tick=time.monotonic()
            fit=linprog(np.r_[np.zeros(V),1.],A_ub=hstack([A,csr_matrix(column[:,None])],format='csr'),b_ub=B,
                bounds=kw['bounds']+[(0,None)],method='highs-ipm',
                options={'time_limit':45.,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-8})
            row={'iteration':iteration,'success':bool(fit.success),'status':int(fit.status),'message':str(fit.message),
                'LP_seconds':time.monotonic()-tick,'base_rows':base_nr,'energy_rows':len(packets)};out['rounds'].append(row);last=fit
            if not fit.success:out['phase']='stopped_LP_status';save();return fit
            row.update({'energy_slack_hint':float(fit.fun),'raw_primal_with_slack':fit.x.tolist(),
                'positive_row_dual_weights':[[i,float(-v)] for i,v in enumerate(fit.ineqlin.marginals) if -v>1e-14],
                'minimum_scaled_row_slack_hint':float(min(B-A@fit.x[:V]-column*fit.x[-1]))})
            print(json.dumps({'iteration':iteration,'energy_slack_hint':fit.fun,'LP_seconds':row['LP_seconds'],'total_seconds':time.monotonic()-started}),flush=True)
            if fit.fun>1e-10 or iteration==1:
                out['phase']='LP_completed';save();fit.x=fit.x[:V];return fit
            packets.append(from_primal(fit.x,prior,matrices));out['phase']='second_h_saved';save()
        raise AssertionError('unreachable')
    base.linprog=solver
    try:
        out['base_result']=base.solve(state,taylor,graph,0)
        if last is not None and last.success and last.fun>1e-10:
            out['phase']='extracting_exact_Farkas';save();ubounds=[]
            for i,j,aw in base.g.TERMS:
                z=base.g.LOOK[i,j];ff,_=graph.facets(state[0][z],state[1][z])
                ubounds.append((max(F(C,SC*base.old.DS) for sign,S,C in ff if sign==-1 and S==0),
                    min(F(C,SC*base.old.DS) for sign,S,C in ff if sign==1 and S==0)))
            model=exact.inputs(state,integer,meta,ubounds,packets);assert len(model['rows'])==base_nr+len(packets)
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
    print(json.dumps({'phase':out['phase'],'LP_calls':len(out['rounds']),'energy_packets':len(packets),
        'strict_integer':out['strict_integer_certificate'] is not None,'seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
