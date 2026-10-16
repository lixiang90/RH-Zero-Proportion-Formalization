"""One bounded reverse-Taylor energy test on the fixed first remaining cell.

Keep the original midpoint lower-Taylor energy row, add only the endpoint-
derivative upper-curvature row, one IPM solve <=45s, no PSD rounds/new point.
All scalar upper bounds are derived from the already frozen jet table.
No numerical optimizer output is accepted as a mathematical exclusion.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time,traceback
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;V=base.V;SC=base.SC
OUT=HERE/'cover-reverse-taylor-pilot.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def reverse_packet(state,oldpacket,second):
    point=list(map(F,oldpacket['centre']));center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    coeff={r:F(b,base.g.D) for r,b in enumerate(base.g.BS)}
    C=F(oldpacket['F_interval'][0])-sum(F(b,base.g.D)*x for b,x in zip(base.g.BS,point));bounds=[]
    def add(k,v):
        q=coeff.get(k,F(0))+v
        if q:coeff[k]=q
        else:coeff.pop(k,None)
    for e,(i,j,aw) in enumerate(base.g.TERMS):
        z=base.g.LOOK[i,j];low,high=second.query(state[0][z],state[1][z]);M=F(high,base.old.DS);a=F(aw,base.g.D)
        assert F(low,base.old.DS)==F(oldpacket['whole_span_second_lower'][e])
        bounds.append([str(F(low,base.old.DS)),str(M)])
        delta=sum(center[i:j])-sum(point[i:j]);C-=a*M*delta*delta/2
        add(9+e,a*delta)
        for r in range(i,j):
            add(base.qindex(r,e),a*radius[r]);add(r,-a*M*delta);C+=a*M*delta*center[r]
            for s in range(r,j):add(base.hindex(r,s),-a*M*radius[r]*radius[s]/(2 if r==s else 1))
    # Exact point-factorization: the u term vanishes at the existing anchor.
    ys=[(x-c)/r for x,c,r in zip(point,center,radius)];factor=[F(0)]*V;factor[:9]=point
    for e in range(41):factor[9+e]=F(e-20,37)
    for r,s in base.PAIRS:factor[base.hindex(r,s)]=ys[r]*ys[s]
    for r in range(9):
        for e in range(41):factor[base.qindex(r,e)]=ys[r]*factor[9+e]
    assert C+sum(v*factor[k] for k,v in coeff.items())==F(oldpacket['F_interval'][0])
    # Independently evaluate at the coordinate-box centre with arbitrary u.
    direct=F(oldpacket['F_interval'][0])+sum(F(b,base.g.D)*(c-p) for b,c,p in zip(base.g.BS,center,point))
    for e,(i,j,aw) in enumerate(base.g.TERMS):
        d=sum(center[i:j])-sum(point[i:j]);direct+=F(aw,base.g.D)*(factor[9+e]*d-F(bounds[e][1])*d*d/2)
    check=[F(0)]*V;check[:9]=center;check[9:50]=factor[9:50]
    assert C+sum(v*check[k] for k,v in coeff.items())==direct
    return {'kind':'reverse_Taylor_endpoint_gradient','centre':oldpacket['centre'],'F_interval':oldpacket['F_interval'],
        'whole_span_second_bounds':bounds,'quadratic_constant':str(C),
        'row':[[k,str(v)] for k,v in sorted(coeff.items())],'bound':str(F(11,1250)-C),
        'anchor_and_box_center_factorization_exact':True,'pointwise_actual_semantics_formalized':False,
        'formula':'F(g)>=F0_lower+P(g)-P(g0)+sum a*((s-s0)*u-M*(s-s0)^2/2)'}

def main():
    assert not OUT.exists();started=time.monotonic();source=HERE/'cover-cross-moment-remaining-six.json'
    prior=json.loads(source.read_bytes())['rows'][0];state=tuple(prior['cell']);original_packet=prior['energy_packets'][0];table=HERE/'cover_newjet.json'
    dependency_paths=[source,table,Path(__file__),Path(base.__file__),Path(base.old.__file__),Path(exact.__file__),
        HERE/'cover_second_order.py',HERE/'cover_correlated_direction.py',base.g.PAR]
    initial={str(p.relative_to(HERE.parent)).replace('\\','/'):sha(p) for p in dependency_paths}
    out={'scope':__doc__,'path':prior['path'],'cell':prior['cell'],'target':'11/1250','input_sha256_start':initial,
        'LP_method':'highs-ipm','LP_time_limit_seconds':45,'PSD_rounds':0,'new_scalar_points':0,
        'strict_integer_certificate':None,'actual_Lean_exclusion_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    def save():
        out['seconds']=time.monotonic()-started;out['input_sha256_end']={str(p.relative_to(HERE.parent)).replace('\\','/'):sha(p) for p in dependency_paths}
        out['all_inputs_unchanged']=out['input_sha256_end']==initial;assert out['all_inputs_unchanged']
        OUT.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    out['phase']='querying_existing_upper_curvature';save()
    taylor=base.old.context.curvature.first.TaylorOracle(table);second=base.old.context.curvature.second.SecondOracle(taylor);graph=base.old.GraphOracle(table)
    newpacket=reverse_packet(state,original_packet,second);packets=[original_packet,newpacket];out['energy_packets']=packets
    rr,bb,integers,meta,data,obj,stats=base.old.build(state,taylor,graph,True)
    actual_lp=base.linprog;fit_saved=None;base_nr=None
    def solver(c,**kw):
        nonlocal fit_saved,base_nr
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
        fit_saved=fit;out['LP']={'status':int(fit.status),'success':bool(fit.success),'message':str(fit.message),
            'seconds':time.monotonic()-tick,'base_rows':base_nr,'energy_rows':2}
        if fit.success:
            out['LP'].update({'energy_slack_hint':float(fit.fun),'raw_primal_with_slack':fit.x.tolist(),
                'positive_row_dual_weights':[[i,float(-v)] for i,v in enumerate(fit.ineqlin.marginals) if -v>1e-14],
                'minimum_scaled_slack_hint':float(min(B-A@fit.x[:V]-column*fit.x[-1]))})
            fit.x=fit.x[:V]
        out['phase']='LP_completed';save();return fit
    base.linprog=solver
    try:
        out['base_result']=base.solve(state,taylor,graph,0)
        if fit_saved is not None and fit_saved.success and fit_saved.fun>1e-10:
            out['phase']='extracting_exact_Farkas';save();ubounds=[]
            for i,j,aw in base.g.TERMS:
                z=base.g.LOOK[i,j];ff,_=graph.facets(state[0][z],state[1][z])
                ubounds.append((max(F(C,SC*base.old.DS) for sign,S,C in ff if sign==-1 and S==0),
                    min(F(C,SC*base.old.DS) for sign,S,C in ff if sign==1 and S==0)))
            model=exact.inputs(state,integers,meta,ubounds,packets);assert len(model['rows'])==base_nr+2
            selected=[i for i,v in enumerate(fit_saved.ineqlin.marginals) if -v>1e-14]
            coeff=[-float(fit_saved.ineqlin.marginals[i])/float(model['rows'][i]['scale']) for i in selected];mx=max(coeff)
            irows=[exact.integerize(model['rows'][i],model['bounds'],10**30) for i in selected];attempts=[]
            for power in [32,48,64]:
                weights=[round(v/mx*2**power) for v in coeff];checked=exact.verify_aggregate(irows,[(i,w) for i,w in enumerate(weights) if w],model['bounds'])
                attempts.append({'power':power,'strict':checked['strict_exclusion'],'margin':str(checked['strict_margin'])})
                if checked['strict_exclusion']:
                    out['strict_integer_certificate']={'selected_rows':[{'index':k,'weight':str(w),'meta':model['rows'][k]['meta'],
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
    finally:base.linprog=actual_lp
    print(json.dumps({'phase':out['phase'],'LP':{k:v for k,v in out.get('LP',{}).items() if k not in ['raw_primal_with_slack','positive_row_dual_weights']},
        'strict_integer':out['strict_integer_certificate'] is not None,'seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
