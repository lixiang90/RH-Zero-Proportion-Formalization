"""Bounded 464-variable residual-PSD pilot on one frozen remaining case.

Same original scalar graph, midpoint energy packet, and target 11/1250.
At most two cut rounds, sixteen integer cuts each, and 45 seconds per IPM.
No new scalar samples, points, derivative tables, span-128 job, Lean job,
or global cover. Every residual cut is stored as exact Fraction data.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time,traceback
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;SC=base.SC;V=base.V
OUT=HERE/'cover-residual-psd-pilot.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def add(row,k,v):
    v=F(v)+row.get(k,F(0))
    if v:row[k]=v
    else:row.pop(k,None)

def to_moments(poly,center,radius,e):
    row={};constant=F(0)
    for mon,value in poly.items():
        if not mon:constant+=value
        elif len(mon)==1:
            i=mon[0]
            if i==9:add(row,9+e,value)
            else:add(row,i,value/radius[i]);constant-=value*center[i]/radius[i]
        elif len(mon)==2:
            i,j=mon
            assert (i,j)!=(9,9),'u^2 must cancel'
            add(row,base.qindex(i,e) if j==9 else base.hindex(i,j),value)
        else:raise AssertionError(mon)
    return row,constant

def square(affine):
    result={}
    for i,a in affine.items():
        for j,b in affine.items():
            mon=tuple(sorted(k for k in [i,j] if k is not None));add(result,mon,a*b)
    return result

def cut_row(e,vector,beta,eps,center,radius):
    v=list(map(int,vector[:10]));t=int(vector[10]);positive={};constant=F(t*t)*eps*eps
    for i in range(10):
        for j in range(10):
            c=F(v[i]*v[j])-2*t*v[i]*beta[j]
            if not c:continue
            if i==j==0:constant+=c
            elif i==0 or j==0:
                r=(j if i==0 else i)-1;add(positive,r,c/radius[r]);constant-=c*center[r]/radius[r]
            else:add(positive,base.hindex(i-1,j-1),c)
        add(positive,9+e if i==0 else base.qindex(i-1,e),2*t*v[i])
    # Independently expand (v.x+t*delta)^2+t^2*(eps^2-delta^2).
    delta={None:-beta[0],**{r:-beta[r+1] for r in range(9)},9:F(1)}
    form={None:F(v[0])-t*beta[0],**{r:F(v[r+1])-t*beta[r+1] for r in range(9)},9:F(t)}
    poly=square(form)
    for mon,value in square(delta).items():add(poly,mon,-t*t*value)
    add(poly,(),F(t*t)*eps*eps)
    checked,cc=to_moments(poly,center,radius,e);assert checked==positive and cc==constant
    row={'coeff':{i:-v for i,v in positive.items()},'bound':constant,'meta':['residual_PSD',e,vector]}
    row['scale']=max([F(1),abs(constant)]+list(map(abs,row['coeff'].values())))
    return row

def serial_row(row):
    return {'coefficients':[[i,str(v)] for i,v in sorted(row['coeff'].items())],
        'bound':str(row['bound']),'scale':str(row['scale']),'meta':row['meta'],
        'exact_factorization_checked':True,
        'factorization':'(v.x+t*(u_e-beta.x))^2+t^2*(eps^2-(u_e-beta.x)^2)'}

def matrix(x,beta,eps,center,radius,e):
    X=np.ones((10,10));ys=(x[:9]-np.array(list(map(float,center))))/np.array(list(map(float,radius)))
    X[0,1:]=ys;X[1:,0]=ys
    for s,r in base.PAIRS:X[s+1,r+1]=X[r+1,s+1]=x[base.hindex(s,r)]
    z=np.r_[x[9+e],[x[base.qindex(s,e)] for s in range(9)]]
    residual=z-X@np.array(list(map(float,beta)));N=np.empty((11,11));N[:10,:10]=X
    N[:10,10]=residual;N[10,:10]=residual;N[10,10]=float(eps*eps)
    return N

def main():
    assert not OUT.exists(),'Use a new immutable output.'
    started=time.monotonic();source=HERE/'cover-cross-moment-remaining-six.json';prior=json.loads(source.read_bytes())['rows'][0]
    state=tuple(prior['cell']);packet=prior['energy_packets'][0];table=HERE/'cover_newjet.json'
    watched=[source,table,Path(__file__),Path(base.__file__),Path(base.old.__file__),Path(exact.__file__)]
    initial={p.name:sha(p) for p in watched};taylor=base.old.context.curvature.first.TaylorOracle(table);graph=base.old.GraphOracle(table)
    rr,bb,integers,meta,data,obj,stats=base.old.build(state,taylor,graph,True)
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])];radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    slabs=[]
    for e,((i,j,aw),(P,m0,m1,err,kind)) in enumerate(zip(base.g.TERMS,data)):
        slope=F(m1,base.old.DS);beta=[F(m0,base.old.DS)+slope*(sum(center[i:j])-F(P,2*SC))]
        beta += [slope*radius[r] if i<=r<j else F(0) for r in range(9)];eps=F(err,base.old.DS);assert eps>=0
        # Check the scale against the old builder's exact integer slab rows.
        for sign in [1,-1]:
            k=meta.index(['slab',e,sign]);ag,au,B=integers[k]
            assert [F(v,base.old.Q) for v in ag]==[-sign*slope if i<=r<j else F(0) for r in range(9)]
            assert F(au[e],base.old.Q)==sign
            assert F(B,base.old.Q)==sign*(F(m0,base.old.DS)-slope*F(P,2*SC))+eps
        slabs.append({'edge':[i,j],'data':[P,str(m0),str(m1),str(err),kind],'beta':list(map(str,beta)),'epsilon':str(eps),
            'old_integer_slab_scaling_checked':True})
    out={'scope':__doc__,'path':prior['path'],'cell':prior['cell'],'target':'11/1250','energy_packet':packet,
        'input_sha256_start':initial,'scalar_slabs':slabs,'rounds':[],'cuts':[],
        'maximum_cut_rounds':2,'maximum_cuts_per_round':16,'LP_time_limit_seconds':45,'LP_method':'highs-ipm',
        'strict_integer_certificate':None,'actual_Lean_exclusion_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    def save():
        out['seconds']=time.monotonic()-started;out['input_sha256_end']={p.name:sha(p) for p in watched}
        out['all_inputs_unchanged']=out['input_sha256_end']==initial;assert out['all_inputs_unchanged']
        OUT.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    out['phase']='building_base_model';save();original=base.linprog;cuts=[];last_fit=None;seen=set();base_bounds=None;base_nr=None
    def run_solver(c,**kw):
        nonlocal last_fit,base_bounds,base_nr
        baseA=kw['A_ub'];baseb=kw['b_ub'];base_bounds=kw['bounds'];base_nr=baseA.shape[0]
        energy=np.zeros(V)
        for k,v in packet['row']:energy[k]=float(F(v))
        B=float(F(packet['bound']));escale=max(1.,max(abs(energy)),abs(B))
        A=vstack([baseA,csr_matrix(energy[None,:]/escale)],format='csr');rhs=np.r_[baseb,B/escale]
        for iteration in range(3):
            if cuts:
                rows=np.zeros((len(cuts),V))
                for j,row in enumerate(cuts):
                    for k,v in row['coeff'].items():rows[j,k]=float(v/row['scale'])
                current=vstack([A,csr_matrix(rows)],format='csr');currentb=np.r_[rhs,[float(row['bound']/row['scale']) for row in cuts]]
            else:current=A;currentb=rhs
            column=np.zeros(len(currentb));column[base_nr]=-1/escale
            out['phase']='LP_running';out['active_iteration']=iteration;save();t0=time.monotonic()
            fit=linprog(np.r_[np.zeros(V),1.],A_ub=hstack([current,csr_matrix(column[:,None])],format='csr'),
                b_ub=currentb,bounds=base_bounds+[(0,None)],method='highs-ipm',
                options={'time_limit':45.,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9,'ipm_optimality_tolerance':1e-8})
            row={'iteration':iteration,'status':int(fit.status),'success':bool(fit.success),'message':str(fit.message),
                'seconds':time.monotonic()-t0,'rows':len(currentb),'cuts_present':len(cuts)};out['rounds'].append(row);last_fit=fit
            if not fit.success:out['phase']='stopped_LP_status';save();return fit
            row['minimum_energy_slack_hint']=float(fit.fun);row['raw_primal_with_energy_slack']=fit.x.tolist()
            row['positive_row_dual_weights']=[[k,float(-v)] for k,v in enumerate(fit.ineqlin.marginals) if -v>1e-14]
            row['minimum_scaled_row_slack_hint']=float(min(currentb-current@fit.x[:V]-column*fit.x[-1]))
            candidates=[];all_eig=[]
            for e,slab in enumerate(slabs):
                beta=list(map(F,slab['beta']));eps=F(slab['epsilon']);N=matrix(fit.x,beta,eps,center,radius,e)
                values,vectors=np.linalg.eigh(N);all_eig.append(float(values[0]))
                for k,val in enumerate(values):
                    if val>=-1e-8:break
                    vec=np.rint(vectors[:,k]/max(abs(vectors[:,k]))*32768).astype(np.int64).tolist()
                    key=(e,tuple(vec))
                    if key in seen:continue
                    cut=cut_row(e,vec,beta,eps,center,radius)
                    violation=float(sum(float(v)*fit.x[k] for k,v in cut['coeff'].items())-float(cut['bound']))
                    if violation>1e-8:candidates.append((float(val),e,vec,cut,violation))
            row['minimum_41_residual_PSD_eigenvalue_hint']=min(all_eig);row['41_minimum_eigenvalue_hints']=all_eig
            print(json.dumps({'iteration':iteration,'status':fit.status,'energy_slack_hint':fit.fun,
                'min_residual_eigenvalue_hint':min(all_eig),'LP_seconds':row['seconds'],'total_seconds':time.monotonic()-started}),flush=True)
            if fit.fun>1e-10:out['phase']='positive_energy_slack_hint';save();fit.x=fit.x[:V];return fit
            if iteration==2 or not candidates:out['phase']='bounded_stop';save();fit.x=fit.x[:V];return fit
            selected=sorted(candidates,key=lambda z:z[0])[:16]
            for eig,e,vec,cut,violation in selected:
                seen.add((e,tuple(vec)));cuts.append(cut);out['cuts'].append({**serial_row(cut),'term':e,'integer_vector':vec,
                    'discovery_iteration':iteration,'eigenvalue_hint':eig,'primal_violation_hint':violation})
            row['cuts_added']=len(selected);out['phase']='cuts_saved';save()
        raise AssertionError('unreachable')
    base.linprog=run_solver
    try:
        result=base.solve(state,taylor,graph,0);out['base_return']=result
        if last_fit is not None and last_fit.success and last_fit.fun>1e-10:
            out['phase']='extracting_exact_Farkas';save()
            ubounds=[]
            for i,j,aw in base.g.TERMS:
                z=base.g.LOOK[i,j];facets,_=graph.facets(state[0][z],state[1][z])
                ubounds.append((max(F(C,SC*base.old.DS) for sign,S,C in facets if sign==-1 and S==0),
                    min(F(C,SC*base.old.DS) for sign,S,C in facets if sign==1 and S==0)))
            model=exact.inputs(state,integers,meta,ubounds,[packet]);assert len(model['rows'])==base_nr+1
            model['rows'].extend(cuts);duals=last_fit.ineqlin.marginals;selected=[k for k,v in enumerate(duals) if -v>1e-14]
            coeff=[-float(duals[k])/float(model['rows'][k]['scale']) for k in selected];mx=max(coeff)
            integer_rows=[exact.integerize(model['rows'][k],model['bounds'],10**30) for k in selected];attempts=[]
            for power in [32,48,64]:
                weights=[round(v/mx*2**power) for v in coeff];checked=exact.verify_aggregate(integer_rows,[(k,w) for k,w in enumerate(weights) if w],model['bounds'])
                attempts.append({'power':power,'strict':checked['strict_exclusion'],'margin':str(checked['strict_margin'])})
                if checked['strict_exclusion']:
                    out['strict_integer_certificate']={'power':power,'selected_rows':[
                        {'model_index':k,'weight':str(w),'meta':model['rows'][k]['meta'],
                            'integer_coefficients':[[j,str(v)] for j,v in sorted(rr['coeff'].items())],'integer_bound':str(rr['bound']),
                            'rounding_payment':str(rr['rounding_payment'])}
                        for k,w,rr in zip(selected,weights,integer_rows) if w],
                        'strict_margin':str(checked['strict_margin']),'aggregate_coefficients':[[i,str(v)] for i,v in sorted(checked['coefficient'].items())],
                        'aggregate_bound':str(checked['bound']),'box_minimum':str(checked['box_minimum']),
                        'bounds':[[str(l),str(u)] for l,u in model['bounds']],'integerization_denominator':str(10**30),
                        'analytic_input_soundness_independently_verified':False};break
            out['integer_attempts']=attempts
        out['phase']='completed_bounded_pilot';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    finally:base.linprog=original
    print(json.dumps({'phase':out['phase'],'rounds':len(out['rounds']),'cuts':len(cuts),
        'strict_integer':out['strict_integer_certificate'] is not None,'seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
