"""One bounded joint residual-PSD and closed-Bregman cone test.

Only the first frozen remaining cell and its original energy packet are
used. Forty-one 11 by 11 PSD blocks use the existing 464 scalar variables.
The conic solver is a discovery tool: no floating result is a certificate.
No new scalar point, LP cut loop, whole cover, or Lean job is run here.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,os,sys,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.sparse import csr_matrix,csc_matrix,hstack,vstack
from scipy.optimize import OptimizeResult
import scs
import cover_cross_moment_probe as base

OUT=HERE/'cover-residual-psd-bregman-full-cone.json'
SC=base.SC;V=base.V

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def linear_add(row,k,v):
    row[k]=row.get(k,F(0))+v
    if not row[k]:del row[k]

def x_entry(i,j,center,radius):
    if i>j:i,j=j,i
    if i==j==0:return F(1),{}
    if i==0:return -center[j-1]/radius[j-1],{j-1:1/radius[j-1]}
    return F(0),{base.hindex(i-1,j-1):F(1)}

def block_entries(e,beta,eps,center,radius):
    """Exact rational affine entries, before SCS's sqrt(2) packing."""
    assert eps>0
    for j in range(11):
        for i in range(j,11):
            if i<10:c,row=x_entry(i,j,center,radius)
            elif j==10:c,row=F(1),{}
            else:
                c=F(0);row={9+e if j==0 else base.qindex(j-1,e):F(1)}
                for k,b in enumerate(beta):
                    cc,rr=x_entry(j,k,center,radius);c-=b*cc
                    for index,v in rr.items():linear_add(row,index,-b*v)
                c/=eps;row={k:v/eps for k,v in row.items()}
            yield i,j,c,row

def unpack(v):
    M=np.empty((11,11));p=0
    for j in range(11):
        for i in range(j,11):
            M[i,j]=M[j,i]=v[p]/(1 if i==j else np.sqrt(2));p+=1
    assert p==len(v)
    return M

def main():
    assert not OUT.exists(),'Use a new immutable experiment path.'
    start=time.monotonic();priorpath=HERE/'cover-cross-moment-remaining-six.json'
    slabpath=HERE/'cover-residual-psd-pilot.json'
    prior=json.loads(priorpath.read_bytes())['rows'][0];slabs=json.loads(slabpath.read_bytes())
    assert prior['path']==slabs['path'] and prior['cell']==slabs['cell']
    state=tuple(prior['cell']);packet=prior['energy_packets'][0]
    closedpath=HERE/'cover-bregman-closed-energy-pilot.json'
    closed=json.loads(closedpath.read_bytes())
    assert closed['path']==prior['path'] and closed['all_nine_coordinates_strictly_free']
    packets=[packet,closed['energy_packets'][1]]
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    dependencies=[Path(__file__),priorpath,slabpath,closedpath,HERE/'cover_newjet.json',
        Path(base.__file__),Path(base.old.__file__),HERE/'cover_residual_psd_pilot.py']
    guard={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in dependencies}
    out={'scope':__doc__,'path':prior['path'],'target':'11/1250','scalar_variables':V,
        'PSD_blocks':[11]*41,'energy_packets':2,'new_scalar_points':0,'cut_rounds':0,
        'solver':'SCS','solver_version':scs.__version__,'numpy_version':np.__version__,
        'scipy_version':scipy.__version__,'time_limit_seconds':45,'maximum_iterations':10000,
        'input_sha256':guard,'strict_integer_certificate':None,'complete_global_cover':False,
        'actual_Lean_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save():
        assert guard=={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in dependencies}
        out['seconds']=time.monotonic()-start
        OUT.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    out['phase']='building_base';save();captured={};original=base.linprog
    def capture(c,**kw):
        captured.update(kw)
        return OptimizeResult(success=False,status=4,message='model capture only; no LP solve')
    base.linprog=capture
    try:
        table=HERE/'cover_newjet.json';taylor=base.old.context.curvature.first.TaylorOracle(table)
        graph=base.old.GraphOracle(table);base.solve(state,taylor,graph,0)
    finally:base.linprog=original
    A=captured['A_ub'];b=captured['b_ub'];nr=A.shape[0]
    A=hstack([A,csr_matrix((nr,1))],format='csr')
    for packet in packets:
        row=np.zeros(V)
        for k,v in packet['row']:row[k]=float(F(v))
        bound=float(F(packet['bound']));scale=max(1.,abs(bound),max(abs(row)))
        A=vstack([A,csr_matrix(np.r_[row/scale,-.001/scale][None,:])],format='csr')
        b=np.r_[b,bound/scale]
    boundrows=[];boundrhs=[]
    for k,(l,u) in enumerate(captured['bounds']+[(0,None)]):
        if l is not None:
            rr=np.zeros(V+1);rr[k]=-1;boundrows.append(rr);boundrhs.append(-l)
        if u is not None:
            rr=np.zeros(V+1);rr[k]=1;boundrows.append(rr);boundrhs.append(u)
    A=vstack([A,csr_matrix(boundrows)],format='csr');b=np.r_[b,boundrhs];linearrows=len(b)
    psdrows=[];psdrhs=[];exacthash=hashlib.sha256()
    for e,slab in enumerate(slabs['scalar_slabs']):
        beta=list(map(F,slab['beta']));eps=F(slab['epsilon'])
        for i,j,c,coeff in block_entries(e,beta,eps,center,radius):
            exacthash.update(json.dumps([e,i,j,str(c),[[k,str(v)] for k,v in sorted(coeff.items())]],separators=(',',':')).encode())
            factor=1 if i==j else np.sqrt(2);rr=np.zeros(V+1)
            for k,v in coeff.items():rr[k]=-factor*float(v)
            psdrows.append(rr);psdrhs.append(factor*float(c))
    AP=csr_matrix(psdrows);bp=np.array(psdrhs)
    # Independently compare the packed affine map with the previously tested
    # matrix formula at the frozen primal, including the exact congruence.
    from cover_residual_psd_pilot import matrix
    x=np.array(slabs['rounds'][0]['raw_primal_with_energy_slack'][:V]);packed=bp-AP@np.r_[x,0.]
    error=0.
    for e,slab in enumerate(slabs['scalar_slabs']):
        eps=float(F(slab['epsilon']));beta=list(map(F,slab['beta']))
        N=matrix(x,beta,F(slab['epsilon']),center,radius,e);D=np.r_[np.ones(10),1/eps]
        expected=N*D[:,None]*D[None,:]
        error=max(error,float(max(abs(unpack(packed[66*e:66*(e+1)])-expected).flat)))
    assert error<1e-7,error
    out.update({'linear_rows':linearrows,'base_rows':nr,'PSD_affine_map_max_error_hint':error,
        'exact_PSD_affine_map_serialization_sha256':exacthash.hexdigest()})
    A=csc_matrix(vstack([A,AP],format='csc'));b=np.r_[b,bp];c=np.r_[np.zeros(V),1.]
    out['phase']='conic_solve_running';save()
    try:
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linearrows,'s':[11]*41},
            verbose=False,time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['raw_primal']=result['x'].tolist()
        out['raw_dual']=result['y'].tolist();out['raw_conic_slack']=result['s'].tolist()
        xx=result['x'];out['raw_energy_slack_hint']=float(xx[-1]*.001)
        out['minimum_linear_slack_hint']=float(min(b[:linearrows]-A[:linearrows]@xx))
        mats=bp-AP@xx
        out['minimum_41_normalized_PSD_eigenvalue_hint']=min(float(np.linalg.eigvalsh(unpack(mats[66*e:66*(e+1)]))[0]) for e in range(41))
        out['phase']='completed_single_full_cone_test';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps({k:out[k] for k in ['phase','solver_info','raw_energy_slack_hint',
        'minimum_linear_slack_hint','minimum_41_normalized_PSD_eigenvalue_hint','seconds']}),flush=True)

if __name__=='__main__':main()
