"""One fixed-cell joint (s,w',w'') graph and full-Hessian PSD pilot.

Only remaining-six case 0 and target 11/1250 are used. The frozen
464-variable residual-PSD/closed-Bregman model is retained, with 41 actual
second-derivative variables and one 9 by 9 Hessian cone. ConvexHull only
suggests normals: every rounded integer normal is paid exactly over all
same-grid rectangular boxes. SCS is called once, <=45 s and <=10000 steps.
No floating outcome is an exclusion certificate or a zero-proportion bound.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import reduce
from math import gcd
import hashlib,json,os,sys,time,traceback
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
import scipy
from scipy.sparse import csr_matrix,csc_matrix,hstack,vstack
from scipy.optimize import OptimizeResult
from scipy.spatial import ConvexHull
import scs
import cover_cross_moment_probe as base
import cover_second_order as second
import cover_residual_psd_bregman_full_cone as frozen

OUT=HERE/'cover-joint-jet-hessian-pilot.json'
SC=base.SC;DS=base.old.DS;V=base.V;NV=V+41;TOTAL=NV+1
NORM_DEN=1000000
HESSIAN_SCALE=F(100)

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def rectangles(l,u,graph,oracle):
    assert 0<=l<=u<=32*SC
    assert graph.width==oracle.width and len(graph.grid)==len(oracle.grid)
    first=l//graph.width;last=(max(l+1,u)+graph.width-1)//graph.width
    return [(max(l,k*graph.width),min(u,(k+1)*graph.width),
             *graph.grid[k],*oracle.grid[k]) for k in range(first,last)]

def joint_facets(rects):
    """Return integer n and C with n_s*s+n_u*u+n_v*v <= C/(SC*DS).

    Floating hull equations are ONLY normal suggestions. C is the exact
    maximum over every box, including boxes whose corners were not hull
    vertices. Endpoints for each summand are chosen by that normal's sign.
    """
    points=[]
    for a,b,L,U,J,K in rects:
        points.extend((x/SC,u/DS,v/DS) for x in (a,b)
                      for u in (L,U) for v in (J,K))
    hull=ConvexHull(np.unique(np.asarray(points),axis=0))
    normals={(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)}
    for eq in hull.equations:
        nn=eq[:3];den=max(abs(nn));n=tuple(int(round(float(x/den)*NORM_DEN)) for x in nn)
        common=reduce(gcd,map(abs,n));assert common>0
        normals.add(tuple(x//common for x in n))
    result=[]
    for n in sorted(normals):
        ns,nu,nv=n
        C=max(ns*(b if ns>=0 else a)*DS+
              SC*(nu*(U if nu>=0 else L)+nv*(K if nv>=0 else J))
              for a,b,L,U,J,K in rects)
        # An independent endpoint enumeration audits sign and scale payment.
        assert C==max(ns*x*DS+SC*(nu*u+nv*v) for a,b,L,U,J,K in rects
                      for x in (a,b) for u in (L,U) for v in (J,K))
        result.append([list(n),str(C)])
    return result,len(hull.equations)

def old_point_check(state,edges,point):
    """Existential v audit; old 464-vector by itself does not assign v."""
    x=list(map(F,point['projected_464_rational_moments']));assert len(x)==V
    details=[];bad=[]
    for e,((i,j,aw),data) in enumerate(zip(base.g.TERMS,edges)):
        s=sum(x[i:j]);u=x[9+e];lo=None;up=None;li=ui=None;zero=[]
        for k,(n,C) in enumerate(data['facets']):
            ns,nu,nv=n;rhs=F(int(C),SC*DS)-ns*s-nu*u
            if nv>0:
                bound=rhs/nv
                if up is None or bound<up:up=bound;ui=k
            elif nv<0:
                bound=rhs/nv
                if lo is None or bound>lo:lo=bound;li=k
            elif rhs<0:zero.append([k,str(-rhs)])
        assert lo is not None and up is not None
        row={'edge':e,'ij':[i,j],'v_lower':str(lo),'v_upper':str(up),
             'lower_facet':li,'upper_facet':ui,'zero_v_violations':zero,
             'empty':bool(lo>up or zero),'lower_minus_upper_hint':float(lo-up)}
        details.append(row)
        if row['empty']:bad.append(e)
    return {'scope':'Existential per-edge v extension of the frozen exact 464-vector; no new actual point.',
            'all_edges_have_joint_facet_v_extension':not bad,'empty_edges':bad,'edges':details}

def unpack_n(packed,n):
    mat=np.empty((n,n));p=0
    for j in range(n):
        for i in range(j,n):
            mat[i,j]=mat[j,i]=packed[p]/(1 if i==j else np.sqrt(2));p+=1
    assert p==len(packed);return mat

def main():
    assert not OUT.exists(),'Use a new immutable output path.'
    start=time.monotonic()
    priorpath=HERE/'cover-cross-moment-remaining-six.json'
    slabpath=HERE/'cover-residual-psd-pilot.json'
    closedpath=HERE/'cover-bregman-closed-energy-pilot.json'
    pointpath=HERE/'cover-residual-psd-rational-projection.json'
    table=HERE/'cover_newjet.json'
    prior=json.loads(priorpath.read_bytes())['rows'][0]
    slabs=json.loads(slabpath.read_bytes());closed=json.loads(closedpath.read_bytes())
    point=json.loads(pointpath.read_bytes())
    assert prior['path']==slabs['path']==closed['path']
    assert prior['cell']==slabs['cell']
    state=tuple(prior['cell']);assert all(l>base.g.SEP for l in state[0][:9])
    assert closed['all_nine_coordinates_strictly_free']
    assert point['status']=='strict_exact_feasible_relaxation_point'
    packets=[prior['energy_packets'][0],closed['energy_packets'][1]]
    center=[F(l+u,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    radius=[F(u-l,2*SC) for l,u in zip(state[0][:9],state[1][:9])]
    dependencies=[Path(__file__),priorpath,slabpath,closedpath,pointpath,table,
        Path(base.__file__),Path(base.old.__file__),Path(second.__file__),Path(frozen.__file__),
        Path(second.engine.__file__),HERE/'cover_residual_psd_pilot.py',
        ROOT/'StructuralGoal20261016/WindowSecondVariation.lean']
    guard={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in dependencies}
    out={'scope':__doc__,'path':prior['path'],'cell':state,'target':'11/1250',
        'base_variables':V,'new_second_derivative_variables':41,'total_variables_including_energy_slack':TOTAL,
        'PSD_blocks':[11]*41+[9],'Hessian_scale':str(HESSIAN_SCALE),
        'all_nine_coordinates_strictly_free':True,'new_scalar_points':0,'cut_rounds':0,
        'solver':'SCS','solver_version':scs.__version__,'numpy_version':np.__version__,
        'scipy_version':scipy.__version__,'time_limit_seconds':45,'maximum_iterations':10000,
        'integer_normal_maximum_hint_scale':NORM_DEN,'integer_intercept_denominator':str(SC*DS),
        'input_sha256':guard,'strict_integer_certificate':None,'complete_global_cover':False,
        'actual_Lean_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save():
        assert guard=={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in dependencies}
        out['seconds']=time.monotonic()-start
        OUT.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    out['phase']='building_shared_grid_and_base';save()
    captured={};original=base.linprog
    def capture(c,**kw):
        captured.update(kw)
        return OptimizeResult(success=False,status=4,message='model capture only; no LP solve')
    base.linprog=capture
    try:
        taylor=base.old.context.curvature.first.TaylorOracle(table)
        graph=base.old.GraphOracle(table);base.solve(state,taylor,graph,0)
    finally:base.linprog=original
    oracle=second.SecondOracle(taylor);edges=[]
    for e,(i,j,aw) in enumerate(base.g.TERMS):
        z=base.g.LOOK[i,j];rects=rectangles(state[0][z],state[1][z],graph,oracle)
        facets,hcount=joint_facets(rects)
        edges.append({'edge':e,'ij':[i,j],'rectangles':[list(r) for r in rects],
                      'facets':facets,'floating_hull_facets_hint_count':hcount})
    out['joint_graph_edges']=edges
    out['joint_graph_facet_count']=sum(len(e['facets']) for e in edges)
    out['joint_graph_mixed_u_v_facet_count']=sum(bool(n[1] and n[2]) for e in edges for n,C in e['facets'])
    out['frozen_exact_point_joint_graph_check']=old_point_check(state,edges,point)
    A=captured['A_ub'];b=captured['b_ub'];nr=A.shape[0]
    A=hstack([A,csr_matrix((nr,42))],format='csr')
    added=[];addedrhs=[]
    for e,data in enumerate(edges):
        i,j,aw=base.g.TERMS[e]
        for n,C in data['facets']:
            ns,nu,nv=n;bound=F(int(C),SC*DS);scale=max(F(1),abs(bound),*map(abs,n))
            row=np.zeros(TOTAL);row[i:j]=float(F(ns)/scale)
            row[9+e]=float(F(nu)/scale);row[V+e]=float(F(nv)/scale)
            added.append(row);addedrhs.append(float(bound/scale))
    for packet in packets:
        row=np.zeros(TOTAL)
        for k,v in packet['row']:row[k]=float(F(v))
        bound=float(F(packet['bound']));scale=max(1.,abs(bound),max(abs(row)))
        row[-1]=-.001;added.append(row/scale);addedrhs.append(bound/scale)
    for k,(l,u) in enumerate(captured['bounds']+[(None,None)]*41+[(0,None)]):
        if l is not None:
            row=np.zeros(TOTAL);row[k]=-1;added.append(row);addedrhs.append(-l)
        if u is not None:
            row=np.zeros(TOTAL);row[k]=1;added.append(row);addedrhs.append(u)
    A=vstack([A,csr_matrix(added)],format='csr');b=np.r_[b,addedrhs];linearrows=len(b)
    psdrows=[];psdrhs=[];exacthash=hashlib.sha256()
    for e,slab in enumerate(slabs['scalar_slabs']):
        beta=list(map(F,slab['beta']));eps=F(slab['epsilon'])
        for i,j,c,coeff in frozen.block_entries(e,beta,eps,center,radius):
            exacthash.update(json.dumps([e,i,j,str(c),[[k,str(v)] for k,v in sorted(coeff.items())]],separators=(',',':')).encode())
            factor=1 if i==j else np.sqrt(2);row=np.zeros(TOTAL)
            for k,v in coeff.items():row[k]=-factor*float(v)
            psdrows.append(row);psdrhs.append(factor*float(c))
    AP=csr_matrix(psdrows);bp=np.array(psdrhs)
    assert exacthash.hexdigest()==json.loads((HERE/'cover-residual-psd-bregman-full-cone.json').read_bytes())['exact_PSD_affine_map_serialization_sha256']
    hrows=[];hmap=[]
    for j in range(9):
        for i in range(j,9):
            coeff={V+e:HESSIAN_SCALE*F(aw,base.g.D) for e,(l,r,aw) in enumerate(base.g.TERMS) if l<=i<r and l<=j<r}
            factor=1 if i==j else np.sqrt(2);row=np.zeros(TOTAL)
            for k,v in coeff.items():row[k]=-factor*float(v)
            hrows.append(row);hmap.append([i,j,[[k,str(v)] for k,v in sorted(coeff.items())]])
    AH=csr_matrix(hrows);bh=np.zeros(45)
    probe=np.r_[np.zeros(V),np.linspace(-2,3,41),0.]
    direct=np.zeros((9,9))
    for e,(i,j,aw) in enumerate(base.g.TERMS):direct[i:j,i:j]+=float(HESSIAN_SCALE*F(aw,base.g.D))*probe[V+e]
    herror=float(np.max(abs(unpack_n(-AH@probe,9)-direct)));assert herror<1e-12
    out.update({'base_rows':nr,'linear_rows':linearrows,'energy_packets':2,
        'exact_residual_PSD_affine_map_serialization_sha256':exacthash.hexdigest(),
        'Hessian_exact_affine_map':hmap,'Hessian_map_max_error_hint':herror})
    A=csc_matrix(vstack([A,AP,AH],format='csc'));b=np.r_[b,bp,bh];c=np.r_[np.zeros(NV),1.]
    out['phase']='single_conic_solve_running';save()
    try:
        result=scs.solve({'A':A,'b':b,'c':c},{'l':linearrows,'s':[11]*41+[9]},
            verbose=False,time_limit_secs=45,max_iters=10000,eps_abs=1e-7,eps_rel=1e-7)
        out['solver_info']=result['info'];out['raw_primal']=result['x'].tolist()
        out['raw_dual']=result['y'].tolist();out['raw_conic_slack']=result['s'].tolist()
        xx=result['x'];out['raw_energy_slack_hint']=float(xx[-1]*.001)
        out['minimum_linear_slack_hint']=float(min(b[:linearrows]-A[:linearrows]@xx))
        mats=bp-AP@xx
        out['minimum_41_normalized_PSD_eigenvalue_hint']=min(float(np.linalg.eigvalsh(unpack_n(mats[66*e:66*(e+1)],11))[0]) for e in range(41))
        out['minimum_physical_Hessian_eigenvalue_hint']=float(np.linalg.eigvalsh(unpack_n(-AH@xx,9))[0])/float(HESSIAN_SCALE)
        out['positive_or_infeasible_hint']=bool(result['info']['status_val']==-2 or xx[-1]*.001>1e-6)
        out['phase']='completed_single_joint_jet_Hessian_test';save()
    except BaseException as exc:
        out['phase']='exception_stopped';out['exception']=repr(exc);out['traceback']=traceback.format_exc();save();raise
    print(json.dumps({k:out[k] for k in ['phase','joint_graph_facet_count',
        'joint_graph_mixed_u_v_facet_count','solver_info','raw_energy_slack_hint',
        'minimum_linear_slack_hint','minimum_41_normalized_PSD_eigenvalue_hint',
        'minimum_physical_Hessian_eigenvalue_hint','positive_or_infeasible_hint','seconds']}),flush=True)

if __name__=='__main__':main()
