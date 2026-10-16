"""Two-cell strong phase/KKT outer approximation, floating hints only.

Retain every old DBM, scalar derivative graph and KKT row.  Add shared
45-pair Hermitian phase layers, exact-rational trigonometric interval/arc
bounds and supplied rational uniform five-coefficient packets.  Negative
eigenvectors are quantized to Gaussian integers before their necessary PSD
rank-one cuts enter HiGHS.  No LP outcome is an accepted exclusion proof.
No old source, packet, main runner or pinned certificate is modified.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache,reduce
from math import gcd
import argparse,gzip,hashlib,json,time
import numpy as np
from scipy.optimize import linprog
import cover_lifted_graph_probe as old
import window_interval_kernel as ik
HERE=Path(__file__).parent;ROOT=HERE.parent;g=old.g;SC=g.SC
sha=lambda b:hashlib.sha256(b).hexdigest()


@lru_cache(None)
def sinpi_point(q):
    q=F(q);q=q-2*((q+1)//2)
    if q in [F(-1),F(0),F(1)]:return F(0),F(0)
    if q==F(1,2):return F(1),F(1)
    if q==F(-1,2):return F(-1),F(-1)
    v=ik.interval.sin_interval(ik.PI*q);return max(F(-1),v.l),min(F(1),v.u)


@lru_cache(None)
def sinpi_range(l,u):
    l,u=F(l),F(u);assert l<=u
    if u-l>=2:return F(-1),F(1)
    a,b=sinpi_point(l),sinpi_point(u);lower=min(a[0],b[0]);upper=max(a[1],b[1])
    first=-((-(l-F(1,2))).numerator//(l-F(1,2)).denominator)
    last=(u-F(1,2)).numerator//(u-F(1,2)).denominator
    for k in range(first,last+1):
        if k%2:lower=F(-1)
        else:upper=F(1)
    return lower,upper


def arc_bounds(l,u,multiple):
    l=F(l*multiple,SC);u=F(u*multiple,SC);real=sinpi_range(l+F(1,2),u+F(1,2));imag=sinpi_range(l,u);chord=None
    if u-l<2:
        center=(l+u)/2;half=(u-l)/2;cosc=sinpi_point(center+F(1,2));sinc=sinpi_point(center)
        a=sum(cosc)/2;b=sum(sinc)/2;error=max(abs(a-cosc[0]),abs(a-cosc[1]))+max(abs(b-sinc[0]),abs(b-sinc[1]))
        cosine_half=sinpi_point(half+F(1,2));chord=(a,b,cosine_half[0]-error)
    return {'real':real,'imag':imag,'chord':chord}


class Model:
    def __init__(self,state,taylor,graph,case):
        self.state=state;self.N=len(g.TERMS);self.P=9+self.N;self.R=self.P+180;self.V=self.R+9
        rr,bb,integer,meta,data,obj,stats=old.build(state,taylor,graph,True);self.rows=[];self.rhs=list(bb);self.row_meta=[['old',m] for m in meta]
        for row in rr:self.rows.append(np.r_[row[:self.P],np.zeros(180),row[self.P:]])
        self.old_row_count=len(self.rows);self.arcs={};self.cut_keys=set();self.cuts=[];self.arc_rows=[];self.payments=[]
        for layer in range(2):
            for z,(i,j) in enumerate(g.ALL):
                bounds=arc_bounds(state[0][z],state[1][z],layer+1);self.arcs[layer,z]=bounds
                for part,name in enumerate(['real','imag']):
                    lower,upper=bounds[name];index=self.index(layer,z,part);row=np.zeros(self.V);row[index]=1
                    self.add(row,float(upper),['phase_interval',layer,z,part,1]);self.add(-row,float(-lower),['phase_interval',layer,z,part,-1])
                    self.arc_rows.append({'layer':layer,'axis':z,'part':part,'lower':str(lower),'upper':str(upper)})
                if bounds['chord']:
                    a,b,target=bounds['chord'];row=np.zeros(self.V);row[self.index(layer,z,0)]=-float(a);row[self.index(layer,z,1)]=-float(b)
                    self.add(row,float(-target),['phase_chord',layer,z,str(a),str(b),str(target)])
        assert case['cell']==[list(v) for v in state];terms=case['terms'];assert len(terms)==self.N
        for t,((i,j,aw),term) in enumerate(zip(g.TERMS,terms)):
            assert term['t']==t and term['i']==i and term['j']==j;z=g.LOOK[i,j]
            if 'l_units' in term:assert term['l_units']==state[0][z] and term['u_units']==state[1][z]
            elif 'l' in term:assert F(term['l'])*SC==state[0][z] and F(term['u'])*SC==state[1][z]
            lower=list(map(F,term['lower']));upper=list(map(F,term['upper']));reference=list(map(F,term['reference']));assert len(reference)==len(lower)==len(upper)==5
            assert all(a<=r<=b for a,r,b in zip(lower,reference,upper))
            errors=[max(r-a,b-r) for a,r,b in zip(lower,reference,upper)]
            absolute=[F(1)]+[max(map(abs,self.arcs[layer,z][part])) for layer,part in [(0,'real'),(0,'imag'),(1,'real'),(1,'imag')]]
            payment=sum(e*a for e,a in zip(errors,absolute));row=np.zeros(self.V);row[9+t]=1
            for coefficient,(layer,part) in zip(reference[1:],[(0,0),(0,1),(1,0),(1,1)]):row[self.index(layer,z,part)]=-float(coefficient)
            self.add(row,float(reference[0]+payment),['uniform_phase_derivative',t,1]);self.add(-row,float(-reference[0]+payment),['uniform_phase_derivative',t,-1])
            self.payments.append({'term':t,'reference':list(map(str,reference)),'component_errors':list(map(str,errors)),
              'phase_absolute_bounds':list(map(str,absolute)),'total_payment':str(payment)})
        self.objective=np.r_[np.zeros(self.R),np.ones(9)];self.bounds=[(None,None)]*self.R+[(0,None)]*9
        self.old_graph_statistics=stats

    def index(self,layer,z,part):return self.P+90*layer+2*z+part
    def add(self,row,bound,meta):self.rows.append(row);self.rhs.append(bound);self.row_meta.append(meta)
    def matrices(self,x):
        layers=[]
        for layer in range(2):
            M=np.eye(10,dtype=complex)
            for z,(i,j) in enumerate(g.ALL):
                value=x[self.index(layer,z,0)]+1j*x[self.index(layer,z,1)];M[i,j]=value;M[j,i]=value.conjugate()
            layers.append(M);yield ['layer',layer],M
        for z,(i,j) in enumerate(g.ALL):
            v=layers[0][i,j];w=layers[1][i,j]
            yield ['edge_Toeplitz',z],np.array([[1,v,w],[v.conjugate(),1,v],[w.conjugate(),v.conjugate(),1]],dtype=complex)

    def rank_one_cut(self,kind,vector,x):
        pivot=next(v for v in vector if abs(v)>1e-9);v=vector/(pivot/abs(pivot));v=v/max(abs(v))
        for scale in [2**16,2**24]:
            values=[[round(float(a.real)*scale),round(float(a.imag)*scale)] for a in v];common=reduce(gcd,[abs(a) for pair in values for a in pair]);assert common>0
            values=[[a//common,b//common] for a,b in values];constant=sum(a*a+b*b for a,b in values);coeff={}
            def insert(layer,z,ri,im):
                for index,coefficient in [(self.index(layer,z,0),2*ri),(self.index(layer,z,1),-2*im)]:coeff[index]=coeff.get(index,0)+coefficient
            def product(i,j):
                a,b=values[i];c,d=values[j];return a*c+b*d,a*d-b*c
            if kind[0]=='layer':
                layer=kind[1]
                for z,(i,j) in enumerate(g.ALL):insert(layer,z,*product(i,j))
            else:
                z=kind[1];a,b=product(0,1);c,d=product(1,2);insert(0,z,a+c,b+d);insert(1,z,*product(0,2))
            key=(tuple(kind),tuple(tuple(v) for v in values))
            value=(constant+sum(c*x[i] for i,c in coeff.items()))/constant
            wanted=next(M for label,M in self.matrices(x) if label==kind);numeric=np.array([a+1j*b for a,b in values])
            direct=float(np.vdot(numeric,wanted@numeric).real)/constant
            assert abs(value-direct)<1e-9,('rank-one cut coefficient/sign mismatch',kind,value,direct)
            if value>=-1e-8:continue
            if key in self.cut_keys:return False
            self.cut_keys.add(key);row=np.zeros(self.V)
            for i,c in coeff.items():row[i]=-c/constant
            stored={'matrix':kind,'vector_gaussian_integers':values,'constant':str(constant),
              'phase_coefficients':[[i-self.P,str(c)] for i,c in sorted(coeff.items()) if c],'violated_primal_value_hint':float(value)}
            self.cuts.append(stored);self.add(row,1.,['rational_rank_one_PSD_cut',len(self.cuts)-1]);return True
        return False

    def run(self,max_rounds):
        history=[];last=None;status='round_limit';eig_rows=[]
        for iteration in range(max_rounds+1):
            lp=linprog(self.objective,A_ub=self.rows,b_ub=self.rhs,bounds=self.bounds,method='highs');last=lp
            report={'iteration':iteration,'LP_status':int(lp.status),'LP_success':bool(lp.success),'rows':len(self.rows),'cuts_before':len(self.cuts),
              'L1_residual_hint':float(lp.fun) if lp.success else None}
            if not lp.success:
                status='infeasible_hint' if lp.status==2 else 'LP_solver_failure';history.append(report);break
            eig_rows=[];negative=[]
            for kind,M in self.matrices(lp.x):
                eigenvalues,eigenvectors=np.linalg.eigh(M);small=float(eigenvalues[0]);eig_rows.append({'matrix':kind,'minimum_eigenvalue_hint':small})
                if small<-1e-8:negative.append((small,kind,eigenvectors[:,0]))
            report['negative_matrices']=len(negative);report['minimum_eigenvalue_hint']=min(r['minimum_eigenvalue_hint'] for r in eig_rows)
            if lp.fun>1e-8:status='positive_KKT_residual_hint';history.append(report);break
            if not negative:status='PSD_feasible_primal_hint';history.append(report);break
            if iteration==max_rounds:history.append(report);break
            added=0
            for small,kind,vector in sorted(negative,key=lambda r:r[0]):added+=self.rank_one_cut(kind,vector,lp.x)
            report['cuts_added']=added;history.append(report)
            if not added:status='no_new_separating_cut';break
        primal=None
        if last is not None and last.success:
            x=last.x;slack=np.array(self.rhs)-np.array(self.rows)@x
            primal={'gaps':x[:9].tolist(),'derivatives':x[9:self.P].tolist(),'phase_layer_pair_real_imag':[[[float(x[self.index(layer,z,0)]),float(x[self.index(layer,z,1)])] for z in range(45)] for layer in range(2)],
              'KKT_slacks':x[self.R:].tolist(),'minimum_linear_slack_hint':float(min(slack)),'phase_matrix_eigenvalues':eig_rows}
        return {'status':status,'positive_or_infeasible_hint':status in ['positive_KKT_residual_hint','infeasible_hint'],'history':history,
          'rational_rank_one_cuts':self.cuts,'final_primal':primal,'coefficient_payments':self.payments,'phase_arc_bounds':self.arc_rows,
          'old_graph_statistics':self.old_graph_statistics,'old_rows_retained':self.old_row_count,'final_rows':len(self.rows),
          'not_a_strict_certificate':True}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--rounds',type=int,default=20);args=ap.parse_args();assert 0<=args.rounds<=20
    args.packet=args.packet.resolve();args.output=args.output.resolve()
    start=time.monotonic();packetraw=args.packet.read_bytes();packet=json.loads(packetraw);assert packet['SC']==SC
    source_raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(source_raw));lookup={r['path']:r for r in source['cases']}
    assert packet['parameters_sha256']==sha(old.context.w.PARAM.read_bytes()) and packet['input_sha256']==sha(source_raw)
    allowed=['r001000001000001101011101','r001000001000001110011100'];assert 1<=len(packet['cases'])<=2 and all(c['path'] in allowed for c in packet['cases'])
    taylor=old.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');oracle=old.GraphOracle(HERE/'cover_newjet.json');rows=[]
    for case in packet['cases']:
        state=tuple(lookup[case['path']]['before']);model=Model(state,taylor,oracle,case);result=model.run(args.rounds);rows.append({'path':case['path'],**result})
        print(json.dumps({'path':case['path'],'status':result['status'],'iterations':len(result['history']),'PSD_cuts':len(result['rational_rank_one_cuts']),
          'final_L1':result['history'][-1]['L1_residual_hint'],'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'packet_sha256':sha(packetraw),'packet_path':args.packet.relative_to(ROOT).as_posix(),
      'parent64_input_sha256':sha(source_raw),'maximum_cut_rounds_per_case':args.rounds,'cases':len(rows),
      'strict_certificates':0,'floating_hints_only':True,'uniform_packet_Lean_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
