"""New-window exact Gram floors in the 69 inherited coherent lattice patterns.

Anchors are reoptimized for the actual new 24-mode profile and weights.
Point value/derivative intervals use its integer Taylor table. Positive
curvatures come from its own 16 convex-core certificates, never the old PT
library. Scalar convex Taylor bridges and the full chamber cover remain
explicit Lean obligations. This file proves no unconditional zero ratio.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse, functools, hashlib, importlib.util, json, sys, time
import numpy as np
from scipy.optimize import minimize
import cover_correlated_direction as engine
g=engine.g;w=engine.w;I=w.ik.I;HERE=Path(__file__).parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'research-20261016-w10-unconditional'))
import analytic_gram_minorant as oldgram

def ceil(x):return -((-x.numerator)//x.denominator)
def floor(x):return x.numerator//x.denominator

class Points:
    def __init__(self,table):
        self.coeff={int(n):[I(F(l),F(u)) for l,u in cs] for n,cs in table['integer_taylor_coefficients'].items()}
    @functools.lru_cache(None)
    def at_integer(self,n):return w.ik.w_jet(n,0)[0]
    @functools.lru_cache(10000)
    def at(self,p):
        n=round(p);x=p-n;coeff=self.coeff[n]
        derivative=I(0)
        for c in reversed(coeff):derivative=derivative*x+c
        integral=I(0)
        for j in range(len(coeff)-1,-1,-1):integral=integral*x+coeff[j]*F(1,j+1)
        value=self.at_integer(n)+integral*x
        ev=F(44,7)**24*abs(x)**24/factorial(24);ed=F(44,7)**24*abs(x)**23/factorial(23)
        return I(value.l-ev,value.u+ev),I(derivative.l-ed,derivative.u+ed)

def sinc_derivative(x):
    x=np.asarray(x);small=np.abs(x)<1e-4;safe=np.where(small,1,x)
    regular=(np.pi*safe*np.cos(np.pi*safe)-np.sin(np.pi*safe))/(np.pi*safe*safe)
    return np.where(small,-np.pi**2*x/3+np.pi**4*x**3/30-np.pi**6*x**5/840,regular)

def w_value_derivative(xs):
    xs=np.asarray(xs);f=w.FREQ;c=w.COEFF;normal=w.NORM
    k=((np.sinc(xs[:,None]+f)+np.sinc(xs[:,None]-f))@c)/(2*normal)
    d=((sinc_derivative(xs[:,None]+f)+sinc_derivative(xs[:,None]-f))@c)/(2*normal)
    return k*k,2*k*d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--floor',default='11/1250')
    ap.add_argument('--output',type=Path,default=HERE/'cover-newwindow-gram.json')
    args=ap.parse_args();start=time.monotonic();target=F(args.floor)
    pattern_source=ROOT/'research-20261016-w10-unconditional/analytic_gram_wide_adaptive.json'
    patterns=json.loads(pattern_source.read_bytes())['results']
    tablepath=HERE/'cover_newjet.json';table=json.loads(tablepath.read_bytes());points=Points(table)
    curvaturepath=HERE/'window_interval_kernel.json';curves=json.loads(curvaturepath.read_bytes())
    assert curves['all_positive']
    alpha={int(r['center']):F(floor(F(r['minimum_lower'])*10**12),2*10**12) for r in curves['regions']}
    assert all(v>0 for v in alpha.values())
    terms=[(i,j,F(a,g.D)) for i,j,a in g.TERMS];bs=[F(b,g.D) for b in g.BS];af=np.array([float(a) for i,j,a in terms]);bf=np.array(list(map(float,bs)))
    spanmatrix=np.zeros((len(terms),9))
    for t,(i,j,a) in enumerate(terms):spanmatrix[t,i:j]=1
    def value(x):return float(bf@x+af@w_value_derivative(spanmatrix@x)[0])
    def gradient(x):return bf+spanmatrix.T@(af*w_value_derivative(spanmatrix@x)[1])
    results=[];radius=F(21,100)
    for k,pattern in enumerate(patterns,1):
        integers=pattern['integer_gaps'];initial=np.array(pattern['anchor_numerators'])/pattern['anchor_denominator']
        optimum=minimize(value,initial,jac=gradient,method='BFGS',options={'gtol':1e-12,'maxiter':1000})
        q=[F(round(float(v)*10**8),10**8) for v in optimum.x]
        integer_spans=[sum(integers[i:j]) for i,j,a in terms]
        spans=[sum(q[i:j]) for i,j,a in terms]
        if not all(abs(s-n)<radius for s,n in zip(spans,integer_spans)):
            constraints=[{'type':'ineq','fun':lambda x:np.array(integer_spans)+float(radius)-spanmatrix@x},
                         {'type':'ineq','fun':lambda x:spanmatrix@x-(np.array(integer_spans)-float(radius))}]
            optimum=minimize(value,initial,jac=gradient,bounds=[(123/128,None)]*9,constraints=constraints,method='SLSQP',options={'ftol':1e-13,'maxiter':1000})
            q=[F(round(float(v)*10**8),10**8) for v in optimum.x];spans=[sum(q[i:j]) for i,j,a in terms]
        assert all(abs(s-n)<radius for s,n in zip(spans,integer_spans)) and all(x>=F(123,128) for x in q)
        C=sum(b*x for b,x in zip(bs,q));grad=bs.copy();A=[[F(0) for _ in range(9)] for _ in range(9)];scalar=[]
        for (i,j,a),anchor,n in zip(terms,spans,integer_spans):
            v,d=points.at(anchor);vlow=F(floor(v.l*10**14),10**14);slope=F(round((d.l+d.u)*10**12/2),10**12)
            err=max(abs(d.l-slope),abs(d.u-slope));R=radius+abs(anchor-n);loss=F(ceil(err*R*10**16),10**16)
            al=alpha[n];C+=a*(vlow-loss)
            for u in range(i,j):
                grad[u]+=a*slope
                for z in range(i,j):A[u][z]+=a*al
            scalar.append({'pair':[i,j],'integer_center':n,'anchor':str(anchor),'value_lower':str(vlow),'slope':str(slope),'slope_error_loss':str(loss),'quadratic_coefficient':str(al)})
        inverse=oldgram.solve_exact(A,grad);L,diag=oldgram.ldl_exact(A);penalty=sum(x*y for x,y in zip(grad,inverse))/4;bound=C-penalty
        results.append({'integer_gaps':integers,'anchor':list(map(str,q)),'quadratic_center_constant':str(C),'gradient':list(map(str,grad)),
          'matrix':[[str(v) for v in row] for row in A],'inverse_gradient':list(map(str,inverse)),'LDL_unit_lower':[[str(v) for v in row] for row in L],
          'LDL_positive_diagonal':list(map(str,diag)),'Gram_correction':str(penalty),'lower_bound':str(bound),'lower_bound_hint':float(bound),
          'passes_floor_exact':bound>=target,'scalar_minorants':scalar,'optimization_value_hint':float(optimum.fun)})
        if k%5==0:print(json.dumps({'patterns':k,'passed':sum(r['passes_floor_exact'] for r in results),'minimum':min(r['lower_bound_hint'] for r in results),'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'parameter_sha256':hashlib.sha256(w.PARAM.read_bytes()).hexdigest(),
      'pattern_source_sha256':hashlib.sha256(pattern_source.read_bytes()).hexdigest(),'Taylor_table_sha256':hashlib.sha256(tablepath.read_bytes()).hexdigest(),
      'curvature_source_sha256':hashlib.sha256(curvaturepath.read_bytes()).hexdigest(),'floor':str(target),'radius':str(radius),'patterns':len(results),
      'passed_exact':sum(r['passes_floor_exact'] for r in results),'minimum_exact_lower_bound':str(min(F(r['lower_bound']) for r in results)),
      'minimum_lower_bound_hint':min(r['lower_bound_hint'] for r in results),'scalar_minorants':sum(len(r['scalar_minorants']) for r in results),
      'actual_kernel_quadratic_bridge_Lean_connected':False,'global_chamber_cover_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'results':results},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
