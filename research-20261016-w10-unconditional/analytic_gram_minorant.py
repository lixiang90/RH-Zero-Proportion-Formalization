"""Exact finite quadratic minorants of the inherited affine PT envelope.

This validates rational inequalities only. The generic envelope argument
is written in analytic_gram_note.md; its Lean implementation and a global
cover by the tested chambers are still absent. No zeta theorem is claimed.
All selected alpha values are heuristic choices, but every accepted scalar
minorant is independently verified with exact rational arithmetic below.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,sys,time
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'research-20261016-w10-cert'))
import generate as g

HERE=Path(__file__).parent;SC=g.SC

def upper_hull(raw,L,U):
    # Tuples are (slope, intercept, PT point). Slopes increase monotonically.
    best={}
    for const,slope,p in raw:
        s=F(slope,10**10);b=F(const,g.WD)
        if s not in best or b>best[s][0]:best[s]=(b,p)
    hull=[];starts=[]
    for s,(b,p) in sorted(best.items()):
        while hull:
            cross=(hull[-1][1]-b)/(s-hull[-1][0])
            if len(hull)==1 or cross>starts[-1]:break
            hull.pop();starts.pop()
        start=None if not hull else cross
        hull.append((s,b,p));starts.append(start)
    segments=[]
    for k,line in enumerate(hull):
        left=L if starts[k] is None else max(L,starts[k])
        right=U if k+1==len(hull) else min(U,starts[k+1])
        if left<right:segments.append((left,right,line))
    assert segments[0][0]==L and segments[-1][1]==U
    assert all(a[1]==b[0] for a,b in zip(segments,segments[1:]))
    for left,right,(s,b,p) in segments:
        for x in [left,right]:
            value=s*x+b
            assert all(value>=ss*x+bb for ss,(bb,pp) in best.items())
    return segments

def solve_exact(A,b):
    n=len(b);rows=[list(A[i])+[b[i]] for i in range(n)]
    for k in range(n):
        assert rows[k][k]>0,('nonpositive Schur pivot',k,rows[k][k])
        pivot=rows[k][k]
        for j in range(k,n+1):rows[k][j]/=pivot
        for i in range(k+1,n):
            v=rows[i][k]
            for j in range(k,n+1):rows[i][j]-=v*rows[k][j]
    x=[F(0)]*n
    for i in range(n-1,-1,-1):x[i]=rows[i][-1]-sum(rows[i][j]*x[j] for j in range(i+1,n))
    assert all(sum(A[i][j]*x[j] for j in range(n))==b[i] for i in range(n))
    return x

def ldl_exact(A):
    n=len(A);L=[[F(int(i==j)) for j in range(n)] for i in range(n)];D=[]
    for j in range(n):
        d=A[j][j]-sum(L[j][k]**2*D[k] for k in range(j));assert d>0;D.append(d)
        for i in range(j+1,n):L[i][j]=(A[i][j]-sum(L[i][k]*L[j][k]*D[k] for k in range(j)))/d
    assert all(A[i][j]==sum(L[i][k]*D[k]*L[j][k] for k in range(n)) for i in range(n) for j in range(n))
    return L,D

def quad_certificate(t0,alpha,segments,epsilon_budget=None):
    # The best affine support at the rational anchor.
    line=max((z[2] for z in segments),key=lambda z:z[0]*t0+z[1]);s,b,p=line
    vertices=sorted(set(x for left,right,l in segments for x in [left,right]))
    if epsilon_budget is not None:
        caps=[(epsilon_budget+ss*x+bb-(s*x+b))/(x-t0)**2
            for left,right,(ss,bb,pp) in segments for x in [left,right] if x!=t0]
        cap=min(caps);assert cap>=0
        quant=10**12;alpha=min(alpha,F(cap.numerator*quant//cap.denominator,quant))
    deficit=max(alpha*(x-t0)**2+s*x+b-(ss*x+bb)
        for left,right,(ss,bb,pp) in segments for x in [left,right])
    epsilon=max(F(0),deficit)
    # Upward round to a stable fixed denominator; every following test exact.
    epsD=10**16;epsilon=F((epsilon.numerator*epsD+epsilon.denominator-1)//epsilon.denominator,epsD)
    for l,r,(ss,bb,pp) in segments:
        for x in [l,r]:assert alpha*(x-t0)**2+s*x+b-epsilon<=ss*x+bb
    return s,b,p,epsilon,len(vertices),alpha

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--radius',default='21/100');ap.add_argument('--output',default='analytic_gram_minorant.json');ap.add_argument('--epsilon-budget');args=ap.parse_args()
    radius=F(args.radius)
    start=time.monotonic();lp=HERE/'analytic_lattice_probe.json';source=json.loads(lp.read_text())
    param=g.PAR;raw=json.loads(param.read_text());D=raw['denominator']
    a=[(i,j,F(v,D)) for i,j,v in raw['a_upper'] if v];bs=[F(b,D) for b in raw['b_numerators']]
    alpha={int(n):F(int(float(v)*10**9/4),10**9) for n,v in source['sampled_scalar_curvature_lower_bounds'].items()}
    hulls={};hull_meta=[]
    for n in range(1,16):
        l=max(F(17,20),F(n)-radius);u=F(n)+radius
        lsc=l.numerator*SC//l.denominator;usc=-(-u.numerator*SC//u.denominator)
        # PT bounds are outward: supports valid on [lsc/SC, usc/SC].
        lines=g.lines(lsc,usc)
        segments=upper_hull(lines,l,u);hulls[n]=segments
        hull_meta.append({'integer_center':n,'lower':str(l),'upper':str(u),'alpha':str(alpha[n]),
            'outward_lower_SC':lsc,'outward_upper_SC':usc,
            'eligible_PT_or_constant_lines':len(lines),'envelope_segments':len(segments),
            'segments':[{'lower':str(lf),'upper':str(rg),'slope':str(s),'intercept':str(b),'PT_point':p}
                for lf,rg,(s,b,p) in segments]})
    results=[]
    for row in source['results']:
        q=[F(v,row['anchor_denominator']) for v in row['anchor_numerators']]
        spans=[sum(q[i:j]) for i,j,aa in a];centers=[round(t) for t in spans]
        A=[[F(0) for _ in range(9)] for _ in range(9)];grad=bs.copy();C=sum(b*x for b,x in zip(bs,q))
        eps_total=F(0);diag=[F(0)]*9;term_data=[]
        for (i,j,aa),t0,n in zip(a,spans,centers):
            al=alpha[n];s,b,p,epsilon,nv,al=quad_certificate(t0,al,hulls[n],None if args.epsilon_budget is None else F(args.epsilon_budget))
            C+=aa*(s*t0+b-epsilon);eps_total+=aa*epsilon
            for r in range(i,j):
                grad[r]+=aa*s
                for rr in range(i,j):A[r][rr]+=aa*al
            if j==i+1:diag[i]+=aa*al
            term_data.append({'pair':[i,j],'center':n,'anchor':str(t0),'PT_point':p,
                'alpha':str(al),'line_slope':str(s),'line_intercept':str(b),'epsilon':str(epsilon),'checked_vertices':nv})
        inv=solve_exact(A,grad);ll,dd=ldl_exact(A);penalty=sum(x*y for x,y in zip(grad,inv))/4
        lower=C-penalty
        diagonal_penalty=sum(v*v/(4*d) for v,d in zip(grad,diag))
        width=max([F(0)]+[sum(q[:k])-sum(row['integer_gaps'][:k]) for k in range(1,10)])-min([F(0)]+[sum(q[:k])-sum(row['integer_gaps'][:k]) for k in range(1,10)])
        results.append({'integer_gaps':row['integer_gaps'],'anchor_numerators':row['anchor_numerators'],
            'anchor_denominator':row['anchor_denominator'],'coherent_phase_width_exact':str(width),
            'anchor_in_chamber':width<=radius,'quadratic_center_value_exact':str(C),
            'total_epsilon_loss_exact':str(eps_total),'total_epsilon_loss_float':float(eps_total),
            'exact_Gram_correction':str(penalty),'Gram_lower_bound_exact':str(lower),'Gram_lower_bound_float':float(lower),
            'matrix_A':[[str(v) for v in rr] for rr in A],'gradient':[str(v) for v in grad],
            'A_inverse_gradient':[str(v) for v in inv],
            'LDL_unit_lower':[[str(v) for v in rr] for rr in ll],'LDL_positive_diagonal':[str(v) for v in dd],
            'diagonal_only_lower_bound_float':float(C-diagonal_penalty),
            'passes_candidate_floor_exact':bool(lower>=F(433,50000)),'terms':term_data})
    outcome={'scope':__doc__,'chamber_span_radius_exact':str(radius),'epsilon_budget_exact':args.epsilon_budget,'parameter_sha256':hashlib.sha256(param.read_bytes()).hexdigest(),
        'lattice_probe_sha256':hashlib.sha256(lp.read_bytes()).hexdigest(),'hulls':hull_meta,
        'chambers':len(results),'exact_scalar_minorants_checked':sum(len(r['terms']) for r in results),
        'exact_scalar_endpoint_checks':sum(2*(t['checked_vertices']-1) for r in results for t in r['terms']),
        'candidate_floor_pass_count':sum(r['passes_candidate_floor_exact'] for r in results),
        'minimum_exact_Gram_lower_bound_float':min(r['Gram_lower_bound_float'] for r in results),
        'maximum_epsilon_loss_float':max(r['total_epsilon_loss_float'] for r in results),
        'results':results,'seconds':time.monotonic()-start,
        'table_soundness_inherited':True,'generic_quadratic_checker_formalized':False,
        'global_chamber_coverage_proven':False,'new_unconditional_zeta_bound_proven':False}
    (HERE/args.output).write_text(json.dumps(outcome,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in outcome.items() if k not in ['results','hulls']}),flush=True)

if __name__=='__main__':main()
