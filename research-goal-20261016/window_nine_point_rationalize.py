"""Freeze and audit the smaller nine-point alternative, without claiming a floor.

All rank capacities and improvement comparisons are exact rational arithmetic.
H is enclosed by the analytic quadratic identity using independent rational
transcendental intervals. A tested energy at a point is only an upper bound
on the unknown infimum. The ten-point primary parameters are untouched.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
import numpy as np
import window_nine_point_search as search
import window_interval_kernel as ik
HERE=Path(__file__).resolve().parent
SITE=F(34191001116882886388531117129201664,50760020691785094633026544189453125)
D=10**10
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ceil(q):return -((-q.numerator)//q.denominator)
def main():
    src=HERE/'window-nine-point-joint-search.json';old=json.loads(src.read_bytes())
    cn=[round(v*10**9) for v in old['window_coefficients_float']]
    coeff=[F(v,10**9) for v in cn]
    # Floor each nonnegative coefficient; this preserves every rank capacity.
    a=[(i,j,int(F(str(v))*D)) for i,j,v in old['a']]
    b=[ceil(F(str(v))*D) for v in old['b']]
    assert all(v>=0 for i,j,v in a) and all(v>0 for v in b)
    caps=[sum(v for i,j,v in a if j-i==d) for d in range(1,9)]
    assert all(v<=2*D for v in caps),caps
    lookup={(i,j):v for i,j,v in a}
    assert all(v==lookup[8-j,8-i] for i,j,v in a) and b==b[::-1]
    l1=sum(map(abs,coeff));assert l1<F(2,25)
    H=F(3,2)-ik.COSTH/ik.Z
    for j,c in enumerate(coeff,1):
        H-=c*c*(F(1,2)-ik.I(F(1,4*j*j))/(ik.PI*ik.PI))/(ik.Z*ik.Z)
    # Quantized conservative H lower bound; its analytic identity is the same
    # generic identity already used for the primary window. No new Lean pass.
    hn=(H.l*10**21).__floor__();h=F(hn,10**21);B=F(sum(b),D)
    assert h<=H.l
    cmin=1-(h-B)/(SITE+F(1,100000))
    candidates=[]
    for c in [F(433,50000),F(1733,200000),F(867,100000)]:
        k=(h-B)/(1-c)
        candidates.append({'floor':str(c),'conditional_kappa':str(k),
          'conditional_percent_hint':float(100*k),'exceeds_site_by_more_than_1e5':k>SITE+F(1,100000),
          'global_floor_proven':False})
    ik.COEFF=[F(1)]+coeff;ik.kernel_jet.cache_clear()
    point=[F(str(v)) for v in old['history'][-1]['worst_gaps']]
    val=sum((F(v,D)*ik.w_jet(sum(point[i:j]),0)[0] for i,j,v in a),ik.I(0))
    val+=sum(F(v,D)*x for v,x in zip(b,point))
    out={'scope':__doc__,'script_sha256':sha(Path(__file__)),
      'source_search_sha256':sha(src),'points':9,'denominator':D,
      'window_coefficient_numerators_1e9':cn,'a_upper':a,'b_numerators':b,
      'rank_capacity_numerators':caps,'profile_l1':str(l1),
      'H_interval':[str(H.l),str(H.u)],'H_conservative_lower':str(h),'B':str(B),
      'site_kappa':str(SITE),'minimum_floor_for_goal_strict':str(cmin),
      'minimum_floor_for_goal_hint':float(cmin),'candidates':candidates,
      'tested_point':list(map(str,point)),
      'tested_point_energy_interval_NOT_INFIMUM_LOWER':[str(val.l),str(val.u)],
      'profile_admissibility_Lean_proven':False,'global_floor_proven':False,
      'new_zero_proportion_proven':False,'submission_ready':False}
    dest=HERE/'window-nine-point-rational.json';dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'points':9,'l1':str(l1),'B':str(B),'H_lower':float(h),
      'minimum_floor_for_goal':float(cmin),'candidates':candidates,'tested_point_upper':float(val.u)}))
if __name__=='__main__':main()
