"""Exact arithmetic for redesigned windows; not a global local-floor proof.

The Taylor inequalities and sinc-sum comparison are mathematical inputs
already proved generically in the inherited Core. This computes rational
specializations and Bernstein coefficients; it does not invoke Lean.
"""
from __future__ import annotations
import argparse, hashlib, json
from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
HERE=Path(__file__).resolve().parent
PI_LO=F(314159265358979323846,10**20)
PI_HI=F(314159265358979323847,10**20)

def interval_sum(terms):
    return tuple(sum((t[i] for t in terms),F(0)) for i in range(2))

def scale(v,c):return (v[0]*c,v[1]*c) if c>=0 else (v[1]*c,v[0]*c)

def sinc_bounds(x2,half_shift=False):
    # Average sinc(pi*x +/- sqrt(2)/2), or sinc(pi*x).
    def powers(r):
        if not half_shift:return (x2[0]**r,x2[1]**r)
        return tuple(sum((F(comb(2*r,2*j),2**j)*x2[k]**(r-j)
                     for j in range(r+1)),F(0)) for k in range(2))
    lower=interval_sum([scale(powers(r),F((-1)**r,factorial(2*r+1))) for r in range(40)])[0]
    upper=interval_sum([scale(powers(r),F((-1)**r,factorial(2*r+1))) for r in range(41)])[1]
    return lower,upper

def small_pair_bound(nums,cut=F(123,128)):
    x2=(PI_LO**2*cut**2,PI_HI**2*cut**2)
    base=sinc_bounds(x2,True);si=sinc_bounds(x2)
    q=sum((F(v,10**9)*(-1)**j*cut**2/(cut**2-j*j)
           for j,v in enumerate(nums,1)),F(0))
    perturb=scale(si,q);K=(base[0]+perturb[0],base[1]+perturb[1])
    zlo=sum((F((-1)**r,2**r*factorial(2*r+1)) for r in range(18)),F(0))
    zhi=sum((F((-1)**r,2**r*factorial(2*r+1)) for r in range(19)),F(0))
    assert K[0]>0 and zlo>0
    kl=K[0]/zhi;ku=K[1]/zlo;wl=kl**2;wu=ku**2
    floor=F(wl.numerator*10**12//wl.denominator,10**12)
    assert floor<=wl<=wu<floor+F(1,10**12)
    return {'cut':str(cut),'kernel_lower':str(F(kl.numerator*10**12//kl.denominator,10**12)),
      'w_lower':str(floor),'w_lower_decimal':float(floor),
      'interval_width_w':float(wu-wl),
      'domain_extension_argument':'Positive even profile implies k is strictly decreasing on (0,1); k(cut)>0, hence w(x)>=w(cut) for 0<=x<=cut.',
      'kernel_interval_proved_in_Lean':False,'all_fraction_checks_passed':True}

def majorant_certificate():
    C=[F(2)-F(119,200)+F(7921,150000)-F(13,5760),
       -F(119,50)+F(7921,6250)-F(13,96),F(31684,37500)-F(13,24),-F(13,90)]
    P=[sum((a*b for i,a in enumerate(C) for j,b in enumerate(C) if i+j==r),F(0))*F(7,10) for r in range(7)]
    P[0]-=F(109,100)*F(27,25);P[1]+=F(109,100);P[2]-=F(109,600)
    bern=[sum((P[i]*F(1,4)**i*F(comb(k,i),comb(6,i)) for i in range(k+1)),F(0)) for k in range(7)]
    # Reconstruct power coefficients in y=4*x exactly.
    reconstructed=[sum((bern[k]*comb(6,k)*comb(6-k,r-k)*(-1)**(r-k)
                        for k in range(r+1)),F(0)) for r in range(7)]
    assert reconstructed==[v/F(4)**r for r,v in enumerate(P)]
    assert min(bern)>F(1,40)
    # C >= 29/20 -5*x/4 >0 follows from the inherited Core hC argument.
    return {'sum_abs_coefficients_limit':'2/25','profile_upper':'(109/100)*(27/25-x+x^2/6), x=s^2',
      'sinc_sum_lower_coefficients':[str(v) for v in C],
      'majorant_gap_power_coefficients':[str(v) for v in P],
      'bernstein_basis':'binomial(6,k)*(4*x)^k*(1-4*x)^(6-k), x in [0,1/4]',
      'bernstein_coefficients':[str(v) for v in bern],
      'minimum_bernstein_coefficient':str(min(bern)),
      'verified_positive_margin':'1/40',
      'consequence':'For every normalized Fourier profile with sum_abs<=2/25, rho*v + 1/40 <= same scaledMajorant. Same separated spectral bound 1253/650 remains available after the analytic bridge is rebuilt.',
      'ordinary_Lean_checked_this_run':False,'all_fraction_checks_passed':True}

def freeze(source,candidate_c):
    data=json.loads(source.read_text());nums=data['final_window_coefficient_numerators_1e9']
    cs=[F(v,10**9) for v in nums]
    C=sum((F((-1)**r,2**r*factorial(2*r)) for r in range(17)),F(0))
    S=sum((F((-1)**r,2**r*factorial(2*r+1)) for r in range(18)),F(0))
    PAM=sum((c*c*(F(1,2)-1/(4*PI_HI**2*j*j)) for j,c in enumerate(cs,1)),F(0))
    Hlower=F(3,2)-C/S-PAM/S**2
    CL=sum((F((-1)**r,2**r*factorial(2*r)) for r in range(18)),F(0))
    SU=sum((F((-1)**r,2**r*factorial(2*r+1)) for r in range(19)),F(0))
    PL=sum((c*c*(F(1,2)-1/(4*PI_LO**2*j*j)) for j,c in enumerate(cs,1)),F(0))
    Hupper=F(3,2)-CL/SU-PL/SU**2
    assert Hlower<Hupper and Hupper-Hlower<F(1,10**22)
    h=F(Hlower.numerator*10**40//Hlower.denominator,10**40)
    pressure=F(10999681,2500000000);kap=(h-pressure)/(1-candidate_c)
    mass=sum(map(abs,cs));assert mass<F(2,25)
    d1=F(2)+F(44,7)*sum((j*abs(c) for j,c in enumerate(cs,1)),F(0))
    d2=F(2)+F(1936,49)*sum((j*j*abs(c) for j,c in enumerate(cs,1)),F(0))
    pair=small_pair_bound(nums);assert F(pair['w_lower'])>candidate_c
    return {'status':'EXACT_WINDOW_PARAMETERS_WITH_UNPROVED_GLOBAL_FLOOR',
      'source':str(source.relative_to(HERE.parent)).replace('\\','/'),
      'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'profile':'v(t)=cos(sqrt(2)*t)+sum_j (num_j/10^9)*cos(2*pi*j*t)',
      'normalization':'Z=sinc(sqrt(2)/2); all integer cosine perturbations have zero integral',
      'coefficient_numerators':nums,'coefficient_denominator':10**9,
      'sum_abs_coefficients_exact':str(mass),
      'positive_profile_lower_rational':'67/100',
      'profile_positive_reason':'cos(sqrt(2)*t)>=1-t^2>=3/4; subtract sumabs<2/25 gives >67/100',
      'global_first_derivative_abs_upper':str(d1),'global_second_derivative_abs_upper':str(d2),
      'energy_identity':'H=3/2-cos(theta)/sinc(theta)-sum_j c_j^2*(1/2-1/(4*pi^2*j^2))/sinc(theta)^2; theta^2=1/2',
      'pi_upper':str(PI_HI),'PAM_upper':str(PAM),'exact_analytic_H_lower_expression':str(Hlower),
      'exact_analytic_H_upper_expression':str(Hupper),'analytic_H_interval_width':float(Hupper-Hlower),
      'rounded_H_lower':str(h),'rounded_H_lower_decimal':float(h),
      'proposed_local_floor':str(candidate_c),'proposed_local_floor_status':'UNPROVED',
      'pressure_sum':str(pressure),'conditional_kappa_exact':str(kap),
      'conditional_percent':100*float(kap),'small_pair_bound':pair,
      'more_ambitious_unproved_local_floor':'2201/250000' if len(nums)==24 else None,
      'more_ambitious_conditional_percent':100*float((h-pressure)/(1-F(2201,250000))) if len(nums)==24 else None,
      'proof_scope':'Fraction arithmetic only. Generic Taylor and energy identities must be specialized in Lean. Whole-domain local floor for the redesigned kernel is not established.',
      'website_upload_ready':False}

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=HERE/'window_exact_parameters.json');args=p.parse_args()
    records=[freeze(HERE/'window_profile_search.json',F(439,50000)),
             freeze(HERE/'window_profile_24.json',F(11,1250))]
    report={'majorant':majorant_certificate(),'windows':records,'higher_zero_proportion_proven':False}
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'majorant_margin':report['majorant']['minimum_bernstein_coefficient'],
      'windows':[{k:r[k] for k in ['coefficient_numerators','sum_abs_coefficients_exact','rounded_H_lower_decimal','proposed_local_floor','conditional_percent','small_pair_bound']} for r in records]},indent=2))

if __name__=='__main__':main()
