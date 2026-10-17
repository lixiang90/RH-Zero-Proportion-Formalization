"""One exact twenty-basis drift diagnostic on five frozen support samples.

Original sample floats are converted by Fraction.from_float without
rounding. Clip(g-sep,0,1) is then evaluated exactly. No new F, optimizer,
point search, alternative support, higher degree or Lean. Default read-only;
--write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'exact-budget.json'
SUPPORT=ROOT/'research-goal-20261017-ternary-coboundary/support-audit.json'
PIN=ROOT/'research-goal-20261017-ternary-coboundary/files.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();assert digest(SUPPORT)=='3d7fc73a21b5f8e8294be0eeb40881a08072412568dd684f7bed785fe1dc24db'
    assert digest(PIN)=='689cae3b63506e640b5c973aa3765682e9a3aa4b01c05913cbb9b44637f1c205'
    inputs={p.relative_to(ROOT).as_posix():digest(p)for p in [Path(__file__),SUPPORT,PIN]};p=json.loads(SUPPORT.read_bytes());assert p['passed']
    support=p['nonzero_dual_sample_support'];assert [r['sample_row']for r in support]==[1,2,7,13,15]
    weights=[F(r['weight'])for r in support];assert weights==[F(2,9),F(1,9),F(2,9),F(2,9),F(2,9)]and sum(weights)==1
    points=[]
    for row in support:
        g=[F.from_float(v)for v in row['sample_float_gaps']];assert len(g)==9 and all(v>=F(123,128)for v in g)
        phi=[min(F(1),max(F(0),v-F(123,128)))for v in g];assert all(0<=v<=1 for v in phi);points.append(phi)
    basis=[('linear',i)for i in range(4)]+[('square',i)for i in range(4)]
    off=[(i,j)for i in range(8)for j in range(i+1,8)if(i,j)<(7-j,7-i)];assert len(off)==12
    basis+=[('cross',i,j)for i,j in off];assert len(basis)==20
    def value(b,x):
        if b[0]=='linear':i=b[1];return x[i]-x[7-i]
        if b[0]=='square':i=b[1];return x[i]**2-x[7-i]**2
        _,i,j=b;return x[i]*x[j]-x[7-j]*x[7-i]
    results=[]
    for b in basis:
        samples=[];R=F(0)
        for w,x in zip(weights,points):
            h=value(b,x[:8]);t=value(b,x[1:]);assert -1<=h<=1 and -1<=t<=1
            assert value(b,x[:8][::-1])==-h and value(b,x[1:][::-1])==-t
            d=h-t;R+=w*d;samples.append(str(d))
        results.append({'basis':list(b),'sample_coboundary_features':samples,'weighted_drift':str(R),'absolute_drift':str(abs(R))})
    M=max(F(r['absolute_drift'])for r in results);maximizers=[r['basis']for r in results if F(r['absolute_drift'])==M]
    Fbar=sum((w*F(r['saved_binary_float_F'])for w,r in zip(weights,support)),F(0));assert Fbar==F(p['finite_binary_float_F_model_upper_bound'])>0
    assert 0<=M<2;upper=2*Fbar/(2-M);gain=upper-Fbar
    # For any coefficient vector a with sum|a|<=c/2:
    # c<=Fbar+sum(a_k R_k)<=Fbar+(c/2)M, hence c<=2Fbar/(2-M).
    assert upper*(1-M/2)==Fbar and gain==Fbar*M/(2-M)
    for n,h in inputs.items():assert digest(ROOT/n)==h
    out={'scope':__doc__,'passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_inputs_unchanged':True,
        'fixed_support_rows':[1,2,7,13,15],'fixed_weights':list(map(str,weights)),'separation':'123/128',
        'clip_rule':'min(1,max(0,Fraction.from_float(g)-123/128)) exactly, no rounding',
        'potential_state_gaps':8,'linear_basis':4,'square_basis':4,'offdiagonal_basis':12,'basis_count':20,
        'basis_values_bounded_by_one':True,'antisymmetry_checked_at_support_points':True,'drifts':results,
        'maximum_absolute_drift':str(M),'maximum_drift_bases':maximizers,'weighted_saved_binary_float_F':str(Fbar),
        'coefficient_budget':'sum(abs(a_k))<=c/2','weighted_necessary_inequality':'c<=Fbar+sum(a_k*R_k)<=Fbar+c*M/2',
        'finite_surrogate_floor_upper':str(upper),'maximum_gain_over_Fbar':str(gain),
        'interpretation':'Only a finite saved-binary-F support bound for this20-basis L1-budget family; no actual-F upper interval or arbitrary-potential impossibility is claimed.',
        'actual_scalar_bounds_newly_computed':False,'LP_calls':0,'kernel_evaluations':0,'new_points':0,'new_Lean_invocations':0,
        'global_mean_floor_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'max_drift_exact':str(M),'max_drift_hint':float(M),'maximizers':maximizers,
        'Fbar_hint':float(Fbar),'finite_surrogate_upper_hint':float(upper),'maximum_gain_hint':float(gain),
        'receipt_sha256':digest(OUT)if args.write_receipt else None}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
