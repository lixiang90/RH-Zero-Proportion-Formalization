"""Independent stdlib replay of the fixed whole-span degree6 Bernstein epsilons.

No producer import, Gram payment evaluation, new oracle, solver or Lean.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import comb,factorial
import argparse,gzip,hashlib,json,sys,time
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
BASE=ROOT/'research-goal-20261017-edge6-bernstein-transfer'
OUT=HERE/'independent-replay.json'
SHA='2df2ba58cd84f1c7a47be57a5f796298b40686a82973a2e476a5c48866eb8b91'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    b=p.read_bytes();return json.loads(gzip.decompress(b)if p.suffix=='.gz'else b)
def add(a,b,s=F(1)):
    out=a.copy()
    for k,v in b.items():
        z=out.get(k,F(0))+s*v
        if z:out[k]=z
        else:out.pop(k,None)
    return out
def padded(v):
    a=list(map(F,v));assert len(a)<=7;return a+[F(0)]*(7-len(a))
def shifted(a,z):
    b=[F(0)]*7
    for k,v in enumerate(a):
        for j in range(k+1):b[j]+=v*comb(k,j)*z**(k-j)
    return b
def linear(a,b,s=F(1)):return[x+s*y for x,y in zip(a,b)]
def bernstein(a,l,u):
    assert l<u
    power=[sum(a[k]*comb(k,j)*l**(k-j)*(u-l)**j for k in range(j,7))for j in range(7)]
    beta=[sum(F(comb(i,j),comb(6,j))*power[j]for j in range(i+1))for i in range(7)]
    restored=[sum(beta[i]*comb(6,i)*comb(6-i,k-i)*(-1)**(k-i)for i in range(k+1))for k in range(7)]
    assert restored==power
    return beta,max(beta)
def signature(a):
    b=json.dumps([[k,str(v)]for k,v in sorted(a.items())],separators=(',',':')).encode()
    return{'nonzero_coefficients':len(a),'canonical_momentID_Fraction_pairs_sha256':hashlib.sha256(b).hexdigest()}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();path=BASE/'packet.json.gz';assert digest(path)==SHA
    p=read(path);report=read(BASE/'preparation.json')
    assert p['schema']=='fixed-edge6-Bernstein-epsilon-preparation-v1'
    sources={**p['source_sha256_start'],path.relative_to(ROOT).as_posix():SHA,
        (BASE/'preparation.json').relative_to(ROOT).as_posix():digest(BASE/'preparation.json'),
        Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert p['source_sha256_start']==p['source_sha256_end']==report['source_sha256_start']==report['source_sha256_end']
    for n,h in sources.items():assert digest(ROOT/n)==h
    old=read(ROOT/'research-goal-20261017-quartic/quartic-model.json.gz')
    new=read(ROOT/'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz')
    ing=read(ROOT/'research-goal-20261016/cover-residual-psd-rational-inputs.json')
    params=read(ROOT/'research-20261016-followup/window_reweight_rational.json')
    mon=[m for degree in range(7)for m in combinations_with_replacement(range(9),degree)];index={m:k for k,m in enumerate(mon)}
    assert list(map(list,mon))==new['monomials']and list(map(list,mon[:715]))==old['monomials']
    assert old['path']==new['path']==p['path']==ing['path']=='r001000001000100110011001'
    assert old['cell']==ing['cell']and old['normalized_gap_center']==new['normalized_gap_center']and old['normalized_gap_radius']==new['normalized_gap_radius']
    c=F(new['target']);assert c==F(p['target'])==F(11,1250)and p['Bernstein_degree']==6 and p['subdivisions_per_edge']==1 and not p['K_payment_evaluated']
    center=list(map(F,new['normalized_gap_center']));radius=list(map(F,new['normalized_gap_radius']))
    powers=[{k:F(v)for k,v in q['terms']}for q in new['span_powers']]
    def multiply(a,b):
        q={}
        for i,v in a.items():
            for j,w in b.items():
                k=index[tuple(sorted(mon[i]+mon[j]))];q[k]=q.get(k,F(0))+v*w
        return{k:v for k,v in q.items()if v}
    def compose(a,pn,ps):
        out={}
        for v,q in zip(shifted(a,pn),ps):out=add(out,q,v)
        return out
    ledger=[(i,j,F(a,params['denominator']))for i,j,a in params['a_upper']if a]
    b=[F(v,params['denominator'])for v in params['b_numerators']]
    assert len(ledger)==len(p['edges'])==len(new['edges'])==len(old['edge_packets'])==41 and all(a>0 for i,j,a in ledger)
    H=[{k:F(v)for k,v in q}for q in old['KKT_cubic_polynomials']];E4=[{k:F(v)for k,v in q}for q in old['KKT_dynamic_error_polynomials']]
    P5=[{0:v}for v in b];E6=[{}for _ in range(9)];Hcheck=[{0:v}for v in b];Echeck=[{}for _ in range(9)]
    Dp=[{}for _ in range(9)];Dm=[{}for _ in range(9)];L6={k:F(v)for k,v in new['pressure_polynomial']}
    energy=ing['energy_packets'][0];point=list(map(F,energy['centre']));G=[sum(map(F,x))/2 for x in energy['gradient_interval']]
    F0=F(energy['F_interval'][0]);payment=F(energy['uniform_gradient_error_payment']);Cbar=F0-payment-sum(v*x for v,x in zip(b,point))
    q0={0:Cbar};taus=[];ups=[];ums=[];uqs=[];powerchecks=0
    for eid,((i,j,a),oe,ne,r)in enumerate(zip(ledger,old['edge_packets'],new['edges'],p['edges'])):
        assert oe['edge']==ne['edge']==r['edge']==[i,j]and r['id']==eid and F(ne['weight'])==F(r['weight'])==a
        axis=oe['span_axis'];assert axis==ne['original_span_axis']==r['span_axis']
        ints=[old['cell'][0][axis],old['cell'][1][axis]];ell,u=[F(v,32768)for v in ints]
        assert ints==r['whole_span_integer_bounds']==ne['whole_span_integer_bounds']and list(map(str,[ell,u]))==r['whole_span_rational_bounds']
        po=F(oe['anchor']);pn=F(ne['anchor']);Ro=F(oe['radius_about_anchor'])
        assert po==sum(point[i:j])==F(r['old_anchor'])and pn==F(r['new_anchor'])
        ps=[powers[k]for k in ne['power_ids']]
        d={0:sum(center[i:j])-pn,**{index[(k,)]:radius[k]for k in range(i,j)}};d={k:v for k,v in d.items()if v};acc={0:F(1)}
        for q in ps:assert acc==q;powerchecks+=1;acc=multiply(acc,d)if len(mon[max(acc)])<6 else acc
        mu=list(map(F,oe['anchor_derivative_midpoints']));ep=list(map(F,oe['anchor_derivative_errors']))
        U3=shifted(padded([mu[k]/factorial(k)for k in range(4)]),-po)
        A4=shifted(padded([ep[0]+ep[1]*Ro,0,ep[2]/2+ep[3]*Ro/6,0,F(oe['whole_span_absolute_w5_bound'])/24]),-po)
        U5=shifted(padded(ne['derivative_U5_coefficients_in_d']),-pn);Enew=shifted(padded(ne['derivative_E6_coefficients_in_d']),-pn);Ln=shifted(padded(ne['absolute_L6_coefficients_in_d']),-pn)
        for field,v in [('old_U3_physical_s',U3),('old_A4_physical_s',A4),('new_U5_physical_s',U5),('new_E6_physical_s',Enew),('new_L6_physical_s',Ln)]:assert list(map(F,r[field]))==v
        oldU={k:F(v)for k,v in oe['derivative_cubic']};oldA={k:F(v)for k,v in oe['derivative_error_dynamic_quartic']}
        assert compose(U3,pn,ps)==oldU and compose(A4,pn,ps)==oldA
        nu=compose(U5,pn,ps);nep=compose(Enew,pn,ps);nl=compose(Ln,pn,ps)
        plus=linear(linear(Enew,A4,-1),linear(U3,U5,-1));minus=linear(linear(Enew,A4,-1),linear(U3,U5,-1),-1)
        pd=compose(plus,pn,ps);md=compose(minus,pn,ps)
        assert pd==add(add(add(nep,oldA,-1),oldU),nu,-1)and md==add(add(add(nep,oldA,-1),oldU,-1),nu)
        for name,co in [('Dplus',plus),('Dminus',minus)]:
            beta,upper=bernstein(co,ell,u);assert list(map(F,r[name+'_physical_s']))==co and list(map(F,r[name+'_Bernstein6']))==beta and F(r[name+'_upper'])==upper
        for name,q in [('identity_old_U3',oldU),('identity_old_A4',oldA),('identity_Dplus',pd),('identity_Dminus',md)]:assert signature(q)==r[name]
        for k in range(i,j):
            Hcheck[k]=add(Hcheck[k],oldU,a);Echeck[k]=add(Echeck[k],oldA,a);P5[k]=add(P5[k],nu,a);E6[k]=add(E6[k],nep,a);Dp[k]=add(Dp[k],pd,a);Dm[k]=add(Dm[k],md,a)
        L6=add(L6,nl,a);tau=(G[i]-b[i])/a if j==i+1 else F(0);taus.append(str(tau));low=F(energy['whole_span_second_lower'][eid])
        qp=linear(shifted(padded([0,tau,low/2]),-po),Ln,-1);beta,up=bernstein(qp,ell,u)
        assert list(map(F,r['q0_edge_physical_s']))==qp and list(map(F,r['q0_Bernstein6']))==beta and F(r['q0_edge_upper'])==up and F(r['q0_tau'])==tau and F(r['old_second_lower'])==low
        q0=add(q0,compose(qp,pn,ps),a);ups.append(F(r['Dplus_upper']));ums.append(F(r['Dminus_upper']));uqs.append(up)
    assert Hcheck==H and Echeck==E4
    eps=[]
    for k,r in enumerate(p['coordinates']):
        inc=[e for e,(i,j,a)in enumerate(ledger)if i<=k<j];assert r['coordinate']==k and r['incident_edges']==inc
        tp=add(add(add(E6[k],E4[k],-1),H[k]),P5[k],-1);tm=add(add(add(E6[k],E4[k],-1),H[k],-1),P5[k])
        assert tp==Dp[k]and tm==Dm[k]and r['identity_plus']==signature(tp)and r['identity_minus']==signature(tm)
        up=sum(ledger[e][2]*ups[e]for e in inc);um=sum(ledger[e][2]*ums[e]for e in inc);eps.append(max(F(0),up,um))
        assert F(r['plus_upper'])==up and F(r['minus_upper'])==um and F(r['epsilon'])==eps[-1]
    L2={k:F(v)for k,v in old['old_quadratic_L2']};assert q0==add(L2,L6,-1)
    rr=p['q0'];raw=Cbar+sum(a*uqs[e]for e,(i,j,a)in enumerate(ledger));eps0=max(F(0),raw/c)
    assert rr['tau_edge_coefficients']==taus and rr['identity_L2_minus_L6']==signature(q0)
    for field,v in [('old_F_lower',F0),('old_uniform_payment',payment),('constant_Cbar',Cbar),('raw_difference_upper_before_dividing_c',raw),('upper_after_dividing_c',raw/c),('epsilon',eps0)]:assert F(rr[field])==v
    assert report['epsilon9']==list(map(str,eps))and F(report['epsilon0'])==eps0
    for n,h in sources.items():assert digest(ROOT/n)==h
    out={'scope':__doc__,'passed':True,'source_sha256_start':sources,'source_sha256_end':sources,'all_inputs_unchanged':True,'packet_sha256':SHA,
        'edges_checked':41,'Bernstein_degree':6,'whole_DBM_spans_unchanged':True,'subdivisions_per_edge':1,'Bernstein_forward_and_inverse_identities':123,
        'shared_normalized_span_power_identities':powerchecks,'shared_monomial_count':5005,'old_U3_A4_and_new_U5_E6_L6_checked':True,'coordinate_difference_identities_checked':18,
        'q0_exact_L2_minus_L6_identity':True,'q0_inverse_c_paid_exactly_once':True,'negative_edge_upper_bounds_preserved':True,'epsilon9':list(map(str,eps)),'epsilon0':str(eps0),
        'K_payment_evaluated':False,'old_analytic_premises_removed':False,'fixed_cell_already_closed_in_historical_baseline':True,'new_frontier_closure_claimed':False,
        'producer_imports':0,'solver_calls':0,'eigh_calls':0,'new_points':0,'Lean_invocations':0,'actual_analytic_Lean_instances_proved':False,'global_cover_completed':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'epsilon9_hints':list(map(float,eps)),'epsilon0_hint':float(eps0),'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
