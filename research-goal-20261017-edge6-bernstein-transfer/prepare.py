"""ONE fixed degree-six per-edge Bernstein transfer preparation.

No optimizer, eigensolver, actual oracle, point selection, rank/precision
change, subdivision, bound scan or Lean invocation. Keep all old/new
polynomials and original whole-span DBM intervals. Construct epsilon9 and
epsilon0, checking full coefficient identities against the shared 5005
moment basis. Do NOT evaluate a Gram/weight payment K in this phase.
"""
from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
import ctypes
import gzip
import hashlib
import json
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'packet.json.gz'
RECEIPT=HERE/'preparation.json'
SC=32768
DEGREE=6
TARGET=F(11,1250)
RSS_LIMIT=1536*1024**2
RAW_LIMIT=40*1024**2


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def read(p):
    raw=p.read_bytes()
    return json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)


def pad(v):
    out=list(map(F,v));assert len(out)<=7
    return out+[F(0)]*(7-len(out))


def translate(v,a):
    """Coefficients of p(t+a), always padded to degree six."""
    return [sum(v[k]*comb(k,j)*a**(k-j) for k in range(j,7)) for j in range(7)]


def plus(a,b,c=F(1)):return [x+c*y for x,y in zip(a,b)]


def bernstein(v,l,u):
    assert l<u
    t=[c*(u-l)**j for j,c in enumerate(translate(v,l))]
    beta=[sum(t[j]*F(comb(i,j),comb(6,j)) for j in range(i+1)) for i in range(7)]
    # Independent inverse basis expansion: sum beta_i C(6,i)t^i(1-t)^(6-i).
    inverse=[F(0)]*7
    for i,b in enumerate(beta):
        for j in range(7-i):inverse[i+j]+=b*comb(6,i)*comb(6-i,j)*(-1)**j
    assert inverse==t
    return beta,max(beta)


def add(target,source,scale=F(1)):
    for k,value in source.items():
        value=target.get(k,F(0))+scale*value
        if value:target[k]=value
        else:target.pop(k,None)


def signature(poly):
    assert all(0<=k<5005 and v for k,v in poly.items())
    encoded=json.dumps([[k,str(v)] for k,v in sorted(poly.items())],separators=(',',':')).encode()
    return {'nonzero_coefficients':len(poly),'canonical_momentID_Fraction_pairs_sha256':hashlib.sha256(encoded).hexdigest()}


def compose(v,anchor,powers):
    out={}
    for coefficient,power in zip(translate(v,anchor),powers):add(out,power,coefficient)
    return out


def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(name,ctypes.c_size_t) for name in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    kernel=ctypes.WinDLL('kernel32');kernel.GetCurrentProcess.restype=W.HANDLE
    psapi=ctypes.WinDLL('psapi');psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}


def main():
    assert not OUT.exists() and not RECEIPT.exists()
    began=time.monotonic()
    names=['research-goal-20261017-quartic/quartic-model.json.gz',
        'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz',
        'research-goal-20261016/cover-residual-psd-rational-inputs.json',
        'research-20261016-followup/window_reweight_rational.json',
        'research-goal-20261017-actual-sextic-exact-ray/exact-enclosure-certificate.json']
    paths=[Path(__file__)]+[ROOT/name for name in names]
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    report={'scope':__doc__,'phase':'checking_frozen_inputs','source_sha256_start':initial,
        'RSS_guard_bytes':RSS_LIMIT,'raw_file_guard_bytes':RAW_LIMIT,'memory_snapshots':[],
        'Gram_payment_K_evaluated':False,'solver_calls':0,'eigensolver_calls':0,'Lean_invocations':0,
        'actual_oracle_calls':0,'new_points':0,'bound_or_parameter_scans':0,
        'old_analytic_dependencies_removed':False,'actual_cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save(phase):
        snapshot=memory();snapshot.update({'phase':phase,'elapsed_milliseconds':int((time.monotonic()-began)*1000)})
        report['memory_snapshots'].append(snapshot)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':snapshot['elapsed_milliseconds']})
        RECEIPT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
        if snapshot['peak_working_set_bytes']>RSS_LIMIT:raise MemoryError('1.5GiB peak-working-set guard')
    save('checking_frozen_inputs')
    try:
        old,new,ingredients,params,certificate=[read(ROOT/name) for name in names]
        assert initial[names[0]]=='080f60fe1a3392e12a37219be13cbd6d9ae305651acebfe01fa1920a74e11233'
        assert initial[names[1]]=='e9a1194205d9d52dfbbae2a33e3a353f6c63dd40c8013d4280cf21e7c30e48b5'
        assert old['path']==new['path']==ingredients['path']=='r001000001000100110011001'
        assert F(old['target'])==F(new['target'])==TARGET
        assert old['cell']==ingredients['cell']
        state=old['cell'];mon=[tuple(m) for m in new['monomials']]
        assert len(mon)==5005 and old['monomials']==new['monomials'][:715]
        assert old['normalized_gap_center']==new['normalized_gap_center']
        assert old['normalized_gap_radius']==new['normalized_gap_radius']
        ledger=[(i,j,F(a,params['denominator'])) for i,j,a in params['a_upper'] if a]
        assert len(ledger)==41 and all(a>0 for _,_,a in ledger)
        b=[F(v,params['denominator']) for v in params['b_numerators']]
        assert b==list(map(F,new['pressure_coefficients_b']))
        powerlist=[{mid:F(v) for mid,v in power['terms']} for power in new['span_powers']]
        oldH=[{mid:F(v) for mid,v in p} for p in old['KKT_cubic_polynomials']]
        oldE=[{mid:F(v) for mid,v in p} for p in old['KKT_dynamic_error_polynomials']]
        newP=[{0:br} for br in b];newE=[{} for _ in range(9)]
        oldP_check=[{0:br} for br in b];oldE_check=[{} for _ in range(9)]
        Dplus=[{} for _ in range(9)];Dminus=[{} for _ in range(9)]
        L6={mid:F(v) for mid,v in new['pressure_polynomial']}
        oldL2={mid:F(v) for mid,v in old['old_quadratic_L2']}
        energy=ingredients['energy_packets'][0]
        point=list(map(F,energy['centre']));assert list(map(F,old['common_anchor']))==point
        F0=F(energy['F_interval'][0]);payment=F(energy['uniform_gradient_error_payment'])
        G=[sum(map(F,interval))/2 for interval in energy['gradient_interval']]
        lower=list(map(F,energy['whole_span_second_lower']));assert len(lower)==41
        Cbar=F0-payment-sum(br*p for br,p in zip(b,point))
        q0_acc={0:Cbar};edge_records=[];tau_records=[]
        for eid,((i,j,weight),oe,ne) in enumerate(zip(ledger,old['edge_packets'],new['edges'])):
            assert oe['edge']==ne['edge']==[i,j] and F(ne['weight'])==weight
            axis=oe['span_axis'];assert axis==ne['original_span_axis']
            ell,upper=F(state[0][axis],SC),F(state[1][axis],SC)
            assert ne['whole_span_integer_bounds']==[state[0][axis],state[1][axis]] and ell<upper
            po=F(oe['anchor']);pn=F(ne['anchor']);Ro=F(oe['radius_about_anchor'])
            assert po==sum(point[i:j])
            powers=[powerlist[k] for k in ne['power_ids']]
            mu=list(map(F,oe['anchor_derivative_midpoints']));eps=list(map(F,oe['anchor_derivative_errors']))
            u3_local=pad([mu[k]/factorial(k) for k in range(4)])
            a4_local=pad([eps[0]+eps[1]*Ro,0,eps[2]/2+eps[3]*Ro/6,0,F(oe['whole_span_absolute_w5_bound'])/24])
            U3=translate(u3_local,-po);A4=translate(a4_local,-po)
            U5=translate(pad(ne['derivative_U5_coefficients_in_d']),-pn)
            E6=translate(pad(ne['derivative_E6_coefficients_in_d']),-pn)
            Lnew=translate(pad(ne['absolute_L6_coefficients_in_d']),-pn)
            expected_oldU={mid:F(v) for mid,v in oe['derivative_cubic']}
            expected_oldA={mid:F(v) for mid,v in oe['derivative_error_dynamic_quartic']}
            expandedU3=compose(U3,pn,powers);expandedA4=compose(A4,pn,powers)
            assert expandedU3==expected_oldU and expandedA4==expected_oldA
            direct_newU={};direct_newE={};direct_newL={}
            for field,poly in [('derivative_U5_coefficients_in_d',direct_newU),('derivative_E6_coefficients_in_d',direct_newE),
                               ('absolute_L6_coefficients_in_d',direct_newL)]:
                for k,value in enumerate(ne[field]):add(poly,powers[k],F(value))
            assert compose(U5,pn,powers)==direct_newU
            assert compose(E6,pn,powers)==direct_newE
            assert compose(Lnew,pn,powers)==direct_newL
            dplus=plus(plus(E6,A4,-1),plus(U3,U5,-1))
            dminus=plus(plus(E6,A4,-1),plus(U3,U5,-1),-1)
            Bplus,up=bernstein(dplus,ell,upper);Bminus,um=bernstein(dminus,ell,upper)
            pd=compose(dplus,pn,powers);md=compose(dminus,pn,powers)
            refp=direct_newE.copy();add(refp,expected_oldA,-1);add(refp,expected_oldU);add(refp,direct_newU,-1)
            refm=direct_newE.copy();add(refm,expected_oldA,-1);add(refm,expected_oldU,-1);add(refm,direct_newU)
            assert pd==refp and md==refm
            for r in range(i,j):
                add(oldP_check[r],expected_oldU,weight);add(oldE_check[r],expected_oldA,weight)
                add(newP[r],direct_newU,weight);add(newE[r],direct_newE,weight)
                add(Dplus[r],pd,weight);add(Dminus[r],md,weight)
            add(L6,direct_newL,weight)
            tau=(G[i]-b[i])/weight if j==i+1 else F(0)
            tau_records.append(str(tau))
            quadratic=pad([0,0,lower[eid]/2]);quadratic[1]=tau
            qpoly=plus(translate(quadratic,-po),Lnew,-1)
            Bq,uq=bernstein(qpoly,ell,upper)
            add(q0_acc,compose(qpoly,pn,powers),weight)
            edge_records.append({'id':eid,'edge':[i,j],'span_axis':axis,'weight':str(weight),
                'whole_span_integer_bounds':[state[0][axis],state[1][axis]],
                'whole_span_rational_bounds':[str(ell),str(upper)],'old_anchor':str(po),'new_anchor':str(pn),
                'old_U3_physical_s':list(map(str,U3)),'old_A4_physical_s':list(map(str,A4)),
                'new_U5_physical_s':list(map(str,U5)),'new_E6_physical_s':list(map(str,E6)),
                'new_L6_physical_s':list(map(str,Lnew)),
                'Dplus_physical_s':list(map(str,dplus)),'Dminus_physical_s':list(map(str,dminus)),
                'Dplus_Bernstein6':list(map(str,Bplus)),'Dminus_Bernstein6':list(map(str,Bminus)),
                'Dplus_upper':str(up),'Dminus_upper':str(um),'negative_edge_uppers_retained':True,
                'q0_tau':str(tau),'old_second_lower':str(lower[eid]),'q0_edge_physical_s':list(map(str,qpoly)),
                'q0_Bernstein6':list(map(str,Bq)),'q0_edge_upper':str(uq),
                'identity_old_U3':signature(expandedU3),'identity_old_A4':signature(expandedA4),
                'identity_Dplus':signature(pd),'identity_Dminus':signature(md),
                'all_shared5005_coefficient_identities_equal':True})
            if (eid+1)%5==0:save('edges_prepared_'+str(eid+1))
        assert oldP_check==oldH and oldE_check==oldE
        coords=[]
        for r in range(9):
            target_plus=newE[r].copy();add(target_plus,oldE[r],-1);add(target_plus,oldH[r]);add(target_plus,newP[r],-1)
            target_minus=newE[r].copy();add(target_minus,oldE[r],-1);add(target_minus,oldH[r],-1);add(target_minus,newP[r])
            assert target_plus==Dplus[r] and target_minus==Dminus[r]
            eids=[eid for eid,(i,j,w) in enumerate(ledger) if i<=r<j]
            up=sum(ledger[eid][2]*F(edge_records[eid]['Dplus_upper']) for eid in eids)
            um=sum(ledger[eid][2]*F(edge_records[eid]['Dminus_upper']) for eid in eids)
            coords.append({'coordinate':r,'incident_edges':eids,'plus_upper':str(up),'minus_upper':str(um),
                'epsilon':str(max(F(0),up,um)),'identity_plus':signature(target_plus),'identity_minus':signature(target_minus),
                'all_shared5005_coefficients_equal':True})
        expected_q0=oldL2.copy();add(expected_q0,L6,-1)
        assert expected_q0==q0_acc
        q0_raw=Cbar+sum(weight*F(edge_records[eid]['q0_edge_upper']) for eid,(i,j,weight) in enumerate(ledger))
        q0_upper=q0_raw/TARGET;eps0=max(F(0),q0_upper)
        assert len(edge_records)==41 and len(coords)==9
        q0={'old_F_lower':str(F0),'old_gradient_midpoints':list(map(str,G)),'old_uniform_payment':str(payment),
            'old_common_anchor':list(map(str,point)),'pressure_coefficients':list(map(str,b)),
            'constant_Cbar':str(Cbar),'tau_edge_coefficients':tau_records,
            'raw_difference_upper_before_dividing_c':str(q0_raw),'upper_after_dividing_c':str(q0_upper),
            'epsilon':str(eps0),'identity_L2_minus_L6':signature(q0_acc),'all_shared5005_coefficients_equal':True}
        doc={'schema':'fixed-edge6-Bernstein-epsilon-preparation-v1','scope':__doc__,
            'source_sha256_start':initial,'source_sha256_end':initial,'all_inputs_unchanged':True,
            'path':old['path'],'target':str(TARGET),'SC':SC,'Bernstein_degree':6,'subdivisions_per_edge':1,
            'physical_s_coefficient_order':'constant through power6, zero padded',
            'Bernstein_convention':'s=ell+(upper-ell)*t, polynomial=sum beta_i*choose(6,i)*t^i*(1-t)^(6-i)',
            'shared_monomial_count':5005,'monomial_source':names[1],'edges':edge_records,'coordinates':coords,'q0':q0,
            'all_41_old_U3_A4_and_new_U5_E6_L6_identities_checked':True,
            'all_18_coordinate_difference_identities_checked':True,'q0_identity_exact_before_dividing_c':True,
            'all_Bernstein_inverse_basis_identities_checked':True,'negative_edge_uppers_retained_before_incidence_aggregation':True,
            'old_polynomials_and_original_DBM_bounds_unchanged':True,
            'K_payment_evaluated':False,'K_status':'waiting_for_frozen_retained_Gram_certificate',
            'must_pay_180_old_KKT_scalar_rows':True,'must_pay_18_old_KKT_Gram_blocks':True,'must_pay_q0_Gram_block':True,
            'eight_swap_actual_dependencies_preserved':True,'old_analytic_dependencies_removed':False,
            'actual_oracle_calls':0,'new_points':0,'solver_calls':0,'eigensolver_calls':0,'Lean_invocations':0,
            'bound_or_parameter_scans':0,'actual_cell_exclusion_proven':False,'new_zero_proportion_proven':False}
        partial=OUT.with_suffix('.partial');assert not partial.exists()
        raw_hash=hashlib.sha256();raw_bytes=0
        with partial.open('wb') as target:
            with gzip.GzipFile(fileobj=target,mode='wb',compresslevel=9,mtime=0) as compressed:
                for chunk in json.JSONEncoder(separators=(',',':'),allow_nan=False).iterencode(doc):
                    data=chunk.encode('utf8');raw_bytes+=len(data)
                    if raw_bytes>RAW_LIMIT:raise MemoryError('40MiB raw packet guard')
                    raw_hash.update(data);compressed.write(data)
        partial.replace(OUT)
        report.update({'epsilon9': [x['epsilon'] for x in coords],'epsilon0':str(eps0),
            'prepared_edges':41,'coordinate_identity_pairs':9,'all_shared5005_coefficient_identities_equal':True,
            'packet':{'path':OUT.relative_to(ROOT).as_posix(),'bytes':OUT.stat().st_size,'sha256':sha(OUT),
                      'uncompressed_bytes':raw_bytes,'uncompressed_sha256':raw_hash.hexdigest()}})
        save('edge6_Bernstein_epsilon_preparation_complete_K_not_evaluated')
        print(json.dumps({'phase':report['phase'],'epsilon9_float_hints':[float(F(x['epsilon'])) for x in coords],
            'epsilon0_float_hint':float(eps0),'packet':report['packet'],'elapsed_milliseconds':report['elapsed_milliseconds'],
            'peak_working_set_bytes':max(m['peak_working_set_bytes'] for m in report['memory_snapshots'])}),flush=True)
    except BaseException as exc:
        report['exception']=repr(exc);save('preparation_stopped_without_retry_or_K');raise


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
