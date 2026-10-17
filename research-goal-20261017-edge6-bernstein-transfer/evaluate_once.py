"""ONE total transfer payment using the fixed retained Gram certificate.

No retry, subdivision, degree/rank/precision change, new oracle/point,
solver, eigensolver or Lean. Include180 normalized scalar KKT payments,
18 retained Gram KKT payments and the q0 Gram payment. The eight swap
analytic obligations remain. This cell was already historically closed;
no new frontier or global-coverage progress is claimed by this gate.
"""
from pathlib import Path
from fractions import Fraction as F
import ctypes
import gzip
import hashlib
import json
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'budget.json'
RSS_LIMIT=1536*1024**2
RAW_LIMIT=40*1024**2
# Exact fixed-input sums have denominators exceeding Python's display guard.
# This changes serialization only, not rational arithmetic or any bound.
sys.set_int_max_str_digits(0)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def read(p):
    raw=p.read_bytes()
    return json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)


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
    assert not OUT.exists(),'The authorized single K evaluation already has a record.'
    began=time.monotonic()
    names=['research-goal-20261017-edge6-bernstein-transfer/packet.json.gz',
        'research-goal-20261017-edge6-bernstein-transfer/preparation.json',
        'research-goal-20261017-fixed-gram-tail/retained-ray.json.gz',
        'research-goal-20261017-fixed-gram-tail/retained-enclosure-certificate.json',
        'research-goal-20261017-quartic/quartic-model.json.gz',
        'research-goal-20261017-degree6-static/degree6-model.json.gz',
        'research-goal-20261017-actual-sextic-exact-ray/quantized-ray.json.gz']
    paths=[Path(__file__),HERE/'evaluate_initial_serialization_failure.py']+[ROOT/name for name in names]
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert initial[names[0]]=='2df2ba58cd84f1c7a47be57a5f796298b40686a82973a2e476a5c48866eb8b91'
    assert initial[names[2]]=='b51724e37d219705828d08a5af8db3d1588563d22908fe75b9dc29261e944d21'
    assert initial[names[3]]=='7c8d083cec89942c19642a8206156a2f77879e3c1278d21c56bf3f2da2233332'
    packet,preparation,ray,cert,old,model,full=[read(ROOT/name) for name in names]
    assert preparation['phase']=='edge6_Bernstein_epsilon_preparation_complete_K_not_evaluated'
    assert packet['K_payment_evaluated'] is False and packet['Bernstein_degree']==6
    assert cert['quantized_ray_sha256']==initial[names[2]] and cert['strict_negative_constant_upper']
    margin=F(cert['strict_margin'])
    assert margin==F(-cert['constant_upper_numerator'],cert['fixed_interval_denominator'])>0
    assert margin==F(190972275995535925423158387453,200000000000000000000000000000)
    eps=[F(row['epsilon']) for row in packet['coordinates']];eps0=F(packet['q0']['epsilon'])
    assert len(eps)==9 and min(eps)>=0 and eps0>=0
    lam=ray['scalar_weight_numerators'];assert lam==full['scalar_weight_numerators']
    den=ray['scalar_weight_denominator'];assert den==10**12
    assert [i for i,v in enumerate(lam) if not v]==[5793,5794]
    assert sum(factor['column_count'] for factor in ray['PSD_factors'])==2885
    scalar_records=[];scalar_total=F(0)
    for rid,row in enumerate(old['linear_rows']):
        if row['meta'][0]!='free_KKT_with_dynamic_error':continue
        r,test,sign=row['meta'][1:];scale=F(row['scale'])
        assert 0<=r<9 and 0<=test<10 and sign in [-1,1] and scale>0 and lam[rid]>0
        term=F(lam[rid],den)*eps[r]/scale;scalar_total+=term
        scalar_records.append({'scalar_row':rid,'coordinate':r,'test':test,'sign':sign,
            'lambda_numerator':lam[rid],'row_scale':str(scale),'epsilon':str(eps[r]),'payment':str(term)})
    assert len(scalar_records)==180
    gram_records=[];gram_kkt=F(0);gram_q0=F(0)
    for factor in ray['PSD_factors']:
        bid=factor['block_id']
        if bid!=1 and not 55<=bid<=72:continue
        n=factor['size'];cols=factor['column_count'];numbers=factor['factor_numerators_by_row']
        denominator=factor['factor_denominator'];divisor=F(factor['positive_rational_block_divisor'])
        assert denominator==10**12 and divisor>0 and len(numbers)==n and all(len(row)==cols for row in numbers)
        original=full['PSD_factors'][bid];ids=factor['retained_original_column_ids']
        assert ids==sorted(set(ids)) and len(ids)==cols
        assert numbers==[[row[k] for k in ids] for row in original['factor_numerators_by_row']]
        q=model['multipliers'][factor['multiplier_id']]
        assert divisor==max([F(1)]+[abs(F(v)) for k,v in q['terms']])
        l1_squared_sum=sum(sum(abs(numbers[i][j]) for i in range(n))**2 for j in range(cols))
        B=F(l1_squared_sum,denominator**2)/divisor
        if bid==1:
            assert q['meta']==['old_PSD_upgrade',1]
            epsilon=eps0;coordinate=None;gram_q0+=epsilon*B
        else:
            coordinate=(bid-55)//2
            assert q['meta']==['free_gradient_E_plus_sign_P',coordinate,-1 if (bid-55)%2==0 else 1]
            epsilon=eps[coordinate];gram_kkt+=epsilon*B
        gram_records.append({'block_id':bid,'basis_size':n,'retained_columns':cols,'coordinate':coordinate,
            'integer_column_l1_squared_sum':l1_squared_sum,'factor_denominator':denominator,
            'positive_block_divisor':str(divisor),'SOS_upper_B':str(B),'epsilon':str(epsilon),'payment':str(epsilon*B)})
    assert len(gram_records)==19 and sum(row['coordinate'] is not None for row in gram_records)==18
    total=scalar_total+gram_kkt+gram_q0;passed=total<margin
    mem=memory();assert mem['peak_working_set_bytes']<=RSS_LIMIT
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    report={'scope':__doc__,'status':'fixed_retained_Gram_edge6_transfer_budget_PASS' if passed else 'fixed_retained_Gram_edge6_transfer_budget_FAIL',
        'source_sha256_start':initial,'source_sha256_end':final,'all_inputs_unchanged':True,
        'path':packet['path'],'target':packet['target'],'epsilon_packet_sha256':initial[names[0]],
        'retained_ray_sha256':initial[names[2]],'retained_exact_certificate_sha256':initial[names[3]],
        'scalar_weight_denominator':den,'Gram_factor_denominator':10**12,'retained_columns':2885,
        'scalar_KKT_payments':scalar_records,'Gram_payments':gram_records,
        'scalar180_total':str(scalar_total),'Gram18_KKT_total':str(gram_kkt),'Gram_q0_total':str(gram_q0),
        'K_total':str(total),'retained_exact_margin':str(margin),'margin_minus_K':str(margin-total),
        'strict_budget_passed':passed,'fixed_mathematical_candidates':1,
        'K_arithmetic_evaluations_including_failed_serialization':2,
        'initial_attempt_failed_after_total_K_at_str_serialization':True,
        'initial_error':'ValueError: Exceeds the limit (4300 digits) for integer string conversion at str(scalar_total)',
        'recovery_changes_only':'sys.set_int_max_str_digits(0) and explicit attempt provenance; no epsilon/weight/factor/divisor/margin/bound changed',
        'Bernstein_degree':6,'subdivisions_per_edge':1,
        'all180_scalar_and18_KKT_Gram_and_q0_included':True,'eight_swap_actual_obligations_preserved':True,
        'actual_old_provider_removed_in_Lean':False,'actual_cell_exclusion_proven':False,
        'cell_already_historically_closed_per_root_audit':True,'new_frontier_closure_claimed':False,
        'new_global_cover_or_source_compliance_claimed':False,'new_zero_proportion_proven':False,
        'solver_calls':0,'eigensolver_calls':0,'Lean_invocations':0,'actual_oracle_calls':0,
        'new_points':0,'rank_precision_parameter_or_bound_scans':0,'RSS_guard_bytes':RSS_LIMIT,
        'raw_file_guard_bytes':RAW_LIMIT,'resource_snapshot':mem,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    raw=(json.dumps(report,indent=2,allow_nan=False)+'\n').encode();assert len(raw)<RAW_LIMIT
    OUT.write_bytes(raw)
    print(json.dumps({'status':report['status'],'scalar180_float_hint':float(scalar_total),
        'Gram18_float_hint':float(gram_kkt),'q0_float_hint':float(gram_q0),'K_float_hint':float(total),
        'retained_margin_float_hint':float(margin),'strict_budget_passed':passed,
        'elapsed_milliseconds':report['elapsed_milliseconds'],'peak_working_set_bytes':mem['peak_working_set_bytes']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
