"""One deterministic coefficient-l1-budgeted deletion of fixed Gram columns.

No eigensolver, optimizer, rounding, precision/rank/parameter trial. Costs
are exact, sorted by(cost,block,column). Delete one maximal prefix with
sum<=delta/4. Preserve every remaining integer column in its old order.
"""
from pathlib import Path
from fractions import Fraction as F
import ctypes,gzip,hashlib,json,sys,time,traceback
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;FULL=ROOT/'research-goal-20261017-actual-sextic-exact-ray'
OUT=HERE/'retained-ray.json.gz';RECEIPT=HERE/'pruning.json';PLAN=HERE/'tail-selection.json';DATA=HERE/'RetainedRayData.lean'
DL=10**12;DS=10**30;LIMIT=1536*1024**2;FILELIMIT=40*1024**2
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi');p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}
def main():
    assert not any(p.exists() for p in [OUT,RECEIPT,PLAN,DATA]);began=time.monotonic()
    paths=[Path(__file__),FULL/'exact-ray-files.json',FULL/'quantized-ray.json.gz',FULL/'exact-enclosure-certificate.json',
        ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert initial[paths[1].relative_to(ROOT).as_posix()]=='c19797f38f2a7687817735b91163bf329d6f2ad7cb26e9989b3e76bb99f5ceae'
    report={'scope':__doc__,'phase':'loading_fixed_full_certificate','source_sha256_start':initial,'memory_snapshots':[],
        'new_eigh_calls':0,'optimizer_calls':0,'integer_rerounding_operations':0,'budget_or_prefix_trials':1,
        'Lean_invocations':0,'same_fixed_lambda_and_integer_entries':True,'actual_cell_exclusion_Lean_proved':False,
        'new_unconditional_zero_proportion_proven':False}
    def save(phase):
        m=memory();m.update({'phase':phase,'elapsed_milliseconds':int((time.monotonic()-began)*1000)});report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        tmp=RECEIPT.with_suffix('.partial');tmp.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8');tmp.replace(RECEIPT)
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('fixed-tail1.5GiB RSS guard')
    save('loading_fixed_full_certificate')
    try:
        ray=json.loads(gzip.decompress(paths[2].read_bytes()));cert=json.loads(paths[3].read_bytes());model=json.loads(gzip.decompress(paths[4].read_bytes()))
        assert ray['scalar_weight_denominator']==DL and cert['strict_negative_constant_upper']
        delta=F(cert['strict_margin']);cap=delta/4;roundreserve=F(1,10**20)
        assert ray['scalar_weight_numerators'][5793]==ray['scalar_weight_numerators'][5794]==0
        assert len(set(b['multiplier_id'] for b in model['blocks']))==73
        plans=model['entry_plans'];assert len({(p[0],p[1]) for p in plans})==len(plans)
        target_count=sum(p[3] for p in plans);assert target_count==1416525
        maxatoms=5803*716+8580*2+181*5005+target_count
        assert F(2*maxatoms,DS)<roundreserve and roundreserve<delta/4
        costs=[];blocks=[];entry_before=0
        for bid,(factor,block) in enumerate(zip(ray['PSD_factors'],model['blocks'])):
            assert factor['block_id']==bid and factor['factor_denominator']==DL and factor['multiplier_id']==block['multiplier_id']
            divisor=F(factor['positive_rational_block_divisor']);assert divisor>0
            terms=model['multipliers'][block['multiplier_id']]['terms'];qnorm=sum(abs(F(v)) for _,v in terms)
            assert divisor==max([F(1)]+[abs(F(v)) for _,v in terms])
            ints=factor['factor_numerators_by_row'];n=factor['size'];rank=factor['column_count']
            assert n==len(ints) and all(len(row)==rank for row in ints)
            l1s=[sum(abs(row[j]) for row in ints) for j in range(rank)]
            for j,l1 in enumerate(l1s):costs.append((qnorm*F(l1*l1,DL*DL)/divisor,bid,j))
            blocks.append({'block_id':bid,'row_count':n,'original_columns':rank,'coefficient_l1_of_q':str(qnorm),
                'positive_rational_block_divisor':str(divisor),'column_l1_integer_norms':l1s})
            entry_before+=n*rank
        assert len(costs)==3010 and entry_before==190150
        costs.sort();deleted=[];tailcost=F(0)
        for cost,bid,j in costs:
            if tailcost+cost>cap:break
            tailcost+=cost;deleted.append([bid,j])
        assert tailcost<=cap
        next_cost=costs[len(deleted)][0] if len(deleted)<len(costs) else None
        assert next_cost is None or tailcost+next_cost>cap
        selected={tuple(v) for v in deleted};newfactors=[];entry_after=0
        for bid,factor in enumerate(ray['PSD_factors']):
            kept=[j for j in range(factor['column_count']) if (bid,j) not in selected]
            newrows=[[row[j] for j in kept] for row in factor['factor_numerators_by_row']]
            f={k:factor[k] for k in ['block_id','size','multiplier_id','factor_denominator','positive_rational_block_divisor']}
            f.update({'column_count':len(kept),'factor_numerators_by_row':newrows,'retained_original_column_ids':kept})
            newfactors.append(f);entry_after+=f['size']*len(kept)
        retained={k:ray[k] for k in ['scalar_row_count','moment_column_count','unbounded_slack_column','scalar_weight_denominator',
            'scalar_weight_numerators','forced_zero_scalar_rows','rounded_weights_before_forced_zero','PSD_block_count','native_scalar_sign','trace_semantics']}
        retained.update({'schema':'deterministically-retained-fixed-integer-Gram-ray-v1','scope':__doc__,'PSD_factors':newfactors,
            'source_sha256':initial,'original_full_ray_sha256':sha(paths[2]),'historical_original_eigh_calls':73,
            'new_eigh_calls':0,'optimizer_calls':0,'integer_rerounding_operations':0,'exact_contradiction_checked':False})
        raw=json.dumps(retained,separators=(',',':'),allow_nan=False).encode();assert len(raw)<FILELIMIT
        compressed=gzip.compress(raw,compresslevel=9,mtime=0);OUT.write_bytes(compressed)
        # An ordinary data-only Lean representation, deliberately uncompiled.
        # It has no decoder or compressed-string machinery.
        def lit(value):
            if isinstance(value,list):return '['+', '.join(lit(v) for v in value)+']'
            return str(value)
        text='/- Fixed retained integer data only. Not compiled; no proof/checker included. -/\nnamespace FixedRetainedRayData\n'
        text+='def commonDenominator : Nat := '+str(DL)+'\n'
        text+='def scalarNumerators : List Nat := '+lit(retained['scalar_weight_numerators'])+'\n'
        text+='def blockColumnCounts : List Nat := '+lit([f['column_count'] for f in newfactors])+'\n'
        text+='def gramFactors : List (List (List Int)) := '+lit([f['factor_numerators_by_row'] for f in newfactors])+'\n'
        text+='end FixedRetainedRayData\n'
        encoded=text.encode();assert len(encoded)<FILELIMIT;DATA.write_bytes(encoded)
        predicted=delta-tailcost-roundreserve;assert predicted>0
        selection={'schema':'fixed-exact-cost-sorted-Gram-prefix-v1','scope':__doc__,'source_sha256':initial,
            'common_integer_denominator':DL,'full_margin_delta':str(delta),'single_tail_budget':str(cap),
            'rounding_reserve':str(roundreserve),'fixed_DS':DS,'atom_count_upper_bound_each_aggregate':maxatoms,
            'both_rounding_cost_upper_bound':str(F(2*maxatoms,DS)),'rounding_cost_strictly_below_reserve':True,
            'cost_formula':'sum(abs(allqcoeff inclconstant))/positiveDiv * column_l1_integer_norm^2 / 10^24',
            'sort_rule':'exact Fraction cost ascending; then block_id, original_column_id ascending',
            'block_cost_data':blocks,'exact_sorted_column_order':[[b,j] for _,b,j in costs],
            'deleted_sorted_prefix':deleted,'total_deleted_cost':str(tailcost),
            'next_column_exact_cost':str(next_cost) if next_cost is not None else None,
            'predicted_retained_margin_at_least':str(predicted),'full_columns':len(costs),'deleted_columns':len(deleted),
            'retained_columns':len(costs)-len(deleted),'full_integer_factor_entries':entry_before,
            'retained_integer_factor_entries':entry_after,'empty_factor_blocks':[f['block_id'] for f in newfactors if not f['column_count']],
            'scalar_weights_unchanged':True,'integer_entries_unchanged':True,'new_eigh_calls':0,'optimizer_calls':0,
            'rebuild_attempts_authorized':1,'new_actual_kernel_inputs':0,'Lean_invocations':0,
            'source_size':{'retained_ray_uncompressed_JSON_bytes':len(raw),'retained_ray_gzip_bytes':len(compressed),
                'ordinary_uncompiled_Lean_data_file_bytes':len(encoded),'website_source_limit_bytes':2000000,
                'remaining_bytes_after_data_only':2000000-len(encoded),
                'checker_and_actual_tables_reserve_allocated':False,'other_cells_and_fullcover_reserve_allocated':False,
                'checker_tables_fullcover_reserve_bytes':None,'complete_source_budget_met':False}}
        planraw=json.dumps(selection,separators=(',',':'),allow_nan=False).encode();assert len(planraw)<FILELIMIT;PLAN.write_bytes(planraw+b'\n')
        report.update({'retained_packet':{'path':OUT.relative_to(ROOT).as_posix(),'bytes':OUT.stat().st_size,'sha256':sha(OUT),'uncompressed_bytes':len(raw)},
            'selection_packet':{'path':PLAN.relative_to(ROOT).as_posix(),'bytes':PLAN.stat().st_size,'sha256':sha(PLAN)},
            'uncompiled_data_source':{'path':DATA.relative_to(ROOT).as_posix(),'bytes':len(encoded),'sha256':sha(DATA)},
            'deleted_columns':len(deleted),'retained_columns':len(costs)-len(deleted),'retained_factor_entries':entry_after,
            'total_deleted_cost':str(tailcost),'predicted_margin':str(predicted),'source_size':selection['source_size']})
        save('one_deterministic_prefix_selected_no_retained_rebuild_yet')
        print(json.dumps({k:report.get(k) for k in ['phase','elapsed_milliseconds','deleted_columns','retained_columns',
            'retained_factor_entries','retained_packet','selection_packet','uncompiled_data_source','source_size']}),flush=True)
    except BaseException as exc:
        report.update({'exception':repr(exc),'traceback':traceback.format_exc()});save('fixed_tail_stopped_without_alternate_trial');raise
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
