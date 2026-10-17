"""One fixed pure-rational budget to transfer old analytic inequalities.

No optimizer, eigensolver, rank/precision/parameter search, new point or
kernel evaluation. Keep the frozen lambda and integer Gram factors.
Use the unique agreed odd/even monomial box supports and column-l1 SOS
bound. A strict exact K<margin is required; failure permits no retry.
"""
from pathlib import Path
from fractions import Fraction as F
import ctypes,gzip,hashlib,json,sys,time,traceback
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
RAY=ROOT/'research-goal-20261017-actual-sextic-exact-ray';ACTUAL=ROOT/'research-goal-20261017-actual-sextic-static'
OUT=HERE/'transfer-budget.json';RECEIPT=HERE/'budget-receipt.json';DL=10**12;LIMIT=1536*1024**2;FILELIMIT=40*1024**2
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def mem():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi');p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}
def add(p,q,scale=F(1)):
    for k,a in q.items():
        v=p.get(k,F(0))+scale*a
        if v:p[k]=v
        else:p.pop(k,None)
    return p
def main():
    assert not OUT.exists() and not RECEIPT.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'run_budget_once.py',RAY/'exact-ray-files.json',RAY/'quantized-ray.json.gz',
        RAY/'exact-enclosure-certificate.json',ROOT/'research-goal-20261017-quartic/quartic-model.json.gz',
        ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz',ACTUAL/'actual-sextic.json.gz',
        ROOT/'research-goal-20261017-actual-sextic-cone/new-row-hashes.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert pins[paths[2].relative_to(ROOT).as_posix()]=='c19797f38f2a7687817735b91163bf329d6f2ad7cb26e9989b3e76bb99f5ceae'
    report={'scope':__doc__,'phase':'loading_fixed_frozen_data','source_sha256_start':pins,'memory_snapshots':[],
        'optimizer_calls':0,'eigh_calls':0,'Lean_invocations':0,'parameter_rank_or_precision_changes':0,
        'actual_cell_exclusion_Lean_proved':False,'new_zero_proportion_proven':False}
    def save(phase):
        m=mem();m.update({'phase':phase,'elapsed_milliseconds':int((time.monotonic()-began)*1000)});report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        tmp=RECEIPT.with_suffix('.partial');tmp.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8');tmp.replace(RECEIPT)
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('fixed-budget1.5GiB RSS guard')
    save('loading_fixed_frozen_data')
    try:
        manifest=json.loads(paths[2].read_bytes())
        for field in ['package_files','dependency_files','reconstructed_dependency_files','runtime_dependency_files']:
            for r in manifest[field]:assert (ROOT/r['path']).stat().st_size==r['bytes'] and sha(ROOT/r['path'])==r['sha256']
        ray=json.loads(gzip.decompress(paths[3].read_bytes()));cert=json.loads(paths[4].read_bytes())
        old=json.loads(gzip.decompress(paths[5].read_bytes()));model=json.loads(gzip.decompress(paths[6].read_bytes()))
        packet=json.loads(gzip.decompress(paths[7].read_bytes()));rowdoc=json.loads(paths[8].read_bytes())
        mon=[tuple(m) for m in model['monomials']];mi={m:k for k,m in enumerate(mon)};c=F(packet['target']);margin=F(cert['strict_margin'])
        assert c==F(11,1250) and margin>0 and cert['strict_negative_constant_upper']
        assert packet['monomials']==model['monomials'] and mon[:715]==[tuple(m) for m in old['monomials']]
        assert packet['normalized_gap_center']==old['normalized_gap_center'] and packet['normalized_gap_radius']==old['normalized_gap_radius']
        assert all(v>0 for v in packet['all_nine_original_free_margins_SC_units'])
        even=[all(m.count(r)%2==0 for r in set(m)) for m in mon]
        def upper(p):
            return sum((a if k==0 else max(F(0),a) if even[k] else abs(a)) for k,a in p.items())
        powers=[{k:F(v) for k,v in p['terms']} for p in packet['span_powers']]
        L6={k:F(v) for k,v in packet['pressure_polynomial']};P5=[{0:F(v)} for v in packet['pressure_coefficients_b']];E6=[{} for _ in range(9)]
        which=[[] for _ in packet['edges']]
        for r,eids in enumerate(packet['coordinate_incident_edges']):
            for eid in eids:which[eid].append(r)
        for eid,e in enumerate(packet['edges']):
            polys=[]
            for field in ['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']:
                p={}
                for j,a in enumerate(e[field]):add(p,powers[e['power_ids'][j]],F(e['weight'])*F(a))
                polys.append(p)
            add(L6,polys[0])
            for r in which[eid]:add(P5[r],polys[1]);add(E6[r],polys[2])
        del powers,polys
        # Bind the reconstructed polynomials to exactly the frozen181 rows.
        for descriptor,record in zip(packet['new_scalar_rows'],rowdoc['rows']):
            if descriptor['kind']=='absolute_energy_L6':
                q={k:-a for k,a in L6.items()};q[0]=q.get(0,F(0))+c;meta=['actual_sextic_absolute_energy_unsoftened']
            else:
                r=descriptor['coordinate'];test=descriptor['test_monomial_id'];sign=descriptor['sign'];q=E6[r].copy()
                add(q,{mi[tuple(sorted(mon[k]+mon[test]))]:a for k,a in P5[r].items()},F(sign));meta=['actual_sextic_free_KKT',r,test,sign]
            canonical={'coefficients':[[k-1,str(-a)] for k,a in sorted(q.items()) if k],
                'bound':str(q.get(0,F(0))),'scale':record['scale'],'meta':meta}
            assert hashlib.sha256(json.dumps(canonical,sort_keys=True,separators=(',',':')).encode()).hexdigest()==record['exact_canonical_row_sha256']
        H=[{k:F(v) for k,v in p} for p in old['KKT_cubic_polynomials']]
        E=[{k:F(v) for k,v in p} for p in old['KKT_dynamic_error_polynomials']]
        L2={k:F(v) for k,v in old['old_quadratic_L2']}
        lambdas=ray['scalar_weight_numerators'];assert ray['scalar_weight_denominator']==DL and lambdas[5793]==lambdas[5794]==0
        epsilon=[];bounds=[]
        for r in range(9):
            base=add(E6[r].copy(),E[r],F(-1));difference=add(H[r].copy(),P5[r],F(-1))
            plus=upper(add(base.copy(),difference));minus=upper(add(base.copy(),difference,F(-1)))
            eps=max(F(0),plus,minus);epsilon.append(eps)
            bounds.append({'coordinate':r,'upper_E6_minus_E4_plus_P3_minus_P5':str(plus),
                'upper_E6_minus_E4_minus_P3_plus_P5':str(minus),'epsilon':str(eps)})
            save('fixed_gradient_epsilon_'+str(r))
        difference=add(L2.copy(),L6,F(-1));upper0=upper({k:a/c for k,a in difference.items()});eps0=max(F(0),upper0)
        q0=add({0:F(1)},L2,F(-1)/c)
        assert q0=={k:F(v) for k,v in model['multipliers'][1]['terms']}
        # Confirm all180 old scalar rows are precisely E4+sign*test*P3.
        scalar_costs=[];kscalar=F(0)
        for r in range(9):
            for test in range(10):
                for si,sign in enumerate([-1,1]):
                    rid=4185+20*r+2*test+si;row=old['linear_rows'][rid]
                    assert row['meta']==['free_KKT_with_dynamic_error',r,test,sign]
                    expected=E[r].copy();shift={mi[tuple(sorted(mon[k]+mon[test]))]:a for k,a in H[r].items()};add(expected,shift,F(sign))
                    actual={k+1:-F(v) for k,v in row['coefficients']};actual[0]=F(row['bound'])
                    actual={k:a for k,a in actual.items() if a};assert actual==expected
                    scale=F(row['scale']);assert scale>0;weight=F(lambdas[rid],DL)
                    cost=weight*epsilon[r]/scale;assert cost>=0;kscalar+=cost
                    scalar_costs.append({'scalar_row':rid,'coordinate':r,'test_monomial_id':test,'sign':sign,
                        'normalized_weight':str(weight),'row_scale':str(scale),'cost':str(cost)})
        def sos_bound(bid):
            f=ray['PSD_factors'][bid];block=model['blocks'][bid]
            assert f['block_id']==bid and f['factor_denominator']==DL and f['multiplier_id']==block['multiplier_id']
            integers=f['factor_numerators_by_row'];rank=f['column_count']
            assert len(integers)==block['size'] and all(len(row)==rank for row in integers)
            numer=sum(sum(abs(row[col]) for row in integers)**2 for col in range(rank))
            divisor=F(f['positive_rational_block_divisor']);assert divisor>0
            assert divisor==max([F(1)]+[abs(F(v)) for _,v in model['multipliers'][block['multiplier_id']]['terms']])
            return numer,F(numer,DL*DL),divisor
        gram_costs=[];kgram=F(0)
        for r in range(9):
            for si,sign in enumerate([-1,1]):
                bid=55+2*r+si;block=model['blocks'][bid];qid=block['multiplier_id']
                assert model['multipliers'][qid]['meta']==['free_gradient_E_plus_sign_P',r,sign]
                expected=add(E[r].copy(),H[r],F(sign));assert expected=={k:F(v) for k,v in model['multipliers'][qid]['terms']}
                numer,bound,divisor=sos_bound(bid);cost=epsilon[r]*bound/divisor;assert cost>=0;kgram+=cost
                gram_costs.append({'Gram_block':bid,'coordinate':r,'sign':sign,'column_l1_square_sum_integer':numer,
                    'Gram_factor_denominator_squared':DL*DL,'SOS_upper_B':str(bound),'block_divisor':str(divisor),'cost':str(cost)})
        numer,bound,divisor=sos_bound(1);ksublevel=eps0*bound/divisor
        sublevel={'Gram_block':1,'upper_L2_minus_L6_divided_by_c':str(upper0),'epsilon0':str(eps0),'c':str(c),
            'column_l1_square_sum_integer':numer,'Gram_factor_denominator_squared':DL*DL,
            'SOS_upper_B':str(bound),'block_divisor':str(divisor),'cost':str(ksublevel)}
        K=kscalar+kgram+ksublevel;passed=K<margin
        data={'schema':'fixed-old-analytic-transfer-budget-v1','scope':__doc__,'source_sha256':pins,'same_original_nine_y':True,
            'fixed_full_certificate_margin':str(margin),'new_necessary_assumptions':['L6<=c','abs(P5_r)<=E6_r for all9free coordinates','y in[-1,1]^9'],
            'epsilon_gradient':bounds,'scalar180_costs':scalar_costs,'old_gradient18_Gram_costs':gram_costs,'old_sublevel_Gram_cost':sublevel,
            'total_old_scalar180_cost':str(kscalar),'total_old_gradient18_Gram_cost':str(kgram),'total_old_sublevel_Gram_cost':str(ksublevel),
            'total_cost_K':str(K),'strict_K_less_than_margin':passed,'remaining_margin':str(margin-K),
            'bound_method':'Exact odd/even monomial box support; fixed B=sum_columns(l1norm_integer_factor_column)^2/10^24; no other bound tried.',
            'old_analytic_dependencies_removed_by_this_budget':passed,'eight_swap_analytic_dependencies_retained':True,
            'new_L6_P5_E6_actual_analytic_obligations_retained':True,'no_E4_nonnegativity_assumption_needed':True,
            'actual_point_polynomial_reasoning_not_a_general_pseudomoment_extension_claim':True,
            'actual_cell_exclusion_Lean_proved':False,'complete_global_cover_proven':False,'new_zero_proportion_proven':False,
            'optimizer_calls':0,'eigh_calls':0,'rank_precision_parameter_trials':0,'Lean_invocations':0}
        encoded=json.dumps(data,separators=(',',':'),allow_nan=False).encode();assert len(encoded)<FILELIMIT;OUT.write_bytes(encoded+b'\n')
        report.update({'budget_packet':{'path':OUT.relative_to(ROOT).as_posix(),'bytes':OUT.stat().st_size,'sha256':sha(OUT)},
            'gradient_epsilons_float_hints':[float(x) for x in epsilon],'sublevel_epsilon_float_hint':float(eps0),
            'cost180_scalar_float_hint':float(kscalar),'cost18_Gram_float_hint':float(kgram),'cost_sublevel_float_hint':float(ksublevel),
            'total_K_float_hint':float(K),'margin_float_hint':float(margin),'strict_K_less_than_margin':passed,
            'K_denominator_bits':K.denominator.bit_length(),'maximum_rational_string_bytes':max(len(str(x)) for x in [K,kscalar,kgram,ksublevel,margin-K]+epsilon+[eps0]),
            'old_analytic_dependencies_removed':passed,'no_alternate_bound_attempted':True})
        save('fixed_transfer_budget_PASS' if passed else 'fixed_transfer_budget_FAILED_cost_not_below_margin')
        print(json.dumps({k:report.get(k) for k in ['phase','elapsed_milliseconds','gradient_epsilons_float_hints','sublevel_epsilon_float_hint',
            'cost180_scalar_float_hint','cost18_Gram_float_hint','cost_sublevel_float_hint','total_K_float_hint','margin_float_hint','budget_packet']}),flush=True)
    except BaseException as exc:
        report.update({'exception':repr(exc),'traceback':traceback.format_exc()});save('fixed_budget_stopped_without_retry');raise
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
