"""Exact atom-enclosure certificate for the one fixed rounded dual ray.

Pure stdlib. No optimizer, eigensolver, sampled point or transcendental
evaluation. DS=10^30 is fixed: each rational atom is enclosed by exact
integer divmod floor/ceil, then the explicit monomial box bounds give a
strict upper bound. This is not literal cancellation of exact residuals.
The independently checkable PSD witnesses are the given integer Gram
factors, not floating positive-eigenvalue assertions.
"""
from pathlib import Path
from fractions import Fraction as F
from array import array
import ctypes,gzip,hashlib,json,math,os,sys,time,traceback
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
STATIC=ROOT/'research-goal-20261017-degree6-static';ACTUAL=ROOT/'research-goal-20261017-actual-sextic-static'
OUT=HERE/'exact-enclosure-certificate.json';RECEIPT=HERE/'exact-combination.json'
DS=10**30;DEN=10**12;LIMIT=1536*1024**2;FILELIMIT=40*1024**2
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi');p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}
def add(p,q,scale=F(1)):
    for k,a in q.items():
        value=p.get(k,F(0))+scale*a
        if value:p[k]=value
        else:p.pop(k,None)
    return p
def main():
    assert not OUT.exists() and not RECEIPT.exists();began=time.monotonic()
    paths=[Path(__file__),HERE/'quantize_ray.py',HERE/'quantized-ray.json.gz',HERE/'quantization.json',
        STATIC/'degree6-model.json.gz',STATIC/'degree6-targets.bin',STATIC/'degree6-entryplans.bin',
        ROOT/'research-goal-20261017-quartic/quartic-model.json.gz',
        ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz',
        ACTUAL/'actual-sextic.json.gz',ROOT/'research-goal-20261017-actual-sextic-cone/new-row-hashes.json',
        ROOT/'research-goal-20261017-actual-sextic-cone/actual-sextic-cone-files.json',
        HERE/'run_exact_once.py']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    report={'scope':__doc__,'phase':'loading_frozen_exact_sources','source_sha256_start':initial,'DS':DS,
        'scalar_weight_denominator':DEN,'Gram_factor_denominator':DEN,'memory_snapshots':[],
        'optimizer_calls':0,'eigh_calls':0,'Lean_invocations':0,'actual_cell_exclusion_proven':False,
        'actual_analytic_instances_Lean_proved':False,'new_zero_proportion_proven':False}
    def save(phase):
        m=memory();m.update({'phase':phase,'elapsed_milliseconds':int((time.monotonic()-began)*1000)});report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        temp=RECEIPT.with_suffix('.partial');temp.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8');temp.replace(RECEIPT)
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('exact-combination1.5GiB RSS guard')
    save('loading_frozen_exact_sources')
    try:
        ray=json.loads(gzip.decompress(paths[2].read_bytes()));quant=json.loads(paths[3].read_bytes())
        assert ray['scalar_weight_denominator']==ray['PSD_factors'][0]['factor_denominator']==DEN
        assert quant['eigh_calls']==73 and quant['all_inputs_unchanged']
        assert sha(paths[2])==quant['quantized_packet']['sha256']
        model=json.loads(gzip.decompress(paths[4].read_bytes()));old=json.loads(gzip.decompress(paths[7].read_bytes()));family=json.loads(gzip.decompress(paths[8].read_bytes()))
        packet=json.loads(gzip.decompress(paths[9].read_bytes()));rowdoc=json.loads(paths[10].read_bytes())
        mon=[tuple(m) for m in model['monomials']];mi={m:i for i,m in enumerate(mon)}
        assert len(mon)==5005 and packet['monomials']==model['monomials']
        assert mon[:715]==[tuple(m) for m in old['monomials']]
        lam=ray['scalar_weight_numerators'];assert len(lam)==14564 and all(isinstance(v,int) and v>=0 for v in lam)
        assert lam[5793]==lam[5794]==0 and ray['forced_zero_scalar_rows']==[5793,5794]
        target=array('H');target.frombytes(paths[5].read_bytes());entry=array('I');entry.frombytes(paths[6].read_bytes())
        if sys.byteorder!='little':target.byteswap();entry.byteswap()
        assert sha(paths[5])==model['target_indices']['sha256'] and sha(paths[6])==model['block_entry_plan_indices']['sha256']
        assert len(target)==1416525 and len(entry)==96580
        lo=[0]*5005;hi=[0]*5005;atoms=0;nonintegral=0;by_section=[]
        def atom(k,n,d):
            nonlocal atoms,nonintegral
            assert 0<=k<5005 and d>0
            if not n:return
            lower,rem=divmod(DS*n,d);upper=lower+bool(rem)
            assert lower*d<=DS*n<=upper*d and upper-lower in [0,1]
            lo[k]+=lower;hi[k]+=upper;atoms+=1;nonintegral+=bool(rem)
        # Existing normalized scalar slacks (b-a.m)/scale. The only
        # unbounded-column rows are deliberately removed with exact0.
        rows=old['linear_rows']+family['additional_linear_rows'];assert len(rows)==5803
        oldbox={};active_meta={};start=atoms
        for rid,row in enumerate(rows):
            w=lam[rid];scale=F(row['scale']);assert scale>0
            if rid in [5793,5794]:
                assert w==0 and any(k==714 for k,_ in row['coefficients']);continue
            assert all(0<=k<714 for k,_ in row['coefficients'])
            if row['meta'][0]=='redundant_cube_moment_box':
                assert len(row['coefficients'])==1 and scale==1
                col,a=row['coefficients'][0];a=F(a);bound=F(row['bound']);assert a in [-1,1]
                oldbox[(col,int(a))]=(rid,bound)
            if w:
                active_meta[row['meta'][0]]=active_meta.get(row['meta'][0],0)+1
                coeff=F(row['bound']);atom(0,w*scale.denominator*coeff.numerator,DEN*scale.numerator*coeff.denominator)
                for k,value in row['coefficients']:
                    coeff=F(value);atom(k+1,-w*scale.denominator*coeff.numerator,DEN*scale.numerator*coeff.denominator)
            if (rid+1)%1000==0:save('old_scalar_rows_'+str(rid+1))
        by_section.append({'section':'old5803_scalar_rows','atoms':atoms-start});start=atoms
        boxes=model['new_moment_boxes'];assert len(boxes)==4290
        boxmap=[]
        for col in range(714):
            lowerrow,lowerbound=oldbox[(col,-1)];upperrow,upperbound=oldbox[(col,1)]
            even=all(mon[col+1].count(v)%2==0 for v in set(mon[col+1]));expectedlower=0 if even else -1
            assert lowerbound==-expectedlower and upperbound==1
            boxmap.append([col+1,expectedlower,1,lowerrow,upperrow])
        rid=5803
        for index,(col,lower,upper) in enumerate(boxes):
            assert col==714+index and upper==1
            even=all(mon[col+1].count(v)%2==0 for v in set(mon[col+1]));assert lower==(0 if even else -1)
            boxmap.append([col+1,lower,upper,rid,rid+1])
            for a,b in [(-1,-lower),(1,upper)]:
                w=lam[rid];atom(0,w*b,DEN);atom(col+1,-w*a,DEN);rid+=1
        assert rid==14383 and len(boxmap)==5004
        by_section.append({'section':'8580_added_moment_boxes','atoms':atoms-start});start=atoms
        save('all14383_existing_scalar_rows_combined_as_exact_intervals')
        # Reconstruct the actual181 exact rows from their frozen factored
        # packet and match the independent canonical exact row hashes.
        powers=[{k:F(v) for k,v in p['terms']} for p in packet['span_powers']]
        L={k:F(v) for k,v in packet['pressure_polynomial']}
        P=[{0:F(b)} for b in packet['pressure_coefficients_b']];E=[{} for _ in range(9)]
        incidence=packet['coordinate_incident_edges'];which=[[] for _ in packet['edges']]
        for r,eids in enumerate(incidence):
            for eid in eids:which[eid].append(r)
        for eid,e in enumerate(packet['edges']):
            polys=[]
            for field in ['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']:
                p={}
                for j,value in enumerate(e[field]):add(p,powers[e['power_ids'][j]],F(value)*F(e['weight']))
                polys.append(p)
            add(L,polys[0])
            for r in which[eid]:add(P[r],polys[1]);add(E[r],polys[2])
        del powers
        row_hash=hashlib.sha256()
        for descriptor,record in zip(packet['new_scalar_rows'],rowdoc['rows']):
            j=descriptor['id'];rid=14383+j;assert 0<=j<181;w=lam[rid]
            if descriptor['kind']=='absolute_energy_L6':
                q={k:-a for k,a in L.items()};q[0]=q.get(0,F(0))+F(descriptor['bound'])
                meta=['actual_sextic_absolute_energy_unsoftened']
            else:
                r=descriptor['coordinate'];test=descriptor['test_monomial_id'];sign=descriptor['sign']
                q=E[r].copy();shift={mi[tuple(sorted(mon[k]+mon[test]))]:a for k,a in P[r].items()};add(q,shift,F(sign))
                meta=['actual_sextic_free_KKT',r,test,sign]
            bound=q.get(0,F(0));coefficients=[[k-1,str(-a)] for k,a in sorted(q.items()) if k]
            scale=F(record['scale']);assert scale==max([F(1,1000),abs(bound)]+[abs(a) for k,a in q.items() if k])
            canonical={'coefficients':coefficients,'bound':str(bound),'scale':str(scale),'meta':meta}
            encoded=json.dumps(canonical,sort_keys=True,separators=(',',':')).encode()
            assert hashlib.sha256(encoded).hexdigest()==record['exact_canonical_row_sha256'];row_hash.update(encoded+b'\n')
            assert str(bound)==record['bound'] and meta==record['meta'] and len(coefficients)==5004
            for k,a in q.items():atom(k,w*scale.denominator*a.numerator,DEN*scale.numerator*a.denominator)
            if (j+1)%30==0:save('actual_sextic_rows_'+str(j+1))
        assert row_hash.hexdigest()==rowdoc['exact_canonical_rows_JSONL_sha256']
        by_section.append({'section':'181_actual_sextic_rows','atoms':atoms-start});start=atoms
        del L,P,E,q,polys,coefficients,encoded,old,family,rows,packet
        # Sum Gram entries having the same exact basis-product monomial
        # before multiplying a block's exact multiplier. This is integer
        # grouping, not rounding, rank truncation or a PSD approximation.
        plans=model['entry_plans'];planmap={(p[0],p[1]):p for p in plans}
        multipliers=model['multipliers'];gram_records=[];alltargets=0
        for bid,(block,factor) in enumerate(zip(model['blocks'],ray['PSD_factors'])):
            assert factor['block_id']==bid and factor['factor_denominator']==DEN
            n=block['size'];qid=block['multiplier_id'];ints=factor['factor_numerators_by_row'];rank=factor['column_count']
            assert factor['size']==len(ints)==n and factor['multiplier_id']==qid and all(len(row)==rank for row in ints)
            terms=[(k,F(v)) for k,v in multipliers[qid]['terms']]
            divisor=F(factor['positive_rational_block_divisor']);assert divisor==max([F(1)]+[abs(v) for _,v in terms]) and divisor>0
            sos={};local=0
            for j in range(n):
                for i in range(j,n):
                    pid=entry[block['entry_plan_offset']+local];pq,shift,offset,count=plans[pid]
                    assert pq==qid and count==len(terms) and mon[shift]==tuple(sorted(mon[i]+mon[j]))
                    z=sum(a*b for a,b in zip(ints[i],ints[j]))
                    sos[shift]=sos.get(shift,0)+(z if i==j else 2*z);local+=1
            assert local==n*(n+1)//2
            blockstart=atoms
            for shift,value in sos.items():
                if not value:continue
                pq,ps,offset,count=planmap[(qid,shift)];assert pq==qid and ps==shift and count==len(terms)
                for j,(k,a) in enumerate(terms):
                    tid=target[offset+j];assert mon[tid]==tuple(sorted(mon[shift]+mon[k]));alltargets+=1
                    atom(tid,value*divisor.denominator*a.numerator,DEN*DEN*divisor.numerator*a.denominator)
            gram_records.append({'block_id':bid,'size':n,'factor_columns':rank,'integer_Gram_nonzero':any(any(row) for row in ints),
                'exact_grouped_SOS_monomials':sum(v!=0 for v in sos.values()),'enclosed_atoms':atoms-blockstart,
                'positive_rational_divisor':str(divisor),'multiplier_id':qid})
            if (bid+1)%5==0:save('exact_Gram_trace_blocks_'+str(bid+1))
        by_section.append({'section':'73_integer_Gram_trace_polynomials','atoms':atoms-start})
        assert len(gram_records)==73 and all(g['integer_Gram_nonzero'] for g in gram_records)
        assert len(lo)==len(hi)==5005 and all(a<=b for a,b in zip(lo,hi))
        payments=[]
        for mid,lower,upper,lowerrow,upperrow in boxmap:
            assert mid==len(payments)+1
            worst=max(lo[mid]*lower,lo[mid]*upper,hi[mid]*lower,hi[mid]*upper)
            assert worst>=0
            payments.append(worst)
        total=hi[0]+sum(payments);passed=total<0
        cert={'schema':'fixed-Gram-ray-exact-atom-enclosure-v1','scope':__doc__,'source_sha256':initial,
            'quantized_ray_sha256':sha(paths[2]),'fixed_interval_denominator':DS,
            'moment_ID_convention':'0 is constant; monID1..5004 map solver columns0..5003. Solver slack column5004 is separate and identically absent.',
            'forced_zero_scalar_rows':[5793,5794],'all_other_rows_unbounded_slack_absent':True,
            'scalar_rows':14564,'scalar_weight_denominator':DEN,'Gram_factor_denominator':DEN,
            'coefficient_lower_numerators':lo,'coefficient_upper_numerators':hi,
            'explicit_monomial_boxes':[{'monomial_id':mid,'lower':a,'upper':b,'lower_scalar_row':lr,'upper_scalar_row':ur} for mid,a,b,lr,ur in boxmap],
            'monomial_box_worst_product_upper_numerators':payments,
            'constant_upper_numerator':total,'strict_negative_constant_upper':passed,
            'strict_margin':str(F(-total,DS)) if passed else None,
            'enclosed_nonzero_atoms':atoms,'nonintegral_atom_enclosures':nonintegral,'enclosure_sections':by_section,
            'PSD_block_records':gram_records,'exact_Gram_target_identities_checked':alltargets,
            'active_old_scalar_metadata_counts':active_meta,
            'actual_analytic_instances_Lean_proved':False,'actual_cell_exclusion_proven':False,
            'outer_polynomial_model_infeasibility_proved_by_this_arithmetic':passed,
            'new_zero_proportion_proven':False,'literal_exact_coefficient_cancellation_claimed':False,
            'proof_rule':'H>=0 from normalized nonnegative scalar slacks and integer-Gram traces. Exact coefficient intervals and all5004 explicit monomial boxes imply H<=constant_upper_numerator/DS. A negative upper is impossible.'}
        encoded=json.dumps(cert,separators=(',',':'),allow_nan=False).encode();assert len(encoded)<FILELIMIT
        OUT.write_bytes(encoded+b'\n');assert OUT.stat().st_size<FILELIMIT
        report.update({'exact_certificate':{'path':OUT.relative_to(ROOT).as_posix(),'bytes':OUT.stat().st_size,'sha256':sha(OUT)},
            'coefficient_interval_count':5005,'enclosed_nonzero_atoms':atoms,'nonintegral_atom_enclosures':nonintegral,
            'box_bounds_checked':5004,'constant_upper_numerator':total,'strict_margin':cert['strict_margin'],
            'strict_negative_constant_upper':passed,'outer_polynomial_model_infeasible':passed,
            'literal_exact_residual_cancellation':False,'maximum_endpoint_bit_length':max(abs(v).bit_length() for v in lo+hi),
            'no_global_common_denominator_constructed':True,'global_common_denominator_bit_length':None,
            'sole_interval_denominator':DS,'exact_Gram_blocks':73,'active_scalar_rows':sum(v!=0 for v in lam),
            'all181_actual_sextic_rows_active':all(v>0 for v in lam[14383:]),'all_old_analytic_KKT_swap_and_sublevel_dependencies_retained':True})
        save('exact_interval_and_box_certificate_PASS' if passed else 'exact_fixed_data_certificate_FAILED_nonnegative_upper')
        print(json.dumps({k:report.get(k) for k in ['phase','elapsed_milliseconds','strict_margin','constant_upper_numerator',
            'enclosed_nonzero_atoms','maximum_endpoint_bit_length','exact_certificate']}),flush=True)
    except BaseException as exc:
        report.update({'exception':repr(exc),'traceback':traceback.format_exc()});save('exact_fixed_data_extraction_stopped_without_retry');raise
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
