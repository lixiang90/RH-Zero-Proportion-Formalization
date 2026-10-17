"""One canonical degree-six extension: sparse/factored STATIC cost gate.

5004 nonconstant moments plus energy slack5004. Preserve all 5803 old
rows (only old slack714 remapped) and all 4070 old PSD principal entries.
M3=220,46 quadratic M2=55,8 global D4 M1=10,18 legal E4+/-P3 M1=10.
Explicit boxes for every degree5/6 moment. No solver, new Taylor input,
analytic sampling, compiler, PSD feasibility claim, or cloud operation.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from array import array
import ctypes,gzip,hashlib,json,os,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PARENT=ROOT/'research-goal-20261017-quartic';FAMILY=ROOT/'research-goal-20261017-swap-family-quartic'
OUT=HERE/'degree6-model.json.gz';RECEIPT=HERE/'degree6-build.json'
TARGETS=HERE/'degree6-targets.bin';ENTRIES=HERE/'degree6-entryplans.bin'
MAX_RSS=1536*1024**2;MAX_FILE=40*1024**2

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def add(p,q,c=F(1)):
    out=p.copy()
    for m,a in q.items():
        z=out.get(m,F(0))+c*a
        if z:out[m]=z
        else:out.pop(m,None)
    return out
def times_y(p,r):return {tuple(sorted(m+(r,))):a for m,a in p.items()}

def memory():
    if os.name=='nt':
        from ctypes import wintypes as W
        class PMC(ctypes.Structure):
            _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
                ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage',
                 'QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
        kernel=ctypes.WinDLL('kernel32',use_last_error=True);kernel.GetCurrentProcess.restype=W.HANDLE
        psapi=ctypes.WinDLL('psapi',use_last_error=True);psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
        q=PMC();q.cb=ctypes.sizeof(q);assert psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(),ctypes.byref(q),q.cb)
        return {'measurement':'Windows GetProcessMemoryInfo','working_set_bytes':q.WorkingSetSize,'peak_working_set_bytes':q.PeakWorkingSetSize,'private_commit_bytes':q.PagefileUsage}
    import resource
    peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*(1 if sys.platform=='darwin' else 1024)
    return {'measurement':'resource.ru_maxrss','working_set_bytes':peak,'peak_working_set_bytes':peak}

def main():
    assert not any(p.exists() for p in [OUT,RECEIPT,TARGETS,ENTRIES]);began=time.monotonic()
    paths=[Path(__file__),PARENT/'quartic-model.json.gz',PARENT/'quartic-build.json',PARENT/'quartic-files.json',
        FAMILY/'swap-family-normalized.json.gz',FAMILY/'swap-family-normalized-build.json',FAMILY/'swap-family-files.json',
        ROOT/'research-goal-20261017-degree6-review/degree6-review-files.json',ROOT/'StructuralGoal20261016/WindowMinimizerCover.lean']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    report={'scope':__doc__,'phase':'start_static_cost_gate','source_sha256_start':initial,
        'RSS_guard_bytes':MAX_RSS,'single_file_uncompressed_guard_bytes':MAX_FILE,'memory_snapshots':[],
        'solver_calls':0,'Lean_invocations':0,'new_actual_kernel_inputs':0,'cloud_operations':0,
        'new_feasibility_or_infeasibility_proven':False,'projection_strictness_proven':False,
        'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save(phase):
        report['phase']=phase;m=memory();m['phase']=phase;m['elapsed_milliseconds']=int((time.monotonic()-began)*1000);report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert initial==final
        report.update({'source_sha256_end':final,'all_sources_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        RECEIPT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
        if m['peak_working_set_bytes']>MAX_RSS:raise MemoryError('1.5GiB working-set guard exceeded')
    save('before_loading_frozen_inputs')
    try:
        oldraw=gzip.decompress(paths[1].read_bytes());old=json.loads(oldraw);oldbuild=json.loads(paths[2].read_bytes())
        assert sha(paths[1])==oldbuild['model_compressed_sha256'] and hashlib.sha256(oldraw).hexdigest()==oldbuild['model_uncompressed_sha256'];del oldraw
        save('old_quartic_loaded')
        fraw=gzip.decompress(paths[4].read_bytes());family=json.loads(fraw);fb=json.loads(paths[5].read_bytes())
        assert sha(paths[4])==fb['packet_compressed_sha256'] and hashlib.sha256(fraw).hexdigest()==fb['packet_uncompressed_sha256'];del fraw
        assert old['path']==family['path']=='r001000001000100110011001' and old['target']==family['target']=='11/1250'
        assert len(old['linear_rows'])==5795 and len(family['additional_linear_rows'])==8 and old['PSD_sizes']==[55]+[10]*46
        assert all(F(l,32768)>F(123,128) for l in old['cell'][0][:9])
        save('all_frozen_inputs_loaded')
        mon=[m for d in range(7) for m in combinations_with_replacement(range(9),d)];mi={m:k for k,m in enumerate(mon)}
        assert len(mon)==5005 and [list(m) for m in mon[:715]]==old['monomials']==family['monomials']
        assert len(mon[:10])==10 and len([m for m in mon if len(m)<=2])==55 and len([m for m in mon if len(m)<=3])==220
        assert mon[715]==(0,0,0,0,0) and mi[mon[714]]==714
        def unpack(p):return {mon[k]:F(v) for k,v in p}
        def pack(p):return [[mi[m],str(v)] for m,v in sorted(p.items(),key=lambda z:mi[z[0]])]
        # The LEGAL free-gradient polynomials are E+P and E-P.
        # P-E>=0 is generally false. Preserve and check all old E+/-y*P rows.
        H=[unpack(p) for p in old['KKT_cubic_polynomials']];E=[unpack(p) for p in old['KKT_dynamic_error_polynomials']]
        assert len(H)==len(E)==9
        kkt_checks=0
        for r in range(9):
            assert max(map(len,H[r]))<=3 and max(map(len,E[r]))<=4
            for s in range(10):
                p=H[r] if s==0 else times_y(H[r],s-1)
                for si,sign in enumerate([-1,1]):
                    q=add(E[r],p,F(sign));row=old['linear_rows'][4185+20*r+2*s+si]
                    expected=[[mi[m]-1,str(-v)] for m,v in sorted(q.items(),key=lambda z:mi[z[0]]) if m]
                    bound=q.get((),F(0));divisor=max([abs(bound)]+[abs(F(v)) for _,v in expected]) or F(1)
                    assert row['coefficients']==expected and F(row['bound'])==bound and F(row['scale'])==divisor
                    assert row['meta']==['free_KKT_with_dynamic_error',r,s,sign];kkt_checks+=1
        assert kkt_checks==180
        multipliers=[];blocks=[]
        def block(name,basis_size,poly,degree,meta):
            assert all(len(mon[k])<=degree and F(v)!=0 for k,v in poly)
            qid=len(multipliers);multipliers.append({'id':qid,'terms':poly,'degree_bound':degree,'meta':meta})
            blocks.append({'name':name,'size':basis_size,'basis_monomial_ids':list(range(basis_size)),'multiplier_id':qid})
        for k,b in enumerate(old['PSD_blocks']):
            q=b['multiplier_polynomial'];block('degree6_'+b['name'],220 if k==0 else 55,q,0 if k==0 else 2,['old_PSD_upgrade',k])
        for r,item in enumerate(family['maps']):
            q=item['difference_upper_quartic'];row=family['additional_linear_rows'][r]
            assert row['coefficients']==[[k-1,str(-F(v))] for k,v in q if k] and F(row['bound'])==F(dict(q).get(0,'0'))
            block('global_adjacent_swap_'+str(r),10,q,4,['global_relevant_swap',r,r+1])
        for r in range(9):
            for sign in [-1,1]:block('free_KKT_'+str(r)+'_'+str(sign),10,pack(add(E[r],H[r],F(sign))),4,['free_gradient_E_plus_sign_P',r,sign])
        assert len(blocks)==len(multipliers)==73
        save('canonical_moments_and_73_multipliers_constructed')
        # One coefficient copy per multiplier. Each entry references a plan;
        # each plan maps its coefficient positions to target moment IDs.
        # No repeated huge Fraction is created in these sparse mappings.
        target_ids=array('H');entry_plan_ids=array('I');plans=[];lookup={};symbolic_terms=0;variable_nonzeros=0;constants=0
        def get_plan(qid,shiftid):
            key=qid,shiftid
            if key not in lookup:
                terms=multipliers[qid]['terms'];offset=len(target_ids);shift=mon[shiftid]
                targets=[mi[tuple(sorted(mon[k]+shift))] for k,_ in terms]
                assert len(set(targets))==len(targets)
                target_ids.extend(targets);pid=len(plans);plans.append([qid,shiftid,offset,len(targets)]);lookup[key]=pid
            return lookup[key]
        for b in blocks:
            n=b['size'];qid=b['multiplier_id'];start=len(entry_plan_ids);qterms=multipliers[qid]['terms']
            for j in range(n):
                for i in range(j,n):
                    shiftid=mi[tuple(sorted(mon[i]+mon[j]))];pid=get_plan(qid,shiftid);entry_plan_ids.append(pid)
                    symbolic_terms+=len(qterms)
                    constant=int(shiftid==0 and any(k==0 for k,_ in qterms));constants+=constant;variable_nonzeros+=len(qterms)-constant
            b.update({'entry_plan_offset':start,'lower_triangle_entries':len(entry_plan_ids)-start,'entry_order':'column-major j then i>=j'})
            assert b['lower_triangle_entries']==n*(n+1)//2
        assert len(entry_plan_ids)==96580 and len(plans)==39325
        # Every old matrix entry is the SAME coefficient form in a principal
        # block of the upgrade. This is checked against the new plan mapping.
        principal_checks=0
        for k,oldblock in enumerate(old['PSD_blocks']):
            b=blocks[k];n=b['size'];qterms=multipliers[b['multiplier_id']]['terms']
            for i,j,form in oldblock['entries']:
                position=b['entry_plan_offset']+j*n-j*(j-1)//2+i-j;plan=plans[entry_plan_ids[position]]
                assert plan[0]==b['multiplier_id']
                targets=target_ids[plan[2]:plan[2]+plan[3]];constant=F(0);coeff={}
                for t,(_,v) in zip(targets,qterms):
                    if t==0:constant+=F(v)
                    else:coeff[t-1]=F(v)
                assert F(form['constant'])==constant and {a:F(v) for a,v in form['coefficients']}==coeff
                principal_checks+=1
        assert principal_checks==4070
        # All old rows are byte-for-byte coefficient values under the ONLY
        # column change714->5004 (old714 was slack, not a moment column).
        oldrows=old['linear_rows']+family['additional_linear_rows'];rowhash=hashlib.sha256();row_nonzeros=0;slack_occurrences=[]
        for k,row in enumerate(oldrows):
            mapped={**row,'coefficients':[[5004 if i==714 else i,v] for i,v in row['coefficients']]}
            assert {**mapped,'coefficients':[[714 if i==5004 else i,v] for i,v in mapped['coefficients']]}==row
            assert all(i<=714 for i,_ in row['coefficients'])
            if any(i==714 for i,_ in row['coefficients']):slack_occurrences.append(k)
            rowhash.update(json.dumps(mapped,sort_keys=True,separators=(',',':')).encode()+b'\n');row_nonzeros+=len(mapped['coefficients'])
        assert len(oldrows)==5803 and slack_occurrences==[5793,5794]
        boxes=[]
        for k in range(715,5005):
            m=mon[k];even=all(m.count(r)%2==0 for r in set(m));boxes.append([k-1,0 if even else -1,1])
        assert len(boxes)==4290 and sum(lo==0 for _,lo,_ in boxes)==165
        assert all(714<=k<5004 for k,_,_ in boxes)
        report.update({'path':old['path'],'target':old['target'],'moment_count_including_constant':5005,'nonconstant_moment_columns':5004,
            'optimization_variables_including_slack':5005,'slack_column':5004,'old_monomial_prefix':715,
            'old_scalar_rows_preserved':5803,'old_slack_column_remap':[714,5004],'old_slack_row_occurrences':slack_occurrences,
            'old_KKT_rows_exactly_checked':kkt_checks,'old_PSD_principal_entries_exactly_checked':principal_checks,
            'new_moment_box_rows':8580,'new_moment_boxes':4290,'new_all_even_lower_zero':165,'total_scalar_rows':14383,
            'PSD_blocks':73,'PSD_lower_triangle_entries':96580,'PSD_sizes':[b['size'] for b in blocks],
            'unique_entry_plans':len(plans),'unique_plan_target_references':len(target_ids),
            'PSD_symbolic_term_occurrences_including_constants':symbolic_terms,'PSD_variable_nonzeros':variable_nonzeros,
            'PSD_constant_term_occurrences':constants,'scalar_variable_nonzeros':row_nonzeros+8580,
            'total_conic_rows_if_SCS_packed':14383+96580,'total_variable_nonzeros_if_SCS_packed':variable_nonzeros+row_nonzeros+8580})
        save('all_96580_entries_mapped_old_principals_and_rows_verified')
        # Actual factored serialization, bounded; no enormous expanded
        # Fraction coefficient matrix is ever materialized.
        assert target_ids.itemsize==2 and entry_plan_ids.itemsize==4
        if sys.byteorder!='little':target_ids.byteswap();entry_plan_ids.byteswap()
        assert len(target_ids)*2<MAX_FILE and len(entry_plan_ids)*4<MAX_FILE
        TARGETS.write_bytes(target_ids.tobytes());ENTRIES.write_bytes(entry_plan_ids.tobytes())
        model={'scope':__doc__,'format_version':1,'path':old['path'],'target':old['target'],'SEP':'123/128',
            'underlying_real_variables':9,'monomials':[list(m) for m in mon],'nonconstant_moment_columns':5004,'energy_slack_column':5004,
            'fixed_constant_moment_id':0,'moment_id_to_column':'momentID>0 maps to column momentID-1; momentID0 is fixed1; slack is separate5004',
            'source_sha256_start':initial,'source_sha256_end':initial,'all_sources_unchanged':True,
            'old_row_adapter':{'sources':[paths[1].relative_to(ROOT).as_posix(),paths[4].relative_to(ROOT).as_posix()],
                'ordered_fields':['linear_rows','additional_linear_rows'],'rows':5803,'only_column_map':[[714,5004]],
                'mapped_canonical_JSONL_sha256':rowhash.hexdigest(),'canonical_JSON':'sort_keys=True,separators=(comma,colon),UTF8,newline per row'},
            'new_moment_boxes':boxes,'new_box_row_semantics':'each[column,lo,hi] gives -moment<=-lo then moment<=hi; no energy slack',
            'multipliers':multipliers,'blocks':blocks,'entry_plans':plans,
            'target_indices':{**rec(TARGETS),'encoding':'little-endian uint16 target MOMENT IDs','offset_units':'uint16 elements'},
            'block_entry_plan_indices':{**rec(ENTRIES),'encoding':'little-endian uint32 entry PLAN IDs','offset_units':'uint32 elements'},
            'entry_plan_schema':['multiplierID','shiftMonomialID','targetIndexOffset','numberOfTerms'],
            'entry_value':'sum_j multiplier.terms[j].coefficient * moment[target_indices[offset+j]], coefficient referenced once; target0 fixed1',
            'analytic_premises':'Exactly the frozen base and normalized swap actual-envelope/global-minimum premises. All9 original gaps strictly aboveSEP. No newly proved scalar tables.',
            'KKT_multiplier_sign':'E4+sign*P3 with sign=-1,+1; NOT P3-E4>=0',
            'old_PSD_principal_embedding':'oldM2 first55 of M3; each oldM1 first10 of upgradedM2, identical multiplier',
            'solver_calls':0,'Lean_invocations':0,'projection_strictness_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
        rawhash=hashlib.sha256();rawbytes=0;partial=OUT.with_suffix(OUT.suffix+'.partial')
        assert not partial.exists()
        with partial.open('wb') as sink:
            with gzip.GzipFile(fileobj=sink,mode='wb',compresslevel=9,mtime=0) as stream:
                for chunk in json.JSONEncoder(separators=(',',':'),allow_nan=False).iterencode(model):
                    b=chunk.encode();rawbytes+=len(b)
                    if rawbytes>MAX_FILE:raise RuntimeError('40MiB uncompressed single-model guard exceeded')
                    rawhash.update(b);stream.write(b)
        partial.replace(OUT)
        coefficient_bytes=sum(sum(len(v.encode()) for _,v in q['terms']) for q in multipliers)
        # A lower bound on naive expansion size: repeated coefficient bytes
        # alone, before target indices, punctuation, or JSON field names.
        expanded_coefficient_lower_bound=sum(sum(len(v.encode()) for _,v in multipliers[b['multiplier_id']]['terms'])*b['lower_triangle_entries'] for b in blocks)
        report.update({'model':rec(OUT),'model_uncompressed_bytes':rawbytes,'model_uncompressed_sha256':rawhash.hexdigest(),
            'target_indices':rec(TARGETS),'block_entry_plan_indices':rec(ENTRIES),
            'coefficient_text_bytes_stored_once':coefficient_bytes,
            'naive_expanded_repeated_coefficient_bytes_lower_bound':expanded_coefficient_lower_bound,
            'mapped_old_rows_canonical_JSONL_sha256':rowhash.hexdigest(),'resource_gate_passed':True,
            'actual_factored_serialization_preserves_all_entries':True,'no_optimization_or_extension_feasibility_attempted':True})
        assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
        save('complete_static_degree6_cost_gate_passed')
    except BaseException as exc:
        report['resource_gate_passed']=False;report['exception']=repr(exc);save('static_build_stopped_without_solver');raise
    print(json.dumps({k:report[k] for k in ['phase','optimization_variables_including_slack','total_scalar_rows','PSD_blocks','PSD_lower_triangle_entries',
        'unique_entry_plans','unique_plan_target_references','total_variable_nonzeros_if_SCS_packed','model_uncompressed_bytes','elapsed_milliseconds']}),flush=True)
    print(json.dumps({'peak_working_set_bytes':max(m['peak_working_set_bytes'] for m in report['memory_snapshots']),
        'model_gzip_bytes':OUT.stat().st_size,'targets_bytes':TARGETS.stat().st_size,'entryplans_bytes':ENTRIES.stat().st_size}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
