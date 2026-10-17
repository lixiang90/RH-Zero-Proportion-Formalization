"""Independent stdlib decode of the completed degree-six STATIC packet.

No producer import, solver, Lean or new point. Verify coefficient references,
all target indices and entry shifts without materializing a large repeated
Fraction matrix. This is a representation/resource check, not feasibility or
strict projection shrink. Default read-only; create an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from collections import Counter
from array import array
import argparse,gzip,hashlib,json,sys,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PACK=ROOT/'research-goal-20261017-degree6-static'
OUT=HERE/'independent-replay.json'
PINS={'build_static.py':'9bd275abdca4d9dcba05e519b340da140ced1a4ffa5988514e1ee9d185f17c06',
      'degree6-model.json.gz':'9aa2e3759d63e4e1c8bdbd3b76004f3c9cf4080dcb5dde5599aff3e96ed0a552',
      'degree6-targets.bin':'2f33955dca14c310a993df8d0930044e00c0af63b137f309bd7252fc3ce5052d',
      'degree6-entryplans.bin':'3f906a5b5abbac6829dd8fb87329bdc3de0f27b5388102305b1792af78d90c01'}


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def add(p,q,s=F(1)):
    out=p.copy()
    for m,v in q.items():
        out[m]=out.get(m,F(0))+s*v
        if not out[m]:del out[m]
    return out


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();paths=[Path(__file__),PACK/'degree6-build.json']
    for name,h in PINS.items():
        p=PACK/name;assert sha(p)==h;paths.append(p)
    build=json.loads(paths[1].read_bytes())
    assert build['resource_gate_passed'] and build['phase']=='complete_static_degree6_cost_gate_passed'
    assert build['source_sha256_start']==build['source_sha256_end']
    for name,h in build['source_sha256_start'].items():
        p=ROOT/name;assert p.resolve().is_relative_to(ROOT.resolve()) and sha(p)==h
        if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    raw=gzip.decompress((PACK/'degree6-model.json.gz').read_bytes())
    assert len(raw)==build['model_uncompressed_bytes'] and hashlib.sha256(raw).hexdigest()==build['model_uncompressed_sha256']
    model=json.loads(raw);del raw
    assert model['format_version']==1 and model['target']=='11/1250'
    assert model['source_sha256_start']==model['source_sha256_end']==build['source_sha256_start']
    old=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    family=json.loads(gzip.decompress((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz').read_bytes()))
    canonical=[m for d in range(7) for m in combinations_with_replacement(range(9),d)]
    mon=[tuple(m) for m in model['monomials']];mi={m:k for k,m in enumerate(mon)}
    assert mon==canonical and len(mon)==5005 and [list(m) for m in mon[:715]]==old['monomials']==family['monomials']
    assert model['fixed_constant_moment_id']==0 and model['nonconstant_moment_columns']==model['energy_slack_column']==5004
    assert model['underlying_real_variables']==9 and mon[715]==(0,0,0,0,0)
    assert min(old['cell'][0][:9])>31488
    qpool=model['multipliers'];blocks=model['blocks'];plans=model['entry_plans']
    assert len(qpool)==len(blocks)==73 and len(plans)==39325
    assert [b['size'] for b in blocks]==[220]+[55]*46+[10]*26
    for i,q in enumerate(qpool):
        assert q['id']==i and len({k for k,_ in q['terms']})==len(q['terms'])
        assert q['terms']==sorted(q['terms']) and all(F(v)!=0 and len(mon[k])<=q['degree_bound'] for k,v in q['terms'])
    for i,block in enumerate(old['PSD_blocks']):
        assert qpool[i]['terms']==block['multiplier_polynomial']
        assert qpool[i]['meta']==['old_PSD_upgrade',i]
        assert blocks[i]['name']=='degree6_'+block['name']
    for i,item in enumerate(family['maps']):
        q=qpool[47+i]
        assert q['terms']==item['difference_upper_quartic'] and q['meta']==['global_relevant_swap',i,i+1]
        row=family['additional_linear_rows'][i]
        assert row['coefficients']==[[k-1,str(-F(v))] for k,v in q['terms'] if k]
        assert F(row['bound'])==F(dict(q['terms']).get(0,'0'))
    def unpack(p):return {mon[k]:F(v) for k,v in p}
    H=list(map(unpack,old['KKT_cubic_polynomials']));E=list(map(unpack,old['KKT_dynamic_error_polynomials']))
    kkt=0
    for r in range(9):
        for si,sign in enumerate([-1,1]):
            q=qpool[55+2*r+si]
            expected=add(E[r],H[r],F(sign))
            assert q['terms']==[[mi[m],str(v)] for m,v in sorted(expected.items(),key=lambda z:mi[z[0]])]
            assert q['meta']==['free_gradient_E_plus_sign_P',r,sign];kkt+=1
    assert kkt==18
    targets=array('H');targets.frombytes((PACK/'degree6-targets.bin').read_bytes())
    entries=array('I');entries.frombytes((PACK/'degree6-entryplans.bin').read_bytes())
    assert targets.itemsize==2 and entries.itemsize==4
    if sys.byteorder!='little':targets.byteswap();entries.byteswap()
    assert len(entries)==96580 and len(targets)==1416525
    assert model['target_indices']['sha256']==PINS['degree6-targets.bin'] and model['block_entry_plan_indices']['sha256']==PINS['degree6-entryplans.bin']
    offset=0;keys=set();target_count=0
    for qid,shiftid,start,count in plans:
        assert 0<=qid<73 and 0<=shiftid<5005 and start==offset
        terms=qpool[qid]['terms'];assert count==len(terms)
        key=qid,shiftid;assert key not in keys;keys.add(key)
        decoded=targets[start:start+count]
        expected=[mi[tuple(sorted(mon[k]+mon[shiftid]))] for k,_ in terms]
        assert list(decoded)==expected and len(set(decoded))==count
        assert all(t<5005 for t in decoded)
        offset+=count;target_count+=count
    assert offset==len(targets)
    cursor=0;used=set();entry_symbolic_terms=0;constant_occurrences=0
    for qid,b in enumerate(blocks):
        n=b['size'];assert b['multiplier_id']==qid and b['basis_monomial_ids']==list(range(n))
        assert b['entry_order']=='column-major j then i>=j' and b['entry_plan_offset']==cursor
        assert b['lower_triangle_entries']==n*(n+1)//2
        for j in range(n):
            for i in range(j,n):
                pid=entries[cursor];cursor+=1;assert pid<len(plans);used.add(pid)
                a,s,start,count=plans[pid]
                assert a==qid and mon[s]==tuple(sorted(mon[i]+mon[j]))
                entry_symbolic_terms+=count
                constant_occurrences+=int(0 in targets[start:start+count])
    assert cursor==len(entries) and len(used)==len(plans)
    assert entry_symbolic_terms==build['PSD_symbolic_term_occurrences_including_constants']
    assert constant_occurrences==build['PSD_constant_term_occurrences']==73
    principal=0
    for k,ob in enumerate(old['PSD_blocks']):
        b=blocks[k];n=b['size'];terms=qpool[k]['terms']
        for i,j,form in ob['entries']:
            position=b['entry_plan_offset']+j*n-j*(j-1)//2+(i-j)
            qid,shiftid,start,count=plans[entries[position]];assert qid==k
            decoded=targets[start:start+count];coeff={};constant='0'
            for target,(_,value) in zip(decoded,terms):
                if target==0:constant=value
                else:coeff[target-1]=value
            assert form['constant']==constant and dict(form['coefficients'])==coeff
            principal+=1
    assert principal==4070
    oldrows=old['linear_rows']+family['additional_linear_rows'];assert len(oldrows)==5803
    adapter=model['old_row_adapter'];assert adapter['only_column_map']==[[714,5004]] and adapter['rows']==5803
    assert adapter['ordered_fields']==['linear_rows','additional_linear_rows']
    assert adapter['sources']==['research-goal-20261017-quartic/quartic-model.json.gz','research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz']
    digest=hashlib.sha256();slack_rows=[];legacy_kkt=0
    for i,row in enumerate(oldrows):
        assert all(k<=714 for k,_ in row['coefficients'])
        mapped={**row,'coefficients':[[5004 if k==714 else k,v] for k,v in row['coefficients']]}
        digest.update(json.dumps(mapped,sort_keys=True,separators=(',',':')).encode()+b'\n')
        if any(k==714 for k,_ in row['coefficients']):slack_rows.append(i)
        if row['meta'][0]=='free_KKT_with_dynamic_error':
            _,r,s,sign=row['meta'];P=H[r] if s==0 else {tuple(sorted(m+(s-1,))):v for m,v in H[r].items()}
            expected=add(E[r],P,F(sign))
            assert row['coefficients']==[[mi[m]-1,str(-v)] for m,v in sorted(expected.items(),key=lambda z:mi[z[0]]) if m]
            assert F(row['bound'])==expected.get((),F(0));legacy_kkt+=1
    assert digest.hexdigest()==adapter['mapped_canonical_JSONL_sha256']==build['mapped_old_rows_canonical_JSONL_sha256']
    assert slack_rows==[5793,5794] and legacy_kkt==180
    expected_boxes=[]
    for k,m in enumerate(mon[715:],715):
        even=all(m.count(r)%2==0 for r in set(m));expected_boxes.append([k-1,0 if even else -1,1])
    assert model['new_moment_boxes']==expected_boxes and len(expected_boxes)==4290
    assert sum(lo==0 for _,lo,_ in expected_boxes)==165 and max(k for k,_,_ in expected_boxes)==5003
    assert not any(name.split('.')[0] in ['numpy','scipy','scs'] for name in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    out={'scope':__doc__,'status':'complete_factored_degree6_representation_independently_decoded',
         'source_sha256_start':initial,'source_sha256_end':final,'all_inputs_unchanged':True,
         'canonical_monomials':5005,'nonconstant_moment_columns':5004,'energy_slack_column':5004,
         'multiplier_polynomials_checked':73,'unique_plans_checked':len(plans),
         'target_references_checked':target_count,'all_plan_target_maps_injective':True,
         'all_target_and_entry_streams_fully_consumed':True,'all_plans_used_by_entries':True,
         'block_entries_checked':cursor,'coefficient_references_in_entries':entry_symbolic_terms,
         'old_exact_principal_forms_preserved':principal,'new_E_plus_or_minus_P_multipliers_checked':kkt,
         'legacy_KKT_rows_checked':legacy_kkt,'old_scalar_rows_preserved_by_adapter':5803,
         'old_slack_occurrence_rows':slack_rows,'only_slack_remap':[714,5004],
         'new_moment_boxes_checked':4290,'new_box_scalar_rows':8580,'all_even_new_lower_zero':165,
         'total_scalar_rows':14383,'mapped_old_rows_JSONL_sha256':digest.hexdigest(),
         'producer_imported':False,'pure_stdlib':True,'expanded_large_Fraction_matrix_created':False,
         'new_points':0,'new_actual_analytic_inputs':0,'solver_calls':0,'Lean_invocations':0,
         'old_exact714_extension_decided':False,'strict_projection_shrink_proved':False,
         'new_exclusion':False,'new_zero_proportion_proven':False,
         'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','unique_plans_checked','target_references_checked',
        'block_entries_checked','old_exact_principal_forms_preserved','elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
