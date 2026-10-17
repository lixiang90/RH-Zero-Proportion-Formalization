"""Independent exact audit of the one fixed Gram-column deletion rule.

No producer import, eigenvalue computation or optimization. The retained
enclosure itself is checked separately by independent_replay.py.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
BASE=ROOT/'research-goal-20261017-fixed-gram-tail'
FULL=ROOT/'research-goal-20261017-actual-sextic-exact-ray'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    b=p.read_bytes();return json.loads(gzip.decompress(b)if p.suffix=='.gz'else b)
def verify():
    path=BASE/'tail-selection.json';assert sha(path)=='01ee6806c3ee6f1486ddcc9cf196cdf516ac829725bf4caf92ecb62582857eef'
    p=read(path);full=read(FULL/'quantized-ray.json.gz');ray=read(BASE/'retained-ray.json.gz');oldcert=read(FULL/'exact-enclosure-certificate.json')
    model=read(ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz')
    assert p['source_sha256']==ray['source_sha256']
    pins={**p['source_sha256'],path.relative_to(ROOT).as_posix():sha(path),(BASE/'retained-ray.json.gz').relative_to(ROOT).as_posix():sha(BASE/'retained-ray.json.gz'),Path(__file__).relative_to(ROOT).as_posix():sha(Path(__file__))}
    for n,h in pins.items():assert sha(ROOT/n)==h
    assert ray['original_full_ray_sha256']==sha(FULL/'quantized-ray.json.gz')and ray['schema']=='deterministically-retained-fixed-integer-Gram-ray-v1'
    D=10**12;DS=10**30;delta=F(oldcert['strict_margin']);cap=delta/4;reserve=F(1,10**20)
    assert F(p['full_margin_delta'])==delta and F(p['single_tail_budget'])==cap and F(p['rounding_reserve'])==reserve and p['fixed_DS']==DS
    assert len(set(b['multiplier_id']for b in model['blocks']))==73
    plans=model['entry_plans'];assert len({(q,s)for q,s,offset,count in plans})==len(plans)
    ntarget=sum(count for q,s,offset,count in plans);assert ntarget==1416525
    bound=5803*716+8580*2+181*5005+ntarget;assert bound==p['atom_count_upper_bound_each_aggregate']
    assert F(2*bound,DS)==F(p['both_rounding_cost_upper_bound'])<reserve<delta/4
    costs=[];totalentries=0
    for bid,(block,f,r)in enumerate(zip(model['blocks'],full['PSD_factors'],p['block_cost_data'])):
        assert block['multiplier_id']==f['multiplier_id']and f['block_id']==bid and f['factor_denominator']==D
        ints=f['factor_numerators_by_row'];n=block['size'];rank=f['column_count'];assert len(ints)==n and all(len(row)==rank for row in ints)
        q=[F(v)for mid,v in model['multipliers'][block['multiplier_id']]['terms']];norm=sum(map(abs,q));div=max([F(1)]+list(map(abs,q)))
        assert div==F(f['positive_rational_block_divisor'])>0
        l1=[sum(abs(row[j])for row in ints)for j in range(rank)]
        assert r=={'block_id':bid,'row_count':n,'original_columns':rank,'coefficient_l1_of_q':str(norm),'positive_rational_block_divisor':str(div),'column_l1_integer_norms':l1}
        costs.extend((F(v*v,D*D)*norm/div,bid,j)for j,v in enumerate(l1));totalentries+=n*rank
    costs.sort(key=lambda x:(x[0],x[1],x[2]));assert [[b,j]for c,b,j in costs]==p['exact_sorted_column_order']
    deleted=[];paid=F(0)
    for cost,b,j in costs:
        if paid+cost>cap:break
        paid+=cost;deleted.append([b,j])
    assert deleted==p['deleted_sorted_prefix']and F(p['total_deleted_cost'])==paid<=cap
    nxt=costs[len(deleted)][0];assert F(p['next_column_exact_cost'])==nxt and paid+nxt>cap
    predicted=delta-paid-reserve;assert predicted==F(p['predicted_retained_margin_at_least'])>0
    deletedset=set(map(tuple,deleted));after=0;columns=0
    for bid,(f,g)in enumerate(zip(full['PSD_factors'],ray['PSD_factors'])):
        keep=[j for j in range(f['column_count'])if(bid,j)not in deletedset]
        assert g['retained_original_column_ids']==keep and g['column_count']==len(keep)
        for field in['block_id','size','multiplier_id','factor_denominator','positive_rational_block_divisor']:assert f[field]==g[field]
        assert g['factor_numerators_by_row']==[[row[j]for j in keep]for row in f['factor_numerators_by_row']]
        after+=g['size']*len(keep);columns+=len(keep)
    for field in['scalar_row_count','moment_column_count','unbounded_slack_column','scalar_weight_denominator','scalar_weight_numerators','forced_zero_scalar_rows','rounded_weights_before_forced_zero','PSD_block_count','native_scalar_sign','trace_semantics']:assert full[field]==ray[field]
    assert len(costs)==p['full_columns']==3010 and len(deleted)==p['deleted_columns']==125 and columns==p['retained_columns']==2885
    assert totalentries==p['full_integer_factor_entries']==190150 and after==p['retained_integer_factor_entries']==182495
    assert [r['block_id']for r in ray['PSD_factors']if not r['column_count']]==p['empty_factor_blocks']==[]
    def literal(a):return '['+', '.join(map(literal,a))+']'if isinstance(a,list)else str(a)
    text='/- Fixed retained integer data only. Not compiled; no proof/checker included. -/\nnamespace FixedRetainedRayData\n'
    text+='def commonDenominator : Nat := '+str(D)+'\n'
    text+='def scalarNumerators : List Nat := '+literal(ray['scalar_weight_numerators'])+'\n'
    text+='def blockColumnCounts : List Nat := '+literal([r['column_count']for r in ray['PSD_factors']])+'\n'
    text+='def gramFactors : List (List (List Int)) := '+literal([r['factor_numerators_by_row']for r in ray['PSD_factors']])+'\nend FixedRetainedRayData\n'
    assert text.encode()==(BASE/'RetainedRayData.lean').read_bytes()
    size=p['source_size'];assert len(text.encode())==size['ordinary_uncompiled_Lean_data_file_bytes']==2394367
    assert len((BASE/'retained-ray.json.gz').read_bytes())==size['retained_ray_gzip_bytes']and len(gzip.decompress((BASE/'retained-ray.json.gz').read_bytes()))==size['retained_ray_uncompressed_JSON_bytes']
    assert size['remaining_bytes_after_data_only']==2000000-len(text.encode())<0 and not size['complete_source_budget_met']
    pins[(BASE/'RetainedRayData.lean').relative_to(ROOT).as_posix()]=sha(BASE/'RetainedRayData.lean')
    for n,h in pins.items():assert sha(ROOT/n)==h
    return{'passed':True,'source_sha256':pins,'exact_sort_and_unique_maximal_prefix_checked':True,'column_costs_checked':3010,'deleted_columns':125,'retained_columns':2885,
        'remaining_integer_entries':182495,'retained_integer_entries_byte_exact':True,'lambda_weights_unchanged':True,'allq_coefficient_l1_includes_constant':True,
        'drop_cost':str(paid),'predicted_margin':str(predicted),'DS30_both_aggregate_roundreserve_proved':True,'uncompiled_Lean_data_bytes':2394367,'complete_source_budget_met':False}
if __name__=='__main__':
    assert __debug__
    print(json.dumps(verify(),indent=2))
