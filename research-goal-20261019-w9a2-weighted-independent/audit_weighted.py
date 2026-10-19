"""Direct independent rational certificate audit; no Karp/LP/geometry search.
Checks the supplied fixed graph, source costs, potential and attaining cycle.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal, localcontext
import gzip, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
WP=ROOT/'research-goal-20261019-w9a2-weighted-graph/weighted-graph.json'
GP=ROOT/'research-goal-20261019-w9a2-certificate-analysis/geometry-audit.json'
LP=ROOT/'research-goal-20261019-w9a2-certificate-analysis/numeric-leaves-sorted.jsonl.gz'
SP=ROOT/'research-goal-20261019-w9a2-record/official/proof/Solution.lean'
INPUTS=[WP,GP,LP,SP]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def relative(p):return p.relative_to(ROOT).as_posix()
def exact(q):
    with localcontext() as c:
        c.prec=70
        return {'fraction':str(q),'decimal':str(Decimal(q.numerator)/Decimal(q.denominator))}
before={relative(p):sha(p) for p in INPUTS}
assert before[relative(WP)]=='7748d5a35b33931dfc66a83d089ca6ad7f9f707fdbb59af75c0a3c2a7cfa3414'
w=json.loads(WP.read_text(encoding='utf-8'))
g=json.loads(GP.read_text(encoding='utf-8'))
leaves=[json.loads(line) for line in gzip.open(LP,'rt',encoding='utf-8')]
assert w['input_path']==relative(GP) and w['input_sha256']==sha(GP)
assert w['source_sha256']==g['source_sha256']==sha(SP)
assert w['numeric_leaves_input_sha256']==g['numeric_leaves_input_sha256']==sha(LP)
assert len(leaves)==11794 and g['first24']==leaves[:24]
assert all(leaves[i]['margin']<=leaves[i+1]['margin'] for i in range(len(leaves)-1))

S=335544320000000000;SA=10**20;GOOD=10**12;G=48
assert sum(r['margin']<S*GOOD for r in leaves)==24
cost=[leaves[v//2]['margin']//S for v in range(48)]+[GOOD]
vertices=w['vertices'];assert len(vertices)==49
for v,row in enumerate(vertices):
    assert row['vertex']==v and row['cost']==cost[v]
    if v<48:
        source=leaves[v//2]
        assert row['rank']==v//2 and row['reversed']==bool(v%2)
        assert row['root']==source['root'] and row['cursor']==source['pos']
        assert row['original_margin']==source['margin']
        assert cost[v]*S<=source['margin']<(cost[v]+1)*S
    else:assert row['kind']=='good'
assert all(r['margin']>=S*GOOD for r in leaves[24:])
assert w['good_threshold_CN_increment']==GOOD
assert F(w['good_threshold_floor_increment'])==F(GOOD,SA)
assert w['source_quantile_count_below_good']==24

bad={tuple(e) for e in g['graphs']['24']['retained_edges']}
assert len(bad)==37 and all(0<=u<48 and 0<=v<48 for u,v in bad)
expected=bad|{(v,G) for v in range(48)}|{(G,v) for v in range(48)}|{(G,G)}
assert len(expected)==134
cert=w['finite_potential_certificate'];rows=cert['all_134_edges']
supplied={(r['from'],r['to']) for r in rows}
assert len(rows)==len(supplied)==134 and supplied==expected
assert (w['vertex_count'],w['bad_edge_count'],w['edge_count'])==(49,37,134)

mu=F(w['mu_exact_CN_units']);assert mu==F(622387738726,5)
den=cert['common_denominator'];assert den==5
pn=cert['potential_numerators'];assert len(pn)==49 and all(isinstance(x,int) for x in pn)
p=[F(x,den) for x in pn]
assert p[G]==F(cert['G_potential'])==0
osc=max(p)-min(p)
assert osc==F(cert['oscillation_CN_units'])==500944400138
checked=[]
for row in rows:
    u,v=row['from'],row['to']
    assert row['source_cost']==cost[u]
    slack=F(cost[u])-mu-p[v]+p[u]
    assert slack>=0 and slack*den==row['scaled_slack']
    checked.append({'from':u,'to':v,'cost':cost[u],'scaled_slack':int(slack*den)})

cycle=w['attaining_cycle']['vertices']
assert cycle==[10,14,11,19,18,10] and cycle[0]==cycle[-1]
ce=list(zip(cycle,cycle[1:]));assert len(ce)==5 and all(e in expected for e in ce)
cycle_cost=sum(cost[u] for u,v in ce)
assert cycle_cost==622387738726==w['attaining_cycle']['source_cost_sum']
assert F(cycle_cost,len(ce))==mu==F(w['attaining_cycle']['mean_exact'])
assert all(F(cost[u])-mu-p[v]+p[u]==0 for u,v in ce)
assert w['attaining_cycle']['edge_count']==5 and w['attaining_cycle']['all_edges_tight'] is True

cn=F(893029029923108825,SA)
H=F(6721237468782417141365717707344332375586,10**40)
B=F(454741897490,10**14)
avg=cn+mu/SA;k0=(H-B)/(1-cn);k1=(H-B)/(1-avg)
candidate=w['conditional_candidate']
assert F(candidate['baseline_floor'])==cn
assert F(candidate['weighted_average_floor_increment'])==mu/SA
assert F(candidate['weighted_average_floor'])==avg
assert F(candidate['ratio_if_all_actual_localization_and_counting_are_formalized'])==k1
assert F(candidate['proportion_gain'])==k1-k0
dag_increment=F(leaves[7]['margin']//S,5*SA)
assert F(candidate['old_first7_DAG_average_floor_increment'])==dag_increment
assert F(candidate['weighted_minus_first7_increment'])==mu/SA-dag_increment
assert F(candidate['weighted_to_first7_factor'])==(mu/SA)/dag_increment
assert k1>k0 and cn<avg<F(1,64)

outside=w['outside_separated_static_compensation']
extra=F(3191486227473,10**15)
assert F(outside['B'])==B
assert F(outside['extra_pressure_at_least'])==extra>F(GOOD,SA)
assert F(outside['extra_pressure_minus_good_threshold_increment'])==extra-F(GOOD,SA)

after={relative(p):sha(p) for p in INPUTS};assert before==after
out={'passed':True,'scope':'Direct verification of frozen 49-vertex/134-edge rational potential certificate. No Karp repeat, no LP, no geometry rerun, no kernel evaluation, no Lean or new unconditional record.',
     'input_sha256_before':before,'input_sha256_after':after,'input_identity_unchanged':True,
     'vertices':49,'edges':134,'bad_edges':37,'complete_G_links_checked':True,
     'numeric_leaf_count':len(leaves),'bad_leaf_count':24,'all_49_source_costs_checked':True,
     'costs':cost,'all_134_potential_inequalities_checked':True,'checked_edges':checked,
     'mu_CN_units':exact(mu),'potential_oscillation_CN_units':exact(osc),
     'attaining_cycle':cycle,'attaining_cycle_cost':cycle_cost,'attaining_cycle_mean':exact(F(cycle_cost,5)),
     'fixed_outer_graph_optimality':'Every cycle average >= mu by summing the potential inequalities. The supplied five-edge cycle attains mu; no discovery algorithm is needed to verify optimality of this fixed outer graph.',
     'conditional_average_floor':exact(avg),'conditional_K':exact(k1),'conditional_percentage':exact(100*k1),
     'conditional_gain_proportion':exact(k1-k0),'conditional_gain_percentage_points':exact(100*(k1-k0)),
     'finite_sum_consequence':'For any N-edge label path, sum source costs >= N*mu - oscillation(p). Thus, after global quantitative localization is formalized, sum F_i >= N*(c0+mu/SA)-500944400138/SA.',
     'boundary_loss_F_units':exact(osc/SA),'good_exterior_pressure_exceeds_threshold':True,
     'scope_limit':'The 37 bad edges are taken from the frozen geometry graph. Their completeness and the full source-walk quantitative localization/reflection/exterior/actual-zeta counting still need Lean integration. An attaining outer-graph cycle need not be one physically periodic low-energy configuration.',
     'new_unconditional_record_proven':False,'new_Lean_theorem':False}
(HERE/'audit.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['passed','vertices','edges','mu_CN_units','conditional_average_floor','conditional_percentage','conditional_gain_percentage_points']},indent=2))
