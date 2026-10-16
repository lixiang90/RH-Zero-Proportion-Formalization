"""Independent exact replay and arbitrary-block extension of an embedding dual.

Standard library only. Reparse the two old nine-point certificates without
importing the LP producer. Check every translation class on seventeen
vertices, including both ledgers; outside that range pressure alone makes
the target profit negative. Thus a nonnegative combination of either frozen
old certificate, embedded in any larger ordered block, cannot meet this
target using the stated fixed H and rank capacities. This is a limitation
of this construction class, not of new profiles, new analytic floors, or RH.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import ast,hashlib,json,re,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PILOT=HERE/'window-large-embedding-pilot.json'
OUT=HERE/'window-large-embedding-replay.json'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def read_certificate(path):
    text=path.read_text(encoding='utf8')
    def nat(s):return int(re.search(r'^def '+s+r' : ℕ := (\d+)\s*$',text,re.M)[1])
    def literal(s):return ast.literal_eval(re.search(r'^def '+s+r' : List[^\n]* := (\[[^\n]*\])\s*$',text,re.M)[1])
    den=nat('SA');a=[(i,j,F(v,den)) for i,j,v,_ in literal('TS')]
    b=[F(v,den) for v in literal('BS')];c=F(nat('cN'),den)
    assert len(a)==34 and len(b)==8 and all(v>0 for v in b)
    assert all(0<=i<j<9 and v>=0 for i,j,v in a)
    assert '∀ g : Fin 8 → ℝ, (∀ i, 0 ≤ g i) →' in re.search(r'^theorem cert_AM :[^\n]+',text,re.M)[0]
    coeff=re.search(r'^def cAMn[^\n]*\n(.*?)^def cAM ',text,re.M|re.S)[1]
    return a,b,c,{int(i):int(v) for i,v in re.findall(r'\| (\d+) => (-?\d+)',coeff)}

def main():
    assert not OUT.exists();began=time.monotonic();p=json.loads(PILOT.read_bytes())
    for path,digest in p['inputs_sha256'].items():assert sha(ROOT/path)==digest
    assert p['vertices']==17 and p['translation_classes']==12870
    y=list(map(F,p['exact_dual']));assert len(y)==16 and min(y)>=0
    K=F(p['target']);H=F(p['H'])
    assert K==F(34191001116882886388531117129201664,50760020691785094633026544189453125)+F(1,100000)
    paths=[ROOT/'GramDefect20261015/Core.lean',ROOT/'research-20261016-w10-cert/current-record-source.txt']
    packets=[read_certificate(path) for path in paths]
    assert packets[0][3]==packets[1][3]
    columns=[];outside=[]
    for dataset,(a,b,c,_) in enumerate(packets):
        # Any omitted translation class has final vertex >=17, so its eight
        # integer positive index gaps contain at least nine extra unit gaps.
        # Its pressure is >= sum(b)+9*min(b)>K*c. Nonnegative dual payouts
        # then verify every omitted column, independently of its rank masses.
        pressure_lower=sum(b)+9*min(b);tail_slack=pressure_lower-K*c
        assert tail_slack>0
        outside.append({'dataset':dataset,'minimum_outside_span':17,
            'pressure_lower':str(pressure_lower),'strict_negative_profit_margin':str(tail_slack)})
        mass=sum(v for _,_,v in a)
        for tail in combinations(range(1,17),8):
            vertices=(0,)+tail;ranks=[F(0)]*16
            for i,j,v in a:ranks[vertices[j]-vertices[i]-1]+=v
            B=sum(b[i]*(vertices[i+1]-vertices[i]) for i in range(8))
            assert sum(ranks)==mass
            columns.append((dataset,ranks,K*c-B,mass))
    # Adding an equal nonnegative payment to ranks 1..16 repairs both
    # ledgers exactly, with no numerical solver or new optimization.
    repair=max([F(0)]+[(profit-sum(u*v for u,v in zip(ranks,y)))/mass
                       for _,ranks,profit,mass in columns])
    y=[v+repair for v in y]
    minimum=min(sum(u*v for u,v in zip(ranks,y))-profit for _,ranks,profit,_ in columns)
    assert len(columns)==25740 and minimum>=0
    gap=K-H-2*sum(y);assert gap>0
    # For any finite admissible nonnegative mixture, sum lambda*(K*c-B)
    # <= sum_rank y_rank*rank_mass <=2*sum(y)<K-H. With C<1 this is
    # exactly (H-B_total)/(1-C)<K. No block-size denominator bound is used.
    output={'scope':__doc__,'passed':True,'finite_columns_checked':len(columns),
        'certificate_families':2,'rank_dual_with_zero_tail':list(map(str,y)),
        'repair_from_pilot_dual':str(repair),'minimum_finite_column_slack':str(minimum),
        'all_omitted_columns_paid_by_pressure':outside,'target':str(K),'fixed_H':str(H),
        'dual_objective_upper':str(2*sum(y)),'strict_goal_shortfall':str(gap),
        'arbitrary_larger_block_size':True,'mixed_old_ledgers_allowed':True,
        'valid_counting_regime_condition':'C=sum(lambda*c_old)<1',
        'uses_numerical_solver':False,'new_global_floor':False,'new_zero_proportion_proven':False,
        'inputs_sha256':{str(path.relative_to(ROOT)).replace('\\','/'):sha(path)
            for path in [Path(__file__),PILOT]+paths},'seconds':time.monotonic()-began}
    OUT.write_text(json.dumps(output,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:output[k] for k in ['passed','finite_columns_checked','arbitrary_larger_block_size',
        'repair_from_pilot_dual','strict_goal_shortfall','seconds']}),flush=True)

if __name__=='__main__':main()
