"""Independent stdlib exact audit of the fixed W9 deletion-gluing obstruction.

Reads actual Core/W10/SharpWindow statements and literal coefficients.
Imports no producer or numerical package; invokes no solver or Lean.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from decimal import Decimal,ROUND_FLOOR,ROUND_CEILING
from itertools import combinations
import argparse,ast,hashlib,json,re,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;BASE=ROOT/'research-goal-20261017-ninepoint-decomposition';OUT=HERE/'independent-replay.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic()
    names=['GramDefect20261015/Core.lean','GramDefect20261015/SharpWindow.lean','StructuralResearch20261016/W10RefinedCandidate.lean','StructuralW10Cert20261016/FinalConditional.lean',
        'research-goal-20261017-ninepoint-decomposition/coefficient-gluing.json','research-goal-20261017-ninepoint-decomposition/support-obstruction.json','research-goal-20261017-ninepoint-decomposition/presolver-failure.json',
        'research-goal-20261017-ninepoint-decomposition/coefficient_gluing.py','research-goal-20261017-ninepoint-decomposition/coefficient_gluing_presolver_failed.py','research-goal-20261017-ninepoint-decomposition/support_obstruction.py']
    pins={n:digest(ROOT/n)for n in names};pins[Path(__file__).relative_to(ROOT).as_posix()]=digest(Path(__file__))
    gl=json.loads((BASE/'coefficient-gluing.json').read_bytes());ob=json.loads((BASE/'support-obstruction.json').read_bytes());failure=json.loads((BASE/'presolver-failure.json').read_bytes())
    assert pins[names[4]]=='e39f511b50d8e45ecf9f058f3f717d050c2cd1c316e2d7c846031b833bbfc25b'and pins[names[5]]=='adad9dbc9ef49a7a024e6564247580cd5b9eeded2c90217ad795e2cea67d01c9'
    for r in gl['source_files']+ob['source_files']:assert digest(ROOT/r['path'])==r['sha256']and(ROOT/r['path']).stat().st_size==r['bytes']
    core=(ROOT/names[0]).read_text(encoding='utf8');sharp=(ROOT/names[1]).read_text(encoding='utf8');new=(ROOT/names[2]).read_text(encoding='utf8');wrapper=(ROOT/names[3]).read_text(encoding='utf8')
    lines=core.splitlines();start=lines.index('namespace AMW.Cert.PC9QB6M');block=lines[start:]
    def rhs(name):return next(line.partition(':=')[2].strip()for line in block if line.startswith('def '+name+' :'))
    terms=ast.literal_eval(rhs('TS'));bs=ast.literal_eval(rhs('BS'));sa=int(rhs('SA'));cn=int(rhs('cN'));c9=F(cn,sa)
    assert len(terms)==34 and len(bs)==8 and len({(i,j)for i,j,a,k in terms})==34 and all(a>0 and 0<=i<j<9 for i,j,a,k in terms)
    assert c9==F(gl['old_proved_floor'])==F(ob['old_floor'])
    olda={(i,j):a for i,j,a,k in terms};newblock=new.split('def aN :',1)[1].split('def bN :',1)[0]
    newa={(int(i),int(j)):int(a)for i,j,a in re.findall(r'\| (\d+), (\d+) => (\d+)',newblock)}
    assert len(newa)==39 and all(a>0 for a in newa.values())
    omiss=sorted(set(combinations(range(9),2))-set(olda));nmiss=sorted(set(combinations(range(10),2))-set(newa))
    degrees=[sum(v in e for e in nmiss)for v in range(10)]
    assert list(map(list,omiss))==ob['old_missing_edges']and list(map(list,nmiss))==ob['target_missing_edges']and degrees==ob['target_missing_graph_degrees']
    assert len(omiss)==2 and len(nmiss)==6 and max(degrees)==3
    support_results=[];columns=[]
    for omitted in range(10):
        image=[i+int(i>=omitted)for i in range(9)];assert len(set(image))==9 and omitted not in image
        mapped={(image[i],image[j]):a for(i,j),a in olda.items()}
        # Reconstruct pressure using the explicit duplicated-old-gap formula,
        # independently of the producer's physical-gap expansion loop.
        bp=([0]+bs)if omitted==0 else(bs+[0])if omitted==9 else(bs[:omitted]+[bs[omitted-1]]+bs[omitted:])
        pressure=list(map(lambda v:F(v,sa),bp));B=sum(pressure,F(0));expected=F(sum(bs)+(bs[omitted-1]if 1<=omitted<=8 else 0),sa);assert B==expected
        mass=[F(0)]*9
        for i,j,a,k in terms:
            span=(j-i)+int(j>=omitted)-int(i>=omitted);assert 1<=span<=9
            mass[span-1]+=F(a,sa)
        r=gl['ordered_deletion_embeddings'][omitted]
        assert r=={'omitted':omitted,'image':image,'span_masses':list(map(str,mass)),'pulled_pressure_by_gap':list(map(str,pressure)),'total_pressure':str(B)}
        clashes=[{'old_pair':[i,j],'image_pair':[image[i],image[j]],'old_positive_integer_coefficient':a,'target_integer_coefficient':0}for(i,j),a in sorted(olda.items())if(image[i],image[j])not in newa]
        absent=sum(1 for e in nmiss if omitted not in e);assert absent==len(nmiss)-degrees[omitted]>len(omiss)and clashes
        sr={'omitted':omitted,'ordered_image':image,'remaining_missing_edges':absent,'all_zero_edge_clashes':clashes,'first_exact_clash':clashes[0]};assert sr==ob['ordered_embeddings'][omitted]
        support_results.append(sr);columns.append((mass,B))
    M=F(sum(olda.values()),sa);assert M==F(1599999987,10**8)==F(gl['old_exact_total_pair_mass'])and M!=16
    oldmass=[sum((F(a,sa)for(i,j),a in olda.items()if j-i==d),F(0))for d in range(1,9)]
    assert list(map(str,oldmass))==gl['old_exact_span_masses']and sum(oldmass,F(0))==M and all(0<m<=2 for m in oldmass)
    assert all(sum(m,F(0))==M for m,B in columns)
    # Actual theorem/domain/kernel and H references are statically inspected,
    # not newly compiled. The embedded gaps are sums of nonnegative gaps.
    certdecl=next(s for s in lines if s.startswith('theorem cert_AM :'))
    assert '∀ g : Fin 8 → ℝ, (∀ i, 0 ≤ g i)'in certdecl and f'(({cn} : ℝ) / {sa}) ≤ Fw W9 g'in certdecl
    assert 'theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl'in core
    assert 'theorem Fw_W9 (g : Fin (9 - 1) → ℝ)'in core and 'def W9 : WCert 9 := ⟨aW9, bW9⟩'in core
    assert 'import GramDefect20261015.Core'in new and 'def W : WCert 10 := ⟨a, b⟩'in new
    hwmatch=re.search(r'def windowFloor : ℝ := (\d+) / 10 \^ 40',wrapper);H=F(int(hwmatch[1]),10**40)
    assert f'theorem HW_ge : ({hwmatch[1]} / 10 ^ 40 : ℝ) ≤ AMW.HW'in sharp and 'using GramDefect20261015.Window.HW_ge'in wrapper
    record=re.search(r'def currentSiteRatio : ℝ :=\s*(\d+) / (\d+)',wrapper);R=F(int(record[1]),int(record[2]));K=R+F(1,10**5)
    assert H==F(gl['window_floor'])and R==F(gl['record'])and K==F(gl['required_strict_target'])
    upper=18/M;assert upper==F(gl['all_capacity_rows_sum_implies_total_weight_at_most'])and c9*upper<F(1,64)<1
    lam=list(map(F,gl['exact_primal_weights']));y=list(map(F,gl['exact_dual_nonnegative_weights']));assert len(lam)==10 and len(y)==9 and min(lam+y)>=0
    loads=[sum((columns[j][0][s]*lam[j]for j in range(10)),F(0))for s in range(9)]
    assert list(map(str,loads))==gl['exact_primal_capacity_loads']and all(x<=2 for x in loads)and sum(lam,F(0))<=upper
    floor=c9*sum(lam,F(0));B=sum((lam[j]*columns[j][1]for j in range(10)),F(0));ratio=(H-B)/(1-floor)
    assert str(floor)==gl['exact_primal_floor']and str(B)==gl['exact_primal_pressure']and str(ratio)==gl['exact_primal_ratio']and 0<floor<F(1,64)and ratio<K
    gains=[K*c9-Bj for mass,Bj in columns];covered=[sum((mass[s]*y[s]for s in range(9)),F(0))for mass,Bj in columns]
    assert list(map(str,gains))==gl['exact_linearized_column_gains']and list(map(str,covered))==gl['exact_dual_covered_column_gains']and all(a>=b for a,b in zip(covered,gains))
    U=2*sum(y,F(0));threshold=K-H;gap=threshold-U
    assert str(U)==gl['exact_dual_upper']and str(threshold)==gl['exact_required_threshold']and str(gap)==gl['exact_strict_gap_threshold_minus_upper']and gap>F(1,100000)>0
    assert (ratio-K)*(1-floor)==sum((gain*w for gain,w in zip(gains,lam)),F(0))-threshold
    # Check the deterministic saved-float-to-rational reconstruction, without
    # using those floats as a validity or optimality assertion.
    D=10**18;roundq=lambda value,mode:F(int((Decimal(str(max(0.,float(value))))*D).to_integral_value(rounding=mode)),D)
    rawlam=[roundq(x,ROUND_FLOOR)for x in gl['raw_primal']];rawloads=[sum((columns[j][0][s]*rawlam[j]for j in range(10)),F(0))for s in range(9)]
    scale=min([F(1)]+[2/z for z in rawloads if z>0]);assert str(scale)==gl['primal_scale']and [v*scale for v in rawlam]==lam
    rawy=[roundq(-v,ROUND_CEILING)for v in gl['raw_dual_minimize_marginals']];before=[sum((mass[s]*rawy[s]for s in range(9)),F(0))for mass,Bj in columns]
    repair=max([F(0)]+[(g-b)/M for g,b in zip(gains,before)]);assert str(repair)==gl['exact_dual_uniform_repair']and[v+repair for v in rawy]==y
    failed=(BASE/'coefficient_gluing_presolver_failed.py').read_text(encoding='utf8');current=(BASE/'coefficient_gluing.py').read_text(encoding='utf8')
    assert failure['solver_calls']==0 and failure['stage']=='before importing scipy or optimizer call'and failure['execution_exit_code']==1
    assert failure['failed_source_sha256']==pins[names[8]]and failed.index('assert sum(mass, F(0)) == 16')<failed.index('import numpy as np')<failed.index('result = linprog(')
    tree=ast.parse(current);calls=[n for n in ast.walk(tree)if isinstance(n,ast.Call)and isinstance(n.func,ast.Name)and n.func.id=='linprog'];assert len(calls)==1
    assert gl['optimizer_calls']==1 and gl['pre_solver_failed_executions']==1 and gl['family_cannot_reach_record_plus_one_over_100000']and not gl['exact_primal_exceeds_strict_goal']
    for n,h in pins.items():assert digest(ROOT/n)==h
    def line_no(text,needle):return next(i for i,line in enumerate(text.splitlines(),1)if needle in line)
    references=[{'path':names[0],'line':line_no(core,'theorem cert_AM :'),'role':'W9 floor on every nonnegative eight-gap vector'},
        {'path':names[0],'line':line_no(core,'theorem cert_wfun_eq'),'role':'same actual kernel identity'},
        {'path':names[0],'line':line_no(core,'def WCert.spanMass'),'role':'capacity by rank, not physical span'},
        {'path':names[1],'line':line_no(sharp,'theorem HW_ge'),'role':'same-kernel H lower bound'},
        {'path':names[3],'line':line_no(wrapper,'def windowFloor'),'role':'frozen H and record wrapper'}]
    out={'scope':__doc__,'passed':True,'source_sha256_start':pins,'source_sha256_end':pins,'all_inputs_unchanged':True,'source_references':references,
        'actual_theorem_domain_statically_checked':'all eight old gaps nonnegative; deletion gaps are sums of original nonnegative gaps','same_old_kernel_identity_statically_checked':True,'theorems_recompiled_or_independently_kernel_replayed':False,
        'ordered_embeddings_rebuilt':10,'capacity_matrix_shape':[9,10],'internal_deletion_pressure_duplication_checked':True,'old_total_pair_mass':str(M),'mass_equals_16':False,'all_feasible_family_floors_below_one_over_64':True,
        'old_floor':str(c9),'H':str(H),'record':str(R),'goal':str(K),'nonnegative_primal_weights_checked':10,'primal_capacity_rows_checked':9,'nonnegative_dual_weights_checked':9,'dual_column_bounds_checked':10,
        'all10_support_embeddings_have_positive_into_zero_clashes':True,'arbitrary_injective_support_embedding_impossible_by_34_vs_at_most33_edges':True,'unchanged_nonnegative_coefficient_decomposition_forces_all_lambda_zero':True,
        'ratio_denominator_positive_for_every_capacity_feasible_lambda':True,'strict_ratio_linearization_identity_checked':True,'exact_dual_upper':str(U),'exact_threshold':str(threshold),'exact_strict_gap':str(gap),'gap_hint':float(gap),'primal_percent_hint':float(100*ratio),
        'fixed_continuous_nonnegative_gluing_family_cannot_reach_goal':True,'no_solver_optimality_assumption':True,'initial_failed_main_executions_before_solver':1,'later_solver_calls_reported':1,'failure_provenance_statically_consistent':True,
        'failure_scope':'Unchanged-ledger nonnegative embedding decomposition and the ten ordered deletion-embedding coefficient family only; no obstruction to signed paid remainders, new kernels, nonlinear arguments or other families.',
        'producer_imports':0,'solver_calls':0,'NumPy_or_SciPy_imports':0,'kernel_evaluations':0,'tree_records_read':0,'Lean_invocations':0,'new_global_floor_proven':False,'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'old_mass':str(M),'embeddings':10,'exact_dual_rules_out_fixed_goal_family':True,'gap_hint':float(gap),'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
