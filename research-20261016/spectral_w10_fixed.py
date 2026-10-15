"""Freeze rational W10 research parameters. Does not assert the analytic floor."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib, json, math, re

HERE=Path(__file__).resolve().parent
source=HERE/'spectral-wcert-reopt.json'
record=json.loads(source.read_text())['results'][0]
assert record['n']==10
D=10**10
A={(i,j):math.floor(value*D) for i,j,value in record['a']}
B=[math.ceil(value*D) for value in record['b']]
C=Q(433,50000)
assert all(value>=0 for value in A.values())
assert all(value>0 for value in B)
capacities=[sum(value for (i,j),value in A.items() if j-i==d) for d in range(1,10)]
assert max(capacities)<=2*D
assert all(A[i,j]==A[9-j,9-i] for i,j in A)
assert B==B[::-1]
H=Q(6721684105641188747759983512104999330646,10**40)
pressure=Q(sum(B),D)
kappa=(H-pressure)/(1-C)
assert kappa>Q(421,625)
text=(HERE.parent/'GramDefect20261015/Core.lean').read_text(encoding='utf8')
asection=text[text.index('def aW9 :'):text.index('def bW9 :')]
bsection=text[text.index('def bW9 :'):text.index('def W9 :')]
a9={(int(i),int(j)):Q(int(v),10**14) for i,j,v in re.findall(r'\| (\d+), (\d+) => \((\d+) :',asection)}
b9=[Q(int(v),10**14) for _,v in re.findall(r'\| (\d+) => \((\d+) :',bsection)]
average={key:Q(0) for key in A};average_b=[Q(0)]*9
for t in range(2):
    for (i,j),value in a9.items():average[i+t,j+t]+=value/2
    for i,value in enumerate(b9):average_b[i+t]+=value/2
differences=[{'i':i,'j':j,'new_numerator':value,'averaged_W9_exact':str(average[i,j]),
    'difference_exact':str(Q(value,D)-average[i,j])} for (i,j),value in A.items()]
report={'scope':'Exact rational admissible W10 parameters; full analytic floor remains unproved',
    'source':str(source.name),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'search_lower_gap_exact':'4/5','actual_remainder_lower_gap_exact':'17/20',
    'denominator':D,'a_upper':[[i,j,value] for (i,j),value in A.items()],
    'b_numerators':B,'span_capacity_numerators':capacities,'B_exact':str(pressure),
    'proposed_floor_exact':str(C),'proposed_floor_decimal':float(C),
    'conditional_kappa_exact':str(kappa),'conditional_percent':100*float(kappa),
    'clean_conditional_target':'kappa > 421/625 = 0.6736',
    'observed_unrounded_minimum':record['history'][-1]['adversarial_c'],
    'observed_margin_before_rounding':record['history'][-1]['adversarial_c']-float(C),
    'rounding_directions':{'a':'down','b':'up'},
    'trivial_global_a_rounding_loss_bound':float(sum(Q(str(value))-Q(A[i,j],D) for i,j,value in record['a'])),
    'coercive_box':{'argument':'Fw >= sum b_i g_i; if Fw<c, each g_i<c/b_i',
        'individual_upper_bounds_exact':[str(C/Q(value,D)) for value in B],
        'maximum_upper_bound':float(C/Q(min(B),D))},
    'changes_from_two_averaged_W9_windows':{'new_distance_9_weight_exact':str(Q(A[0,9],D)),
        'pressure_increase_exact':str(pressure-sum(b9)),
        'total_absolute_a_change_exact':str(sum(abs(Q(value,D)-average[i,j]) for (i,j),value in A.items())),
        'a_differences':differences,
        'b_differences_exact':[str(Q(value,D)-old) for value,old in zip(B,average_b)]}}
challenge_path=HERE/'spectral-w10-challenge.json'
if challenge_path.exists():
    challenge=json.loads(challenge_path.read_text())
    report['scope']='Exact rational admissible parameters only; proposed floor REFUTED, no proportion follows'
    report['proposed_floor_status']='REFUTED by continuous central-three-gap counterexample'
    report['counterexample']={'value':challenge['best_observed_minimum'],'gaps':challenge['gaps'],
        'source':challenge_path.name}
    lower=Q(27,3125);lower_kappa=(H-pressure)/(1-lower)
    old=Q(3338957652820594373879991756052499665323,4957023073704306225950000000000000000000)
    report['alternative_unproved_floor']={'exact':str(lower),'decimal':float(lower),
        'conditional_percent':100*float(lower_kappa),
        'conditional_gain_percentage_points':100*float(lower_kappa-old),
        'status':'Unproved; currently survives the recorded counterexample only'}
(HERE/'spectral-w10-rational.json').write_text(json.dumps(report,indent=2)+'\n')
lines=['/- Exact research parameters only; the analytic Fw floor is not claimed. -/',
    'import GramDefect20261015.Core','', 'noncomputable section',
    'open Finset Zeta23Ext.BridgeW','open scoped BigOperators',
    'set_option maxHeartbeats 2000000',
    'namespace StructuralResearch20261016.W10Candidate',
    'def aN : Fin 10 → Fin 10 → ℕ']
lines += [f'  | {i}, {j} => {value}' for (i,j),value in A.items() if value]
lines += ['  | _, _ => 0','def bN : Fin 9 → ℕ']
lines += [f'  | {i} => {value}' for i,value in enumerate(B)]
lines += [f'def a (i j : Fin 10) : ℝ := (aN i j : ℝ) / {D}',
    f'def b (i : Fin 9) : ℝ := (bN i : ℝ) / {D}',
    'def W : WCert 10 := ⟨a, b⟩',
    'theorem a_nonneg : ∀ i j, 0 ≤ W.a i j := by',
    '  intro i j', '  dsimp [W, a]', '  positivity',
    'theorem b_nonneg : ∀ i, 0 ≤ W.b i := by',
    '  intro i', '  dsimp [W, b]', '  positivity',
    'def spanN (s : ℕ) : ℕ := ∑ i : Fin 10, ∑ j : Fin 10,',
    '  if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then aN i j else 0',
    f'theorem nat_capacity : ∀ s : ℕ, spanN s ≤ {2*D} := by',
    '  intro s', '  rcases lt_or_ge s 10 with hs | hs',
    '  · interval_cases s <;> decide',
    '  · have h0 : ∀ i j : Fin 10, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by',
    '      intro i j ⟨_, h⟩', '      have := j.2', '      omega',
    '    simp only [spanN, h0, if_false, Finset.sum_const_zero]', '    norm_num',
    f'theorem span_eq (s : ℕ) : W.spanMass s = (spanN s : ℝ) / {D} := by',
    '  simp only [WCert.spanMass, W, a, spanN, Nat.cast_sum, Nat.cast_ite,',
    '    Nat.cast_zero, Finset.sum_div, ite_div, zero_div]',
    'theorem capacity (s : ℕ) : W.spanMass s ≤ 2 := by',
    '  rw [span_eq]',
    f'  have hn : (spanN s : ℝ) ≤ {2*D} := by exact_mod_cast nat_capacity s',
    '  nlinarith',
    'theorem adm : W.Adm := ⟨a_nonneg, b_nonneg, capacity⟩',
    f'theorem bN_sum : (∑ i : Fin 9, bN i) = {sum(B)} := by decide',
    f'theorem pressure_eq : W.B = ({pressure.numerator} : ℝ) / {pressure.denominator} := by',
    f'  change (∑ i : Fin 9, (bN i : ℝ) / {D}) = _',
    '  rw [← Finset.sum_div, ← Nat.cast_sum, bN_sum]', '  norm_num',
    '-- No analytic floor or zeta proportion theorem is asserted in this module.',
    '#print axioms adm','#print axioms pressure_eq',
    'end StructuralResearch20261016.W10Candidate','end','']
(HERE.parent/'StructuralResearch20261016/W10Candidate.lean').write_text('\n'.join(lines),encoding='utf8')
print(json.dumps({key:report[key] for key in ['B_exact','proposed_floor_exact','proposed_floor_status','alternative_unproved_floor'] if key in report},indent=2))
