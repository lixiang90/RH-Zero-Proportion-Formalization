"""Compose finite aggregate checks with actual grouped rows and energy.

Generated local exclusions are proof obligations until ordinary Lean passes.
They concern exactly two cells; no complete global cover is asserted.
"""
from window_moment_frozen_write import write_lean
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
cases=json.loads((HERE/'cover-cross-moment-factor-friendly-cases.json').read_bytes())['cases']
opts='set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
source='/- SPDX-License-Identifier: Apache-2.0 -/\n'
for k in range(2):
 for label in ['Gap','Scalar','H','Q0','Q1','Q2','Bounds']:
  source+=f'import StructuralGoal20261016.WindowMomentAggregate{k}{label}\n'
 for m in ['EnergyCase','BoxCase']:source+=f'import StructuralGoal20261016.WindowMoment{m}{k:02}\n'
source+=opts+'''noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentExclusions
open WindowMomentAggregateData WindowMomentAggregateChecks WindowMomentPolynomial
open WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
'''
for k,n in [(0,103),(1,106)]:
 weight=cases[k]['energy_weight']
 source+=f'''theorem radius{k} : ∀ r : Fin 9, 0 < box{k}.radius r := by decide +kernel

theorem qComplete{k} (s : Fin 9) (e : Fin 41) :
 (row{k}.coeff (WindowMomentLayout.qIndex s e):ℚ) =
 (den{k}:ℚ)*flatten aggregate{k} (WindowMomentLayout.qIndex s e) := by
 fin_cases s
'''+''.join(f' · exact check{k}Q{r//3} {r%3} e\n'for r in range(9))+f'''
theorem exactChecked{k} : WindowMomentExactInteger.check den{k}
 (flatten aggregate{k}) aggregate{k}.bound row{k} = true := by
 unfold WindowMomentExactInteger.check
 rw [decide_eq_true_eq]
 refine ⟨check{k}Scale,?_,check{k}Bound⟩
 intro i
 rw [← WindowMomentPolynomial.encode_decode i]
 generalize WindowMomentPolynomial.decode i = b
 cases b with
 | inl r => exact check{k}Gap r
 | inr b =>
   cases b with
   | inl e => exact check{k}Scalar e
   | inr b =>
     cases b with
     | inl e => exact check{k}H e
     | inr p => exact qComplete{k} p.1 p.2

theorem actualBound{k} {{g : Fin 9 → ℝ}}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell{k} g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) :
 eval aggregate{k} (realVector box{k}.center) (realVector box{k}.radius) g ≤
 (aggregate{k}.bound:ℝ) := by
 have hr : ∀ r, (0:ℝ) < (box{k}.radius r:ℝ) := fun r => Rat.cast_pos.mpr (radius{k} r)
 have hn : ∀ r, box{k}.radius r ≠ 0 := fun r => ne_of_gt (radius{k} r)
 have hcoord : ∀ r, (box{k}.center r:ℝ)-(box{k}.radius r:ℝ) ≤ g r ∧
     g r ≤ (box{k}.center r:ℝ)+(box{k}.radius r:ℝ) := by
   intro r
   have h := WindowMomentBoxCase{k:02}.bounds hcell (WindowMomentLayout.gapIndex r)
   simpa [WindowMomentBox.lower,WindowMomentBox.upper,WindowMomentBox.actual,
     WindowMomentLayout.actual,WindowMomentLayout.gapIndex] using h
 have hden : (0:ℝ) < (WindowDirectionalFlow.denominator:ℝ) := by
   norm_num [WindowDirectionalFlow.denominator,WindowDirectionalFlow.SC,
     WindowDirectionalFlow.DS,WindowDirectionalFlow.D]
 have hgroups : ∀ i : Fin {n}, eval (groups{k} i)
     (realVector box{k}.center) (realVector box{k}.radius) g ≤ ((groups{k} i).bound:ℝ) := by
   intro i
   have hf : (∑ r : Fin 9, |(factorB{k} i r:ℝ)|) ≤ (factorA{k} i:ℝ) := by
     exact_mod_cast (WindowMomentAtomsAll.factor{k} i).2
   have hA : (∑ r : Fin 9, |((((factorB{k} i r:ℚ)/(WindowDirectionalFlow.denominator:ℚ)):ℚ):ℝ)|) ≤
       ((((factorA{k} i:ℚ)/(WindowDirectionalFlow.denominator:ℚ)):ℚ):ℝ) := by
     push_cast
     simp_rw [abs_div,abs_of_pos hden]
     rw [← Finset.sum_div]
     exact div_le_div_of_nonneg_right hf hden.le
   exact grouped_nonpos (WindowLiftedKKT.form cell{k} (atoms{k} i))
     box{k}.center box{k}.radius _ _ g hA hr hcoord (WindowMomentAtomsAll.valid{k} hg hcell i)
 have henergy : eval energy{k} (realVector box{k}.center) (realVector box{k}.radius) g ≤
     (energy{k}.bound:ℝ) := by
   have he := WindowMomentEnergyPolynomial.energyForm_sublevel
     WindowMomentEnergyCase{k:02}.checked box{k}.center box{k}.radius (11/1250) hn hcell hbelow
   exact WindowMomentFormSum.scale_valid ({weight}:ℚ) _ _ _ _ (by norm_num) he.le
 rw [aggregate{k},WindowMomentFormSum.eval_add,WindowMomentFormSum.eval_sum]
 change (∑ i, eval (groups{k} i) (realVector box{k}.center) (realVector box{k}.radius) g)+
   eval energy{k} (realVector box{k}.center) (realVector box{k}.radius) g ≤
   (((∑ i, (groups{k} i).bound)+energy{k}.bound:ℚ):ℝ)
 push_cast
 exact add_le_add (Finset.sum_le_sum (fun i _ => hgroups i)) henergy

theorem exclude{k} {{g : Fin 9 → ℝ}}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell{k} g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) : False := by
 have hgeometry : WindowMomentBox.checkGeometry cell{k} box{k} = true := by decide +kernel
 have hb := WindowMomentGlobalBox.sound hgeometry hcell
 have hx : ∀ i, (lower{k} i:ℝ)/(boxScale:ℝ) ≤ WindowMomentBox.actual box{k} g i ∧
     WindowMomentBox.actual box{k} g i ≤ (upper{k} i:ℝ)/(boxScale:ℝ) := by
   intro i
   have hl : (((lower{k} i:ℚ)/(boxScale:ℚ):ℚ):ℝ) =
       ((WindowMomentBox.lower (WindowMomentGlobalBox.global box{k}) i):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (check{k}Box i).1
   have hu : (((upper{k} i:ℚ)/(boxScale:ℚ):ℚ):ℝ) =
       ((WindowMomentBox.upper (WindowMomentGlobalBox.global box{k}) i):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (check{k}Box i).2
   push_cast at hl hu
   rw [hl,hu]
   exact hb i
 exact WindowMomentExactInteger.exclude lower{k} upper{k} exactChecked{k} check{k}Strict
   (WindowMomentBox.actual box{k} g) hx (actualBound{k} hg hcell hbelow)
'''
source+='set_option pp.fullNames true\n'
for k in range(2):
 for m in ['exactChecked','actualBound','exclude']:source+=f'#print axioms {m}{k}\n'
source+='end StructuralGoal20261016.WindowMomentExclusions\nend\n'
actual='''/- SPDX-License-Identifier: Apache-2.0
Actual inequalities for the complete exact rational moment aggregate.
Integer coefficient matching and strict separation are separate obligations.
-/
import StructuralGoal20261016.WindowMomentAggregateData
import StructuralGoal20261016.WindowMomentEnergyCase00
import StructuralGoal20261016.WindowMomentEnergyCase01
import StructuralGoal20261016.WindowMomentBoxCase00
import StructuralGoal20261016.WindowMomentBoxCase01
'''+opts+'''noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentAggregateActual
open WindowMomentAggregateData WindowMomentPolynomial
open WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
'''
for k in range(2):
 actual+=source[source.index(f'theorem radius{k}'):source.index(f'theorem qComplete{k}')]
 block=source[source.index(f'theorem actualBound{k}'):source.index(f'theorem exclude{k}')]
 actual+=block
actual+='set_option pp.fullNames true\n#print axioms actualBound0\n#print axioms actualBound1\n'
actual+='end StructuralGoal20261016.WindowMomentAggregateActual\nend\n'
actual_path=ROOT/'StructuralGoal20261016/WindowMomentAggregateActual.lean'
if not actual_path.exists() or actual_path.read_text(encoding='utf8')!=actual:
 write_lean(actual_path,actual)
# Reuse the separately checked actual inequalities in the final wrapper.
source=source.replace('import StructuralGoal20261016.WindowMomentAggregate0Gap\n',
 'import StructuralGoal20261016.WindowMomentAggregateActual\nimport StructuralGoal20261016.WindowMomentAggregate0Gap\n',1)
for k in range(2):
 block=source[source.index(f'theorem actualBound{k}'):source.index(f'theorem exclude{k}')]
 statement=block.split(' := by\n',1)[0]
 source=source.replace(block,statement+f' :=\n WindowMomentAggregateActual.actualBound{k} hg hcell hbelow\n\n',1)
# Each local exclusion has its own durable checkpoint and prerequisites.
for k in range(2):
 imports='import StructuralGoal20261016.WindowMomentAggregateActual\n'
 for label in ['Gap','Scalar','H','Q0','Q1','Q2','Bounds']:
  imports+=f'import StructuralGoal20261016.WindowMomentAggregate{k}{label}\n'
 for m in ['EnergyCase','BoxCase']:imports+=f'import StructuralGoal20261016.WindowMoment{m}{k:02}\n'
 start=source.index(f'theorem radius{k}')
 stop=source.index('theorem radius1') if k==0 else source.index('set_option pp.fullNames true')
 part='/- SPDX-License-Identifier: Apache-2.0 -/\n'+imports+opts+'''noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentExclusions
open WindowMomentAggregateData WindowMomentAggregateChecks WindowMomentPolynomial
open WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
'''+source[start:stop]+'set_option pp.fullNames true\n'
 for name in ['exactChecked','actualBound','exclude']:part+=f'#print axioms {name}{k}\n'
 part+='end StructuralGoal20261016.WindowMomentExclusions\nend\n'
 write_lean(ROOT/f'StructuralGoal20261016/WindowMomentExclusionCase{k:02}.lean',part)
wrapper='''/- SPDX-License-Identifier: Apache-2.0
Two actual local moment exclusions. This is not a complete global cover.
-/
import StructuralGoal20261016.WindowMomentExclusionCase00
import StructuralGoal20261016.WindowMomentExclusionCase01
set_option Elab.async false
set_option pp.fullNames true
'''
for k in range(2):
 for name in ['exactChecked','actualBound','exclude']:
  wrapper+=f'#print axioms StructuralGoal20261016.WindowMomentExclusions.{name}{k}\n'
write_lean(ROOT/'StructuralGoal20261016/WindowMomentExclusions.lean',wrapper)
print(json.dumps({'generated':'StructuralGoal20261016.WindowMomentExclusions','ordinary_Lean_verified':False,'complete_global_cover':False}))
