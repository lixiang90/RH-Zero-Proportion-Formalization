/- SPDX-License-Identifier: Apache-2.0
Actual inequalities for the complete exact rational moment aggregate.
Integer coefficient matching and strict separation are separate obligations.
-/
import StructuralGoal20261016.WindowMomentAggregateData
import StructuralGoal20261016.WindowMomentEnergyCase00
import StructuralGoal20261016.WindowMomentEnergyCase01
import StructuralGoal20261016.WindowMomentBoxCase00
import StructuralGoal20261016.WindowMomentBoxCase01
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentAggregateActual
open WindowMomentAggregateData WindowMomentPolynomial
open WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
theorem radius0 : ∀ r : Fin 9, 0 < box0.radius r := by decide +kernel

theorem actualBound0 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell0 g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) :
 eval aggregate0 (realVector box0.center) (realVector box0.radius) g ≤
 (aggregate0.bound:ℝ) := by
 have hr : ∀ r, (0:ℝ) < (box0.radius r:ℝ) := fun r => Rat.cast_pos.mpr (radius0 r)
 have hn : ∀ r, box0.radius r ≠ 0 := fun r => ne_of_gt (radius0 r)
 have hcoord : ∀ r, (box0.center r:ℝ)-(box0.radius r:ℝ) ≤ g r ∧
     g r ≤ (box0.center r:ℝ)+(box0.radius r:ℝ) := by
   intro r
   have h := WindowMomentBoxCase00.bounds hcell (WindowMomentLayout.gapIndex r)
   simpa [WindowMomentBox.lower,WindowMomentBox.upper,WindowMomentBox.actual,
     WindowMomentLayout.actual,WindowMomentLayout.gapIndex] using h
 have hden : (0:ℝ) < (WindowDirectionalFlow.denominator:ℝ) := by
   norm_num [WindowDirectionalFlow.denominator,WindowDirectionalFlow.SC,
     WindowDirectionalFlow.DS,WindowDirectionalFlow.D]
 have hgroups : ∀ i : Fin 103, eval (groups0 i)
     (realVector box0.center) (realVector box0.radius) g ≤ ((groups0 i).bound:ℝ) := by
   intro i
   have hf : (∑ r : Fin 9, |(factorB0 i r:ℝ)|) ≤ (factorA0 i:ℝ) := by
     exact_mod_cast (WindowMomentAtomsAll.factor0 i).2
   have hA : (∑ r : Fin 9, |((((factorB0 i r:ℚ)/(WindowDirectionalFlow.denominator:ℚ)):ℚ):ℝ)|) ≤
       ((((factorA0 i:ℚ)/(WindowDirectionalFlow.denominator:ℚ)):ℚ):ℝ) := by
     push_cast
     simp_rw [abs_div,abs_of_pos hden]
     rw [← Finset.sum_div]
     exact div_le_div_of_nonneg_right hf hden.le
   exact grouped_nonpos (WindowLiftedKKT.form cell0 (atoms0 i))
     box0.center box0.radius _ _ g hA hr hcoord (WindowMomentAtomsAll.valid0 hg hcell i)
 have henergy : eval energy0 (realVector box0.center) (realVector box0.radius) g ≤
     (energy0.bound:ℝ) := by
   have he := WindowMomentEnergyPolynomial.energyForm_sublevel
     WindowMomentEnergyCase00.checked box0.center box0.radius (11/1250) hn hcell hbelow
   exact WindowMomentFormSum.scale_valid (3969825841:ℚ) _ _ _ _ (by norm_num) he.le
 rw [aggregate0,WindowMomentFormSum.eval_add,WindowMomentFormSum.eval_sum]
 change (∑ i, eval (groups0 i) (realVector box0.center) (realVector box0.radius) g)+
   eval energy0 (realVector box0.center) (realVector box0.radius) g ≤
   (((∑ i, (groups0 i).bound)+energy0.bound:ℚ):ℝ)
 push_cast
 exact add_le_add (Finset.sum_le_sum (fun i _ => hgroups i)) henergy

theorem radius1 : ∀ r : Fin 9, 0 < box1.radius r := by decide +kernel

theorem actualBound1 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hcell : WindowDifferenceCell.Contains cell1 g)
 (hbelow : WindowGapEnergy.Fw24 g < ((11/1250:ℚ):ℝ)) :
 eval aggregate1 (realVector box1.center) (realVector box1.radius) g ≤
 (aggregate1.bound:ℝ) := by
 have hr : ∀ r, (0:ℝ) < (box1.radius r:ℝ) := fun r => Rat.cast_pos.mpr (radius1 r)
 have hn : ∀ r, box1.radius r ≠ 0 := fun r => ne_of_gt (radius1 r)
 have hcoord : ∀ r, (box1.center r:ℝ)-(box1.radius r:ℝ) ≤ g r ∧
     g r ≤ (box1.center r:ℝ)+(box1.radius r:ℝ) := by
   intro r
   have h := WindowMomentBoxCase01.bounds hcell (WindowMomentLayout.gapIndex r)
   simpa [WindowMomentBox.lower,WindowMomentBox.upper,WindowMomentBox.actual,
     WindowMomentLayout.actual,WindowMomentLayout.gapIndex] using h
 have hden : (0:ℝ) < (WindowDirectionalFlow.denominator:ℝ) := by
   norm_num [WindowDirectionalFlow.denominator,WindowDirectionalFlow.SC,
     WindowDirectionalFlow.DS,WindowDirectionalFlow.D]
 have hgroups : ∀ i : Fin 106, eval (groups1 i)
     (realVector box1.center) (realVector box1.radius) g ≤ ((groups1 i).bound:ℝ) := by
   intro i
   have hf : (∑ r : Fin 9, |(factorB1 i r:ℝ)|) ≤ (factorA1 i:ℝ) := by
     exact_mod_cast (WindowMomentAtomsAll.factor1 i).2
   have hA : (∑ r : Fin 9, |((((factorB1 i r:ℚ)/(WindowDirectionalFlow.denominator:ℚ)):ℚ):ℝ)|) ≤
       ((((factorA1 i:ℚ)/(WindowDirectionalFlow.denominator:ℚ)):ℚ):ℝ) := by
     push_cast
     simp_rw [abs_div,abs_of_pos hden]
     rw [← Finset.sum_div]
     exact div_le_div_of_nonneg_right hf hden.le
   exact grouped_nonpos (WindowLiftedKKT.form cell1 (atoms1 i))
     box1.center box1.radius _ _ g hA hr hcoord (WindowMomentAtomsAll.valid1 hg hcell i)
 have henergy : eval energy1 (realVector box1.center) (realVector box1.radius) g ≤
     (energy1.bound:ℝ) := by
   have he := WindowMomentEnergyPolynomial.energyForm_sublevel
     WindowMomentEnergyCase01.checked box1.center box1.radius (11/1250) hn hcell hbelow
   exact WindowMomentFormSum.scale_valid (560310308:ℚ) _ _ _ _ (by norm_num) he.le
 rw [aggregate1,WindowMomentFormSum.eval_add,WindowMomentFormSum.eval_sum]
 change (∑ i, eval (groups1 i) (realVector box1.center) (realVector box1.radius) g)+
   eval energy1 (realVector box1.center) (realVector box1.radius) g ≤
   (((∑ i, (groups1 i).bound)+energy1.bound:ℚ):ℝ)
 push_cast
 exact add_le_add (Finset.sum_le_sum (fun i _ => hgroups i)) henergy

set_option pp.fullNames true
#print axioms actualBound0
#print axioms actualBound1
end StructuralGoal20261016.WindowMomentAggregateActual
end
