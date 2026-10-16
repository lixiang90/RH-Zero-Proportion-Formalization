/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentSecondChecks00
import StructuralGoal20261016.WindowMomentSecondChecks01
import StructuralGoal20261016.WindowMomentSecondChecks02
import StructuralGoal20261016.WindowMomentSecondChecks03
import StructuralGoal20261016.WindowMomentSecondChecks04
import StructuralGoal20261016.WindowMomentSecondChecks05
import StructuralGoal20261016.WindowMomentSecondChecks06
import StructuralGoal20261016.WindowMomentSecondChecks07
import StructuralGoal20261016.WindowMomentSecondChecks08
import StructuralGoal20261016.WindowMomentSecondChecks09
import StructuralGoal20261016.WindowMomentSecondChecks10
import StructuralGoal20261016.WindowMomentSecondChecks11
import StructuralGoal20261016.WindowMomentSecondChecks12
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowMomentSecondAll
open WindowCurvatureGrid WindowMomentSecondData WindowMomentSecondChecks
theorem checks : ∀ g : Fin 13, ∀ j : Fin 32, (g:ℕ)*32+(j:ℕ) < 403 →
 check (newRow ((g:ℕ)*32+(j:ℕ))) = true := by
 intro g
 fin_cases g
 · exact checks00
 · exact checks01
 · exact checks02
 · exact checks03
 · exact checks04
 · exact checks05
 · exact checks06
 · exact checks07
 · exact checks08
 · exact checks09
 · exact checks10
 · exact checks11
 · exact checks12

theorem newValid (i : ℕ) (hi : i < 403) : Valid (newRow i) := by
 have hg : i/32 < 13 := by omega
 have hj : i%32 < 32 := Nat.mod_lt i (by decide)
 have he : i/32*32+i%32 = i := by omega
 have hc := checks ⟨i/32,hg⟩ ⟨i%32,hj⟩ (by change i/32*32+i%32 < 403; omega)
 change check (newRow (i/32*32+i%32)) = true at hc
 rw [he] at hc
 exact WindowCurvatureGrid.sound hc
theorem valid (i : ℕ) (hi : i < 734) : Valid (row i) := by
 by_cases hold : i < 331
 · simpa only [row,if_pos hold] using WindowCurvatureGridAll.valid i hold
 · simpa only [row,if_neg hold] using newValid (i-331) (by omega)
theorem second {k0 k1 : ℕ} {a b L U : ℚ}
 (hc : secondCheck row index 734 k0 k1 a b L U = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ iteratedDeriv 2 WindowScalarMinorant.f x ∧
   iteratedDeriv 2 WindowScalarMinorant.f x ≤ (U:ℝ) :=
 WindowCurvatureGrid.second valid hc hx
set_option pp.fullNames true
#print axioms newValid
#print axioms valid
#print axioms second
end StructuralGoal20261016.WindowMomentSecondAll
end
