/- SPDX-License-Identifier: Apache-2.0
All selected actual q2/q4 derivative cells, with finite-query consumers.
-/
import StructuralGoal20261016.WindowCurvatureGridChecks00
import StructuralGoal20261016.WindowCurvatureGridChecks01
import StructuralGoal20261016.WindowCurvatureGridChecks02
import StructuralGoal20261016.WindowCurvatureGridChecks03
import StructuralGoal20261016.WindowCurvatureGridChecks04
import StructuralGoal20261016.WindowCurvatureGridChecks05
import StructuralGoal20261016.WindowCurvatureGridChecks06
import StructuralGoal20261016.WindowCurvatureGridChecks07
import StructuralGoal20261016.WindowCurvatureGridChecks08
import StructuralGoal20261016.WindowCurvatureGridChecks09
import StructuralGoal20261016.WindowCurvatureGridChecks10
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCurvatureGridAll
open WindowCurvatureGrid WindowCurvatureGridData WindowCurvatureGridChecks
theorem checks : ∀ g : Fin 11, ∀ j : Fin 32, (g:ℕ)*32+(j:ℕ) < 331 →
 check (row ((g:ℕ)*32+(j:ℕ))) = true := by
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

theorem valid (i : ℕ) (hi : i < 331) : Valid (row i) := by
 have hg : i/32 < 11 := by omega
 have hj : i%32 < 32 := Nat.mod_lt i (by decide)
 have he : i/32*32+i%32 = i := by omega
 have hc := checks ⟨i/32,hg⟩ ⟨i%32,hj⟩
   (by change i/32*32+i%32 < 331; omega)
 change check (row (i/32*32+i%32)) = true at hc
 rw [he] at hc
 exact WindowCurvatureGrid.sound hc

theorem second {k0 k1 : ℕ} {a b L U : ℚ}
 (hc : secondCheck row index 331 k0 k1 a b L U = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ iteratedDeriv 2 WindowScalarMinorant.f x ∧
 iteratedDeriv 2 WindowScalarMinorant.f x ≤ (U:ℝ) :=
 WindowCurvatureGrid.second valid hc hx

theorem fourth {k0 k1 : ℕ} {a b M : ℚ}
 (hc : fourthCheck row index 331 k0 k1 a b M = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 |iteratedDeriv 4 WindowScalarMinorant.f x| ≤ (M:ℝ) :=
 WindowCurvatureGrid.fourth valid hc hx

set_option pp.fullNames true
#print axioms valid
#print axioms second
#print axioms fourth
end StructuralGoal20261016.WindowCurvatureGridAll
end
