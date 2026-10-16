/- SPDX-License-Identifier: Apache-2.0
All 1567 actual value and slope certificates.
-/
import StructuralGoal20261016.WindowAnchorChecks00
import StructuralGoal20261016.WindowAnchorChecks01
import StructuralGoal20261016.WindowAnchorChecks02
import StructuralGoal20261016.WindowAnchorChecks03
import StructuralGoal20261016.WindowAnchorChecks04
import StructuralGoal20261016.WindowAnchorChecks05
import StructuralGoal20261016.WindowAnchorChecks06
import StructuralGoal20261016.WindowAnchorChecks07
import StructuralGoal20261016.WindowAnchorChecks08
import StructuralGoal20261016.WindowAnchorChecks09
import StructuralGoal20261016.WindowAnchorChecks10
import StructuralGoal20261016.WindowAnchorChecks11
import StructuralGoal20261016.WindowAnchorChecks12
import StructuralGoal20261016.WindowAnchorChecks13
import StructuralGoal20261016.WindowAnchorChecks14
import StructuralGoal20261016.WindowAnchorChecks15
import StructuralGoal20261016.WindowAnchorChecks16
import StructuralGoal20261016.WindowAnchorChecks17
import StructuralGoal20261016.WindowAnchorChecks18
import StructuralGoal20261016.WindowAnchorChecks19
import StructuralGoal20261016.WindowAnchorChecks20
import StructuralGoal20261016.WindowAnchorChecks21
import StructuralGoal20261016.WindowAnchorChecks22
import StructuralGoal20261016.WindowAnchorChecks23
import StructuralGoal20261016.WindowAnchorChecks24
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowAnchorAll
open WindowAnchorCertificate WindowAnchorCertificateData WindowAnchorChecks WindowScalarMinorant

theorem checks : ∀ g : Fin 25, ∀ j : Fin 64, (g:ℕ)*64+(j:ℕ) < 1567 →
 check (row ((g:ℕ)*64+(j:ℕ))) = true := by
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
 · exact checks13
 · exact checks14
 · exact checks15
 · exact checks16
 · exact checks17
 · exact checks18
 · exact checks19
 · exact checks20
 · exact checks21
 · exact checks22
 · exact checks23
 · exact checks24

theorem valid (i : ℕ) (hi : i < 1567) : Valid (row i) := by
 have hg : i/64 < 25 := by omega
 have hj : i%64 < 64 := Nat.mod_lt i (by decide)
 have he : i/64*64+i%64 = i := by omega
 have hc := checks ⟨i/64,hg⟩ ⟨i%64,hj⟩ (by change i/64*64+i%64 < 1567; omega)
 change check (row (i/64*64+i%64)) = true at hc
 rw [he] at hc
 exact WindowAnchorCertificate.sound hc

theorem value (i : ℕ) (hi : i < 1567) : ((row i).lower:ℝ) ≤ f (row i).anchor := (valid i hi).1
theorem slope (i : ℕ) (hi : i < 1567) :
 |iteratedDeriv 1 f (row i).anchor-((row i).slope:ℝ)| ≤ ((row i).error:ℝ) := (valid i hi).2

set_option pp.fullNames true
#print axioms valid
#print axioms value
#print axioms slope
end StructuralGoal20261016.WindowAnchorAll
end
