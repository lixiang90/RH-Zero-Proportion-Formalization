/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentPointChecks00
import StructuralGoal20261016.WindowMomentPointChecks01
import StructuralGoal20261016.WindowMomentPointChecks02
import StructuralGoal20261016.WindowMomentPointChecks03
import StructuralGoal20261016.WindowMomentPointChecks04
import StructuralGoal20261016.WindowMomentPointChecks05
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowMomentPointAll
open WindowAnchorCertificate WindowMomentPointData WindowMomentPointChecks
theorem checks : ∀ g : Fin 6, ∀ j : Fin 16, (g:ℕ)*16+(j:ℕ) < 82 →
 check (row ((g:ℕ)*16+(j:ℕ))) = true := by
 intro g
 fin_cases g
 · exact checks00
 · exact checks01
 · exact checks02
 · exact checks03
 · exact checks04
 · exact checks05

theorem valid (i : ℕ) (hi : i < 82) : Valid (row i) := by
 have hg : i/16 < 6 := by omega
 have hj : i%16 < 16 := Nat.mod_lt i (by decide)
 have he : i/16*16+i%16 = i := by omega
 have hc := checks ⟨i/16,hg⟩ ⟨i%16,hj⟩ (by change i/16*16+i%16 < 82; omega)
 change check (row (i/16*16+i%16)) = true at hc
 rw [he] at hc
 exact WindowAnchorCertificate.sound hc
set_option pp.fullNames true
#print axioms valid
end StructuralGoal20261016.WindowMomentPointAll
