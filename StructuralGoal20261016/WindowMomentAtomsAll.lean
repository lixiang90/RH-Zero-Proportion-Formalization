/- SPDX-License-Identifier: Apache-2.0 -/
import StructuralGoal20261016.WindowMomentAtoms0Checks00
import StructuralGoal20261016.WindowMomentAtoms0Checks01
import StructuralGoal20261016.WindowMomentAtoms0Checks02
import StructuralGoal20261016.WindowMomentAtoms0Checks03
import StructuralGoal20261016.WindowMomentAtoms0Checks04
import StructuralGoal20261016.WindowMomentAtoms0Checks05
import StructuralGoal20261016.WindowMomentAtoms0Checks06
import StructuralGoal20261016.WindowMomentAtoms1Checks00
import StructuralGoal20261016.WindowMomentAtoms1Checks01
import StructuralGoal20261016.WindowMomentAtoms1Checks02
import StructuralGoal20261016.WindowMomentAtoms1Checks03
import StructuralGoal20261016.WindowMomentAtoms1Checks04
import StructuralGoal20261016.WindowMomentAtoms1Checks05
import StructuralGoal20261016.WindowMomentAtoms1Checks06
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators
noncomputable section
namespace StructuralGoal20261016.WindowMomentAtomsAll
open WindowMomentAtomData WindowMomentEnergyData WindowMomentAtomChecks
theorem checks0 : ∀ g : Fin 7, ∀ j : Fin 16, (g:ℕ)*16+(j:ℕ) < 103 →
 WindowLiftedKKT.checkAtom (123/128) cell0 (atom0 ((g:ℕ)*16+(j:ℕ))) = true := by
 intro g
 fin_cases g
 · exact checks0_00
 · exact checks0_01
 · exact checks0_02
 · exact checks0_03
 · exact checks0_04
 · exact checks0_05
 · exact checks0_06

theorem checked0 (i : Fin 103) :
 WindowLiftedKKT.checkAtom (123/128) cell0 (atoms0 i) = true := by
 have hi := i.isLt
 have h := checks0 ⟨(i:ℕ)/16,by omega⟩ ⟨(i:ℕ)%16,Nat.mod_lt _ (by decide)⟩
   (by change (i:ℕ)/16*16+(i:ℕ)%16 < 103; omega)
 have he : (i:ℕ)/16*16+(i:ℕ)%16 = (i:ℕ) := by omega
 change WindowLiftedKKT.checkAtom (123/128) cell0 (atom0 ((i:ℕ)/16*16+(i:ℕ)%16)) = true at h
 rw [he] at h
 simpa only [atom0,Nat.mod_eq_of_lt hi] using h

theorem factor0 : ∀ i : Fin 103, 0 ≤ factorA0 i ∧
 (∑ r : Fin 9, |factorB0 i r|) ≤ factorA0 i := by decide +kernel

theorem valid0 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hc : WindowDifferenceCell.Contains cell0 g) (i : Fin 103) :
 WindowLiftedFarkas.eval (WindowLiftedKKT.form cell0 (atoms0 i)) g ≤
   ((WindowLiftedKKT.form cell0 (atoms0 i)).bound:ℝ) :=
 WindowLiftedKKT.atom_sound (atoms0 i) (checked0 i) hg hc
theorem checks1 : ∀ g : Fin 7, ∀ j : Fin 16, (g:ℕ)*16+(j:ℕ) < 106 →
 WindowLiftedKKT.checkAtom (123/128) cell1 (atom1 ((g:ℕ)*16+(j:ℕ))) = true := by
 intro g
 fin_cases g
 · exact checks1_00
 · exact checks1_01
 · exact checks1_02
 · exact checks1_03
 · exact checks1_04
 · exact checks1_05
 · exact checks1_06

theorem checked1 (i : Fin 106) :
 WindowLiftedKKT.checkAtom (123/128) cell1 (atoms1 i) = true := by
 have hi := i.isLt
 have h := checks1 ⟨(i:ℕ)/16,by omega⟩ ⟨(i:ℕ)%16,Nat.mod_lt _ (by decide)⟩
   (by change (i:ℕ)/16*16+(i:ℕ)%16 < 106; omega)
 have he : (i:ℕ)/16*16+(i:ℕ)%16 = (i:ℕ) := by omega
 change WindowLiftedKKT.checkAtom (123/128) cell1 (atom1 ((i:ℕ)/16*16+(i:ℕ)%16)) = true at h
 rw [he] at h
 simpa only [atom1,Nat.mod_eq_of_lt hi] using h

theorem factor1 : ∀ i : Fin 106, 0 ≤ factorA1 i ∧
 (∑ r : Fin 9, |factorB1 i r|) ≤ factorA1 i := by decide +kernel

theorem valid1 {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant ((123/128:ℚ):ℝ) g)
 (hc : WindowDifferenceCell.Contains cell1 g) (i : Fin 106) :
 WindowLiftedFarkas.eval (WindowLiftedKKT.form cell1 (atoms1 i)) g ≤
   ((WindowLiftedKKT.form cell1 (atoms1 i)).bound:ℝ) :=
 WindowLiftedKKT.atom_sound (atoms1 i) (checked1 i) hg hc
set_option pp.fullNames true
#print axioms checked0
#print axioms factor0
#print axioms valid0
#print axioms checked1
#print axioms factor1
#print axioms valid1
end StructuralGoal20261016.WindowMomentAtomsAll
end
