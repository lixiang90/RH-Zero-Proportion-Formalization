/- SPDX-License-Identifier: Apache-2.0
Transfer a complete finite cell cover to the separated W10 objective.
The cover is an explicit hypothesis here; Final supplies its finite proof. -/
import StructuralW10Cert20261016.RootBounds
import StructuralW10Cert20261016.Reflection
import StructuralW10Cert20261016.FinalConditional

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.RootBounds
open StructuralResearch20261016.W10RefinedCandidate
open Zeta23Ext.BridgeW

namespace StructuralW10Cert20261016.FloorTransfer

theorem reflection_leaf {c : Cl}
    (h : c.U.getD 8 0 < c.L.getD 0 0) :
    CovBy 9 PR (Pg cN 9 BS TS) c := by
  intro g hg
  right
  have h0 := (hg.1 0 (by decide)).1
  have h8 := (hg.1 8 (by decide)).2
  have hh : (c.U.getD 8 0 : ℝ) / SC < (c.L.getD 0 0 : ℝ) / SC := by
    exact (div_lt_div_iff_of_pos_right SC_pos).mpr (by exact_mod_cast h)
  exact lt_of_le_of_lt h8 (lt_of_lt_of_le hh h0)

def extend (g : Fin 9 → ℝ) : ℕ → ℝ := fun r => if h : r < 9 then g ⟨r,h⟩ else 0

theorem extend_fin (g : Fin 9 → ℝ) : (fun r : Fin 9 => extend g r) = g := by
  ext r
  simp [extend]

theorem ordered_floor
    (hcov : CovBy 9 PR (Pg cN 9 BS TS) initialCell)
    (g : Fin 9 → ℝ) (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (horder : g 0 ≤ g 8) : (433 : ℝ) / 50000 ≤ Fw W g := by
  by_contra h
  have hcounter : Fw W g < (433 : ℝ) / 50000 := lt_of_not_ge h
  have hn : ∀ r < 9, (17 / 20 : ℝ) ≤ extend g r := by
    intro r hr
    simpa only [extend, dif_pos hr] using hg ⟨r,hr⟩
  have hc : Fw W (fun r : Fin 9 => extend g r) < (433 : ℝ) / 50000 := by
    simpa only [extend_fin] using hcounter
  rcases hcov (extend g) (counterexample_in_root hn hc) with hf | hr
  · rw [fg_eq_scaled_Fw, extend_fin] at hf
    norm_num only [cN, Nat.cast_ofNat] at hf
    nlinarith only [hf, hcounter]
  · have ho : extend g 0 ≤ extend g 8 := by simpa [extend] using horder
    exact (not_lt_of_ge ho) hr

theorem separated_floor
    (hcov : CovBy 9 PR (Pg cN 9 BS TS) initialCell) :
    FinalConditional.SeparatedFloor := by
  intro g hg
  change (433 : ℝ) / 50000 ≤ Fw W g
  by_cases ho : g 0 ≤ g 8
  · exact ordered_floor hcov g hg ho
  · have hr : Reflection.reverse g 0 ≤ Reflection.reverse g 8 := by
      simpa [Reflection.reverse, Fin.rev] using (le_of_lt (lt_of_not_ge ho))
    have hf := ordered_floor hcov (Reflection.reverse g)
      (Reflection.reverse_lower g (17 / 20) hg) hr
    simpa only [Reflection.Fw_reverse] using hf

#print axioms separated_floor
end StructuralW10Cert20261016.FloorTransfer
end
