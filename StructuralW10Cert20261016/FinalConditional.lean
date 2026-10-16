/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.

Exact counting wrapper for the frozen ten-point candidate.  Every theorem
whose conclusion improves the zeta proportion explicitly takes SeparatedFloor
as a hypothesis.  This file does not assert that hypothesis, and is therefore
not a complete website submission by itself.
-/
import StructuralResearch20261016.W10RefinedCandidate
import StructuralResearch20261016.CoboundaryCounting
import GramDefect20261015.SharpWindow

noncomputable section
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
open StructuralResearch20261016.Coboundary

namespace StructuralW10Cert20261016.FinalConditional

abbrev W := StructuralResearch20261016.W10RefinedCandidate.W
def windowFloor : ℝ := 6721684105641188747759983512104999330646 / 10 ^ 40
def localFloor : ℝ := 433 / 50000
def pressure : ℝ := 10999681 / 2500000000
def candidateRatio : ℝ :=
  3338842690820594373879991756052499665323 /
    4956700000000000000000000000000000000000
def currentSiteRatio : ℝ :=
  34191001116882886388531117129201664 / 50760020691785094633026544189453125

/-- This analytic finite-dimensional inequality is the remaining local premise. -/
def SeparatedFloor : Prop :=
  ∀ g : Fin 9 → ℝ, (∀ i, (17 / 20 : ℝ) ≤ g i) → localFloor ≤ Fw W g

/-- The wider domain used in the original numerical exploration is sufficient,
but the final proof needs only the actual matching separation. -/
theorem separated_of_wider
    (h : ∀ g : Fin 9 → ℝ, (∀ i, (4 / 5 : ℝ) ≤ g i) → localFloor ≤ Fw W g) :
    SeparatedFloor := by
  intro g hg
  exact h g (fun i => le_trans (by norm_num) (hg i))

theorem exact_formula : (windowFloor - pressure) / (1 - localFloor) = candidateRatio := by
  norm_num [windowFloor, pressure, localFloor, candidateRatio]

theorem strict_improvement : currentSiteRatio < candidateRatio := by
  norm_num [currentSiteRatio, candidateRatio]

/-- The actual matching remainder has gaps at least 17/20.
The potential is identically zero. -/
theorem separated_summed (hCert : SeparatedFloor) :
    SeparatedSummedCertificate W localFloor 0 (17 / 20) := by
  have h : SeparatedSummedCertificate W localFloor ((0 : ℝ) - 0) (17 / 20) :=
    summed_of_separated_coboundary (by norm_num : 2 ≤ 10) W
    (fun _ => (0 : ℝ)) localFloor 0 0 (17 / 20)
    (by intro g hg; exact ⟨le_rfl, le_rfl⟩)
    (by
      intro g hg
      simpa only [add_zero, sub_zero] using hCert g hg)
  intro m hm y hy hsep
  simpa only [sub_self] using h (m := m) hm y hy hsep

theorem simple_dyadic (hCert : SeparatedFloor) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateRatio - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  have h := StructuralResearch20261016.CoboundaryCounting.simple_dyadic
    (hw := windowFloor) (c := localFloor) (C := 0) (B := pressure)
    (by norm_num : 2 ≤ 10) W StructuralResearch20261016.W10RefinedCandidate.adm
    (by norm_num [localFloor]) (by norm_num) (by norm_num [localFloor])
    (by norm_num [localFloor])
    (by simpa only [pressure] using StructuralResearch20261016.W10RefinedCandidate.pressure_eq)
    (by simpa only [windowFloor] using GramDefect20261015.Window.HW_ge)
    (separated_summed hCert)
  simpa only [exact_formula] using h

theorem simple_cumulative (hCert : SeparatedFloor) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam) (simple_dyadic hCert)

theorem distinct_dyadic (hCert : SeparatedFloor) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateRatio - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := simple_dyadic hCert ε hε
  exact ⟨T₀, fun T hT => (hT₀ T hT).trans (by
    exact_mod_cast AMW.N0simple_le_N0star' T (2 * T))⟩

theorem distinct_cumulative (hCert : SeparatedFloor) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (distinct_dyadic hCert)

#print axioms exact_formula
#print axioms strict_improvement
#print axioms separated_summed
#print axioms simple_dyadic
#print axioms simple_cumulative
#print axioms distinct_dyadic
#print axioms distinct_cumulative

end StructuralW10Cert20261016.FinalConditional
end
