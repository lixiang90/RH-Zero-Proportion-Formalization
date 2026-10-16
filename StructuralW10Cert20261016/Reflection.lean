/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Reflection symmetry of the frozen rational ten-point certificate.
-/
import StructuralResearch20261016.W10RefinedCandidate

noncomputable section
open Finset Zeta23Ext.Bridge Zeta23Ext.BridgeW
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace StructuralW10Cert20261016.Reflection

abbrev W := StructuralResearch20261016.W10RefinedCandidate.W
def reverse (g : Fin 9 → ℝ) : Fin 9 → ℝ := fun i => g i.rev

theorem reverse_reverse (g : Fin 9 → ℝ) : reverse (reverse g) = g := by
  ext i
  simp [reverse]

theorem point_reverse (g : Fin 9 → ℝ) (i : Fin 10) :
    ptsN 10 (reverse g) i = ptsN 10 g 9 - ptsN 10 g i.rev := by
  fin_cases i <;> norm_num [ptsN, reverse, Fin.sum_univ_succ, Fin.rev, Fin.succ] <;> ring_nf

theorem point_difference_reverse (g : Fin 9 → ℝ) (i j : Fin 10) :
    ptsN 10 (reverse g) j - ptsN 10 (reverse g) i =
      ptsN 10 g i.rev - ptsN 10 g j.rev := by
  rw [point_reverse, point_reverse]
  ring

theorem Fw_reverse (g : Fin 9 → ℝ) : Fw W (reverse g) = Fw W g := by
  simp [Fw, W, StructuralResearch20261016.W10RefinedCandidate.W,
    StructuralResearch20261016.W10RefinedCandidate.a,
    StructuralResearch20261016.W10RefinedCandidate.aN,
    StructuralResearch20261016.W10RefinedCandidate.b,
    StructuralResearch20261016.W10RefinedCandidate.bN,
    ptsN, reverse, Fin.sum_univ_succ, Fin.rev, Fin.succ]
  ring_nf

theorem reverse_lower (g : Fin 9 → ℝ) (s : ℝ) (h : ∀ i, s ≤ g i) :
    ∀ i, s ≤ reverse g i := fun i => h i.rev

#print axioms point_reverse
#print axioms Fw_reverse
end StructuralW10Cert20261016.Reflection
end
