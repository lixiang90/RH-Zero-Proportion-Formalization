/- SPDX-License-Identifier: Apache-2.0
Mixed minimizer covers with actual lifted derivative-graph leaves.
The finite cover check at the complete pressure root is the remaining
hypothesis; the graph leaves require no external analytic inequality.
-/
import StructuralGoal20261016.WindowMixedCover
import StructuralGoal20261016.WindowLiftedKKT
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowGraphCover

structure Certificate where
  size : ℕ
  atom : Fin size → WindowLiftedKKT.Atom
  multiplier : Fin size → ℤ
  minimum : ℤ
  edges : List FlowBasisCodec.Edge

inductive Leaf where
  | ordinary (leaf : WindowMixedLeaves.Leaf)
  | graph (cert : Certificate)

def leafCheck (cN : ℤ) (cell : DifferenceCell.Cell 10) : Leaf → Bool
  | .ordinary leaf => WindowMixedLeaves.check cN cell leaf
  | .graph cert => WindowLiftedKKT.check ((123:ℚ)/128) cell
      cert.atom cert.multiplier cert.minimum cert.edges

theorem leaf_sound {cN : ℤ} {cell : DifferenceCell.Cell 10} {leaf : Leaf}
    (hc : leafCheck cN cell leaf = true) {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.RelevantBelow ((123:ℝ)/128) (WindowMixedLeaves.floor cN) g)
    (hcell : WindowDifferenceCell.Contains cell g) : WindowMixedLeaves.floor cN ≤ WindowGapEnergy.Fw24 g := by
  cases leaf with
  | ordinary leaf => exact WindowMixedLeaves.sound hc hg hcell
  | graph cert =>
    have hrel : WindowMinimizerCover.Relevant (((123:ℚ)/128:ℚ):ℝ) g := by
      norm_num only [Rat.cast_div,Rat.cast_ofNat]
      exact hg.1
    exact False.elim (WindowLiftedKKT.exclude cert.atom cert.multiplier cert.minimum cert.edges hc hrel hcell)

structure Store where
  leaf : ℕ → Leaf
  contraction : ℕ → WindowMixedContractions.Contraction

def operations (cN : ℤ) (store : Store) :
    MinimizerCover.Operations (DifferenceCell.Cell 10) (Fin 9 → ℝ) where
  contains := WindowDifferenceCell.Contains
  leafCheck := fun cell i => leafCheck cN cell (store.leaf i)
  branchCheck := fun _ axis _ => WindowCellCuts.branchCheck axis
  left := WindowCellCuts.left
  right := WindowCellCuts.right
  contractionCheck := fun cell i => WindowMixedContractions.check cN cell (store.contraction i)
  contract := fun cell i => WindowMixedContractions.contract cell (store.contraction i)

theorem sound (cN : ℤ) (store : Store) :
    MinimizerCover.Sound (operations cN store)
      (WindowMinimizerCover.RelevantBelow ((123:ℝ)/128) (WindowMixedLeaves.floor cN))
      WindowGapEnergy.Fw24 (WindowMixedLeaves.floor cN) where
  leaf := by
    intro cell i g hc hrel hg
    exact leaf_sound hc hrel hg
  split := by
    intro cell axis cut g _ _ hg
    exact WindowCellCuts.split_sound hg axis cut
  contract := by
    intro cell i g hc hrel hg
    exact WindowMixedContractions.sound hc hrel hg

theorem global_floor884 (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations WindowMixedCover.target884 store) WindowRootCell.root = true)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant ((123:ℝ)/128) g) :
    (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
  have h := WindowPressureRoot.global_floor_of_checked (operations WindowMixedCover.target884 store)
    (sound WindowMixedCover.target884 store) tree WindowRootCell.root checked
    (fun m hm => WindowRootCell.contains m (by simpa only [WindowMixedCover.floor884_eq] using hm)) g hg
  simpa only [WindowMixedCover.floor884_eq] using h

theorem global_floor880 (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations WindowMixedCover.target880 store) WindowLowerRootCell.root = true)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant ((123:ℝ)/128) g) :
    (11:ℝ)/1250 ≤ WindowGapEnergy.Fw24 g := by
  have h := WindowPressureRoot.global_floor_of_checked (operations WindowMixedCover.target880 store)
    (sound WindowMixedCover.target880 store) tree WindowLowerRootCell.root checked
    (fun m hm => WindowLowerRootCell.contains m (by simpa only [WindowMixedCover.floor880_eq] using hm)) g hg
  simpa only [WindowMixedCover.floor880_eq] using h

theorem lower_counting (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations WindowMixedCover.target880 store) WindowLowerRootCell.root = true) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (WindowRecordLowerFloor.kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T :=
  WindowRecordLowerFloor.distinct_cumulative (global_floor880 store tree checked)

theorem lower_dyadic (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations WindowMixedCover.target880 store) WindowLowerRootCell.root = true) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (WindowRecordLowerFloor.kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) :=
  WindowRecordLowerFloor.distinct_dyadic (global_floor880 store tree checked)

set_option pp.fullNames true
#print axioms leaf_sound
#print axioms sound
#print axioms global_floor884
#print axioms global_floor880
#print axioms lower_counting
#print axioms lower_dyadic
end StructuralGoal20261016.WindowGraphCover
end
