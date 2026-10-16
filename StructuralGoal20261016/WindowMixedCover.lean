/- SPDX-License-Identifier: Apache-2.0
Concrete checked mixed-cover operations for the actual redesigned energy.
Leaves and contractions are interpreted by proved finite consumers. A
complete true Boolean tree check is still required; no such tree is
asserted by these conditional transfer theorems.
-/
import StructuralGoal20261016.WindowMixedLeaves
import StructuralGoal20261016.WindowMixedContractions
import StructuralGoal20261016.WindowRootCell
import StructuralGoal20261016.WindowLowerRootCell
import StructuralGoal20261016.WindowRecordFromFloor
import StructuralGoal20261016.WindowRecordLowerFloor
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowMixedCover

structure Store where
  leaf : ℕ → WindowMixedLeaves.Leaf
  contraction : ℕ → WindowMixedContractions.Contraction

def operations (cN : ℤ) (store : Store) :
    MinimizerCover.Operations (DifferenceCell.Cell 10) (Fin 9 → ℝ) where
  contains := WindowDifferenceCell.Contains
  leafCheck := fun cell i => WindowMixedLeaves.check cN cell (store.leaf i)
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
    exact WindowMixedLeaves.sound hc hrel hg
  split := by
    intro cell axis cut g _ _ hg
    exact WindowCellCuts.split_sound hg axis cut
  contract := by
    intro cell i g hc hrel hg
    exact WindowMixedContractions.sound hc hrel hg

def target884 : ℤ := 221*(WindowValueFlow.denominator/25000)
def target880 : ℤ := 11*(WindowValueFlow.denominator/1250)

theorem floor884_eq : WindowMixedLeaves.floor target884 = (221:ℝ)/25000 := by
  norm_num [WindowMixedLeaves.floor,target884,WindowValueFlow.denominator]

theorem floor880_eq : WindowMixedLeaves.floor target880 = (11:ℝ)/1250 := by
  norm_num [WindowMixedLeaves.floor,target880,WindowValueFlow.denominator]

theorem global_floor884 (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations target884 store) WindowRootCell.root = true)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant ((123:ℝ)/128) g) :
    (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
  have h := WindowPressureRoot.global_floor_of_checked (operations target884 store)
    (sound target884 store) tree WindowRootCell.root checked
    (fun m hm => WindowRootCell.contains m (by simpa only [floor884_eq] using hm)) g hg
  simpa only [floor884_eq] using h

theorem global_floor880 (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations target880 store) WindowLowerRootCell.root = true)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant ((123:ℝ)/128) g) :
    (11:ℝ)/1250 ≤ WindowGapEnergy.Fw24 g := by
  have h := WindowPressureRoot.global_floor_of_checked (operations target880 store)
    (sound target880 store) tree WindowLowerRootCell.root checked
    (fun m hm => WindowLowerRootCell.contains m (by simpa only [floor880_eq] using hm)) g hg
  simpa only [floor880_eq] using h

theorem primary_counting (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations target884 store) WindowRootCell.root = true) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (WindowRecordFromFloor.kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T :=
  WindowRecordFromFloor.distinct_cumulative (global_floor884 store tree checked)

theorem primary_dyadic (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations target884 store) WindowRootCell.root = true) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (WindowRecordFromFloor.kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) :=
  WindowRecordDyadic.distinct_dyadic (global_floor884 store tree checked)

theorem lower_counting (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations target880 store) WindowLowerRootCell.root = true) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (WindowRecordLowerFloor.kappa-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T :=
  WindowRecordLowerFloor.distinct_cumulative (global_floor880 store tree checked)

theorem lower_dyadic (store : Store) (tree : MinimizerCover.Tree)
    (checked : tree.check (operations target880 store) WindowLowerRootCell.root = true) :
    ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (WindowRecordLowerFloor.kappa-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) :=
  WindowRecordLowerFloor.distinct_dyadic (global_floor880 store tree checked)

set_option pp.fullNames true
#print axioms sound
#print axioms global_floor884
#print axioms global_floor880
#print axioms primary_counting
#print axioms primary_dyadic
#print axioms lower_counting
#print axioms lower_dyadic
end StructuralGoal20261016.WindowMixedCover
end
