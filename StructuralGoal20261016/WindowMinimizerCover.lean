/- SPDX-License-Identifier: Apache-2.0
The actual 24-mode energy instance of the relevant-minimizer cover.
The only numerical obligation is a checked cover for its pressure root;
minimum existence, orientation and the pressure root are proved here.
-/
import StructuralGoal20261016.WindowGapEnergy
import StructuralGoal20261016.MinimizerCover
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section

namespace StructuralGoal20261016.WindowMinimizerCover
open WindowGapEnergy

def Relevant (sep : ℝ) (g : Fin 9 → ℝ) : Prop :=
  CoverCoerciveKKT.Orthant sep g ∧ g 0 ≤ g 8 ∧
    ∀ y, CoverCoerciveKKT.Orthant sep y → Fw24 g ≤ Fw24 y

def PressureBox (sep c : ℝ) (g : Fin 9 → ℝ) : Prop :=
  ∀ r, sep ≤ g r ∧ g r < sep +
    (c - sep * StructuralW10Followup20261016.NewLedger.W.B) /
      StructuralW10Followup20261016.NewLedger.W.b r

theorem exists_relevant (sep : ℝ) : ∃ g, Relevant sep g :=
  exists_ordered_global_min sep

theorem pressureBox_of_sublevel {sep c : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (hc : Fw24 g < c) : PressureBox sep c g := by
  intro r
  exact ⟨hg.1 r, coordinate_upper_of_lt g hg.1 hc r⟩

theorem directional_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (v : Fin 9 → ℝ)
    (hv : ∀ r, g r = sep → 0 ≤ v r) :
    0 ≤ directional StructuralW10Followup20261016.NewLedger.W g v :=
  WindowGapEnergy.directional_nonneg_at_min (n := 10)
    StructuralW10Followup20261016.NewLedger.W g v hg.1 hg.2.2 hv

/-- A Boolean cover of this pressure root proves a floor for every separated
gap vector. Its contractions need preserve only the actual ordered global
minimizers, with no assumption that all points survive a contraction. -/
theorem global_floor_of_checked {Cell : Type}
    (ops : MinimizerCover.Operations Cell (Fin 9 → ℝ))
    {sep c : ℝ}
    (sound : MinimizerCover.Sound ops (Relevant sep) Fw24 c)
    (tree : MinimizerCover.Tree) (root : Cell)
    (checked : tree.check ops root = true)
    (root_box : ∀ g, PressureBox sep c g → ops.contains root g)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant sep g) : c ≤ Fw24 g := by
  apply MinimizerCover.global_floor sound tree root checked
    (domain := {y | CoverCoerciveKKT.Orthant sep y})
  · obtain ⟨m, hm⟩ := exists_relevant sep
    exact ⟨m, hm, hm.2.2⟩
  · intro m hm hmc
    exact root_box m (pressureBox_of_sublevel hm hmc)
  · exact hg

/-- Relevance for contractions that are valid only below the proposed floor.
In particular a pressure payment may discard points at or above the floor. -/
def RelevantBelow (sep c : ℝ) (g : Fin 9 → ℝ) : Prop :=
  Relevant sep g ∧ Fw24 g < c

theorem global_floor_of_checked_below {Cell : Type}
    (ops : MinimizerCover.Operations Cell (Fin 9 → ℝ))
    {sep c : ℝ}
    (sound : MinimizerCover.Sound ops (RelevantBelow sep c) Fw24 c)
    (tree : MinimizerCover.Tree) (root : Cell)
    (checked : tree.check ops root = true)
    (root_box : ∀ g, PressureBox sep c g → ops.contains root g)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant sep g) : c ≤ Fw24 g := by
  by_contra h
  have hgc : Fw24 g < c := lt_of_not_ge h
  obtain ⟨m, hm, ho, hmin, hmc⟩ :=
    exists_ordered_min_below (sep := sep) (c := c) ⟨g, hg, hgc⟩
  have hrel : Relevant sep m := ⟨hm, ho, hmin⟩
  have hbelow : RelevantBelow sep c m := ⟨hrel, hmc⟩
  have hroot := root_box m (pressureBox_of_sublevel hrel hmc)
  have hfloor := tree.check_sound sound root checked m hbelow hroot
  exact (not_lt_of_ge hfloor) hmc

#print axioms exists_relevant
#print axioms pressureBox_of_sublevel
#print axioms directional_nonneg
#print axioms global_floor_of_checked
#print axioms global_floor_of_checked_below
end StructuralGoal20261016.WindowMinimizerCover
end
