/- SPDX-License-Identifier: Apache-2.0
Actual OBBT and Newton contraction batches. Every bound in a batch is
checked at the same original parent cell. Bounds are then intersected
and closed without assuming that arbitrary parent points survive.
-/
import StructuralGoal20261016.WindowFirstOrderCertificate
import StructuralGoal20261016.WindowCellCuts
import StructuralGoal20261016.WindowNewtonFlow
import StructuralGoal20261016.WindowMixedLeaves
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowMixedContractions

structure OBBTBound where
  size : ℕ
  lam : Fin 41 → Fin size → ℤ
  scalar : Fin 41 → Fin size → WindowScalarLine.Support
  cut : WindowCellCuts.Cut
  payment : ℤ
  scale : ℤ
  minimum : ℤ
  edges : List FlowBasisCodec.Edge

def obbtCheck (cN : ℤ) (cell : DifferenceCell.Cell 10) (c : OBBTBound) : Bool :=
  WindowValueSublevel.check cell c.lam c.scalar
    (WindowCellCuts.negativeIncidence c.cut.i c.cut.j)
    c.payment c.scale cN c.minimum (-c.cut.bound) c.edges

theorem obbt_sound {cN : ℤ} {cell : DifferenceCell.Cell 10} {c : OBBTBound}
    (hc : obbtCheck cN cell c = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g)
    (hbelow : WindowGapEnergy.Fw24 g < WindowMixedLeaves.floor cN) :
    WindowDifferenceCell.positions g c.cut.j-WindowDifferenceCell.positions g c.cut.i ≤ (c.cut.bound:ℝ) := by
  have h := WindowValueSublevel.lower cell c.lam c.scalar
    (WindowCellCuts.negativeIncidence c.cut.i c.cut.j)
    c.payment c.scale cN c.minimum (-c.cut.bound) c.edges g hg hbelow hc
  rw [WindowCellCuts.objective_eq] at h
  push_cast at h
  linarith

structure NewtonBound where
  direction : Fin 9 → ℤ
  scalar : Fin 41 → WindowFirstOrderCertificate.Scalar
  coordinate : Fin 9
  minimum : List FlowBasisCodec.Edge
  maximum : List FlowBasisCodec.Edge
  L : ℤ
  U : ℤ
  lower : ℤ
  upper : ℤ

def newtonCheck (cell : DifferenceCell.Cell 10) (c : NewtonBound) : Bool :=
  (WindowFirstOrderCertificate.check cell c.scalar &&
    WindowCellCuts.supportCheck (123/128) cell c.direction) &&
    WindowNewtonFlow.check cell c.minimum c.maximum c.direction
      (WindowFirstOrderCertificate.rows c.scalar) c.coordinate c.L c.U c.lower c.upper

def newtonCuts (c : NewtonBound) : List WindowCellCuts.Cut :=
  [⟨c.coordinate.castSucc,c.coordinate.succ,c.upper⟩,
   ⟨c.coordinate.succ,c.coordinate.castSucc,-c.lower⟩]

theorem newton_sound {cell : DifferenceCell.Cell 10} {c : NewtonBound}
    (hc : newtonCheck cell c = true) {g : Fin 9 → ℝ}
    (hrel : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
    (hg : WindowDifferenceCell.Contains cell g) :
    ∀ e ∈ newtonCuts c,
      WindowDifferenceCell.positions g e.j-WindowDifferenceCell.positions g e.i ≤ (e.bound:ℝ) := by
  have hh : (WindowFirstOrderCertificate.check cell c.scalar = true ∧
      WindowCellCuts.supportCheck (123/128) cell c.direction = true) ∧
      WindowNewtonFlow.check cell c.minimum c.maximum c.direction
        (WindowFirstOrderCertificate.rows c.scalar) c.coordinate c.L c.U c.lower c.upper = true := by
    simpa only [newtonCheck,Bool.and_eq_true] using hc
  have hs := WindowCellCuts.support_sound hh.1.2 hg
  norm_num at hs
  have hr := WindowNewtonFlow.retain hrel cell hg c.minimum c.maximum c.direction
    (WindowFirstOrderCertificate.rows c.scalar) c.coordinate c.L c.U c.lower c.upper hs
    (WindowFirstOrderCertificate.valid hh.1.1 hg) hh.2
  have ha := WindowCellCuts.adjacent g c.coordinate
  intro e he
  simp [newtonCuts] at he
  rcases he with rfl | rfl
  · change WindowDifferenceCell.positions g c.coordinate.succ-
      WindowDifferenceCell.positions g c.coordinate.castSucc ≤ (c.upper:ℝ)
    linarith [hr.2]
  · change WindowDifferenceCell.positions g c.coordinate.castSucc-
      WindowDifferenceCell.positions g c.coordinate.succ ≤ ((-c.lower:ℤ):ℝ)
    push_cast
    linarith [hr.1]

inductive Contraction where
  | obbt (bounds : List OBBTBound)
  | newton (bounds : List NewtonBound)

def check (cN : ℤ) (cell : DifferenceCell.Cell 10) : Contraction → Bool
  | .obbt cs => cs.all (obbtCheck cN cell)
  | .newton cs => cs.all (newtonCheck cell)

def cuts : Contraction → List WindowCellCuts.Cut
  | .obbt cs => cs.map OBBTBound.cut
  | .newton cs => cs.flatMap newtonCuts

def contract (cell : DifferenceCell.Cell 10) (c : Contraction) : DifferenceCell.Cell 10 :=
  WindowCellCuts.restrict cell (cuts c)

theorem sound {cN : ℤ} {cell : DifferenceCell.Cell 10} {c : Contraction}
    (hc : check cN cell c = true) {g : Fin 9 → ℝ}
    (hrel : WindowMinimizerCover.RelevantBelow ((123:ℝ)/128) (WindowMixedLeaves.floor cN) g)
    (hg : WindowDifferenceCell.Contains cell g) : WindowDifferenceCell.Contains (contract cell c) g := by
  apply WindowCellCuts.restrict_sound (cuts c) hg
  intro e he
  cases c with
  | obbt cs =>
    have hh : ∀ b ∈ cs, obbtCheck cN cell b = true := by
      simpa only [check,List.all_eq_true] using hc
    simp only [cuts,List.mem_map] at he
    obtain ⟨b,hb,rfl⟩ := he
    exact obbt_sound (hh b hb) hg hrel.2
  | newton cs =>
    have hh : ∀ b ∈ cs, newtonCheck cell b = true := by
      simpa only [check,List.all_eq_true] using hc
    simp only [cuts,List.mem_flatMap] at he
    obtain ⟨b,hb,he⟩ := he
    exact newton_sound (hh b hb) hrel.1 hg e he

set_option pp.fullNames true
#print axioms obbt_sound
#print axioms newton_sound
#print axioms sound
end StructuralGoal20261016.WindowMixedContractions
end
