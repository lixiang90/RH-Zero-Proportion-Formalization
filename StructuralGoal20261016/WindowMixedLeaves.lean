/- SPDX-License-Identifier: Apache-2.0
Concrete actual-kernel leaves for the mixed minimizer cover. All scalar,
feasibility and flow premises are Boolean checks in the leaf payload.
None is an asserted real oracle or a presupposed global energy floor.
-/
import StructuralGoal20261016.WindowFirstOrderCertificate
import StructuralGoal20261016.WindowCellCuts
import StructuralGoal20261016.WindowBasinCell
import StructuralGoal20261016.WindowCurvatureScalar
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowMixedLeaves

def floor (cN : ℤ) : ℝ := (cN:ℝ)/(WindowValueFlow.denominator:ℝ)

structure ValueCertificate where
  size : ℕ
  lam : Fin 41 → Fin size → ℤ
  scalar : Fin 41 → Fin size → WindowScalarLine.Support
  edges : List FlowBasisCodec.Edge
  target : ℤ

structure DirectionCertificate where
  direction : Fin 9 → ℤ
  scalar : Fin 41 → WindowFirstOrderCertificate.Scalar
  edges : List FlowBasisCodec.Edge

structure CurvatureCertificate where
  direction : Fin 9 → ℤ
  row : Fin 41 → WindowDirectionalFlow.Row
  packet : Fin 41 → WindowCurvatureScalar.Packet
  edges : List FlowBasisCodec.Edge

inductive Leaf where
  | value (c : ValueCertificate)
  | basin (index : ℕ)
  | direction (c : DirectionCertificate)
  | curvature (c : CurvatureCertificate)
  | empty (index : Fin 10)
  | reflection

def check (cN : ℤ) (cell : DifferenceCell.Cell 10) : Leaf → Bool
  | .value c => decide (cN ≤ c.target) &&
      WindowScalarLine.valueCheck cell c.lam c.scalar c.edges c.target
  | .basin i => decide ((cN:ℚ)/(WindowValueFlow.denominator:ℚ) ≤ 221/25000) &&
      WindowBasinCell.check cell i
  | .direction c =>
      (WindowFirstOrderCertificate.check cell c.scalar &&
        WindowCellCuts.feasibleCheck (123/128) cell c.direction) &&
        WindowDirectionalFlow.check cell c.edges c.direction (WindowFirstOrderCertificate.rows c.scalar)
  | .curvature c =>
      (WindowCurvatureScalar.allCheck cell c.row c.packet &&
        WindowCurvatureScalar.supportCheck cell c.direction) &&
        WindowCurvatureFlow.check cell c.edges c.direction c.row
  | .empty i => decide (cell i i < 0)
  | .reflection => decide (cell 8 9+cell 1 0 < 0)

theorem sound {cN : ℤ} {cell : DifferenceCell.Cell 10} {leaf : Leaf}
    (hc : check cN cell leaf = true) {g : Fin 9 → ℝ}
    (hrel : WindowMinimizerCover.RelevantBelow ((123:ℝ)/128) (floor cN) g)
    (hg : WindowDifferenceCell.Contains cell g) : floor cN ≤ WindowGapEnergy.Fw24 g := by
  cases leaf with
  | value c =>
    have hh : decide (cN ≤ c.target) = true ∧
        WindowScalarLine.valueCheck cell c.lam c.scalar c.edges c.target = true := by
      simpa only [check,Bool.and_eq_true] using hc
    have hn : cN ≤ c.target := of_decide_eq_true hh.1
    have hR : (cN:ℝ) ≤ (c.target:ℝ) := by exact_mod_cast hn
    have hd : (0:ℝ) < (WindowValueFlow.denominator:ℝ) := by norm_num [WindowValueFlow.denominator]
    exact (div_le_div_of_nonneg_right hR hd.le).trans
      (WindowScalarLine.value_bound cell c.lam c.scalar c.edges c.target g hg hh.2)
  | basin i =>
    have hh : decide ((cN:ℚ)/(WindowValueFlow.denominator:ℚ) ≤ 221/25000) = true ∧
        WindowBasinCell.check cell i = true := by
      simpa only [check,Bool.and_eq_true] using hc
    have hn : (cN:ℚ)/(WindowValueFlow.denominator:ℚ) ≤ 221/25000 := of_decide_eq_true hh.1
    have hR : (((cN:ℚ)/(WindowValueFlow.denominator:ℚ):ℚ):ℝ) ≤ ((221/25000:ℚ):ℝ) :=
      Rat.cast_le.mpr hn
    push_cast at hR
    exact hR.trans (WindowBasinCell.floor hh.2 hg)
  | direction c =>
    have hh : (WindowFirstOrderCertificate.check cell c.scalar = true ∧
        WindowCellCuts.feasibleCheck (123/128) cell c.direction = true) ∧
        WindowDirectionalFlow.check cell c.edges c.direction (WindowFirstOrderCertificate.rows c.scalar) = true := by
      simpa only [check,Bool.and_eq_true] using hc
    have hf := WindowCellCuts.feasible_sound hh.1.2 hg
    norm_num at hf
    exact False.elim (WindowDirectionalFlow.exclude hrel.1 cell hg c.edges c.direction
      (WindowFirstOrderCertificate.rows c.scalar)
      (WindowFirstOrderCertificate.valid hh.1.1 hg) hh.2 hf)
  | curvature c =>
    have hh : (WindowCurvatureScalar.allCheck cell c.row c.packet = true ∧
        WindowCurvatureScalar.supportCheck cell c.direction = true) ∧
        WindowCurvatureFlow.check cell c.edges c.direction c.row = true := by
      simpa only [check,Bool.and_eq_true] using hc
    exact False.elim (WindowCurvatureScalar.exclude hh.1.1 hh.1.2 hh.2 hrel.1 hg)
  | empty i =>
    have hn : cell i i < 0 := of_decide_eq_true hc
    exact False.elim (DifferenceCell.negative_diagonal_empty i hn (WindowDifferenceCell.positions g) hg)
  | reflection =>
    have hn : cell 8 9+cell 1 0 < 0 := of_decide_eq_true hc
    exact False.elim (WindowDifferenceCell.reflection_exclusion hg hrel.1.2.1 hn)

set_option pp.fullNames true
#print axioms sound
end StructuralGoal20261016.WindowMixedLeaves
end
