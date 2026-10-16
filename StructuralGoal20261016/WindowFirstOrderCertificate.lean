/- SPDX-License-Identifier: Apache-2.0
Finite point/grid checks supply the actual first-order scalar enclosures
used by integer directional and Newton certificates.
-/
import StructuralGoal20261016.WindowDerivativeOracleAll
import StructuralGoal20261016.WindowDirectionalFlow
import StructuralGoal20261016.WindowScalarLine
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowFirstOrderCertificate

structure Scalar where
  row : WindowDirectionalFlow.Row
  affine : Bool
  n : ℕ
  firstCell : ℕ
  lastCell : ℕ
  gridLower : ℚ
  gridUpper : ℚ
  third : ℚ

def rows (sc : Fin 41 → Scalar) : Fin 41 → WindowDirectionalFlow.Row := fun e => (sc e).row

def leftQ (cell : DifferenceCell.Cell 10) (e : Fin 41) : ℚ :=
  (WindowScalarLine.lower cell e:ℚ)/32768
def rightQ (cell : DifferenceCell.Cell 10) (e : Fin 41) : ℚ :=
  (WindowScalarLine.upper cell e:ℚ)/32768
def pointQ (s : Scalar) : ℚ := (s.row.anchor:ℚ)/(2*(WindowDirectionalFlow.SC:ℚ))
def valueQ (s : Scalar) : ℚ := (s.row.value:ℚ)/(WindowDirectionalFlow.DS:ℚ)
def slopeQ (s : Scalar) : ℚ := (s.row.slope:ℚ)/(WindowDirectionalFlow.DS:ℚ)
def errorQ (s : Scalar) : ℚ := (s.row.error:ℚ)/(WindowDirectionalFlow.DS:ℚ)

def gridCheck (cell : DifferenceCell.Cell 10) (e : Fin 41) (s : Scalar) : Bool :=
  WindowGridRange.check s.firstCell s.lastCell (leftQ cell e) (rightQ cell e)
    s.gridLower s.gridUpper s.third

def checkScalar (cell : DifferenceCell.Cell 10) (e : Fin 41) (s : Scalar) : Bool :=
  if s.affine then
    WindowDerivativeAffineOracle.check s.n (leftQ cell e) (rightQ cell e)
      (pointQ s) (valueQ s) (slopeQ s) s.third (errorQ s) && gridCheck cell e s
  else
    decide (s.row.slope = 0 ∧ valueQ s-errorQ s ≤ s.gridLower ∧
      s.gridUpper ≤ valueQ s+errorQ s) && gridCheck cell e s

def check (cell : DifferenceCell.Cell 10) (sc : Fin 41 → Scalar) : Bool :=
  decide (∀ e, checkScalar cell e (sc e) = true)

theorem scalar_valid {cell : DifferenceCell.Cell 10} {e : Fin 41} {s : Scalar}
    (hc : checkScalar cell e s = true) {x : ℝ}
    (hx : x ∈ Icc (leftQ cell e:ℝ) (rightQ cell e:ℝ)) :
    |WindowGapEnergy.w1 x-((s.row.value:ℝ)/(WindowDirectionalFlow.DS:ℝ)+
      (s.row.slope:ℝ)/(WindowDirectionalFlow.DS:ℝ)*
        (x-(s.row.anchor:ℝ)/(2*(WindowDirectionalFlow.SC:ℝ))))| ≤
      (s.row.error:ℝ)/(WindowDirectionalFlow.DS:ℝ) := by
  by_cases hmode : s.affine = true
  · have hh : WindowDerivativeAffineOracle.check s.n (leftQ cell e) (rightQ cell e)
        (pointQ s) (valueQ s) (slopeQ s) s.third (errorQ s) = true ∧
        gridCheck cell e s = true := by
      simpa only [checkScalar,hmode,ite_true,Bool.and_eq_true] using hc
    have h := WindowDerivativeOracleAll.affine hh.1 hh.2 hx
    simpa only [pointQ,valueQ,slopeQ,errorQ,Rat.cast_div,Rat.cast_intCast,
      Rat.cast_mul,Rat.cast_ofNat] using h
  · have hh : decide (s.row.slope = 0 ∧ valueQ s-errorQ s ≤ s.gridLower ∧
        s.gridUpper ≤ valueQ s+errorQ s) = true ∧ gridCheck cell e s = true := by
      simpa [checkScalar,hmode,Bool.and_eq_true] using hc
    have hp : s.row.slope = 0 ∧ valueQ s-errorQ s ≤ s.gridLower ∧
        s.gridUpper ≤ valueQ s+errorQ s := of_decide_eq_true hh.1
    have h := WindowDerivativeOracleAll.interval hh.2 hp.2.1 hp.2.2 hx
    simpa only [valueQ,errorQ,Rat.cast_div,Rat.cast_intCast,hp.1,
      Int.cast_zero,zero_div,zero_mul,add_zero] using h

theorem valid {cell : DifferenceCell.Cell 10} {sc : Fin 41 → Scalar}
    (hc : check cell sc = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g) :
    WindowDirectionalFlow.ScalarValid g (rows sc) := by
  have hh : ∀ e, checkScalar cell e (sc e) = true := of_decide_eq_true hc
  intro e
  have hs := WindowScalarLine.span_bounds hg e
  have hx : WindowGramTransfer.span g e ∈ Icc (leftQ cell e:ℝ) (rightQ cell e:ℝ) := by
    unfold leftQ rightQ
    push_cast
    exact hs
  exact scalar_valid (hh e) hx

set_option pp.fullNames true
#print axioms scalar_valid
#print axioms valid
end StructuralGoal20261016.WindowFirstOrderCertificate
end
