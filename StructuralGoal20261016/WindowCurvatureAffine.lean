/- SPDX-License-Identifier: Apache-2.0
Actual 41-edge second variations and correlated affine upper bounds.
A feasible negative second variation excludes a global minimizer even
when the available first-order certificate fails. Scalar upper inputs
remain explicit until supplied by checked actual derivative enclosures.
-/
import StructuralGoal20261016.WindowSecondVariation
import StructuralGoal20261016.WindowDirectionalAffine
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Finset
open scoped BigOperators
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowCurvatureAffine
open WindowGapEnergy WindowGramTransfer WindowSecondVariation
open WindowDirectionalAffine (span_eq_sum incidence)
open StructuralW10Followup20261016.NewLedger (W)

theorem curvature_eq (g d : Fin 9 → ℝ) :
    curvature W g d = ∑ e : Fin 41, weight e*(span d e)^2*w2 (span g e) := by
  have he (e : Fin 41) : HasDerivAt
      (fun t : ℝ => weight e*span d e*w1 (span (line (n := 10) g d t) e))
      (weight e*(span d e)^2*w2 (span g e)) 0 := by
    have hs : HasDerivAt (fun t : ℝ => span (line (n := 10) g d t) e)
        (span d e) 0 :=
      (ptsN_line_hasDerivAt (n := 10) g d (pairJ e)).sub
        (ptsN_line_hasDerivAt (n := 10) g d (pairI e))
    have hw := (WindowSecondVariation.w1_hasDerivAt
      (span (line (n := 10) g d 0) e)).comp 0 hs
    rw [line_zero] at hw
    exact (hw.const_mul (weight e*span d e)).congr_deriv (by ring)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun e _ => he e)
  have hh : HasDerivAt (fun t : ℝ => directional W (line (n := 10) g d t) d)
      (∑ e : Fin 41, weight e*(span d e)^2*w2 (span g e)) 0 := by
    have hf : (fun t : ℝ => directional W (line (n := 10) g d t) d) =
        (fun t => pressure d+∑ e : Fin 41,
          weight e*span d e*w1 (span (line (n := 10) g d t) e)) := by
      funext t
      exact WindowDirectionalAffine.directional_eq _ _
    rw [hf]
    exact hsum.const_add (pressure d)
  exact (curvature_hasDerivAt W g d).unique hh

def mass (d : Fin 9 → ℝ) (e : Fin 41) : ℝ := weight e*(span d e)^2
def intercept (d : Fin 9 → ℝ) (a : Fin 41 → ℝ) : ℝ := ∑ e, mass d e*a e
def coefficient (d : Fin 9 → ℝ) (b : Fin 41 → ℝ) (r : Fin 9) : ℝ :=
  ∑ e, mass d e*b e*incidence e r
def error (d : Fin 9 → ℝ) (epsilon : Fin 41 → ℝ) : ℝ := ∑ e, mass d e*epsilon e

theorem mass_nonneg (d : Fin 9 → ℝ) (e : Fin 41) : 0 ≤ mass d e :=
  mul_nonneg (weight_nonneg e) (sq_nonneg _)

theorem affine_identity (g d : Fin 9 → ℝ) (a b : Fin 41 → ℝ) :
    (∑ e, mass d e*(a e+b e*span g e)) =
      intercept d a+∑ r, coefficient d b r*g r := by
  simp only [intercept,coefficient,mul_add,Finset.sum_add_distrib]
  congr 1
  simp_rw [span_eq_sum g,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem upper (g d : Fin 9 → ℝ) (a b epsilon : Fin 41 → ℝ)
    (hscalar : ∀ e, w2 (span g e) ≤ a e+b e*span g e+epsilon e) :
    curvature W g d ≤ intercept d a+(∑ r, coefficient d b r*g r)+error d epsilon := by
  rw [curvature_eq]
  have hs : (∑ e, mass d e*w2 (span g e)) ≤
      ∑ e, mass d e*(a e+b e*span g e+epsilon e) :=
    Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hscalar e) (mass_nonneg d e))
  have he : (∑ e, mass d e*(a e+b e*span g e+epsilon e)) =
      (∑ e, mass d e*(a e+b e*span g e))+error d epsilon := by
    simp only [mul_add,Finset.sum_add_distrib,error]
  rw [he,affine_identity] at hs
  exact hs

theorem exclude {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.Relevant sep g) (d : Fin 9 → ℝ)
    (hsupport : ∀ r, d r ≠ 0 → sep < g r) (a b epsilon : Fin 41 → ℝ)
    (hscalar : ∀ e, w2 (span g e) ≤ a e+b e*span g e+epsilon e)
    (hnegative : intercept d a+(∑ r, coefficient d b r*g r)+error d epsilon < 0) : False := by
  have hn := curvature_nonneg_of_relevant hg d hsupport
  have hu := upper g d a b epsilon hscalar
  linarith

set_option pp.fullNames true
#print axioms curvature_eq
#print axioms affine_identity
#print axioms upper
#print axioms exclude
end StructuralGoal20261016.WindowCurvatureAffine
end
