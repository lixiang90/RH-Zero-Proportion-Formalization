/- SPDX-License-Identifier: Apache-2.0
Algebraic signed Gram projection for the actual 41-edge window energy.
The comparison vector u is arbitrary; no phase decomposition or global floor
is assumed. This source is supplied for owner compilation before acceptance.
-/
import StructuralGoal20261016.WindowGramExpansion
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset
open scoped BigOperators
namespace StructuralGoal20261016.WindowSignedGramProjection
open WindowGramTransfer

def actualK (g : Fin 9 → ℝ) (e : Fin 41) : ℝ :=
  WindowKernel.k 24 WindowKernel.d24 (span g e)

def residual (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) (e : Fin 41) : ℝ :=
  actualK g e-u e

def Q (u : Fin 41 → ℝ) : ℝ := ∑ e, weight e*(u e)^2

def R (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) : ℝ :=
  ∑ e, weight e*(residual g u e)^2

def T (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) : ℝ :=
  ∑ e, weight e*u e*residual g u e

theorem actual_expansion (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) :
    WindowGapEnergy.Fw24 g = pressure g+Q u+2*T g u+R g u := by
  have hsum : (∑ e : Fin 41, weight e*(actualK g e)^2) =
      Q u+2*T g u+R g u := by
    calc
      (∑ e : Fin 41, weight e*(actualK g e)^2) =
          ∑ e : Fin 41, (weight e*(u e)^2+
            2*(weight e*u e*residual g u e)+weight e*(residual g u e)^2) := by
        apply Finset.sum_congr rfl
        intro e _
        dsimp only [residual]
        ring
      _ = Q u+2*T g u+R g u := by
        simp only [Q,R,T,Finset.sum_add_distrib,Finset.mul_sum]
  calc
    WindowGapEnergy.Fw24 g = pressure g+∑ e : Fin 41,
        weight e*(actualK g e)^2 := by
      simpa only [actualK,WindowKernel.w] using actual_energy_expansion g
    _ = pressure g+(Q u+2*T g u+R g u) := by rw [hsum]
    _ = pressure g+Q u+2*T g u+R g u := by ring

theorem Q_nonneg (u : Fin 41 → ℝ) : 0 ≤ Q u := by
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (weight_nonneg e) (sq_nonneg (u e))

theorem T_eq_zero_of_Q_eq_zero (g : Fin 9 → ℝ) (u : Fin 41 → ℝ)
    (hQ : Q u = 0) : T g u = 0 := by
  have hnonneg (e : Fin 41) : 0 ≤ weight e*(u e)^2 :=
    mul_nonneg (weight_nonneg e) (sq_nonneg (u e))
  have hzero (e : Fin 41) : weight e*(u e)^2 = 0 := by
    apply le_antisymm
    · have hle : weight e*(u e)^2 ≤ Q u :=
        Finset.single_le_sum (fun f _ => hnonneg f) (Finset.mem_univ e)
      simpa only [hQ] using hle
    · exact hnonneg e
  unfold T
  apply Finset.sum_eq_zero
  intro e _
  rcases mul_eq_zero.mp (hzero e) with hw | hu
  · simp only [hw,zero_mul]
  · have hu0 : u e = 0 := sq_eq_zero_iff.mp hu
    simp only [hu0,mul_zero,zero_mul]

theorem actual_of_Q_eq_zero (g : Fin 9 → ℝ) (u : Fin 41 → ℝ)
    (hQ : Q u = 0) : WindowGapEnergy.Fw24 g = pressure g+R g u := by
  have hT := T_eq_zero_of_Q_eq_zero g u hQ
  rw [actual_expansion g u,hQ,hT]
  ring

theorem actual_of_u_zero (g : Fin 9 → ℝ) (u : Fin 41 → ℝ)
    (hu : ∀ e, u e = 0) : WindowGapEnergy.Fw24 g = pressure g+R g u := by
  apply actual_of_Q_eq_zero g u
  simp [Q,hu]

theorem real_projection_lower (q r t : ℝ) (hq : 0 < q) :
    r-t^2/q ≤ q+2*t+r := by
  have hmul : -(q+2*t)*q ≤ t^2 := by
    nlinarith only [sq_nonneg (q+t)]
  have hdiv : -(q+2*t) ≤ t^2/q := (le_div_iff₀ hq).mpr hmul
  linarith only [hdiv]

theorem actual_projection (g : Fin 9 → ℝ) (u : Fin 41 → ℝ)
    (hQ : 0 < Q u) :
    pressure g+R g u-(T g u)^2/Q u ≤ WindowGapEnergy.Fw24 g := by
  have h := real_projection_lower (Q u) (R g u) (T g u) hQ
  rw [actual_expansion g u]
  linarith only [h]

theorem actual_projection_all (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) :
    pressure g+R g u-(T g u)^2/Q u ≤ WindowGapEnergy.Fw24 g := by
  by_cases hQ : Q u = 0
  · have hT := T_eq_zero_of_Q_eq_zero g u hQ
    rw [actual_of_Q_eq_zero g u hQ,hQ,hT]
    simp
  · exact actual_projection g u (lt_of_le_of_ne (Q_nonneg u) (Ne.symm hQ))

theorem actual_gram_identity (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) :
    (WindowGapEnergy.Fw24 g-pressure g)*Q u-
      (Q u*R g u-(T g u)^2) = (Q u+T g u)^2 := by
  rw [actual_expansion g u]
  ring

theorem actual_det_le_energy_mul (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) :
    Q u*R g u-(T g u)^2 ≤ (WindowGapEnergy.Fw24 g-pressure g)*Q u := by
  have h := actual_gram_identity g u
  nlinarith only [h,sq_nonneg (Q u+T g u)]

theorem actual_sublevel_det (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) {c : ℝ}
    (hQ : 0 < Q u) (hc : WindowGapEnergy.Fw24 g < c) :
    Q u*R g u-(T g u)^2 < (c-pressure g)*Q u := by
  exact lt_of_le_of_lt (actual_det_le_energy_mul g u)
    (mul_lt_mul_of_pos_right (sub_lt_sub_right hc (pressure g)) hQ)

theorem actual_floor_of_det (g : Fin 9 → ℝ) (u : Fin 41 → ℝ) (c : ℝ)
    (hQ : 0 < Q u)
    (hdet : (c-pressure g)*Q u ≤ Q u*R g u-(T g u)^2) :
    c ≤ WindowGapEnergy.Fw24 g := by
  by_contra h
  have hc : WindowGapEnergy.Fw24 g < c := lt_of_not_ge h
  exact (not_lt_of_ge hdet) (actual_sublevel_det g u hQ hc)

set_option pp.fullNames true
#print axioms actual_expansion
#print axioms Q_nonneg
#print axioms T_eq_zero_of_Q_eq_zero
#print axioms actual_of_Q_eq_zero
#print axioms actual_of_u_zero
#print axioms actual_projection
#print axioms actual_projection_all
#print axioms actual_gram_identity
#print axioms actual_det_le_energy_mul
#print axioms actual_sublevel_det
#print axioms actual_floor_of_det
end StructuralGoal20261016.WindowSignedGramProjection
end
