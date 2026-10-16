/- SPDX-License-Identifier: Apache-2.0
Dynamic secant-sector bounds for the actual scalar derivative. The square
payment retains the actual displacement squared, rather than replacing it
by a uniform cell radius. Numerical instantiation and coverage are separate.
-/
import StructuralGoal20261016.WindowScalarBregman
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowScalarSector
open WindowScalarBregman

theorem secant_abs {a b p x m M : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hsecond : ∀ y ∈ Icc a b,
      m ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ M) :
    |iteratedDeriv 1 f x-iteratedDeriv 1 f p-
      ((m+M)/2)*(x-p)| ≤ ((M-m)/2)*|x-p| := by
  obtain ⟨k,hk0,hk1,hincrement⟩ := derivative_increment hp hx hM hsecond
  have hk : |k-(m+M)/2| ≤ (M-m)/2 :=
    abs_le.mpr ⟨by linarith only [hk0],by linarith only [hk1]⟩
  rw [hincrement]
  have he : k*(x-p)-((m+M)/2)*(x-p) = (k-(m+M)/2)*(x-p) := by ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)

theorem square_from_abs {eta A E tau : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (htau : 0 < tau) (habs : |eta| ≤ A+E) :
    eta^2 ≤ (1+tau)*A^2+(1+1/tau)*E^2 := by
  have hb := abs_le.mp habs
  have hsq : eta^2 ≤ (A+E)^2 := by
    nlinarith [mul_nonneg (by linarith [hb.2] : 0 ≤ A+E-eta)
      (by linarith [hb.1] : 0 ≤ A+E+eta)]
  apply (mul_le_mul_iff_left₀ htau).mp
  have hs := mul_le_mul_of_nonneg_right hsq htau.le
  have hi : ((1+tau)*A^2+(1+1/tau)*E^2)*tau =
      tau*(1+tau)*A^2+(tau+1)*E^2 := by
    field_simp [ne_of_gt htau]
    <;> ring
  rw [hi]
  nlinarith only [hs,sq_nonneg (tau*A-E)]

theorem actual_square {a b p x m M S E tau : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hsecond : ∀ y ∈ Icc a b,
      m ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ M)
    (hslope : |iteratedDeriv 1 f p-S| ≤ E) (htau : 0 < tau) :
    (iteratedDeriv 1 f x-S-((m+M)/2)*(x-p))^2 ≤
      (1+tau)*((M-m)/2)^2*(x-p)^2+(1+1/tau)*E^2 := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hslope
  have hA : 0 ≤ ((M-m)/2)*|x-p| := by positivity
  have he : iteratedDeriv 1 f x-S-((m+M)/2)*(x-p) =
      (iteratedDeriv 1 f x-iteratedDeriv 1 f p-((m+M)/2)*(x-p))+
        (iteratedDeriv 1 f p-S) := by ring
  have ha : |iteratedDeriv 1 f x-S-((m+M)/2)*(x-p)| ≤
      ((M-m)/2)*|x-p|+E := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (secant_abs hp hx hM hsecond) hslope)
  have hh := square_from_abs hA hE htau ha
  simpa only [mul_pow,sq_abs,mul_assoc] using hh

/-- Any dynamic upper bound for the residual square gives a valid cut. -/
theorem residual_cut {eta D : ℝ} (hsector : eta^2 ≤ D) (A t : ℝ) :
    0 ≤ A^2+2*t*A*eta+t^2*D := by
  have hp := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsector)
  nlinarith only [sq_nonneg (A+t*eta),hp]

set_option pp.fullNames true
#print axioms secant_abs
#print axioms square_from_abs
#print axioms actual_square
#print axioms residual_cut
end StructuralGoal20261016.WindowScalarSector
end
