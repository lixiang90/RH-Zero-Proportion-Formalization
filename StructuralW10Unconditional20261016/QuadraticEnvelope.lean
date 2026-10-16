/- SPDX-License-Identifier: Apache-2.0
Finite affine envelopes can certify convex quadratic lower bounds. These
generic lemmas assert no concrete kernel minorant or global W10 coverage.
-/
import Mathlib

noncomputable section
open Finset
open scoped BigOperators
namespace StructuralW10Unconditional20261016.QuadraticEnvelope

def quad (a b c x : ℝ) : ℝ := a*x^2+b*x+c
def line (s v x : ℝ) : ℝ := s*x+v

/-- A convex quadratic below an affine function at both endpoints remains
below that affine function throughout the interval. -/
theorem below_line {a b c s v l u x : ℝ} (ha : 0 ≤ a)
    (hxl : l ≤ x) (hxu : x ≤ u)
    (hl : quad a b c l ≤ line s v l)
    (hu : quad a b c u ≤ line s v u) :
    quad a b c x ≤ line s v x := by
  by_cases hlu : l = u
  · have hx : x = l := by linarith
    simpa only [hx] using hl
  have hpos : 0 < u-l := by
    rcases lt_or_eq_of_le (hxl.trans hxu) with hlt | heq
    · linarith
    · exact False.elim (hlu heq)
  have heq : (u-l)*(quad a b c x-line s v x) =
      (u-x)*(quad a b c l-line s v l)+
      (x-l)*(quad a b c u-line s v u)-a*(u-l)*(x-l)*(u-x) := by
    unfold quad line
    ring
  have h1 : (u-x)*(quad a b c l-line s v l) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxu) (sub_nonpos.mpr hl)
  have h2 : (x-l)*(quad a b c u-line s v u) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxl) (sub_nonpos.mpr hu)
  have h3 : 0 ≤ a*(u-l)*(x-l)*(u-x) :=
    mul_nonneg (mul_nonneg (mul_nonneg ha hpos.le) (sub_nonneg.mpr hxl)) (sub_nonneg.mpr hxu)
  have hh : (u-l)*(quad a b c x-line s v x) ≤ 0 := by rw [heq]; linarith
  by_contra h
  have hp : 0 < quad a b c x-line s v x := sub_pos.mpr (lt_of_not_ge h)
  exact (not_lt_of_ge hh) (mul_pos hpos hp)

theorem piece_sound {w : ℝ → ℝ} {a b c s v l u : ℝ} (ha : 0 ≤ a)
    (hl : quad a b c l ≤ line s v l)
    (hu : quad a b c u ≤ line s v u)
    (hsound : ∀ x, l ≤ x → x ≤ u → line s v x ≤ w x) :
    ∀ x, l ≤ x → x ≤ u → quad a b c x ≤ w x := by
  intro x hxl hxu
  exact (below_line ha hxl hxu hl hu).trans (hsound x hxl hxu)

/-- The affine line actually used by the existing integer oracle follows
from a tangent and a bounded slope uncertainty, including anchors outside
the interval. The uncertainty is paid only on the distance to its left end. -/
theorem uncertain_tangent {w : ℝ → ℝ} {p value d s err l x : ℝ}
    (hsl : s ≤ d) (hsu : d ≤ s+err) (hxl : l ≤ x)
    (ht : value+d*(x-p) ≤ w x) :
    value+s*(x-p)-err*max (p-l) 0 ≤ w x := by
  have he : 0 ≤ err := by linarith
  have h0 : 0 ≤ (d-s)*(x-l) := mul_nonneg (sub_nonneg.mpr hsl) (sub_nonneg.mpr hxl)
  have h1 : (d-s)*(p-l) ≤ err*max (p-l) 0 := by
    calc
      (d-s)*(p-l) ≤ (d-s)*max (p-l) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hsl)
      _ ≤ err*max (p-l) 0 :=
        mul_le_mul_of_nonneg_right (by linarith) (le_max_right _ _)
  nlinarith only [ht,h0,h1]

/-- A rational completion-of-squares identity is sufficient for a global
lower bound on its polynomial; no computed optimizer is a premise. -/
theorem sos_lower {ι α : Type*} [Fintype ι] (f : α → ℝ)
    (lower : ℝ) (weight : ι → ℝ) (form : ι → α → ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hid : ∀ x, f x = lower+∑ i, weight i*(form i x)^2) :
    ∀ x, lower ≤ f x := by
  intro x
  rw [hid]
  exact le_add_of_nonneg_right (sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _))

#print axioms below_line
#print axioms uncertain_tangent
#print axioms sos_lower
end StructuralW10Unconditional20261016.QuadraticEnvelope
end
