/- SPDX-License-Identifier: Apache-2.0
Actual quantized affine supports, including extensions below zero.
This matches the new-window value leaf's asymmetric derivative rounding.
-/
import StructuralGoal20261016.WindowScalarMinorant
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowQuantizedSupport
open WindowScalarMinorant

def line (p V D E lower x : ℝ) : ℝ :=
  V + D*(x-p) - E*max (p-lower) 0

theorem line_le_tangent {p V D E lower x value slope : ℝ}
    (hlower : lower ≤ x) (hV : V ≤ value) (hE : 0 ≤ E)
    (hD : D ≤ slope) (hU : slope ≤ D+E) :
    line p V D E lower x ≤ value + slope*(x-p) := by
  have hmax : p-x ≤ max (p-lower) 0 :=
    (by linarith : p-x ≤ p-lower).trans (le_max_left _ _)
  have hnonneg : 0 ≤ E*max (p-lower) 0 := mul_nonneg hE (le_max_right _ _)
  unfold line
  by_cases h : p ≤ x
  · have hm := mul_le_mul_of_nonneg_right hD (by linarith : 0 ≤ x-p)
    linarith
  · have hm := mul_le_mul_of_nonneg_right hU (by linarith : 0 ≤ p-x)
    have he := mul_le_mul_of_nonneg_left hmax hE
    nlinarith

theorem core_support {a b p V D E lower x : ℝ}
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hlower : lower ≤ x)
    (hV : V ≤ f p) (hE : 0 ≤ E)
    (hD : D ≤ iteratedDeriv 1 f p) (hU : iteratedDeriv 1 f p ≤ D+E)
    (hsecond : ∀ y ∈ Icc a b, 0 ≤ iteratedDeriv 2 f y) :
    line p V D E lower x ≤ f x := by
  have ht := quadratic_tangent (A := 0) hp hx (by simpa using hsecond)
  have hl := line_le_tangent (p := p) hlower hV hE hD hU
  nlinarith

theorem zero_extension {a b p V D E lower x : ℝ}
    (hp : p ∈ Icc a b) (hlower : lower ≤ x)
    (hV : V ≤ f p) (hE : 0 ≤ E)
    (hD : D ≤ iteratedDeriv 1 f p) (hU : iteratedDeriv 1 f p ≤ D+E)
    (hsecond : ∀ y ∈ Icc a b, 0 ≤ iteratedDeriv 2 f y)
    (hleft : x < a → 0 ≤ D+E ∧ V+(D+E)*(a-p) ≤ 0)
    (hright : b < x → D ≤ 0 ∧ V+D*(b-p) ≤ 0) :
    line p V D E lower x ≤ f x := by
  have hf : 0 ≤ f x := by
    dsimp [f, WindowKernel.w]
    positivity
  by_cases hxa : x < a
  · obtain ⟨hs, hval⟩ := hleft hxa
    have hlin := line_le_tangent (p := p) hlower (le_refl V) hE (by linarith : D ≤ D+E) (le_refl (D+E))
    have hm := mul_le_mul_of_nonneg_left hxa.le hs
    exact (by nlinarith : line p V D E lower x ≤ 0).trans hf
  · by_cases hxb : x ≤ b
    · exact core_support hp ⟨le_of_not_gt hxa,hxb⟩ hlower hV hE hD hU hsecond
    · obtain ⟨hs,hval⟩ := hright (lt_of_not_ge hxb)
      have hm := mul_le_mul_of_nonpos_left (le_of_not_ge hxb) hs
      have he := mul_nonneg hE (le_max_right (p-lower) 0)
      unfold line
      linarith

set_option pp.fullNames true
#print axioms core_support
#print axioms zero_extension
end StructuralGoal20261016.WindowQuantizedSupport
end
