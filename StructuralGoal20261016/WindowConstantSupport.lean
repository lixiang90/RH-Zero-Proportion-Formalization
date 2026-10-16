/- SPDX-License-Identifier: Apache-2.0
Constant supports for actual w=k^2. The whole-cell k interval is paid
from actual k/k' point intervals and the proved global |k''| <= 4.
No value-LP constant is accepted merely because w is nonnegative.
-/
import StructuralGoal20261016.WindowKernelPoint
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real
namespace StructuralGoal20261016.WindowConstantSupport
open WindowKernelPoint (f)
open WindowTaylorBridge WindowConvexityCertificate

theorem taylor_one (p x : ℝ) :
    taylorPoly f 1 p x = f p+iteratedDeriv 1 f p*(x-p) := by
  simp only [taylorPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one,
    pow_zero, pow_one, mul_one, iteratedDeriv_zero]

theorem interval_from_point {p x L U D E R : ℝ}
    (hL : L ≤ f p) (hU : f p ≤ U)
    (hD : D ≤ iteratedDeriv 1 f p) (hE : iteratedDeriv 1 f p ≤ E)
    (hR : |x-p| ≤ R) :
    L-(max |D| |E| *R+2*R^2) ≤ f x ∧
      f x ≤ U+(max |D| |E| *R+2*R^2) := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hM0 : 0 ≤ max |D| |E| := (abs_nonneg D).trans (le_max_left _ _)
  have hdl : -(max |D| |E|) ≤ D :=
    (neg_le_neg (le_max_left |D| |E|)).trans (neg_abs_le D)
  have heu : E ≤ max |D| |E| := (le_abs_self E).trans (le_max_right _ _)
  have hd : |iteratedDeriv 1 f p| ≤ max |D| |E| :=
    abs_le.mpr ⟨hdl.trans hD,hE.trans heu⟩
  have hs : |iteratedDeriv 1 f p*(x-p)| ≤ max |D| |E| *R := by
    rw [abs_mul]
    exact mul_le_mul hd hR (abs_nonneg _) hM0
  have ht := taylor_remainder f (k_contDiff 24 WindowKernel.d24) 1 k24_second_abs_le p x
  rw [taylor_one] at ht
  change |f x-(f p+iteratedDeriv 1 f p*(x-p))| ≤ 4*|x-p|^2/2 at ht
  have hsq : |x-p|^2 ≤ R^2 := pow_le_pow_left₀ (abs_nonneg _) hR 2
  have he : |f x-(f p+iteratedDeriv 1 f p*(x-p))| ≤ 2*R^2 := by
    nlinarith only [ht,hsq]
  constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2,
    (abs_le.mp hs).1,(abs_le.mp hs).2]

theorem square_lower {L U V x : ℝ} (hx : L ≤ f x ∧ f x ≤ U)
    (hV : (0 ≤ L ∧ V ≤ L^2) ∨ (U ≤ 0 ∧ V ≤ U^2)) :
    V ≤ WindowKernel.w 24 WindowKernel.d24 x := by
  change V ≤ (f x)^2
  rcases hV with h | h
  · have h0 : 0 ≤ f x-L := sub_nonneg.mpr hx.1
    have h1 : 0 ≤ f x+L := by linarith [hx.1,h.1]
    nlinarith [mul_nonneg h0 h1,h.2]
  · have h0 : 0 ≤ U-f x := sub_nonneg.mpr hx.2
    have h1 : 0 ≤ -(U+f x) := by linarith [hx.2,h.1]
    nlinarith [mul_nonneg h0 h1,h.2]

structure Support where
  center : ℕ
  anchor : ℤ
  kLower : ℚ
  kUpper : ℚ
  dLower : ℚ
  dUpper : ℚ
  radius : ℚ
  value : ℤ

def point (s : Support) : ℚ := (s.anchor:ℚ)/32768
def error (s : Support) : ℚ :=
  max |s.dLower| |s.dUpper| *s.radius+2*s.radius^2
def lower (s : Support) : ℚ := s.kLower-error s
def upper (s : Support) : ℚ := s.kUpper+error s

abbrev Checks (s : Support) (l u : ℤ) : Prop :=
  l ≤ u ∧ 0 ≤ s.radius ∧
  |(l:ℚ)/32768-point s| ≤ s.radius ∧
  |(u:ℚ)/32768-point s| ≤ s.radius ∧
  WindowKernelPoint.check s.center (point s) s.kLower s.kUpper s.dLower s.dUpper = true ∧
  ((0 ≤ lower s ∧ (s.value:ℚ)/10000000000 ≤ (lower s)^2) ∨
    (upper s ≤ 0 ∧ (s.value:ℚ)/10000000000 ≤ (upper s)^2))

def check (s : Support) (l u : ℤ) : Bool := decide (Checks s l u)

theorem sound {s : Support} {l u : ℤ} (hc : check s l u = true)
    {x : ℝ} (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    (s.value:ℝ)/10000000000 ≤ WindowKernel.w 24 WindowKernel.d24 x := by
  have hh : Checks s l u := of_decide_eq_true hc
  rcases hh with ⟨_,hR,hL,hU,hpoint,hvalue⟩
  have hp := WindowKernelPoint.sound hpoint
  have hl : |(l:ℝ)/32768-(point s:ℝ)| ≤ (s.radius:ℝ) := by exact_mod_cast hL
  have hu : |(u:ℝ)/32768-(point s:ℝ)| ≤ (s.radius:ℝ) := by exact_mod_cast hU
  have hr : |x-(point s:ℝ)| ≤ (s.radius:ℝ) := by
    rw [abs_le] at hl hu ⊢
    constructor <;> linarith [hx.1,hx.2,hl.1,hu.2]
  have hi := interval_from_point hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hr
  have he : (error s:ℝ) = max |(s.dLower:ℝ)| |(s.dUpper:ℝ)| *(s.radius:ℝ)+2*(s.radius:ℝ)^2 := by
    unfold error
    push_cast
    rfl
  have hex : (lower s:ℝ) ≤ f x ∧ f x ≤ (upper s:ℝ) := by
    simpa only [lower,upper,Rat.cast_sub,Rat.cast_add,he] using hi
  apply square_lower hex
  rcases hvalue with h | h
  · left
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · right
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2

theorem integer_line_sound {s : Support} {l u : ℤ} (hc : check s l u = true)
    {x : ℝ} (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    (((32768*s.value:ℤ):ℝ)+32768*(0:ℝ)*x)/(10000000000*32768) ≤
      WindowKernel.w 24 WindowKernel.d24 x := by
  have h := sound hc hx
  push_cast
  convert h using 1 <;> ring

set_option pp.fullNames true
#print axioms interval_from_point
#print axioms square_lower
#print axioms sound
#print axioms integer_line_sound
end StructuralGoal20261016.WindowConstantSupport
end
