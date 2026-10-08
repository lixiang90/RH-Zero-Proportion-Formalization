import Mathlib

/-!
Finite analytic interfaces for the c260 record submission.

These are proved helper lemmas, not a proof of the challenge.  They add no
axioms or admitted facts.  The actual AM window, PC8 coverage, nine-point
certificate and dyadic zero-side assembly must supply their hypotheses.
-/

noncomputable section

open scoped BigOperators

namespace RHWeilRecord

def localReward : ℝ := 805260 / 100000000
def gapPressure : ℝ := 404350 / 100000000
def energyUpper : ℝ := 2 - 67216841 / 100000000
def recordRatio : ℝ := 66812491 / 99194740

theorem localReward_lt_one : localReward < 1 := by
  norm_num [localReward]

theorem gapPressure_nonneg : 0 ≤ gapPressure := by
  norm_num [gapPressure]

theorem recordRatio_identity :
    recordRatio = (2 - energyUpper - gapPressure) / (1 - localReward) := by
  norm_num [recordRatio, energyUpper, gapPressure, localReward]

/-- A certified point tangent yields two lines valid on its whole interval. -/
theorem interval_anchored_lines
    {w : ℝ → ℝ} {v d dm dp p l u : ℝ}
    (hdm : dm ≤ d) (hdp : d ≤ dp) (hlp : l ≤ p) (hpu : p ≤ u)
    (ht : ∀ x, l ≤ x → x ≤ u → v + d * (x - p) ≤ w x) :
    ∀ x, l ≤ x → x ≤ u →
      v + dp * (l - p) + dm * (x - l) ≤ w x ∧
      v + dm * (u - p) + dp * (x - u) ≤ w x := by
  intro x hlx hxu
  have h1 := mul_nonneg (sub_nonneg.mpr hdm) (sub_nonneg.mpr hlx)
  have h2 := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hlp)
  have h3 := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hxu)
  have h4 := mul_nonneg (sub_nonneg.mpr hdm) (sub_nonneg.mpr hpu)
  have htx := ht x hlx hxu
  constructor <;> nlinarith

def dot {n : ℕ} (a b : Fin n → ℝ) : ℝ := ∑ j, a j * b j

/-- Exact duality with every nonzero residual paid by its finite box. -/
theorem finite_box_dual_lower {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b lam : Fin m → ℝ)
    (q r lo hi x : Fin n → ℝ)
    (hlam : ∀ i, 0 ≤ lam i)
    (hrow : ∀ i, dot (A i) x ≤ b i)
    (hbox : ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hr : ∀ j, r j = q j + ∑ i, lam i * A i j) :
    -dot lam b + ∑ j, if 0 ≤ r j then r j * lo j else r j * hi j
      ≤ dot q x := by
  have hs :
      (∑ j, ∑ i, (lam i * A i j) * x j)
        = ∑ i, lam i * (∑ j, A i j * x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hid : dot q x = dot r x - ∑ i, lam i * dot (A i) x := by
    unfold dot
    simp_rw [hr]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    rw [hs]
    ring
  have hrows : (∑ i, lam i * dot (A i) x) ≤ dot lam b := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hrow i) (hlam i)
  have hbounds :
      (∑ j, if 0 ≤ r j then r j * lo j else r j * hi j) ≤ dot r x := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : 0 ≤ r j
    · rw [if_pos hj]
      exact mul_le_mul_of_nonneg_left (hbox j).1 hj
    · rw [if_neg hj]
      exact mul_le_mul_of_nonpos_left (hbox j).2 (le_of_lt (lt_of_not_ge hj))
  linarith

/-- The separated and paired spectral blocks may be assembled before counting. -/
theorem finite_count_transport
    {N n tr span err c B C : ℝ}
    (hc : c < 1) (hB : 0 ≤ B) (hspan : span ≤ N)
    (henergy : tr ≤ C * N)
    (hseam : 2 * N - n + (c * n - B * span - err) ≤ tr) :
    ((2 - C - B) / (1 - c)) * N - err / (1 - c) ≤ n := by
  have hden : 0 < 1 - c := sub_pos.mpr hc
  have hp : B * span ≤ B * N := mul_le_mul_of_nonneg_left hspan hB
  have hkey : (2 - C - B) * N - err ≤ (1 - c) * n := by
    nlinarith
  have hid :
      ((2 - C - B) / (1 - c)) * N - err / (1 - c)
        = ((2 - C - B) * N - err) / (1 - c) := by
    field_simp
  rw [hid]
  exact (div_le_iff₀ hden).mpr (by simpa [mul_comm] using hkey)

theorem c260_finite_count_transport {N n tr span err : ℝ}
    (hspan : span ≤ N) (henergy : tr ≤ energyUpper * N)
    (hseam : 2 * N - n + (localReward * n - gapPressure * span - err) ≤ tr) :
    recordRatio * N - err / (1 - localReward) ≤ n := by
  rw [recordRatio_identity]
  exact finite_count_transport localReward_lt_one gapPressure_nonneg hspan henergy hseam

/-- A genuine o(N) error is small after the positive denominator is paid. -/
theorem error_div_small {N err : ℝ → ℝ} {den : ℝ}
    (hden : 0 < den) (hN : ∀ T, 0 ≤ N T)
    (hErr : Asymptotics.IsLittleO Filter.atTop err N) :
    ∀ e > 0, ∀ᶠ T in Filter.atTop, err T / den ≤ e * N T := by
  intro e he
  filter_upwards [hErr.def (mul_pos he hden)] with T h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hN T)] at h
  apply (div_le_iff₀ hden).mpr
  calc err T ≤ |err T| := le_abs_self _
    _ ≤ (e * den) * N T := h
    _ = (e * N T) * den := by ring

/-- Generic dyadic endgame; all zero-side and spectral hypotheses stay explicit. -/
theorem asymptotic_count_transport {N n tr span err : ℝ → ℝ} {c B C : ℝ}
    (hc : c < 1) (hB : 0 ≤ B) (hN : ∀ T, 0 ≤ N T)
    (hspan : ∀ᶠ T in Filter.atTop, span T ≤ N T)
    (henergy : ∀ d > 0, ∀ᶠ T in Filter.atTop, tr T ≤ (C + d) * N T)
    (hseam : ∀ᶠ T in Filter.atTop,
      2 * N T - n T + (c * n T - B * span T - err T) ≤ tr T)
    (hErr : Asymptotics.IsLittleO Filter.atTop err N) :
    ∀ e > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((2 - C - B) / (1 - c) - e) * N T ≤ n T := by
  intro e he
  have hden : 0 < 1 - c := sub_pos.mpr hc
  let d : ℝ := e * (1 - c) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hid :
      (2 - (C + d) - B) / (1 - c) = (2 - C - B) / (1 - c) - e / 2 := by
    dsimp [d]
    field_simp
    ring
  have hmain : ∀ᶠ T in Filter.atTop,
      ((2 - C - B) / (1 - c) - e) * N T ≤ n T := by
    filter_upwards [hspan, henergy d hd, hseam,
      error_div_small hden hN hErr (e / 2) (by positivity)] with T hsp hE hS herr
    have h := finite_count_transport hc hB hsp hE hS
    rw [hid] at h
    nlinarith
  exact Filter.eventually_atTop.mp hmain

/-- This is the last monotone counting step, not a change of zero definitions. -/
theorem asymptotic_mono_counts
    {k : ℝ} {N simple distinct : ℝ → ℕ}
    (hle : ∀ T, simple T ≤ distinct T)
    (h : ∀ e > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (k - e) * (N T : ℝ) ≤ simple T) :
    ∀ e > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (k - e) * (N T : ℝ) ≤ distinct T := by
  intro e he
  obtain ⟨T₀, hT₀⟩ := h e he
  refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
  exact_mod_cast hle T

end RHWeilRecord

#print axioms RHWeilRecord.interval_anchored_lines
#print axioms RHWeilRecord.finite_box_dual_lower
#print axioms RHWeilRecord.finite_count_transport
#print axioms RHWeilRecord.c260_finite_count_transport
#print axioms RHWeilRecord.error_div_small
#print axioms RHWeilRecord.asymptotic_count_transport
#print axioms RHWeilRecord.asymptotic_mono_counts
