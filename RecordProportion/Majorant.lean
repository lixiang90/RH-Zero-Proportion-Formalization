/-
The AM lossless majorant at the existing parameters 4/5 and 61/100.
Adapted proof text Copyright 2026 Kristian Muri Knausgård, Apache-2.0.
The upstream Zeta23-derived notices apply to its Poisson summation API.
Fourier inversion and the separated quadratic-form proof are adapted from
Simple673/Majorant/{Fourier,Separated}.lean in arXiv:2610.08965v1.
The elementary alternating Taylor proof is adapted from
Distinct839/Majorant/Taylor.lean in the same archive.
AM definitions and taper facts are imported without alteration.
Every assertion below has an explicit proof term.
-/
import RecordProportion.ImportedAM

noncomputable section
open Real Set MeasureTheory Filter Topology
open scoped BigOperators
namespace RHWeilRecord.MajorantAM

def sep : ℝ := 4 / 5
def gammaM : ℝ := 61 / 100
def sincN (x : ℝ) : ℝ := Real.sinc (π * x)
def gMaj (u : ℝ) : ℝ :=
  gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2
def LMaj : ℝ := 2 * gammaM / sep * (1 + sincN sep)

end RHWeilRecord.MajorantAM

open Real MeasureTheory
open scoped FourierTransform

namespace RHWeilRecord.MajorantAM.Majorant

/-! ## Elementary facts -/

lemma sep_pos : 0 < sep := by unfold sep; norm_num

lemma sep_ne_zero : sep ≠ 0 := sep_pos.ne'

lemma gammaM_nonneg : 0 ≤ gammaM := by unfold gammaM; norm_num

/-- `sin x = x · sinc x`, for every real `x`. -/
lemma sin_eq_mul_sinc (x : ℝ) : sin x = x * sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinc_of_ne_zero hx]
    field_simp

/-- `sinc x² ≤ 2/(1 + x²)`. -/
lemma sinc_sq_le (x : ℝ) : sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hA : sinc x ^ 2 ≤ 1 := by
    calc sinc x ^ 2 = |sinc x| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_sinc_le_one x) 2
      _ = 1 := one_pow 2
  have hB : sinc x ^ 2 * x ^ 2 ≤ 1 := by
    have h : sinc x * x = sin x := by rw [mul_comm]; exact (sin_eq_mul_sinc x).symm
    rw [← mul_pow, h]
    exact sin_sq_le_one x
  rw [← div_eq_mul_inv, le_div_iff₀ h1, mul_add, mul_one]
  linarith

/-- `gMaj u ≤ 4γ (1/(1 + x₋²) + 1/(1 + x₊²))`, `x_± = π d (u ± 1/2)`. -/
lemma gMaj_le (u : ℝ) :
    gMaj u ≤ gammaM * (4 * (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹
      + 4 * (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹) := by
  unfold gMaj sincN
  rw [show π * (sep * (u - 1 / 2)) = π * sep * (u - 1 / 2) by ring,
    show π * (sep * (u + 1 / 2)) = π * sep * (u + 1 / 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ gammaM_nonneg
  have h1 := sinc_sq_le (π * sep * (u - 1 / 2))
  have h2 := sinc_sq_le (π * sep * (u + 1 / 2))
  nlinarith [sq_nonneg (sinc (π * sep * (u - 1 / 2)) - sinc (π * sep * (u + 1 / 2)))]

end RHWeilRecord.MajorantAM.Majorant

/-! ## The majorant: positivity, continuity, integrability -/

namespace RHWeilRecord.MajorantAM

open Majorant

/-- The majorant is nonnegative. -/
theorem gMaj_nonneg (u : ℝ) : 0 ≤ gMaj u := mul_nonneg gammaM_nonneg (sq_nonneg _)

/-- The majorant is continuous. -/
theorem continuous_gMaj : Continuous gMaj := by
  have h : Continuous fun u : ℝ =>
      gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2 := by
    unfold sincN
    fun_prop
  exact h

/-- The majorant is integrable on `ℝ`: it is bounded by a sum of two Cauchy densities. -/
theorem integrable_gMaj : Integrable gMaj := by
  have hne : π * sep ≠ 0 := mul_ne_zero pi_ne_zero sep_ne_zero
  have h1 : Integrable fun x : ℝ => (1 + (π * sep * x) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' hne
  have hm : Integrable fun u : ℝ => (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹ :=
    h1.comp_sub_right (1 / 2)
  have hp : Integrable fun u : ℝ => (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹ :=
    h1.comp_add_right (1 / 2)
  have hB : Integrable fun u : ℝ => gammaM * (4 * (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹
      + 4 * (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹) :=
    ((hm.const_mul 4).add (hp.const_mul 4)).const_mul gammaM
  refine hB.mono' continuous_gMaj.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gMaj_nonneg u)]
  exact gMaj_le u

end RHWeilRecord.MajorantAM

namespace RHWeilRecord.MajorantAM.Majorant

lemma integrable_gMaj_mul_cos (t : ℝ) :
    Integrable fun u : ℝ => gMaj u * cos (2 * π * t * u) := by
  refine integrable_gMaj.mono' (continuous_gMaj.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gMaj_nonneg u)]
  exact mul_le_of_le_one_right (gMaj_nonneg u) (abs_cos_le_one _)

lemma integrable_gMaj_mul_sin (t : ℝ) :
    Integrable fun u : ℝ => gMaj u * sin (2 * π * t * u) := by
  refine integrable_gMaj.mono' (continuous_gMaj.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gMaj_nonneg u)]
  exact mul_le_of_le_one_right (gMaj_nonneg u) (abs_sin_le_one _)

/-! ## Two elementary integrals -/

/-- `∫₀^d (d - t) cos(a t) dt = (1 - cos(a d))/a²` for `a ≠ 0`. -/
lemma integral_tri_cos_of_ne {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos (a * t) = (1 - cos (a * sep)) / a ^ 2 := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) sep,
      HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y) / a - cos (a * y) / a ^ 2)
        ((sep - t) * cos (a * t)) t := by
    intro t _
    have hlin : HasDerivAt (fun y : ℝ => a * y) a t := by
      have h := (hasDerivAt_id' t).const_mul a
      rwa [mul_one] at h
    have h1 : HasDerivAt (fun y : ℝ => sep - y) (-1) t := (hasDerivAt_id' t).const_sub sep
    have h2 : HasDerivAt (fun y : ℝ => sin (a * y)) (cos (a * t) * a) t := hlin.sin
    have h3 : HasDerivAt (fun y : ℝ => cos (a * y)) (-sin (a * t) * a) t := hlin.cos
    have h4 : HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y))
        (-1 * sin (a * t) + (sep - t) * (cos (a * t) * a)) t := h1.mul h2
    have h5 : HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y) / a - cos (a * y) / a ^ 2)
        ((-1 * sin (a * t) + (sep - t) * (cos (a * t) * a)) / a
          - (-sin (a * t) * a) / a ^ 2) t := (h4.div_const a).sub (h3.div_const (a ^ 2))
    refine h5.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => (sep - t) * cos (a * t)).intervalIntegrable _ _)]
  simp only [mul_zero, sin_zero, cos_zero]
  ring

/-- `∫₀^d (d - t) cos(a t) dt = (d²/2) sinc(a d/2)²`. -/
lemma integral_tri_cos (a : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos (a * t) = sep ^ 2 / 2 * sinc (a * sep / 2) ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hd : ∀ t ∈ Set.uIcc (0 : ℝ) sep,
        HasDerivAt (fun y : ℝ => sep * y - y * y / 2) ((sep - t) * cos (0 * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => sep * y) (sep * 1) t := (hasDerivAt_id' t).const_mul sep
      have h2 : HasDerivAt (fun y : ℝ => y * y) (1 * t + t * 1) t :=
        (hasDerivAt_id' t).mul (hasDerivAt_id' t)
      have h3 : HasDerivAt (fun y : ℝ => sep * y - y * y / 2)
          (sep * 1 - (1 * t + t * 1) / 2) t := h1.sub (h2.div_const 2)
      refine h3.congr_deriv ?_
      rw [zero_mul, cos_zero]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (sep - t) * cos (0 * t)).intervalIntegrable _ _)]
    simp only [zero_mul, zero_div, sinc_zero]
    ring
  · have hs := sep_ne_zero
    have hx : a * sep / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha hs) two_ne_zero
    have hcos : cos (a * sep) = 1 - 2 * sin (a * sep / 2) ^ 2 := by
      have h := cos_two_mul (a * sep / 2)
      rw [show 2 * (a * sep / 2) = a * sep by ring, cos_sq'] at h
      rw [h]
      ring
    rw [integral_tri_cos_of_ne ha, sinc_of_ne_zero hx, hcos]
    field_simp
    ring

/-- `∫₀^d sin(π d - b t) dt = d · sin(π d - b d/2) · sinc(b d/2)`. -/
lemma integral_sin_sub (b : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - b * t)
      = sep * sin (π * sep - b * sep / 2) * sinc (b * sep / 2) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [zero_mul, zero_div, sub_zero, sinc_zero, mul_one, intervalIntegral.integral_const,
      smul_eq_mul]
  · have hs := sep_ne_zero
    have hx : b * sep / 2 ≠ 0 := div_ne_zero (mul_ne_zero hb hs) two_ne_zero
    have hgen : ∀ X Y : ℝ, cos (X - Y) - cos (X + Y) = 2 * sin X * sin Y := by
      intro X Y
      rw [cos_sub, cos_add]
      ring
    have key : cos (π * sep - b * sep) - cos (π * sep)
        = 2 * sin (π * sep - b * sep / 2) * sin (b * sep / 2) := by
      have h := hgen (π * sep - b * sep / 2) (b * sep / 2)
      rw [show π * sep - b * sep / 2 - b * sep / 2 = π * sep - b * sep by ring,
        show π * sep - b * sep / 2 + b * sep / 2 = π * sep by ring] at h
      exact h
    rw [intervalIntegral.integral_comp_sub_mul (f := sin) hb, integral_sin, mul_zero, sub_zero,
      key, sinc_of_ne_zero hx, smul_eq_mul]
    field_simp

/-- The first triangle term, in terms of `sincN`. -/
lemma integral_half1 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos ((2 * π * u + π) * t)
      = sep ^ 2 / 2 * sincN (sep * (u + 1 / 2)) ^ 2 := by
  unfold sincN
  rw [integral_tri_cos, show (2 * π * u + π) * sep / 2 = π * (sep * (u + 1 / 2)) by ring]

/-- The second triangle term, in terms of `sincN`. -/
lemma integral_half2 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos ((2 * π * u - π) * t)
      = sep ^ 2 / 2 * sincN (sep * (u - 1 / 2)) ^ 2 := by
  unfold sincN
  rw [integral_tri_cos, show (2 * π * u - π) * sep / 2 = π * (sep * (u - 1 / 2)) by ring]

/-- The first cross term, in terms of `sincN`. -/
lemma integral_half3 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - (π - 2 * π * u) * t)
      = π * sep ^ 2 * (u + 1 / 2) * sincN (sep * (u + 1 / 2)) * sincN (sep * (u - 1 / 2)) := by
  unfold sincN
  rw [integral_sin_sub,
    show π * sep - (π - 2 * π * u) * sep / 2 = π * (sep * (u + 1 / 2)) by ring,
    show (π - 2 * π * u) * sep / 2 = -(π * (sep * (u - 1 / 2))) by ring, sinc_neg,
    sin_eq_mul_sinc]
  ring

/-- The second cross term, in terms of `sincN`. -/
lemma integral_half4 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - (π + 2 * π * u) * t)
      = -(π * sep ^ 2 * (u - 1 / 2) * sincN (sep * (u + 1 / 2)) * sincN (sep * (u - 1 / 2))) := by
  unfold sincN
  rw [integral_sin_sub,
    show π * sep - (π + 2 * π * u) * sep / 2 = -(π * (sep * (u - 1 / 2))) by ring,
    show (π + 2 * π * u) * sep / 2 = π * (sep * (u + 1 / 2)) by ring, sin_neg,
    sin_eq_mul_sinc]
  ring

/-! ## The function `FMaj` -/

/-- The function whose Fourier transform is `gMaj`:
`FMaj t = (2γ/d²) (m cos(π t) + sin(π m)/π)` with `m = max(d - |t|, 0)`. -/
noncomputable def FMaj (t : ℝ) : ℝ :=
  2 * gammaM / sep ^ 2 * (max (sep - |t|) 0 * cos (π * t) + sin (π * max (sep - |t|) 0) / π)

lemma FMaj_neg (t : ℝ) : FMaj (-t) = FMaj t := by
  unfold FMaj
  rw [abs_neg, mul_neg, cos_neg]

lemma FMaj_eq_zero {t : ℝ} (ht : sep ≤ |t|) : FMaj t = 0 := by
  unfold FMaj
  rw [max_eq_right (by linarith : sep - |t| ≤ 0)]
  simp

lemma FMaj_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ sep) :
    FMaj t = 2 * gammaM / sep ^ 2 * ((sep - t) * cos (π * t) + sin (π * (sep - t)) / π) := by
  unfold FMaj
  rw [abs_of_nonneg h0, max_eq_left (by linarith : (0 : ℝ) ≤ sep - t)]

lemma FMaj_zero : FMaj 0 = LMaj := by
  have hs := sep_ne_zero
  have hp := pi_ne_zero
  have hx : π * sep ≠ 0 := mul_ne_zero hp hs
  unfold FMaj LMaj sincN
  rw [abs_zero, sub_zero, max_eq_left sep_pos.le, mul_zero, cos_zero, sinc_of_ne_zero hx]
  field_simp

lemma continuous_FMaj : Continuous FMaj := by
  have hm : Continuous fun t : ℝ => max (sep - |t|) 0 :=
    (continuous_const.sub continuous_abs).max continuous_const
  have h : Continuous fun t : ℝ => 2 * gammaM / sep ^ 2
      * (max (sep - |t|) 0 * cos (π * t) + sin (π * max (sep - |t|) 0) / π) :=
    continuous_const.mul ((hm.mul (by fun_prop)).add
      ((continuous_sin.comp (continuous_const.mul hm)).div_const π))
  exact h

lemma hasCompactSupport_FMaj : HasCompactSupport FMaj :=
  HasCompactSupport.intro (isCompact_Icc (a := -sep) (b := sep)) fun t ht => by
    apply FMaj_eq_zero
    by_contra hcon
    have h := abs_lt.mp (not_le.mp hcon)
    exact ht ⟨h.1.le, h.2.le⟩

lemma integrable_FMaj_mul_cos (u : ℝ) :
    Integrable fun t : ℝ => FMaj t * cos (2 * π * u * t) :=
  (continuous_FMaj.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_FMaj.mul_right

lemma integrable_FMaj_mul_sin (u : ℝ) :
    Integrable fun t : ℝ => FMaj t * sin (2 * π * u * t) :=
  (continuous_FMaj.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_FMaj.mul_right

/-! ## The cosine transform of `FMaj` is `gMaj` -/

lemma integral_FMaj_cos_half (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, FMaj t * cos (2 * π * u * t) = gMaj u / 2 := by
  have hs := sep_ne_zero
  have hp := pi_ne_zero
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) sep, FMaj t * cos (2 * π * u * t) =
      gammaM / sep ^ 2 * ((sep - t) * cos ((2 * π * u + π) * t))
      + gammaM / sep ^ 2 * ((sep - t) * cos ((2 * π * u - π) * t))
      + gammaM / (sep ^ 2 * π) * sin (π * sep - (π - 2 * π * u) * t)
      + gammaM / (sep ^ 2 * π) * sin (π * sep - (π + 2 * π * u) * t) := by
    intro t ht
    rw [Set.uIcc_of_le sep_pos.le] at ht
    rw [FMaj_of_mem ht.1 ht.2]
    have c1 : cos ((2 * π * u + π) * t)
        = cos (2 * π * u * t) * cos (π * t) - sin (2 * π * u * t) * sin (π * t) := by
      rw [add_mul, cos_add]
    have c2 : cos ((2 * π * u - π) * t)
        = cos (2 * π * u * t) * cos (π * t) + sin (2 * π * u * t) * sin (π * t) := by
      rw [sub_mul, cos_sub]
    have s1 : sin (π * sep - (π - 2 * π * u) * t)
        = sin (π * (sep - t)) * cos (2 * π * u * t)
          + cos (π * (sep - t)) * sin (2 * π * u * t) := by
      rw [show π * sep - (π - 2 * π * u) * t = π * (sep - t) + 2 * π * u * t by ring, sin_add]
    have s2 : sin (π * sep - (π + 2 * π * u) * t)
        = sin (π * (sep - t)) * cos (2 * π * u * t)
          - cos (π * (sep - t)) * sin (2 * π * u * t) := by
      rw [show π * sep - (π + 2 * π * u) * t = π * (sep - t) - 2 * π * u * t by ring, sin_sub]
    rw [c1, c2, s1, s2]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_half1 u, integral_half2 u, integral_half3 u, integral_half4 u]
  · unfold gMaj
    field_simp
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The cosine transform of `FMaj` is the majorant. -/
theorem integral_FMaj_mul_cos (u : ℝ) : ∫ t, FMaj t * cos (2 * π * u * t) = gMaj u := by
  have hsupp : Function.support (fun t : ℝ => FMaj t * cos (2 * π * u * t))
      ⊆ Set.Ioc (-sep) sep := by
    intro t ht
    rw [Function.mem_support] at ht
    have hF : FMaj t ≠ 0 := left_ne_zero_of_mul ht
    have hlt : |t| < sep := by
      by_contra hcon
      exact hF (FMaj_eq_zero (not_lt.mp hcon))
    exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  have hcont : Continuous fun t : ℝ => FMaj t * cos (2 * π * u * t) :=
    continuous_FMaj.mul (by fun_prop)
  have hneg : ∫ t in (-sep)..0, FMaj t * cos (2 * π * u * t)
      = ∫ t in (0 : ℝ)..sep, FMaj t * cos (2 * π * u * t) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := sep)
      (f := fun t : ℝ => FMaj t * cos (2 * π * u * t))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [FMaj_neg, mul_neg, cos_neg]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
    ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (-sep) 0)
      (hcont.intervalIntegrable 0 sep), hneg, integral_FMaj_cos_half]
  ring

/-- The sine transform of the even function `FMaj` vanishes. -/
lemma integral_FMaj_mul_sin (u : ℝ) : ∫ t, FMaj t * sin (2 * π * u * t) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => FMaj t * sin (2 * π * u * t)) volume
  simp only [FMaj_neg, mul_neg, sin_neg, integral_neg] at h
  linarith

/-! ## Fourier inversion -/

/-- `FMaj` as a complex-valued function. -/
noncomputable def FMajC (t : ℝ) : ℂ := (FMaj t : ℂ)

lemma continuous_FMajC : Continuous FMajC :=
  Complex.continuous_ofReal.comp continuous_FMaj

lemma integrable_FMajC : Integrable FMajC :=
  (continuous_FMaj.integrable_of_hasCompactSupport hasCompactSupport_FMaj).ofReal

/-- The Fourier transform of `FMaj` is the majorant. -/
theorem fourier_FMajC (u : ℝ) : 𝓕 FMajC u = ((gMaj u : ℝ) : ℂ) := by
  have hc := integrable_FMaj_mul_cos u
  have hs := integrable_FMaj_mul_sin u
  have hpt : ∀ t : ℝ, Complex.exp (((-2 * π * t * u : ℝ) : ℂ) * Complex.I) • FMajC t
      = ((FMaj t * cos (2 * π * u * t) : ℝ) : ℂ)
        - ((FMaj t * sin (2 * π * u * t) : ℝ) : ℂ) * Complex.I := by
    intro t
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * t * u = -(2 * π * u * t) by ring, cos_neg, sin_neg]
    unfold FMajC
    push_cast
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hpt]
  rw [integral_sub hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, integral_FMaj_mul_sin,
    integral_FMaj_mul_cos]
  simp

/-- **Fourier inversion for the majorant**: the cosine transform of `gMaj` is `FMaj`. -/
theorem integral_gMaj_mul_cos (t : ℝ) : ∫ u, gMaj u * cos (2 * π * t * u) = FMaj t := by
  have hF : 𝓕 FMajC = fun u : ℝ => ((gMaj u : ℝ) : ℂ) := funext fourier_FMajC
  have hinv : 𝓕⁻ (𝓕 FMajC) t = FMajC t :=
    MeasureTheory.Integrable.fourierInv_fourier_eq integrable_FMajC
      (by rw [hF]; exact integrable_gMaj.ofReal) continuous_FMajC.continuousAt
  rw [hF, Real.fourierInv_eq'] at hinv
  have hc := integrable_gMaj_mul_cos t
  have hs := integrable_gMaj_mul_sin t
  have hpt : ∀ v : ℝ, Complex.exp (((2 * π * inner ℝ v t : ℝ) : ℂ) * Complex.I)
        • ((gMaj v : ℝ) : ℂ)
      = ((gMaj v * cos (2 * π * t * v) : ℝ) : ℂ)
        + ((gMaj v * sin (2 * π * t * v) : ℝ) : ℂ) * Complex.I := by
    intro v
    have hin : inner ℝ v t = t * v := by simp
    rw [hin, smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show 2 * π * (t * v) = 2 * π * t * v by ring]
    push_cast
    ring
  simp_rw [hpt] at hinv
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal] at hinv
  have hre := congrArg Complex.re hinv
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    add_zero] at hre
  exact hre.trans (Complex.ofReal_re _)

end RHWeilRecord.MajorantAM.Majorant

namespace RHWeilRecord.MajorantAM

open Majorant

/-- `∫ gMaj = LMaj`. -/
theorem integral_gMaj : ∫ u, gMaj u = LMaj := by
  have h := integral_gMaj_mul_cos 0
  simp only [mul_zero, zero_mul, cos_zero, mul_one] at h
  rw [h, FMaj_zero]

/-- The cosine transform of `gMaj` vanishes at frequencies `|t| ≥ d`. -/
theorem integral_gMaj_cos (t : ℝ) (ht : sep ≤ |t|) :
    ∫ u, gMaj u * cos (2 * π * t * u) = 0 := by
  rw [integral_gMaj_mul_cos, FMaj_eq_zero ht]

end RHWeilRecord.MajorantAM

open Real MeasureTheory

namespace RHWeilRecord.MajorantAM.Taylor

/-! ## Partial sums -/

/-- Partial sum `∑_{k<n} (-1)^k x^{2k}/(2k)!` of the cosine series. -/
def cosPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => cosPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : F)

/-- Partial sum `∑_{k<n} (-1)^k x^{2k+1}/(2k+1)!` of the sine series. -/
def sinPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => sinPoly x n + (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : F)

/-- Partial sum `∑_{k<n} (-1)^k x^{2k}/(2k+1)!` of the series of `sin x / x`. -/
def sincPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => sincPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n + 1).factorial : F)

section Field

variable {F : Type*} [Field F]

lemma cosPoly_succ (x : F) (n : ℕ) :
    cosPoly x (n + 1) = cosPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : F) := rfl

lemma sinPoly_succ (x : F) (n : ℕ) :
    sinPoly x (n + 1) = sinPoly x n + (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : F) :=
  rfl

lemma sincPoly_succ (x : F) (n : ℕ) :
    sincPoly x (n + 1) = sincPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n + 1).factorial : F) :=
  rfl

@[simp] lemma cosPoly_zero (x : F) : cosPoly x 0 = 0 := rfl
@[simp] lemma sinPoly_zero (x : F) : sinPoly x 0 = 0 := rfl
@[simp] lemma sincPoly_zero (x : F) : sincPoly x 0 = 0 := rfl

/-- `sinPoly x n = x * sincPoly x n`. -/
lemma sinPoly_eq_mul_sincPoly (x : F) (n : ℕ) : sinPoly x n = x * sincPoly x n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sinPoly_succ, sincPoly_succ, ih, pow_succ]; ring

end Field

/-- The rational partial sums cast to the real partial sums. -/
lemma cast_cosPoly (q : ℚ) (n : ℕ) : ((cosPoly q n : ℚ) : ℝ) = cosPoly (q : ℝ) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [cosPoly_succ, cosPoly_succ, ← ih]; push_cast; rfl

/-- The rational partial sums cast to the real partial sums. -/
lemma cast_sincPoly (q : ℚ) (n : ℕ) : ((sincPoly q n : ℚ) : ℝ) = sincPoly (q : ℝ) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sincPoly_succ, sincPoly_succ, ← ih]; push_cast; rfl

/-! ## Values at zero and parity -/

lemma sinPoly_at_zero (n : ℕ) : sinPoly (0 : ℝ) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sinPoly_succ, ih]; simp

lemma cosPoly_at_zero (n : ℕ) : cosPoly (0 : ℝ) (n + 1) = 1 := by
  induction n with
  | zero => simp [cosPoly_succ]
  | succ n ih => rw [cosPoly_succ, ih]; simp

lemma sincPoly_at_zero (n : ℕ) : sincPoly (0 : ℝ) (n + 1) = 1 := by
  induction n with
  | zero => simp [sincPoly_succ]
  | succ n ih => rw [sincPoly_succ, ih]; simp

lemma cosPoly_abs (x : ℝ) (n : ℕ) : cosPoly |x| n = cosPoly x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cosPoly_succ, cosPoly_succ, ih, pow_mul, sq_abs, ← pow_mul]

lemma sincPoly_abs (x : ℝ) (n : ℕ) : sincPoly |x| n = sincPoly x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sincPoly_succ, sincPoly_succ, ih, pow_mul, sq_abs, ← pow_mul]

/-! ## Derivatives -/

lemma hasDerivAt_sinPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => sinPoly y n) (cosPoly x n) x := by
  induction n with
  | zero => exact hasDerivAt_const x (0 : ℝ)
  | succ n ih =>
    have h : HasDerivAt (fun y : ℝ => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        ((-1) ^ n * (((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n + 1 - 1)) / ((2 * n + 1).factorial : ℝ)) x :=
      ((hasDerivAt_pow (2 * n + 1) x).const_mul ((-1 : ℝ) ^ n)).div_const _
    have h1 : HasDerivAt (fun y : ℝ => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        ((-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ)) x := by
      refine h.congr_deriv ?_
      have hc : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul, mul_left_comm,
        mul_div_mul_left _ _ hc]
    exact ih.add h1

lemma hasDerivAt_cosPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosPoly y (n + 1)) (-sinPoly x n) x := by
  induction n with
  | zero =>
    have h : (fun y : ℝ => cosPoly y (0 + 1)) = fun _ => (1 : ℝ) := by
      funext y; simp [cosPoly_succ]
    rw [h]
    simpa using hasDerivAt_const x (1 : ℝ)
  | succ n ih =>
    have h : HasDerivAt
        (fun y : ℝ => (-1) ^ (n + 1) * y ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1).factorial : ℝ))
        ((-1) ^ (n + 1) * (((2 * n + 1 + 1 : ℕ) : ℝ) * x ^ (2 * n + 1 + 1 - 1))
          / ((2 * n + 1 + 1).factorial : ℝ)) x :=
      ((hasDerivAt_pow (2 * n + 1 + 1) x).const_mul ((-1 : ℝ) ^ (n + 1))).div_const _
    have h1 : HasDerivAt
        (fun y : ℝ => (-1) ^ (n + 1) * y ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1).factorial : ℝ))
        (-((-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) x := by
      refine h.congr_deriv ?_
      have hc : ((2 * n + 1 + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [Nat.factorial_succ (2 * n + 1), Nat.add_sub_cancel, Nat.cast_mul, mul_left_comm,
        mul_div_mul_left _ _ hc, pow_succ ((-1 : ℝ)) n]
      ring
    have h2 := ih.add h1
    rw [← neg_add] at h2
    exact h2

/-! ## The alternating enclosures -/

/-- A differentiable function vanishing at `0` with nonnegative derivative on `[0, ∞)` is
nonnegative on `[0, ∞)`. -/
private lemma nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) :
    ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt).continuousOn
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      exact hpos y (le_of_lt hy)
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h0] at h
  exact h

/-- The signs of the Taylor remainders of `cos` and `sin` on `[0, ∞)`: with `m + 1` terms the
partial sum minus the function has the sign `(-1)^m`. -/
theorem taylor_sign (m : ℕ) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (cosPoly x (m + 1) - cos x)) ∧
    (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (sinPoly x (m + 1) - sin x)) := by
  -- the sine statement follows from the cosine statement of the same order
  have step : ∀ m : ℕ, (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (cosPoly x (m + 1) - cos x)) →
      ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (sinPoly x (m + 1) - sin x) := by
    intro m hc
    refine nonneg_of_hasDerivAt (f := fun y => (-1 : ℝ) ^ m * (sinPoly y (m + 1) - sin y))
      (f' := fun y => (-1 : ℝ) ^ m * (cosPoly y (m + 1) - cos y)) ?_ ?_ hc
    · simp [sinPoly_at_zero]
    · intro y
      have h : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ m * (sinPoly z (m + 1) - sin z))
          ((-1 : ℝ) ^ m * (cosPoly y (m + 1) - cos y)) y :=
        ((hasDerivAt_sinPoly (m + 1) y).sub (hasDerivAt_sin y)).const_mul _
      exact h
  induction m with
  | zero =>
    have hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ 0 * (cosPoly x (0 + 1) - cos x) := by
      intro x _
      have h1 : cosPoly x (0 + 1) = 1 := by rw [cosPoly_succ, cosPoly_zero]; simp
      rw [h1, pow_zero, one_mul]
      linarith [cos_le_one x]
    exact ⟨hc, step 0 hc⟩
  | succ m ih =>
    have hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ (m + 1) * (cosPoly x (m + 1 + 1) - cos x) := by
      refine nonneg_of_hasDerivAt
        (f := fun y => (-1 : ℝ) ^ (m + 1) * (cosPoly y (m + 1 + 1) - cos y))
        (f' := fun y => (-1 : ℝ) ^ m * (sinPoly y (m + 1) - sin y)) ?_ ?_ ih.2
      · simp [cosPoly_at_zero]
      · intro y
        have h : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ (m + 1) * (cosPoly z (m + 1 + 1) - cos z))
            ((-1 : ℝ) ^ (m + 1) * (-sinPoly y (m + 1) - -sin y)) y :=
          ((hasDerivAt_cosPoly (m + 1) y).sub (hasDerivAt_cos y)).const_mul _
        refine h.congr_deriv ?_
        rw [pow_succ]
        ring
    exact ⟨hc, step (m + 1) hc⟩

/-- Upper Taylor bound for `cos`, valid for every real `x`. -/
theorem cos_le_cosPoly (x : ℝ) (n : ℕ) : cos x ≤ cosPoly x (2 * n + 1) := by
  have h := (taylor_sign (2 * n)).1 |x| (abs_nonneg x)
  rw [Even.neg_one_pow (even_two_mul n), one_mul, cosPoly_abs, cos_abs] at h
  linarith

/-- Lower Taylor bound for `cos`, valid for every real `x`. -/
theorem cosPoly_le_cos (x : ℝ) (n : ℕ) : cosPoly x (2 * n + 2) ≤ cos x := by
  have h : 0 ≤ (-1 : ℝ) ^ (2 * n + 1) * (cosPoly |x| (2 * n + 2) - cos |x|) :=
    (taylor_sign (2 * n + 1)).1 |x| (abs_nonneg x)
  rw [Odd.neg_one_pow (odd_two_mul_add_one n), cosPoly_abs, cos_abs] at h
  linarith

/-- Upper Taylor bound for `sin` on `[0, ∞)`. -/
theorem sin_le_sinPoly {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : sin x ≤ sinPoly x (2 * n + 1) := by
  have h := (taylor_sign (2 * n)).2 x hx
  rw [Even.neg_one_pow (even_two_mul n), one_mul] at h
  linarith

/-- Lower Taylor bound for `sin` on `[0, ∞)`. -/
theorem sinPoly_le_sin {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : sinPoly x (2 * n + 2) ≤ sin x := by
  have h : 0 ≤ (-1 : ℝ) ^ (2 * n + 1) * (sinPoly x (2 * n + 2) - sin x) :=
    (taylor_sign (2 * n + 1)).2 x hx
  rw [Odd.neg_one_pow (odd_two_mul_add_one n)] at h
  linarith

lemma sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact sinc_neg x

/-- Lower Taylor bound for `sinc`, valid for every real `x`. -/
theorem sincPoly_le_sinc (x : ℝ) (n : ℕ) : sincPoly x (2 * n + 2) ≤ sinc x := by
  rw [← sincPoly_abs, ← sinc_abs]
  rcases eq_or_lt_of_le (abs_nonneg x) with h0 | hpos
  · rw [← h0, sinc_zero]
    exact le_of_eq (sincPoly_at_zero (2 * n + 1))
  · rw [sinc_of_ne_zero (ne_of_gt hpos), le_div_iff₀ hpos,
      mul_comm (sincPoly |x| (2 * n + 2)) |x|, ← sinPoly_eq_mul_sincPoly]
    exact sinPoly_le_sin (le_of_lt hpos) n

end RHWeilRecord.MajorantAM.Taylor

namespace RHWeilRecord.MajorantAM.Majorant

/-! ## The quadratic form -/

/-- The quadratic form `∑_{i,j} x_i x_j cos(2π (y_i - y_j) u)`. -/
noncomputable def quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * cos (2 * π * (y i - y j) * u)

/-- The quadratic form is `|∑ x_i e^{2π i y_i u}|²`. -/
lemma quadForm_eq {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) :
    quadForm y x u = (∑ i, x i * cos (2 * π * y i * u)) ^ 2
      + (∑ i, x i * sin (2 * π * y i * u)) ^ 2 := by
  unfold quadForm
  rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * π * (y i - y j) * u = 2 * π * y i * u - 2 * π * y j * u by ring, cos_sub]
  ring

lemma quadForm_nonneg {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) : 0 ≤ quadForm y x u := by
  rw [quadForm_eq]
  positivity

lemma continuous_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) : Continuous (quadForm y x) := by
  have h : Continuous fun u : ℝ => ∑ i, ∑ j, x i * x j * cos (2 * π * (y i - y j) * u) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop
  exact h

lemma integrable_gMaj_mul_term (a c : ℝ) :
    Integrable fun u : ℝ => gMaj u * (c * cos (2 * π * a * u)) := by
  have h := (integrable_gMaj_mul_cos a).const_mul c
  have e : (fun u : ℝ => gMaj u * (c * cos (2 * π * a * u)))
      = fun u : ℝ => c * (gMaj u * cos (2 * π * a * u)) := by
    funext u; ring
  rw [e]
  exact h

lemma quadForm_expand {ι : Type} [Fintype ι] (y x : ι → ℝ) :
    (fun u : ℝ => gMaj u * quadForm y x u)
      = fun u : ℝ => ∑ i, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) := by
  funext u
  simp only [quadForm, Finset.mul_sum]

lemma integrable_gMaj_mul_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) :
    Integrable fun u : ℝ => gMaj u * quadForm y x u := by
  rw [quadForm_expand]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_gMaj_mul_term (y i - y j) (x i * x j)

/-- On a `sep`-separated set the majorant gives the quadratic form `LMaj ∑ x_i²`. -/
theorem integral_gMaj_mul_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |y i - y j|) :
    ∫ u, gMaj u * quadForm y x u = LMaj * ∑ i, x i ^ 2 := by
  classical
  have hval : ∀ i j, ∫ u, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u))
      = if i = j then LMaj * x i ^ 2 else 0 := by
    intro i j
    have e : (fun u : ℝ => gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)))
        = fun u : ℝ => x i * x j * (gMaj u * cos (2 * π * (y i - y j) * u)) := by
      funext u; ring
    rw [e, integral_const_mul]
    split_ifs with hij
    · subst hij
      rw [sub_self, integral_gMaj_mul_cos, FMaj_zero]
      ring
    · rw [integral_gMaj_cos _ (hsep i j hij), mul_zero]
  rw [quadForm_expand]
  calc ∫ u, ∑ i, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u))
      = ∑ i, ∫ u, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          integrable_gMaj_mul_term (y i - y j) (x i * x j)
    _ = ∑ i, ∑ j, ∫ u, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
          integrable_gMaj_mul_term (y i - y j) (x i * x j)
    _ = ∑ i, ∑ j, if i = j then LMaj * x i ^ 2 else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hval i j
    _ = ∑ i, LMaj * x i ^ 2 := Finset.sum_congr rfl fun i _ => by simp
    _ = LMaj * ∑ i, x i ^ 2 := (Finset.mul_sum _ _ _).symm

end RHWeilRecord.MajorantAM.Majorant

namespace RHWeilRecord.MajorantAM

open Majorant

/-- **The separated bound**: a measurable weight below the majorant has quadratic form at most
`LMaj` on every `sep`-separated finite set. -/
theorem separatedBound {ι : Type} [Fintype ι] (y x : ι → ℝ) (w : ℝ → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |y i - y j|) (hw : Measurable w)
    (hw0 : ∀ u, 0 ≤ w u) (hwg : ∀ u, w u ≤ gMaj u) :
    (∫ u, w u * Majorant.quadForm y x u) ≤ LMaj * ∑ i, x i ^ 2 := by
  have hDnn := quadForm_nonneg y x
  have hgD := integrable_gMaj_mul_quadForm y x
  have hwD : Integrable fun u : ℝ => w u * quadForm y x u := by
    refine hgD.mono' (hw.mul (continuous_quadForm y x).measurable).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 u) (hDnn u))]
    exact mul_le_mul_of_nonneg_right (hwg u) (hDnn u)
  have h1 : ∫ u, w u * quadForm y x u ≤ ∫ u, gMaj u * quadForm y x u :=
    integral_mono hwD hgD fun u => mul_le_mul_of_nonneg_right (hwg u) (hDnn u)
  rw [integral_gMaj_mul_quadForm y x hsep] at h1
  exact h1

end RHWeilRecord.MajorantAM

namespace RHWeilRecord.MajorantAM

/-- The normalization of the *original AM* sharp density. -/
def ZAM : ℝ := AMW.MAM * AMW.aInf

def fAM (u : ℝ) : ℝ := if |u| ≤ 1/2 then AMW.vAM u / ZAM else 0

lemma ZAM_eq : ZAM = Real.sinc (Real.sqrt 2 / 2) := by
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : ZAM = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
    rw [ZAM, AMW.aInf_eq]
    field_simp [AMW.MAM_pos.ne']
  rw [he, Real.sinc_of_ne_zero (div_ne_zero hs (by norm_num))]
  apply (eq_div_iff (div_ne_zero hs (by norm_num))).2
  calc Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2)
      = Real.sqrt 2 ^ 2 / 2 * Real.sin (Real.sqrt 2 / 2) := by ring
    _ = Real.sin (Real.sqrt 2 / 2) := by rw [hsq]; ring

lemma ZAM_ge : (11:ℝ)/12 ≤ ZAM := by
  rw [ZAM_eq]
  have h := Taylor.sincPoly_le_sinc (Real.sqrt 2 / 2) 0
  norm_num [Taylor.sincPoly] at h
  have hsq : (Real.sqrt 2 / 2) ^ 2 = (1:ℝ)/2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [hsq] at h
  linarith

lemma ZAM_pos : 0 < ZAM := lt_of_lt_of_le (by norm_num) ZAM_ge

lemma fAM_nonneg (u : ℝ) : 0 ≤ fAM u := by
  unfold fAM
  split_ifs with hu
  · exact div_nonneg (le_trans (by norm_num) (AMW.vAM_ge_core hu)) ZAM_pos.le
  · exact le_rfl

lemma cos_sqrt_two_upper (u : ℝ) :
    Real.cos (Real.sqrt 2 * u) ≤ 1 - u^2 + u^4/6 := by
  have h := Taylor.cos_le_cosPoly (Real.sqrt 2 * u) 1
  norm_num [Taylor.cosPoly] at h
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hfour : Real.sqrt 2 ^ 4 = 4 := by
    calc Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2)^2 := by ring
      _ = 4 := by rw [hsq]; norm_num
  simp only [mul_pow, hsq, hfour] at h
  linarith

lemma fAM_upper {u : ℝ} (hu : |u| ≤ 1/2) :
    fAM u ≤ (12:ℝ)/11 * (1 - u^2 + u^4/6 + 13/200) := by
  have hnum : AMW.vAM u ≤ 1 - u^2 + u^4/6 + 13/200 := by
    rw [AMW.vAM_eq]
    linarith [cos_sqrt_two_upper u, (abs_le.mp (AMW.abs_pAM_le u)).2]
  have hv : 0 ≤ AMW.vAM u := (AMW.vAM_ge_core hu).trans' (by norm_num)
  rw [fAM, if_pos hu]
  calc AMW.vAM u / ZAM ≤ AMW.vAM u / ((11:ℝ)/12) :=
      div_le_div_of_nonneg_left hv (by norm_num) ZAM_ge
    _ ≤ (1 - u^2 + u^4/6 + 13/200) / ((11:ℝ)/12) := by
      exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ = (12:ℝ)/11 * (1 - u^2 + u^4/6 + 13/200) := by ring

/-- Coarse rational bounds suffice for the existing continuous Bernstein proof. -/
lemma scaled_pi_sq_bounds :
    (63:ℝ)/10 ≤ (π * sep)^2 ∧ (π * sep)^2 ≤ (633:ℝ)/100 := by
  have hlo := Real.pi_gt_d6
  have hhi := Real.pi_lt_d6
  norm_num at hlo hhi
  have hlow : (314:ℝ)/100 ≤ π := by linarith
  have hhigh : π ≤ (22:ℝ)/7 := by linarith
  have hlo2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 314/100) hlow 2
  have hhi2 := pow_le_pow_left₀ Real.pi_pos.le hhigh 2
  unfold sep
  constructor <;> nlinarith [hlo2, hhi2]

/-- Four-term sinc Taylor polynomial, with no numerical evaluation of sin. -/
lemma sinc_lower (x : ℝ) :
    1 - x^2/6 + x^4/120 - x^6/5040 ≤ Real.sinc x := by
  have h := Taylor.sincPoly_le_sinc x 1
  norm_num [Taylor.sincPoly] at h
  convert h using 1
  ring

/-- The cubic lower polynomial in v=4u². -/
def qLower (v : ℝ) : ℝ := ((27099898207 : ℝ) / 17920000000) * v ^ 0 + ((-1086049379 : ℝ) / 3584000000) * v ^ 1 + ((63630621 : ℝ) / 3584000000) * v ^ 2 + ((-28181793 : ℝ) / 17920000000) * v ^ 3

lemma qLower_formula (v : ℝ) :
    qLower v =
      2 - (633:ℝ)/100/12 + ((63:ℝ)/10)^2/960 - ((633:ℝ)/100)^3/161280
      + (-(633:ℝ)/100/3 + ((63:ℝ)/10)^2/40 - ((633:ℝ)/100)^3/2688)*v/4
      + (((63:ℝ)/10)^2/60 - ((633:ℝ)/100)^3/672)*v^2/16
      - ((633:ℝ)/100)^3/161280*v^3 := by
  unfold qLower
  ring

lemma qLower_ge {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : (6:ℝ)/5 ≤ qLower v := by
  have he : qLower v - (6:ℝ)/5 =
      ((5595898207 : ℝ) / 17920000000) * 1 * v ^ 0 * (1-v) ^ 3 +
      ((5678723863 : ℝ) / 26880000000) * 3 * v ^ 1 * (1-v) ^ 2 +
      ((390334621 : ℝ) / 3360000000) * 3 * v ^ 2 * (1-v) ^ 1 +
      ((14238207 : ℝ) / 560000000) * 1 * v ^ 3 * (1-v) ^ 0 := by
    unfold qLower
    ring
  have hn : 0 ≤ qLower v - (6:ℝ)/5 := by
    rw [he]
    have hh : 0 ≤ 1-v := by linarith
    positivity
  linarith

lemma qLower_square_gap {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    (12:ℝ)/11*(1+13/200) - 3*v/11 + v^2/88 + 1/100
      ≤ gammaM * qLower v ^ 2 := by
  have he : gammaM * qLower v^2
      - ((12:ℝ)/11*(1+13/200) - 3*v/11 + v^2/88) - 1/100 =
      ((78853478378770177763679 : ℝ) / 353239040000000000000000) * 1 * v ^ 0 * (1-v) ^ 6 +
      ((92992806737827008953111 : ℝ) / 529858560000000000000000) * 6 * v ^ 1 * (1-v) ^ 5 +
      ((457400427562429125367 : ℝ) / 3440640000000000000000) * 15 * v ^ 2 * (1-v) ^ 4 +
      ((374777069437800868679 : ℝ) / 3942400000000000000000) * 20 * v ^ 3 * (1-v) ^ 3 +
      ((2543788748160668479333 : ℝ) / 41395200000000000000000) * 15 * v ^ 4 * (1-v) ^ 2 +
      ((65671612297342311037 : ℝ) / 2069760000000000000000) * 6 * v ^ 5 * (1-v) ^ 1 +
      ((1918850296951723679 : ℝ) / 344960000000000000000) * 1 * v ^ 6 * (1-v) ^ 0 := by
    unfold qLower gammaM
    ring
  have hn : 0 ≤ gammaM * qLower v^2
      - ((12:ℝ)/11*(1+13/200) - 3*v/11 + v^2/88) - 1/100 := by
    rw [he]
    have hh : 0 ≤ 1-v := by linarith
    positivity
  linarith

lemma sinc_pair_lower (u : ℝ) :
    qLower (4*u^2) ≤ sincN (sep*(u-1/2)) + sincN (sep*(u+1/2)) := by
  let t : ℝ := π * sep
  let x : ℝ := t^2
  have hx0 : 0 ≤ x := sq_nonneg t
  have hxlo : (63:ℝ)/10 ≤ x := scaled_pi_sq_bounds.1
  have hxhi : x ≤ (633:ℝ)/100 := scaled_pi_sq_bounds.2
  have hx2 : ((63:ℝ)/10)^2 ≤ x^2 :=
    pow_le_pow_left₀ (by norm_num) hxlo 2
  have hx3 : x^3 ≤ ((633:ℝ)/100)^3 := by
    exact pow_le_pow_left₀ hx0 hxhi 3
  have hm := sinc_lower (t*(u-1/2))
  have hp := sinc_lower (t*(u+1/2))
  have hsum :
      2-x*(u^2/3+1/12)+x^2*(u^4/60+u^2/40+1/960)
        -x^3*(u^6/2520+u^4/672+u^2/2688+1/161280)
      ≤ Real.sinc (t*(u-1/2)) + Real.sinc (t*(u+1/2)) := by
    have he :
        (1-(t*(u-1/2))^2/6+(t*(u-1/2))^4/120-(t*(u-1/2))^6/5040)
        +(1-(t*(u+1/2))^2/6+(t*(u+1/2))^4/120-(t*(u+1/2))^6/5040)
        = 2-x*(u^2/3+1/12)+x^2*(u^4/60+u^2/40+1/960)
          -x^3*(u^6/2520+u^4/672+u^2/2688+1/161280) := by
      dsimp [x]; ring
    calc _ = _ := he.symm
      _ ≤ _ := add_le_add hm hp
  have h2 : x*(u^2/3+1/12) ≤ (633:ℝ)/100*(u^2/3+1/12) :=
    mul_le_mul_of_nonneg_right hxhi (by positivity)
  have h4 : ((63:ℝ)/10)^2*(u^4/60+u^2/40+1/960)
      ≤ x^2*(u^4/60+u^2/40+1/960) :=
    mul_le_mul_of_nonneg_right hx2 (by positivity)
  have h6 : x^3*(u^6/2520+u^4/672+u^2/2688+1/161280)
      ≤ ((633:ℝ)/100)^3*(u^6/2520+u^4/672+u^2/2688+1/161280) :=
    mul_le_mul_of_nonneg_right hx3 (by positivity)
  have hq : qLower (4*u^2) =
      2-(633:ℝ)/100*(u^2/3+1/12)+((63:ℝ)/10)^2*(u^4/60+u^2/40+1/960)
        -((633:ℝ)/100)^3*(u^6/2520+u^4/672+u^2/2688+1/161280) := by
    rw [qLower_formula]; ring
  rw [hq]
  unfold sincN
  have ht : ∀ z : ℝ, π*(sep*z) = t*z := by intro z; dsimp [t]; ring
  rw [ht, ht]
  linarith

/-- Existing AM pointwise majorant, proved on the entire real line. -/
theorem fAM_le_gMaj (u : ℝ) : fAM u ≤ gMaj u := by
  by_cases hu : |u| ≤ 1/2
  · have hv0 : 0 ≤ 4*u^2 := by positivity
    have hv1 : 4*u^2 ≤ 1 := by
      have hh := abs_le.mp hu
      nlinarith
    have hq := qLower_ge hv0 hv1
    have hpair := sinc_pair_lower u
    have hsq : qLower (4*u^2)^2 ≤
        (sincN (sep*(u-1/2)) + sincN (sep*(u+1/2)))^2 := by
      exact pow_le_pow_left₀ (by linarith) hpair 2
    have hgap := qLower_square_gap hv0 hv1
    have hup := fAM_upper hu
    unfold gMaj
    have hg : gammaM*qLower (4*u^2)^2 ≤
        gammaM*(sincN (sep*(u-1/2)) + sincN (sep*(u+1/2)))^2 :=
      mul_le_mul_of_nonneg_left hsq Majorant.gammaM_nonneg
    nlinarith
  · rw [fAM, if_neg hu]
    exact gMaj_nonneg u

/-- The Fourier mass at the actual parameters is below 2. -/
theorem lMajBound : LMaj ≤ (61:ℝ)/32 := by
  have hsin : Real.sin (π*sep) = Real.sin (π/5) := by
    rw [← Real.sin_pi_sub]
    congr 1
    unfold sep
    ring
  have hx : 0 < π*sep := mul_pos Real.pi_pos Majorant.sep_pos
  have hsc : sincN sep ≤ (1:ℝ)/4 := by
    unfold sincN
    rw [Real.sinc_of_ne_zero hx.ne', div_le_iff₀ hx, hsin]
    have h := Taylor.sin_le_sinPoly (by positivity : (0:ℝ) ≤ π/5) 0
    norm_num [Taylor.sinPoly] at h
    unfold sep
    linarith
  unfold sep at hsc
  unfold LMaj sep gammaM
  linarith

end RHWeilRecord.MajorantAM

namespace RHWeilRecord.MajorantAM

/-- The actual realised AM weight; its scale is 1/aInf, never 5/2. -/
def wSep (ϱ : ℝ → ℝ) (L w s : ℝ) : ℝ :=
  AMW.phiW ϱ L w (L*s)^2 / AMW.aInf

lemma wSep_nonneg (ϱ : ℝ → ℝ) (L w s : ℝ) : 0 ≤ wSep ϱ L w s :=
  div_nonneg (sq_nonneg _) AMW.aInf_pos.le

lemma wSep_measurable {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hwL : 2*w ≤ L) :
    Measurable (wSep ϱ L w) := by
  have hc : Continuous (wSep ϱ L w) :=
    (((AMW.phiW_continuous hϱ hw hwL).comp
      (continuous_const.mul continuous_id)).pow 2).div_const _
  exact hc.measurable

/-- The taper is below the *same AM* sharp density before normalization. -/
lemma wSep_le_fAM {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (s : ℝ) :
    wSep ϱ L w s ≤ fAM s := by
  by_cases hs : |s| ≤ 1/2
  · have ht0 := Zeta23.Taper.phi_nonneg hϱ (L*s) (L := L) (w := w)
    have ht1 := Zeta23.Taper.phi_le_one hϱ (L*s) (L := L) (w := w)
    have ht : Zeta23.Taper.phi ϱ L w (L*s)^2 ≤ 1 := pow_le_one₀ ht0 ht1
    have hv : 0 ≤ AMW.vAM s := le_trans (by norm_num) (AMW.vAM_ge_core hs)
    have he : (L*s)/L = s := by field_simp
    rw [wSep, AMW.phiW_sq_eq hϱ hw hL, AMW.hW, he, fAM, if_pos hs, ZAM]
    have hmul : AMW.vAM s / AMW.MAM * Zeta23.Taper.phi ϱ L w (L*s)^2
        ≤ AMW.vAM s / AMW.MAM :=
      (mul_le_mul_of_nonneg_left ht (div_nonneg hv AMW.MAM_pos.le)).trans_eq (mul_one _)
    calc (AMW.vAM s / AMW.MAM * Zeta23.Taper.phi ϱ L w (L*s)^2) / AMW.aInf
        ≤ (AMW.vAM s / AMW.MAM) / AMW.aInf :=
          div_le_div_of_nonneg_right hmul AMW.aInf_pos.le
      _ = AMW.vAM s / (AMW.MAM * AMW.aInf) := by rw [div_div]
  · have hsfar : L/2 ≤ |L*s| := by
      rw [abs_mul, abs_of_pos hL]
      nlinarith [lt_of_not_ge hs]
    rw [wSep, AMW.phiW_eq_zero hϱ hw hsfar, fAM, if_neg hs]
    simp

lemma wSep_le_gMaj {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (s : ℝ) :
    wSep ϱ L w s ≤ gMaj s :=
  (wSep_le_fAM hϱ hw hL s).trans (fAM_le_gMaj s)

/-- A genuinely separated realised AM weight, with every finite set and coefficient vector. -/
theorem actual_weight_separated {ϱ : ℝ → ℝ} {L w : ℝ}
    (hϱ : Zeta23.TaperProfile ϱ) (hw : 0 < w) (hwL : 2*w ≤ L)
    {ι : Type} [Fintype ι] (y x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |y i-y j|) :
    (∫ s, AMW.phiW ϱ L w (L*s)^2 * Majorant.quadForm y x s)
      ≤ AMW.aInf * LMaj * ∑ i, x i^2 := by
  have hL : 0 < L := by linarith
  have hs := separatedBound y x (wSep ϱ L w) hsep
    (wSep_measurable hϱ hw hwL) (wSep_nonneg ϱ L w)
    (wSep_le_gMaj hϱ hw hL)
  have he : (fun s => AMW.phiW ϱ L w (L*s)^2 * Majorant.quadForm y x s)
      = fun s => AMW.aInf * (wSep ϱ L w s * Majorant.quadForm y x s) := by
    funext s
    unfold wSep
    field_simp [AMW.aInf_pos.ne']
  rw [he, integral_const_mul]
  calc AMW.aInf * (∫ s, wSep ϱ L w s * Majorant.quadForm y x s)
      ≤ AMW.aInf * (LMaj * ∑ i, x i^2) :=
        mul_le_mul_of_nonneg_left hs AMW.aInf_pos.le
    _ = AMW.aInf * LMaj * ∑ i, x i^2 := by ring

/-- The strict clipping guard is an ordinary positive normalization fact. -/
theorem normalized_mass_lt_two {a : ℝ} (ha : (61:ℝ)/64 * AMW.aInf < a) :
    AMW.aInf / a * LMaj < 2 := by
  have ha0 : 0 < a := lt_trans (mul_pos (by norm_num) AMW.aInf_pos) ha
  have hmul : AMW.aInf / a * LMaj ≤ AMW.aInf / a * ((61:ℝ)/32) :=
    mul_le_mul_of_nonneg_left lMajBound (div_nonneg AMW.aInf_pos.le ha0.le)
  have hstrict : AMW.aInf / a * ((61:ℝ)/32) < 2 := by
    have he : AMW.aInf/a*((61:ℝ)/32) = (AMW.aInf*((61:ℝ)/32))/a := by ring
    rw [he, div_lt_iff₀ ha0]
    linarith
  exact hmul.trans_lt hstrict

/-- The guard follows from the already proved convergence of the actual AM taper mass. -/
theorem eventually_normalized_mass_lt_two {P : Zeta23.Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, AMW.aInf / (AMW.atAM P T).a T * LMaj < 2 := by
  have hbound : (61:ℝ)/64 * AMW.aInf < AMW.aInf := by
    nlinarith [AMW.aInf_pos]
  have ht := (AMW.tendsto_aW hP).eventually (lt_mem_nhds hbound)
  filter_upwards [ht] with T hT
  apply normalized_mass_lt_two
  rw [AMW.atAM_a hP T]
  exact hT

end RHWeilRecord.MajorantAM

namespace RHWeilRecord.MajorantAM.Actual
open Zeta23

/-- The real part of the transform of a real, continuous, compactly supported function is its
cosine transform. -/
lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Continuous g) (hs : HasCompactSupport g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * Real.cos (r * u) := by
  exact Zeta23Ext.Bridge.re_paperFT_ofReal
    (hg.integrable_of_hasCompactSupport hs) r

/-- `Φ(r) = ∫ v(u)² cos(r u) du` for a window of the class. -/
lemma VPhiR_eq_integral {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (r : ℝ) :
    AdmWindow.VPhiR v r = ∫ u, v u ^ 2 * Real.cos (r * u) :=
  re_paperFT_ofReal hW.sq_continuous hW.sq_hasCompactSupport r

/-- Integrability of the integrand of the cosine form. -/
lemma integrable_sq_mul_cos {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (r : ℝ) :
    Integrable (fun u => v u ^ 2 * Real.cos (r * u)) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hW.sq_continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))) ?_
  refine hW.sq_hasCompactSupport.mono fun u hu => ?_
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  rw [h0, zero_mul]


/-- A nonnegative series dominates its partial sum over `0 ≤ k < d`. -/
lemma sum_fin_le_hasSum {f : ℤ → ℝ} {S : ℝ} (d : ℕ) (hf : HasSum f S) (h0 : ∀ k, 0 ≤ f k) :
    ∑ k : Fin d, f ((k : ℕ) : ℤ) ≤ S := by
  classical
  have e : ∑ k : Fin d, f ((k : ℕ) : ℤ)
      = ∑ k ∈ (Finset.range d).map Nat.castEmbedding, f k := by
    rw [Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d
  rw [e]
  exact sum_le_hasSum _ (fun k _ => h0 k) hf

/-- Poisson summation for the square of a linear combination of shifted transforms:
`∑_{k ∈ ℤ} (∑_i x_i φ̂(γ_i - τ_k))² = L ∑_{i,j} x_i x_j Φ(γ_i - γ_j)`. -/
lemma hasSum_sq_comb {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c) (T : ℝ)
    {ι : Type*} [Fintype ι] (γ x : ι → ℝ) :
    HasSum (fun k : ℤ => (∑ i, x i * AdmWindow.vHatR v (γ i - (T + k * (2 * π / L)))) ^ 2)
      (L * ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR v (γ i - γ j)) := by
  have h : HasSum (fun k : ℤ => ∑ i, ∑ j, x i * x j *
        (AdmWindow.vHatR v (γ i - (T + k * (2 * π / L)))
          * AdmWindow.vHatR v (γ j - (T + k * (2 * π / L)))))
      (∑ i, ∑ j, x i * x j * (L * AdmWindow.VPhiR v (γ i - γ j))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (hW.hasSum_vHatR_mul T (γ i) (γ j)).mul_left (x i * x j)
  convert h using 1
  · funext k
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The quadratic form of `Φ` as an integral against `φ²`:
`∑_{i,j} x_i x_j Φ(γ_i - γ_j) = ∫ φ(u)² ∑_{i,j} x_i x_j cos((γ_i - γ_j) u) du`. -/
lemma sum_VPhiR_eq_integral {v : ℝ → ℝ} {L w c : ℝ} (hW : AdmWindow v L w c)
    {ι : Type*} [Fintype ι] (γ x : ι → ℝ) :
    ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR v (γ i - γ j)
      = ∫ u, v u ^ 2 * ∑ i, ∑ j, x i * x j * Real.cos ((γ i - γ j) * u) := by
  have hint : ∀ i j,
      Integrable (fun u => x i * x j * (v u ^ 2 * Real.cos ((γ i - γ j) * u))) :=
    fun i j => (integrable_sq_mul_cos hW (γ i - γ j)).const_mul _
  calc ∑ i, ∑ j, x i * x j * AdmWindow.VPhiR v (γ i - γ j)
      = ∑ i, ∑ j, ∫ u, x i * x j * (v u ^ 2 * Real.cos ((γ i - γ j) * u)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [VPhiR_eq_integral hW, integral_const_mul]
    _ = ∫ u, ∑ i, ∑ j, x i * x j * (v u ^ 2 * Real.cos ((γ i - γ j) * u)) := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => hint i j]
    _ = ∫ u, v u ^ 2 * ∑ i, ∑ j, x i * x j * Real.cos ((γ i - γ j) * u) := by
        refine integral_congr_ae (ae_of_all _ fun u => ?_)
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring

/-- Substitution `u = L s`: `∫ g(u) du = L ∫ g(L s) ds` for `L > 0`. -/
lemma integral_eq_mul_integral_comp (g : ℝ → ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u, g u = L * ∫ s, g (L * s) := by
  rw [Measure.integral_comp_mul_left g L, smul_eq_mul, abs_of_pos (inv_pos.mpr hL), ← mul_assoc,
    mul_inv_cancel₀ hL.ne', one_mul]


/-- All finite frequency packets are bounded by the actual AM separated envelope.
The left side is the original finite lattice Gram quadratic form, with no change of window. -/
theorem actual_transform_bound {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8*P.w ≤ P.L T) (ha : 0 < (AMW.atAM P T).a T)
    (d : ℕ) {ι : Type} [Fintype ι] (γ x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |γ i * P.L T/(2*π)-γ j * P.L T/(2*π)|) :
    ((AMW.atAM P T).a T * (P.L T)^2)⁻¹ *
        ∑ k : Fin d, (∑ i, x i * AdmWindow.vHatR (AMW.WAM P T)
          (γ i-(T+((k:ℕ):ℤ)*(2*π/P.L T))))^2
      ≤ AMW.aInf / (AMW.atAM P T).a T * LMaj * ∑ i, x i^2 := by
  let L := P.L T
  let a := (AMW.atAM P T).a T
  have hW := AMW.admWindow_WAM hP T h8
  have hL : 0 < L := hW.L_pos
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  have hB := sum_fin_le_hasSum d (hasSum_sq_comb hW T γ x) (fun _ => sq_nonneg _)
  let y : ι → ℝ := fun i => γ i * L/(2*π)
  have hD : (∑ i, ∑ j, x i*x j*AdmWindow.VPhiR (AMW.WAM P T) (γ i-γ j))
      = L * (∫ s, AMW.phiW P.ϱ L P.w (L*s)^2 * Majorant.quadForm y x s) := by
    rw [sum_VPhiR_eq_integral hW γ x,
      integral_eq_mul_integral_comp
        (fun u => AMW.WAM P T u^2 * ∑ i, ∑ j, x i*x j*cos ((γ i-γ j)*u)) hL]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    have harg : ∀ i j, (γ i-γ j)*(L*s) = 2*π*(y i-y j)*s := by
      intro i j
      dsimp [y]
      field_simp
    simp only [harg, AMW.WAM, Majorant.quadForm, L]
  have hE := actual_weight_separated hP.taper hw (by linarith : 2*P.w ≤ L) y x hsep
  have ha' : 0 < a := ha
  have hc : 0 < a*L^2 := by positivity
  change (a*L^2)⁻¹ * _ ≤ _
  calc (a*L^2)⁻¹ * ∑ k : Fin d,
        (∑ i, x i*AdmWindow.vHatR (AMW.WAM P T)
          (γ i-(T+((k:ℕ):ℤ)*(2*π/L))))^2
      ≤ (a*L^2)⁻¹ * (L * (L * (AMW.aInf * LMaj * ∑ i, x i^2))) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
        apply hB.trans
        rw [hD]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE hL.le) hL.le
    _ = AMW.aInf/a * LMaj * ∑ i, x i^2 := by
      field_simp

/-- On the existing eventual taper guard, the original finite separated Gram form is <2.
A zero coefficient vector gives ≤2, as required for the spectral clipping argument. -/
theorem eventually_actual_transform_le_two {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, ∀ (d : ℕ) (ι : Type) [Fintype ι] (γ x : ι → ℝ),
      (∀ i j, i ≠ j → sep ≤ |γ i*P.L T/(2*π)-γ j*P.L T/(2*π)|) →
      ((AMW.atAM P T).a T * (P.L T)^2)⁻¹ *
        ∑ k : Fin d, (∑ i, x i * AdmWindow.vHatR (AMW.WAM P T)
          (γ i-(T+((k:ℕ):ℤ)*(2*π/P.L T))))^2 ≤ 2 * ∑ i, x i^2 := by
  filter_upwards [AMW.eventually_w32 hP, AMW.eventually_aAM_range hP,
    eventually_normalized_mass_lt_two hP] with T h32 ha hnorm
  intro d ι _ γ x hsep
  have hab : 0 < (AMW.atAM P T).a T := by linarith [ha.1]
  have h := actual_transform_bound hP T (by linarith [hP.one_le_w]) hab d γ x hsep
  exact h.trans (mul_le_mul_of_nonneg_right hnorm.le (Finset.sum_nonneg fun _ _ => sq_nonneg _))

end RHWeilRecord.MajorantAM.Actual

#print axioms RHWeilRecord.MajorantAM.fAM_le_gMaj
#print axioms RHWeilRecord.MajorantAM.integral_gMaj_cos
#print axioms RHWeilRecord.MajorantAM.lMajBound
#print axioms RHWeilRecord.MajorantAM.Actual.eventually_actual_transform_le_two
