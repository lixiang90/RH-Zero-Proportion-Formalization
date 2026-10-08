import Mathlib
import RecordProportion.ImportedAM
import RecordProportion.Majorant

/-!
Finite analytic interfaces for the c260 record submission.

These are proved helper lemmas, not a proof of the challenge.  They add no
axioms or admitted facts.  The actual AM window, PC8 coverage, nine-point
certificate and dyadic zero-side assembly must supply their hypotheses.
-/

noncomputable section

open scoped BigOperators ComplexOrder
open Matrix Finset RHLinalg Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.StableRankTrace

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

/-!
This section consumes the original AM all-zero seam.  Its conditional dyadic
theorem exposes the one missing lossless defect estimate; it does not assert
that the new local numerical certificate has already been formalized.
-/

namespace RHWeilRecord

open Matrix Finset RHLinalg Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.StableRankTrace
open scoped ComplexOrder

/-- The clipping-at-two functional underlying the original AM defect. -/
def clipTwo (t : ℝ) : ℝ := if t ≤ 2 then t ^ 2 else 4 * t - 4

theorem psi_clipTwo_identity (t : ℝ) :
    Psi t = clipTwo t - 2 * t + 1 := by
  unfold Psi clipTwo
  split_ifs <;> ring

/-- A real quadratic-form bound controls every complex Hermitian eigenvalue.
Adapted from the real/imaginary Rayleigh argument of
Knausgard's Distinct839.Gram.eigenvalues_le_of_real_form. -/
theorem eigenvalues_le_of_real_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {B : ι → ι → ℝ}
    (hAB : ∀ a b, A a b = (B a b : ℂ)) {c : ℝ}
    (hform : ∀ x : ι → ℝ,
      ∑ a, ∑ b, x a * B a b * x b ≤ c * ∑ a, x a ^ 2) (k : ι) :
    hA.eigenvalues k ≤ c := by
  have h1 : ‖hA.eigenvectorBasis k‖ = 1 := hA.eigenvectorBasis.orthonormal.1 k
  have h2 := EuclideanSpace.norm_eq (hA.eigenvectorBasis k)
  rw [h1] at h2
  have heig := hA.eigenvalues_eq k
  set v : ι → ℂ := ⇑(hA.eigenvectorBasis k) with hv
  have h3 : ∑ a, ‖v a‖ ^ 2 = 1 := Real.sqrt_eq_one.1 h2.symm
  have hnorm : ∑ a, (v a).re ^ 2 + ∑ a, (v a).im ^ 2 = 1 := by
    have h6 : ∀ a, (v a).re ^ 2 + (v a).im ^ 2 = ‖v a‖ ^ 2 := fun a => by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h6 a, h3]
  have heq : hA.eigenvalues k =
      (∑ a, ∑ b, (v a).re * B a b * (v b).re) +
      ∑ a, ∑ b, (v a).im * B a b * (v b).im := by
    rw [heig]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, hAB,
      Finset.mul_sum, map_sum, RCLike.re_to_complex]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  have hre := hform fun a => (v a).re
  have him := hform fun a => (v a).im
  calc hA.eigenvalues k =
      (∑ a, ∑ b, (v a).re * B a b * (v b).re) +
      ∑ a, ∑ b, (v a).im * B a b * (v b).im := heq
    _ ≤ c * ∑ a, (v a).re ^ 2 + c * ∑ a, (v a).im ^ 2 :=
      add_le_add hre him
    _ = c := by rw [← mul_add, hnorm, mul_one]

/-- Under the actual spectral bound two no clipping loss occurs. -/
theorem offdiag_le_defect_of_eigenvalues_le_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (heig : ∀ i, hA.eigenvalues i ≤ 2) :
    offDiagSqOn A univ ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  have hsum : (∑ i, Psi (hA.eigenvalues i)) =
      ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by simp [Psi, heig i]
  have hfrob := frobSq_specMap hA (fun t => t - 1)
  rw [specMap_sub_one] at hfrob
  rw [hsum, ← hfrob]
  exact offDiagSqOn_le_frobSq_sub_one A

/-- The separated operator estimate feeds the defect without block clipping. -/
theorem offdiag_le_defect_of_real_form
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {B : ι → ι → ℝ}
    (hAB : ∀ a b, A a b = (B a b : ℂ))
    (hform : ∀ x : ι → ℝ,
      ∑ a, ∑ b, x a * B a b * x b ≤ 2 * ∑ a, x a ^ 2) :
    offDiagSqOn A univ ≤ defect hA :=
  offdiag_le_defect_of_eigenvalues_le_two hA
    (eigenvalues_le_of_real_form hA hAB hform)

/-- A finite Gram quadratic form is a sum of complete squares. -/
theorem quad_gram_sum_squares
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → κ → ℝ) (x : ι → ℝ) (scale : ℝ) :
    (∑ i, ∑ j, x i * (scale * ∑ k, F i k * F j k) * x j) =
      scale * ∑ k, (∑ i, x i * F i k) ^ 2 := by
  have hterm : ∀ i j,
      x i * (scale * ∑ k, F i k * F j k) * x j =
        ∑ k, scale * ((x i * F i k) * (x j * F j k)) := by
    intro i j
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hterm]
  calc (∑ i, ∑ j, ∑ k, scale * ((x i * F i k) * (x j * F j k))) =
      ∑ i, ∑ k, ∑ j, scale * ((x i * F i k) * (x j * F j k)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, scale * ((x i * F i k) * (x j * F j k)) :=
      Finset.sum_comm
    _ = scale * ∑ k, (∑ i, x i * F i k) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

def amRealEntry (Z : ZeroConfig) (T : ℝ)
    (z z' : retained Z (mtParams T) T) : ℝ :=
  (aL2 (mtParams T) T)⁻¹ *
    ∑ k : Fin ((mtParams T).d T),
      (mtParams T).phiHatR T ((z.1 : ℂ).im - (mtParams T).tau T k) *
      (mtParams T).phiHatR T ((z'.1 : ℂ).im - (mtParams T).tau T k)

theorem am_gram_real_entry (Z : ZeroConfig) (T : ℝ)
    (hc : 0 ≤ aL2 (mtParams T) T) (z z' : retained Z (mtParams T) T) :
    gram Z (mtParams T) T z z' = (amRealEntry Z T z z' : ℂ) :=
  gram_apply Z (mtParams T) T (phiHatReal_atAM P₀_valid T) hc z z'

/-- The actual AM taper majorant, not an abstract stationary replacement,
controls every separated principal Gram quadratic form. -/
theorem eventually_am_real_form_le_two (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ S : Finset (retained Z (mtParams T) T),
      (∀ i j : S, i ≠ j →
        MajorantAM.sep ≤ |xret Z (mtParams T) T i - xret Z (mtParams T) T j|) →
      ∀ v : S → ℝ,
        (∑ i : S, ∑ j : S, v i * amRealEntry Z T i j * v j) ≤ 2 * ∑ i, v i ^ 2 := by
  filter_upwards [MajorantAM.Actual.eventually_actual_transform_le_two P₀_valid] with T hn
  intro S hs v
  let γ : S → ℝ := fun z => (z.1.1 : ℂ).im
  have hsepγ : ∀ i j : S, i ≠ j →
      MajorantAM.sep ≤ |γ i * P₀.L T / (2 * Real.pi) -
        γ j * P₀.L T / (2 * Real.pi)| := by
    intro i j hij
    have harg : γ i * P₀.L T / (2 * Real.pi) - γ j * P₀.L T / (2 * Real.pi) =
        xret Z (mtParams T) T i - xret Z (mtParams T) T j := by
      dsimp [γ, xret, xnorm, mtParams, P₀]
      ring
    rw [harg]
    exact hs i j hij
  have hactual := hn ((mtParams T).d T) S γ v hsepγ
  have hφ : (mtParams T).phiHatR T = AdmWindow.vHatR (AMW.WAM P₀ T) :=
    atAM_phiHatR_eq P₀_valid T
  have hτ : ∀ k : Fin ((mtParams T).d T),
      (mtParams T).tau T k = T + (k : ℤ) * (2 * Real.pi / P₀.L T) := fun k => rfl
  unfold amRealEntry
  rw [quad_gram_sum_squares]
  simp only [aL2, hφ, hτ]
  exact hactual

/-- The exact off-diagonal energy of every actual separated retained subset
is paid by its own Psi defect. Cross-block cancellation is left to pinching. -/
theorem eventually_am_separated_offdiag_le_defect (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ S : Finset (retained Z (mtParams T) T),
      (∀ i j : S, i ≠ j →
        MajorantAM.sep ≤ |xret Z (mtParams T) T i - xret Z (mtParams T) T j|) →
      offDiagSqOn (gram Z (mtParams T) T) S ≤
        blockDefect (gram_isHermitian Z (mtParams T) T) S := by
  filter_upwards [eventually_am_real_form_le_two Z,
    AMW.eventually_aAM_range P₀_valid] with T hform ha
  intro S hsep
  have hc : 0 ≤ aL2 (mtParams T) T :=
    mul_nonneg (by change 0 ≤ (AMW.atAM P₀ T).a T; linarith [ha.1]) (sq_nonneg _)
  have hreal : ∀ i j : S,
      (gram Z (mtParams T) T).submatrix (Subtype.val : S → retained Z (mtParams T) T)
        Subtype.val i j = (amRealEntry Z T i j : ℂ) := fun i j =>
          am_gram_real_entry Z T hc i j
  have h := offdiag_le_defect_of_real_form
    ((gram_isHermitian Z (mtParams T) T).submatrix
      (Subtype.val : S → retained Z (mtParams T) T)) hreal (hform S hsep)
  rw [offDiagSqOn_submatrix] at h
  exact h

/-- The near-pair reward uses the original AM min-one defect bound, including
the complete tolerance and without assuming a principal submatrix norm bound. -/
theorem near_pair_defect_gain
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {c η : ℝ}
    (hcap : 2 * c - 4 * η ≤ 1)
    (hoff : 2 * c - 4 * η ≤ offDiagSqOn A univ) :
    2 * c - 4 * η ≤ defect hA :=
  (le_min hcap hoff).trans (block_defect_of_isHermitian hA)

/-- All partition blocks are combined by convex pinching before counting.
The finite error budget stays explicit and can include the single separated
remainder's endpoint and pressure terms. -/
theorem defect_gain_of_partition
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (β : ι → κ)
    (loss : κ → ℝ) {c budget : ℝ}
    (hblocks : ∀ b,
      c * ((univ.filter fun i => β i = b).card : ℝ) - loss b
        ≤ blockDefect hA (univ.filter fun i => β i = b))
    (hloss : ∑ b, loss b ≤ budget) :
    c * (Fintype.card ι : ℝ) - budget ≤ defect hA := by
  have hpin := pinching_partition hA κ β
  have hsum := Finset.sum_le_sum (s := (univ : Finset κ)) fun b _ => hblocks b
  have hcard : (∑ b : κ, ((univ.filter fun i : ι => β i = b).card : ℝ))
      = Fintype.card ι := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (univ : Finset ι)) (t := (univ : Finset κ)) (f := β)
      (fun i _ => Finset.mem_univ (β i))
    simp only [Finset.card_univ] at h
    exact_mod_cast h.symm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hcard] at hsum
  linarith

/-- The old all-zero seam supplies the new dyadic conclusion as soon as the
lossless defect estimate is proved.  No old block-size ratio is reused. -/
theorem am_simple_dyadic_of_lossless_defect
    (Z : ZeroConfig) (H : PaperInputs Z)
    (hgain : ∀ d > 0, ∀ᶠ T in atTop,
      localReward * (Z.N0s T (2 * T) : ℝ) -
        gapPressure * (Z.N T (2 * T) : ℝ) -
        d * (Z.N T (2 * T) : ℝ) ≤ Dcirc Z (mtParams T) T) :
    ∀ e > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - e) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  intro e he
  have hden : 0 < 1 - localReward := sub_pos.mpr localReward_lt_one
  let d : ℝ := e * (1 - localReward) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have htail := tail_passage Z H (eventually_h7 Z) d hd
  have hmain : ∀ᶠ T in atTop,
      (recordRatio - e) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
    filter_upwards [htail, hgain d hd] with T ht hg
    have hN : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hHW := mul_le_mul_of_nonneg_right AMW.HW_ge hN
    have hkey :
        (67216841 / 100000000 - gapPressure - 2 * d) *
          (Z.N T (2 * T) : ℝ)
            ≤ (1 - localReward) * (Z.N0s T (2 * T) : ℝ) := by
      nlinarith
    have hid : 67216841 / 100000000 - gapPressure - 2 * d =
        (recordRatio - e) * (1 - localReward) := by
      dsimp [d]
      norm_num [recordRatio, gapPressure, localReward]
      ring
    rw [hid] at hkey
    exact (mul_le_mul_iff_right₀ hden).mp (by simpa [mul_assoc, mul_comm, mul_left_comm] using hkey)
  exact Filter.eventually_atTop.mp hmain

theorem am_distinct_dyadic_of_lossless_defect
    (hgain : ∀ d > 0, ∀ᶠ T in atTop,
      localReward * (Zeta23.N0simple T (2 * T) : ℝ) -
        gapPressure * (Zeta23.Ncount T (2 * T) : ℝ) -
        d * (Zeta23.Ncount T (2 * T) : ℝ) ≤
          Dcirc zetaZeroConfig (mtParams T) T) :
    ∀ e > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - e) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ Zeta23.N0star T (2 * T) := by
  have hs := am_simple_dyadic_of_lossless_defect zetaZeroConfig paperInputs_zeta
    (by simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using hgain)
  intro e he
  obtain ⟨T₀, hT₀⟩ := hs e he
  refine ⟨T₀, fun T hT => ?_⟩
  have hsimple := hT₀ T hT
  simp only [zetaZeroConfig_N, zetaZeroConfig_N0s] at hsimple
  exact hsimple.trans (by exact_mod_cast AMW.N0simple_le_N0star' T (2 * T))

theorem am_distinct_cumulative_of_lossless_defect
    (hgain : ∀ d > 0, ∀ᶠ T in atTop,
      localReward * (Zeta23.N0simple T (2 * T) : ℝ) -
        gapPressure * (Zeta23.Ncount T (2 * T) : ℝ) -
        d * (Zeta23.Ncount T (2 * T) : ℝ) ≤
          Dcirc zetaZeroConfig (mtParams T) T) :
    ∀ e > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - e) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => N0star_add' zetaSeam)
    (am_distinct_dyadic_of_lossless_defect hgain)

end RHWeilRecord

/-! The following finite matching proof is adapted verbatim (namespace only)
from Knausgard, 2610.08965v1, Distinct839/Gram/Matching.lean. Its parameters
remain arbitrary; it does not import the external paper's window constants. -/
/-
Distinct839/Gram/Matching.lean — a maximal matching of close pairs.

Given positions `y : ι → ℝ` on a finite index set and a threshold `d`, a *close matching* is an
involution `σ` of `ι` such that every point moved by `σ` is at distance less than `d` from its
partner. A close matching with the largest number of moved points has a `d`-separated set of
fixed points: two fixed points at distance less than `d` could be matched to each other.
The pairs `{i, σ i}` are the removed pairs of the Gram theorem, the fixed points form the
separated remainder.
-/

open Finset

namespace RHWeilRecord.Matching

variable {ι : Type*}

/-- `σ` is a close matching for the positions `y` and the threshold `d`: an involution whose
moved points are at distance less than `d` from their partners. -/
structure IsCloseMatching (y : ι → ℝ) (d : ℝ) (σ : ι → ι) : Prop where
  /-- `σ` is an involution -/
  invol : ∀ i, σ (σ i) = i
  /-- partners are close -/
  close : ∀ i, σ i ≠ i → |y i - y (σ i)| < d

lemma IsCloseMatching.id (y : ι → ℝ) (d : ℝ) : IsCloseMatching y d (fun i => i) :=
  ⟨fun _ => rfl, fun _ h => absurd rfl h⟩

/-- Matching two fixed points of a close matching that are close to each other gives a close
matching. -/
lemma IsCloseMatching.addPair [DecidableEq ι] {y : ι → ℝ} {d : ℝ} {σ : ι → ι}
    (hσ : IsCloseMatching y d σ) {i j : ι} (hi : σ i = i) (hj : σ j = j) (hij : i ≠ j)
    (hd : |y i - y j| < d) :
    IsCloseMatching y d (fun x => if x = i then j else if x = j then i else σ x) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · by_cases hxi : x = i
    · subst hxi
      simp [hij.symm]
    · by_cases hxj : x = j
      · subst hxj
        simp [hxi]
      · have h1 : σ x ≠ i := fun h => hxi (by rw [← hσ.invol x, h, hi])
        have h2 : σ x ≠ j := fun h => hxj (by rw [← hσ.invol x, h, hj])
        simp [hxi, hxj, h1, h2, hσ.invol x]
  · by_cases hxi : x = i
    · subst hxi
      simpa using hd
    · by_cases hxj : x = j
      · subst hxj
        simp only [if_neg hxi, if_true]
        rw [abs_sub_comm]; exact hd
      · simp only [if_neg hxi, if_neg hxj] at hx ⊢
        exact hσ.close x hx

/-- **Maximal matching.** There is a close matching whose fixed points are pairwise at
distance at least `d`. -/
theorem exists_maximal_matching [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (d : ℝ) :
    ∃ σ : ι → ι, IsCloseMatching y d σ ∧
      ∀ i j, σ i = i → σ j = j → i ≠ j → d ≤ |y i - y j| := by
  classical
  -- a close matching with the largest number of moved points
  obtain ⟨σ, hσmem, hσmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : ι → ι => IsCloseMatching y d σ)
    (fun σ => (Finset.univ.filter fun i => σ i ≠ i).card)
    ⟨fun i => i, by simp [IsCloseMatching.id]⟩
  have hσ : IsCloseMatching y d σ := by simpa using hσmem
  refine ⟨σ, hσ, fun i j hi hj hij => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set τ : ι → ι := fun x => if x = i then j else if x = j then i else σ x with hτ
  have hτm : IsCloseMatching y d τ := hσ.addPair hi hj hij hlt
  have hlt' : (Finset.univ.filter fun x => σ x ≠ x).card
      < (Finset.univ.filter fun x => τ x ≠ x).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, ?_, ?_⟩
      · simp [hτ, hij.symm]
      · simp [hi]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hxi : x ≠ i := fun h => hx (h ▸ hi)
      have hxj : x ≠ j := fun h => hx (h ▸ hj)
      simpa [hτ, hxi, hxj] using hx
  exact absurd (hσmax τ (by simpa using hτm)) (not_le.2 hlt')

/-! ### The block labels of a matching -/

/-- The block label of a point: `none` for a fixed point of `σ`, and the unordered pair
`{i, σ i}` for a moved point. The fibres of this map are the remainder set and the pairs. -/
def matchLabel [DecidableEq ι] (σ : ι → ι) (i : ι) : Option (Sym2 ι) :=
  if σ i = i then none else some s(i, σ i)

lemma matchLabel_eq_none [DecidableEq ι] {σ : ι → ι} {i : ι} :
    matchLabel σ i = none ↔ σ i = i := by
  unfold matchLabel
  split_ifs with h <;> simp [h]

lemma matchLabel_eq_some [DecidableEq ι] {σ : ι → ι} {i : ι} {z : Sym2 ι} :
    matchLabel σ i = some z ↔ σ i ≠ i ∧ s(i, σ i) = z := by
  unfold matchLabel
  split_ifs with h <;> simp [h]

/-- The partner of a moved point has the same label. -/
lemma matchLabel_partner [DecidableEq ι] {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) {i : ι}
    (hi : σ i ≠ i) : matchLabel σ (σ i) = some s(i, σ i) := by
  rw [matchLabel_eq_some, hσ i]
  exact ⟨fun h => hi h.symm, Sym2.eq_swap⟩

/-- The fibre of the label of a moved point `i` is `{i, σ i}`. -/
lemma eq_or_eq_of_matchLabel [DecidableEq ι] {σ : ι → ι} {i l : ι}
    (h : matchLabel σ l = some s(i, σ i)) : l = i ∨ l = σ i := by
  rw [matchLabel_eq_some] at h
  rcases Sym2.eq_iff.1 h.2 with h1 | h1
  · exact Or.inl h1.1
  · exact Or.inr h1.1

end RHWeilRecord.Matching

namespace RHWeilRecord

open Matrix Finset RHLinalg Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.StableRankTrace
open scoped ComplexOrder

/-- The original AM complex Gram approximation supplies the reward of a
two-point block. Both ordered entries and the complete error are retained. -/
theorem pair_defect_from_am_kernel
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℝ)
    {i j : ι} (hne : i ≠ j) (huniv : (univ : Finset ι) = {i, j})
    {c η : ℝ} (hc : c ≤ 1 / 2) (hη : 0 ≤ η)
    (hw : c ≤ wfun (x i - x j))
    (hij : ‖A i j - (Zeta23Ext.Bridge.kfun (x i - x j) : ℂ)‖ ≤ η)
    (hji : ‖A j i - (Zeta23Ext.Bridge.kfun (x j - x i) : ℂ)‖ ≤ η) :
    2 * c - 4 * η ≤ defect hA := by
  have hij' := wfun_sub_le_norm_sq hij
  have hji' := wfun_sub_le_norm_sq hji
  have hwji : wfun (x j - x i) = wfun (x i - x j) := by
    rw [show x j - x i = -(x i - x j) by ring, wfun_neg]
  rw [hwji] at hji'
  apply near_pair_defect_gain hA (by linarith)
  have hoff : offDiagSqOn A univ = ‖A i j‖ ^ 2 + ‖A j i‖ ^ 2 := by
    simp [offDiagSqOn, huniv, hne, hne.symm]
  rw [hoff]
  linarith

/-- A proved separated-subset reward is combined with all close pairs through
the actual AM spectral defect. The only analytic input left explicit is the
separated-subset reward; no principal-submatrix norm monotonicity is used. -/
theorem defect_gain_from_separated_subsets
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (x : ι → ℝ)
    {θ c η C budget : ℝ}
    (hc : c ≤ 1 / 2) (hη : 0 ≤ η) (hC : 2 ≤ C)
    (hnear : ∀ i j, i ≠ j → |x i - x j| < θ → c ≤ wfun (x i - x j))
    (hclose : ∀ i j, i ≠ j → |x i - x j| < θ →
      ‖A i j - (Zeta23Ext.Bridge.kfun (x i - x j) : ℂ)‖ ≤ η)
    (hsep : ∀ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → θ ≤ |x i - x j|) →
        (c - C * η) * (S.card : ℝ) - budget ≤ blockDefect hA S) :
    (c - C * η) * (Fintype.card ι : ℝ) - budget ≤ defect hA := by
  obtain ⟨σ, hσ, hσsep⟩ := Matching.exists_maximal_matching x θ
  let β : ι → Option (Sym2 ι) := Matching.matchLabel σ
  let loss : Option (Sym2 ι) → ℝ := fun k => if k = none then budget else 0
  apply defect_gain_of_partition hA β loss
  · intro k
    rcases k with _ | z
    · dsimp only [loss]
      rw [if_pos rfl]
      apply hsep
      intro i hi j hj hij
      have hi' : β i = none := by simpa using hi
      have hj' : β j = none := by simpa using hj
      exact hσsep i j
        (Matching.matchLabel_eq_none.mp hi')
        (Matching.matchLabel_eq_none.mp hj') hij
    · dsimp only [loss]
      rw [if_neg (Option.some_ne_none z), sub_zero]
      let S : Finset ι := univ.filter fun i => β i = some z
      change (c - C * η) * (S.card : ℝ) ≤ blockDefect hA S
      by_cases hempty : S = ∅
      · rw [hempty]
        simp only [card_empty, Nat.cast_zero, mul_zero]
        exact blockDefect_nonneg hA ∅
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        have hiβ : Matching.matchLabel σ i = some z := by simpa [S, β] using hi
        obtain ⟨hi1, hi2⟩ := Matching.matchLabel_eq_some.mp hiβ
        subst z
        have hjβ := Matching.matchLabel_partner hσ.invol hi1
        have hj : σ i ∈ S := by simpa [S, β] using hjβ
        have hne : i ≠ σ i := fun h => hi1 h.symm
        have hS : S = {i, σ i} := by
          ext l
          simp only [mem_insert, mem_singleton]
          constructor
          · intro hl
            have hl' : Matching.matchLabel σ l = some s(i, σ i) := by
              simpa [S, β] using hl
            exact Matching.eq_or_eq_of_matchLabel hl'
          · intro hl
            rcases hl with rfl | rfl
            · exact hi
            · exact hj
        have hcard : S.card = 2 := by rw [hS]; simp [hne]
        let ai : S := ⟨i, hi⟩
        let aj : S := ⟨σ i, hj⟩
        have haij : ai ≠ aj := fun h => hne (congrArg Subtype.val h)
        have hu : (univ : Finset S) = {ai, aj} := by
          ext l
          simp only [mem_univ, mem_insert, mem_singleton, true_iff]
          have hl : l.1 = i ∨ l.1 = σ i := by
            have := l.2
            simpa [hS] using this
          rcases hl with hl | hl
          · exact Or.inl (Subtype.ext hl)
          · exact Or.inr (Subtype.ext hl)
        have hd : |x i - x (σ i)| < θ := hσ.close i hi1
        have hd' : |x (σ i) - x i| < θ := by simpa [abs_sub_comm] using hd
        have hp := pair_defect_from_am_kernel
          (hA.submatrix (Subtype.val : S → ι)) (fun l : S => x l)
          haij hu hc hη (hnear i (σ i) hne hd)
          (hclose i (σ i) hne hd) (hclose (σ i) i hne.symm hd')
        change 2 * c - 4 * η ≤ blockDefect hA S at hp
        rw [hcard]
        have hmul := mul_le_mul_of_nonneg_right hC hη
        norm_num only [Nat.cast_ofNat]
        nlinarith
  · dsimp only [loss]
    simp

end RHWeilRecord

namespace RHWeilRecord

open Finset Zeta23Ext.BridgeW

/-- Sparse sliding pair charges for an arbitrary symmetric nonnegative
energy. This is the original AM window-pair proof with the stationary kernel
replaced by a genuine two-index energy, so it applies to the realized Gram
entries before taking a height limit. -/
theorem window_pair_weights_le_energy {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (W : WCert n) (hW : W.Adm) (E : ℕ → ℕ → ℝ)
    (hE0 : ∀ i j, 0 ≤ E i j) (hEsym : ∀ i j, E i j = E j i) :
    (∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then W.a a b * E (i + b) (i + a) else 0)
        ≤ ∑ r : Fin m × Fin m, if r.1 = r.2 then 0 else E r.1 r.2 := by
  classical
  have hm0 : 0 < m := by omega
  set T : Finset (ℕ × (Fin n × Fin n)) :=
    (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
    with hTdef
  set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
    W.a t.2.1 t.2.2 * E (t.1 + t.2.2) (t.1 + t.2.1) with hfdef
  have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      (if (a : ℕ) < (b : ℕ) then
        W.a a b * E (i + b) (i + a) else 0)
      = ∑ t ∈ T, f t := by
    rw [hTdef, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
      W.a a b * E (i + b) (i + a) else 0)).symm
  rw [hLHS]
  set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
  set I := T.image φ with hIdef
  have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
    intro t ht
    simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
    exact ht
  have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
    obtain ⟨h1, h2⟩ := hmem t ht
    have hb := t.2.2.2
    simp only [hφdef]
    omega
  rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]
  have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * E q.2 q.1 := by
    intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := hI q hq
    set r := q.2 - q.1 with hrdef
    have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
        f t = W.a t.2.1 t.2.2 * E q.2 q.1 := by
      intro t ht
      rw [mem_filter] at ht
      obtain ⟨ht, hφt⟩ := ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
      simp only [hfdef]
      rw [e1, e2]
    rw [sum_congr rfl hconst, ← sum_mul]
    set ψ : ℕ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
    have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
      intro t ht t' ht' hee
      rw [mem_coe, mem_filter] at ht ht'
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
      simp only [hψdef] at hee
      have ha : (t.2.1 : ℕ) = t'.2.1 := by rw [hee]
      have hi : t.1 = t'.1 := by omega
      exact Prod.ext hi hee
    have hsub : (T.filter (fun t => φ t = q)).image ψ
        ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
            (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
      rw [mem_filter] at ht
      have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
      have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
      obtain ⟨-, hlt⟩ := hmem t ht.1
      rw [mem_filter, mem_product]
      refine ⟨⟨mem_univ _, mem_univ _⟩, hlt, ?_⟩
      simp only [hψdef]
      omega
    have hmass : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2 ≤ 2 := by
      have h1 : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2
          = ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2 := by
        rw [sum_image hψinj]
      have h2 : ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2
          ≤ ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2
      have h3 : ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
              (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2
          = W.spanMass r := by
        unfold WCert.spanMass
        rw [sum_filter, sum_product]
      rw [h1]
      exact h2.trans (h3 ▸ hW.capacity r)
    exact mul_le_mul_of_nonneg_right hmass (hE0 _ _)
  refine (sum_le_sum hfib).trans ?_
  set G : Fin m × Fin m → ℝ := fun r => if r.1 = r.2 then 0 else E r.1 r.2 with hGdef
  set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
  have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
    intro n h; simp only [htoFin, dif_pos h]
  set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
  set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
  have hG1 : ∀ q ∈ I, G (ψ₁ q) = E q.2 q.1 := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne), hEsym q.1 q.2]
  have hG2 : ∀ q ∈ I, G (ψ₂ q) = E q.2 q.1 := by
    intro q hq
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    have hq1m : q.1 < m := by omega
    simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2]
    rw [if_neg (by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne')]
  have hsplit : ∑ q ∈ I, 2 * E q.2 q.1 = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [hG1 q hq, hG2 q hq]; ring
  have hinj₁ : Set.InjOn ψ₁ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hinj₂ : Set.InjOn ψ₂ I := by
    intro q hq q' hq' h
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
    rw [disjoint_left]
    intro r hr1 hr2
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
    obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
    obtain ⟨hq1, hq2, -⟩ := hI q hq
    obtain ⟨hq1', hq2', -⟩ := hI q' hq'
    simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
      htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
    omega
  have hGnn : ∀ r, 0 ≤ G r := by
    intro r; simp only [hGdef]; split_ifs
    · exact le_rfl
    · exact hE0 _ _
  rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r

end RHWeilRecord

namespace RHWeilRecord

open Finset Zeta23Ext.BridgeW

private theorem sparse_sum_gap_shift (Y : ℕ → ℝ) (r N : ℕ) :
    (∑ i ∈ range N, (Y (i + (r + 1)) - Y (i + r))) = Y (N + r) - Y r := by
  have h : ∀ i, i + (r + 1) = i + 1 + r := fun i => by omega
  simp_rw [h]
  have := Finset.sum_range_sub (fun i => Y (i + r)) N
  simpa using this

/-- The actual frame inequalities give a linear, lossless reward. The error
is charged once per frame; it is not replaced by the number of all point pairs.
The complete endpoint cost is c*(n-1). -/
theorem sparse_window_lossless_reward {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m)
    (W : WCert n) (hW : W.Adm) (Y : ℕ → ℝ) (E : ℕ → ℕ → ℝ)
    (hE0 : ∀ i j, 0 ≤ E i j) (hEsym : ∀ i j, E i j = E j i)
    {c err R : ℝ} (herr : 0 ≤ err)
    (hframes : ∀ i ∈ range (m - (n - 1)),
      c - err ≤
        (∑ r : Fin (n - 1), W.b r * (Y (i + (r + 1)) - Y (i + r))) +
        ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then W.a a b * E (i + b) (i + a) else 0)
    (hspan : ∀ r : Fin (n - 1), Y (m - (n - 1) + r) - Y r ≤ R) :
    c * (m : ℝ) - c * ((n - 1 : ℕ) : ℝ) - err * (m : ℝ) ≤
      (∑ q : Fin m × Fin m, if q.1 = q.2 then 0 else E q.1 q.2) + W.B * R := by
  have hsum := Finset.sum_le_sum hframes
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_add_distrib] at hsum
  have hpress :
      (∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1),
        W.b r * (Y (i + (r + 1)) - Y (i + r))) ≤ W.B * R := by
    calc (∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1),
            W.b r * (Y (i + (r + 1)) - Y (i + r)))
        = ∑ r : Fin (n - 1), W.b r * (Y (m - (n - 1) + r) - Y r) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r _
          rw [← Finset.mul_sum, sparse_sum_gap_shift]
      _ ≤ ∑ r : Fin (n - 1), W.b r * R :=
        Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left (hspan r) (hW.b_nonneg r)
      _ = W.B * R := by rw [← Finset.sum_mul]; rfl
  have hpair := window_pair_weights_le_energy hn hm W hW E hE0 hEsym
  have hcast : ((m - (n - 1) : ℕ) : ℝ) = (m : ℝ) - ((n - 1 : ℕ) : ℝ) :=
    Nat.cast_sub (by omega)
  rw [hcast] at hsum
  have hdrop : 0 ≤ err * ((n - 1 : ℕ) : ℝ) := mul_nonneg herr (Nat.cast_nonneg _)
  nlinarith

/-- The sparse frame's exact mass controls transport from the AM kernel to
actual squared Gram entries. The caller supplies the approximation only for
this frame's used entries. -/
theorem sparse_frame_kernel_transfer {n : ℕ} (W : WCert n) (hW : W.Adm)
    (K E : Fin n → Fin n → ℝ) {c pressure η mass : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ a b : Fin n, (a : ℕ) < (b : ℕ) → K a b - 2 * η ≤ E a b)
    (hcert : c ≤ pressure + ∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then W.a a b * K a b else 0)
    (hmass : (∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then W.a a b else 0) ≤ mass) :
    c - 2 * η * mass ≤ pressure + ∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then W.a a b * E a b else 0 := by
  have hsum : (∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then W.a a b * K a b - 2 * η * W.a a b else 0)
        ≤ ∑ a : Fin n, ∑ b : Fin n,
          if (a : ℕ) < (b : ℕ) then W.a a b * E a b else 0 := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    by_cases hab : (a : ℕ) < (b : ℕ)
    · simp only [if_pos hab]
      have h := mul_le_mul_of_nonneg_left (hclose a b hab) (hW.a_nonneg a b)
      nlinarith
    · simpa only [if_neg hab] using (le_rfl : (0 : ℝ) ≤ 0)
  have hsplit : (∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then W.a a b * K a b - 2 * η * W.a a b else 0)
      = (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) < (b : ℕ) then W.a a b * K a b else 0) -
        2 * η * (∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) < (b : ℕ) then W.a a b else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> ring
  rw [hsplit] at hsum
  have hpaid := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 2 * η)
  linarith

end RHWeilRecord

namespace RHWeilRecord

open Finset Zeta23Ext.BridgeW Zeta23Ext.Bridge

/- The finite sorting lemma below is adapted from Knausgard v1,
Distinct839/Gram/Remainder.lean, with its parameters unchanged. -/
theorem exists_increasing_enumeration {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hy : Function.Injective y) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, StrictMono fun i => y (e i) := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' y hy
  refine ⟨(Fintype.orderIsoFinOfCardEq ι rfl).toEquiv, fun i j hij => ?_⟩
  have h : (Fintype.orderIsoFinOfCardEq ι rfl) i <
      (Fintype.orderIsoFinOfCardEq ι rfl) j :=
    (Fintype.orderIsoFinOfCardEq ι rfl).strictMono hij
  exact h

/-- The complete finite chain transport uses the original AM all-pair
uniform Gram approximation. Small chains retain the same endpoint allowance. -/
theorem sparse_finite_energy_lower {n m : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm) (y : Fin m → ℝ)
    (hgap : ∀ a b : Fin m, a < b → 4/5 ≤ y b-y a)
    (E : Fin m → Fin m → ℝ) (hE0 : ∀ a b, 0 ≤ E a b)
    (hEsym : ∀ a b, E a b = E b a)
    {c R η mass : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) (hη : 0 ≤ η)
    (hspan : ∀ a b, y a-y b ≤ R)
    (hcert : ∀ g : Fin (n-1) → ℝ, (∀ r, 4/5 ≤ g r) → c ≤ Fw W g)
    (hmass : (∑ a : Fin n, ∑ b : Fin n,
      if (a:ℕ) < (b:ℕ) then W.a a b else 0) ≤ mass)
    (hentry : ∀ a b, wfun (y a-y b)-2*η ≤ E a b) :
    c*(m:ℝ)-c*((n-1:ℕ):ℝ)-2*η*mass*(m:ℝ) ≤
      (∑ q : Fin m × Fin m, if q.1=q.2 then 0 else E q.1 q.2)+W.B*R := by
  classical
  have hmass0 : 0 ≤ mass := by
    refine le_trans ?_ hmass
    exact sum_nonneg fun a _ => sum_nonneg fun b _ => by
      split_ifs <;> first | exact hW.a_nonneg _ _ | exact le_rfl
  have hEtotal : 0 ≤ ∑ q : Fin m × Fin m,
      if q.1=q.2 then 0 else E q.1 q.2 := by
    apply sum_nonneg
    intro q _
    split_ifs <;> first | exact le_rfl | exact hE0 _ _
  by_cases hm : n ≤ m
  · have hm0 : 0 < m := by omega
    let Y : ℕ → ℝ := sortedExt y
    let f : ℕ → Fin m := fun i => if h : i < m then ⟨i,h⟩ else ⟨0,hm0⟩
    let EE : ℕ → ℕ → ℝ := fun a b => E (f a) (f b)
    have hf : ∀ a (ha : a< m), f a = ⟨a,ha⟩ := by
      intro a ha
      simp [f, ha]
    have hEE : ∀ a b, 0 ≤ EE a b := fun a b => hE0 _ _
    have hEEsym : ∀ a b, EE a b = EE b a := fun a b => hEsym _ _
    have hframes : ∀ i ∈ range (m-(n-1)),
        c-2*η*mass ≤
        (∑ r : Fin (n-1), W.b r*(Y (i+(r+1))-Y (i+r)))+
        ∑ a : Fin n, ∑ b : Fin n,
          if (a:ℕ) < (b:ℕ) then W.a a b*EE (i+b) (i+a) else 0 := by
      intro i hi
      have hi' := mem_range.mp hi
      have hgap' : ∀ r : Fin (n-1), 4/5 ≤ Y (i+(r+1))-Y (i+r) := by
        intro r
        have hr := r.2
        have ha : i+(r:ℕ)< m := by omega
        have hb : i+((r:ℕ)+1)< m := by omega
        dsimp [Y]
        rw [sortedExt_of_lt y hb, sortedExt_of_lt y ha]
        exact hgap _ _ (by simp only [Fin.mk_lt_mk]; omega)
      have hkernel := hcert (windowGaps n Y i) hgap'
      rw [Fw_windowGaps] at hkernel
      apply sparse_frame_kernel_transfer W hW
        (fun a b => wfun (Y (i+b)-Y (i+a)))
        (fun a b => EE (i+b) (i+a)) hη ?_ hkernel hmass
      intro a b _
      have ia : i+(a:ℕ)< m := by have := a.2; omega
      have ib : i+(b:ℕ)< m := by have := b.2; omega
      dsimp [Y, EE]
      rw [sortedExt_of_lt y ib, sortedExt_of_lt y ia, hf _ ib, hf _ ia]
      exact hentry _ _
    have hspans : ∀ r : Fin (n-1), Y (m-(n-1)+r)-Y r ≤ R := by
      intro r
      have hr : (r:ℕ)< m := by have := r.2; omega
      have hk : m-(n-1)+(r:ℕ)< m := by have := r.2; omega
      dsimp [Y]
      rw [sortedExt_of_lt y hk, sortedExt_of_lt y hr]
      exact hspan _ _
    have h := sparse_window_lossless_reward hn hm W hW Y EE hEE hEEsym
      (by positivity : 0 ≤ 2*η*mass) hframes hspans
    have hEeq : (∑ q : Fin m × Fin m, if q.1=q.2 then 0 else EE q.1 q.2) =
        ∑ q : Fin m × Fin m, if q.1=q.2 then 0 else E q.1 q.2 := by
      apply sum_congr rfl
      intro q _
      dsimp [EE]
      rw [hf _ q.1.2, hf _ q.2.2]
    rw [hEeq] at h
    exact h
  · have hmn : (m:ℝ) ≤ ((n-1:ℕ):ℝ) := by exact_mod_cast (by omega : m ≤ n-1)
    have hcm := mul_le_mul_of_nonneg_left hmn hc
    have he : 0 ≤ 2*η*mass*(m:ℝ) := by positivity
    have hp : 0 ≤ W.B*R := mul_nonneg (WCert.B_nonneg hW) hR
    linarith

end RHWeilRecord

namespace RHWeilRecord

open Real MeasureTheory

/-- A continuous rational certificate for the sinc lower bound on the entire
near-pair interval. The six Bernstein coefficients are strictly positive. -/
private theorem sinc_ten_lower_near {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 158/25) :
    7/30 ≤ 1-v/6+v^2/120-v^3/5040+v^4/362880-v^5/39916800 := by
  let w : ℝ := v / (158/25)
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by dsimp [w]; norm_num; linarith
  have hv : v = (158/25)*w := by dsimp [w]; ring
  have he :
      1-v/6+v^2/120-v^3/5040+v^4/362880-v^5/39916800-7/30 =
      (23/30)*(1-w)^5 + (139/250)*5*w*(1-w)^4 +
      (70991/187500)*10*w^2*(1-w)^3 +
      (11296393/49218750)*10*w^3*(1-w)^2 +
      (4631534881/44296875000)*5*w^4*(1-w) +
      (82581041/338378906250)*w^5 := by rw [hv]; ring
  have hn : 0 ≤
      (23/30)*(1-w)^5 + (139/250)*5*w*(1-w)^4 +
      (70991/187500)*10*w^2*(1-w)^3 +
      (11296393/49218750)*10*w^3*(1-w)^2 +
      (4631534881/44296875000)*5*w^4*(1-w) +
      (82581041/338378906250)*w^5 := by positivity
  linarith

theorem sinc_pi_near {x : ℝ} (hx : |x| ≤ 4/5) :
    7/30 ≤ Real.sinc (Real.pi*x) := by
  have hπ := Real.pi_lt_d6
  norm_num at hπ
  have hπ2 : Real.pi^2 ≤ 79/8 := by nlinarith [Real.pi_pos]
  have hx2 : x^2 ≤ 16/25 := by
    have h := abs_le.mp hx
    nlinarith [h.1, h.2]
  have hp := mul_le_mul hπ2 hx2 (sq_nonneg x) (by norm_num : (0:ℝ) ≤ 79/8)
  have hv : (Real.pi*x)^2 ≤ 158/25 := by nlinarith
  have hpoly := sinc_ten_lower_near (sq_nonneg (Real.pi*x)) hv
  have ht := MajorantAM.Taylor.sincPoly_le_sinc (Real.pi*x) 2
  norm_num [MajorantAM.Taylor.sincPoly] at ht
  have h4 : (Real.pi*x)^4 = ((Real.pi*x)^2)^2 := by ring
  have h6 : (Real.pi*x)^6 = ((Real.pi*x)^2)^3 := by ring
  have h8 : (Real.pi*x)^8 = ((Real.pi*x)^2)^4 := by ring
  have h10 : (Real.pi*x)^10 = ((Real.pi*x)^2)^5 := by ring
  rw [h4, h6, h8, h10] at ht
  exact hpoly.trans (by linarith [ht])

private theorem am_normalization_eq : AMW.KfunAM 0 = MajorantAM.ZAM := by
  rw [AMW.KfunAM_zero_closed, MajorantAM.ZAM, AMW.aInf_eq]
  field_simp [AMW.MAM_pos.ne']

/-- The AM perturbation is charged before normalization. This bound uses
cos(MT)-1 ≤ 0 and |cos| ≤ 1, so requires no unformalized covariance theorem. -/
private theorem am_kernel_triangle (x : ℝ) :
    Real.sinc (Real.pi*x)+MajorantAM.ZAM-1-13/200 ≤ AMW.KfunAM x := by
  let lower : ℝ → ℝ := fun t => Real.cos (2*Real.pi*x*t) +
    Real.cos (Real.sqrt 2*t)-1-13/200
  have hpt : ∀ t, lower t ≤ AMW.vAM t * Real.cos (2*Real.pi*x*t) := by
    intro t
    have hc := mul_le_mul_of_nonpos_left (Real.cos_le_one (2*Real.pi*x*t))
      (sub_nonpos.mpr (Real.cos_le_one (Real.sqrt 2*t)))
    have ha : |AMW.pAM t * Real.cos (2*Real.pi*x*t)| ≤ 13/200 := by
      rw [abs_mul]
      calc |AMW.pAM t| * |Real.cos (2*Real.pi*x*t)| ≤ (13/200)*1 :=
        mul_le_mul (AMW.abs_pAM_le t) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 13/200 := by ring
    have hp := (abs_le.mp ha).1
    dsimp [lower]
    rw [AMW.vAM_eq]
    nlinarith
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num : (-(1:ℝ)/2) ≤ 1/2)
    ((by fun_prop : Continuous lower).intervalIntegrable (-(1:ℝ)/2) (1/2))
    ((AMW.vAM_continuous.mul (by fun_prop : Continuous fun t : ℝ =>
      Real.cos (2*Real.pi*x*t))).intervalIntegrable (-(1:ℝ)/2) (1/2))
    (fun t _ => hpt t)
  have hcos : (∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (2*Real.pi*x*t)) =
      Real.sinc (Real.pi*x) := by
    rw [AMW.integral_cos_mul_sinc]
    congr 1
    ring
  have hmt : (∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (Real.sqrt 2*t)) =
      MajorantAM.ZAM := by
    rw [AMW.integral_cos_sqrt2, ← am_normalization_eq, AMW.KfunAM_zero_closed]
  have hlow : (∫ t in (-(1:ℝ)/2)..(1/2), lower t) =
      Real.sinc (Real.pi*x)+MajorantAM.ZAM-1-13/200 := by
    dsimp [lower]
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (2*Real.pi*x*t) +
        Real.cos (Real.sqrt 2*t)-1).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (2*Real.pi*x*t) +
        Real.cos (Real.sqrt 2*t)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_add
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (2*Real.pi*x*t)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => Real.cos (Real.sqrt 2*t)).intervalIntegrable _ _),
      hcos, hmt]
    norm_num
  rw [hlow] at hi
  exact hi

/-- The original AM normalized kernel is uniformly positive on [.−8,.8]. -/
theorem am_near_kernel_lower {x : ℝ} (hx : |x| ≤ 4/5) :
    51/550 ≤ AMW.kfunAM x := by
  have hraw := am_kernel_triangle x
  have hs := sinc_pi_near hx
  have hZ := MajorantAM.ZAM_ge
  have hmul : (51/550)*MajorantAM.ZAM ≤ AMW.KfunAM x := by nlinarith
  rw [AMW.kfunAM, am_normalization_eq]
  exact (le_div_iff₀ MajorantAM.ZAM_pos).2 hmul

theorem am_near_weight_ge_reward {x : ℝ} (hx : |x| ≤ 4/5) :
    localReward ≤ AMW.wfunAM x := by
  have hk := am_near_kernel_lower hx
  unfold AMW.wfunAM localReward
  nlinarith [sq_nonneg (AMW.kfunAM x-51/550)]

end RHWeilRecord

namespace RHWeilRecord

open Zeta23Ext.BridgeW Zeta23Ext.Bridge Zeta23.ZeroSide Zeta23.ThmD

/-- This is the original AM kernel-limit proof with its unused radius premise
removed. The estimate is uniform over all retained pairs, including far pairs. -/
theorem eventually_am_all_entries_close (Z : ZeroConfig) (H : PaperInputs Z) :
    ∀ δ>0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      ‖gram Z (mtParams T) T z z' -
        (Zeta23Ext.Bridge.kfun (xret Z (mtParams T) T z-xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨T₀,hT₀⟩ := AMW.localHypsCoreAM_eventually hP
  set K : ℝ := (AMW.cAMW (paramsOf stdProfile 1).ϱ /
    (paramsOf stdProfile 1).w)^2
  have hw : 0<(paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0,eventually_w8 hP,AMW.eventually_w32 hP,
    eventually_ge_atTop T₀,(tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop
      ((10*K+12*(paramsOf stdProfile 1).w)/δ)]
    with T hT h8 h32 hTT₀ hL1 hLδ
  intro z z'
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hT h8 h32 hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T
  have hL : 0< L := by linarith
  have hL4 : L≤ L^4 := by nlinarith [pow_pos hL 2,pow_pos hL 3]
  have h1 : 10*K/L^4≤10*K/L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10*K+12*(paramsOf stdProfile 1).w)/L≤δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc 10*K/L^4+12*(paramsOf stdProfile 1).w/L
      ≤10*K/L+12*(paramsOf stdProfile 1).w/L := by gcongr
    _ = (10*K+12*(paramsOf stdProfile 1).w)/L := by ring
    _ ≤ δ := h2

/-- The lossless sparse transport is invariant under enumeration of the true
finite point set. No canonical subfamily replaces the actual signed entries. -/
theorem sparse_fintype_energy_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (hn : 2≤ n) (W : WCert n) (hW : W.Adm)
    (x : ι→ℝ) (E : ι→ι→ℝ)
    (hsep : ∀ a b,a≠b→4/5≤|x a-x b|)
    (hE0 : ∀ a b,0≤ E a b) (hEsym : ∀ a b,E a b=E b a)
    {c R η mass : ℝ} (hc : 0≤ c) (hR : 0≤ R) (hη : 0≤η)
    (hspan : ∀ a b,x a-x b≤ R)
    (hcert : ∀ g : Fin (n-1)→ℝ,(∀ r,4/5≤ g r)→ c≤ Fw W g)
    (hmass : (∑ a : Fin n,∑ b : Fin n,
      if (a:ℕ)<(b:ℕ) then W.a a b else 0) ≤ mass)
    (hentry : ∀ a b,wfun (x a-x b)-2*η≤ E a b) :
    c*(Fintype.card ι:ℝ)-c*((n-1:ℕ):ℝ)-
      2*η*mass*(Fintype.card ι:ℝ) ≤
      (∑ a,∑ b,if a=b then 0 else E a b)+W.B*R := by
  classical
  have hx : Function.Injective x := by
    intro a b hab
    by_contra hne
    have h := hsep a b hne
    rw [hab,sub_self,abs_zero] at h
    norm_num at h
  obtain ⟨e,he⟩ := exists_increasing_enumeration x hx
  have hg : ∀ a b : Fin (Fintype.card ι),a< b→4/5≤ x (e b)-x (e a) := by
    intro a b hab
    have hp := he hab
    have hs := hsep (e b) (e a) (fun h => hab.ne' (e.injective h))
    rwa [abs_of_pos (by linarith)] at hs
  have h := sparse_finite_energy_lower hn W hW (fun i=>x (e i)) hg
    (fun a b=>E (e a) (e b)) (fun _ _=>hE0 _ _) (fun _ _=>hEsym _ _)
    hc hR hη (fun _ _=>hspan _ _) hcert hmass (fun _ _=>hentry _ _)
  have hsum :
      (∑ q : Fin (Fintype.card ι)×Fin (Fintype.card ι),
        if q.1=q.2 then 0 else E (e q.1) (e q.2)) =
      ∑ a,∑ b,if a=b then 0 else E a b := by
    rw [Fintype.sum_prod_type]
    rw [← Equiv.sum_comp e (fun a=>∑ b,if a=b then 0 else E a b)]
    apply sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp e (fun b=>if e i=b then 0 else E (e i) b)]
    apply sum_congr rfl
    intro j _
    by_cases hij : i=j
    · subst j
      simp
    · rw [if_neg hij,if_neg (fun h=>hij (e.injective h))]
  rw [hsum] at h
  exact h

end RHWeilRecord

#print axioms RHWeilRecord.eventually_am_all_entries_close
#print axioms RHWeilRecord.sparse_fintype_energy_lower

namespace RHWeilRecord

open Zeta23Ext.BridgeW Zeta23Ext.Bridge

set_option maxHeartbeats 2000000 in
/-- The actual finite retained Gram assembly for any nine-point certificate
with the stipulated true span budget and pair mass. -/
theorem eventually_am_retained_lossless_defect (Z : ZeroConfig) (H : PaperInputs Z)
    (W : WCert 9) (hW : W.Adm)
    (hB : W.B=gapPressure)
    (hmass : (∑ a : Fin 9,∑ b : Fin 9,
      if (a:ℕ)<(b:ℕ) then W.a a b else 0)≤16)
    (hcert : ∀ g : Fin 8→ℝ,(∀ r,4/5≤ g r)→ localReward≤ Fw W g) :
    ∀ η>0, ∀ᶠ T in atTop,
      (localReward-32*η)*((retained Z (mtParams T) T).card:ℝ) -
        (gapPressure*spanOf (xret Z (mtParams T) T) univ+8*localReward)
        ≤ Dcirc Z (mtParams T) T := by
  intro η hη
  filter_upwards [eventually_am_all_entries_close Z H η hη,
    eventually_am_separated_offdiag_le_defect Z] with T hclose hform
  let x := xret Z (mtParams T) T
  let G := gram Z (mtParams T) T
  let R := spanOf x univ
  have hR : 0≤ R := spanOf_nonneg x univ
  have hsym : ∀ i j, ‖G i j‖^2=‖G j i‖^2 := by
    intro i j
    simpa only [norm_star] using
      (congrArg (fun z : ℂ => ‖z‖^2)
        ((gram_isHermitian Z (mtParams T) T).apply i j)).symm
  have hnear : ∀ i j,i≠j→|x i-x j|<4/5→ localReward≤ wfun (x i-x j) := by
    intro i j _ hij
    exact am_near_weight_ge_reward hij.le
  have hsep : ∀ S : Finset (retained Z (mtParams T) T),
      (∀ i∈S,∀ j∈S,i≠j→4/5≤|x i-x j|) →
      (localReward-32*η)*(S.card:ℝ) -
        (gapPressure*R+8*localReward) ≤ blockDefect (gram_isHermitian Z (mtParams T) T) S := by
    intro S hs
    have hs' : ∀ i j : S,i≠j→4/5≤|x i-x j| := by
      intro i j hij
      exact hs i i.2 j j.2 (fun h=>hij (Subtype.ext h))
    have hf : offDiagSqOn G S≤ blockDefect (gram_isHermitian Z (mtParams T) T) S :=
      hform S (by simpa only [MajorantAM.sep] using hs')
    have he := sparse_fintype_energy_lower (by norm_num : 2≤9) W hW
      (fun i : S=>x i) (fun i j : S=>‖G i j‖^2)
      hs' (fun _ _=>sq_nonneg _) (fun _ _=>hsym _ _)
      (by norm_num [localReward] : 0≤ localReward) hR hη.le
      (fun i j=>(le_abs_self _).trans (abs_sub_le_spanOf x (mem_univ i.1) (mem_univ j.1)))
      hcert hmass
      (fun i j=>wfun_sub_le_norm_sq (hclose i j))
    rw [Fintype.card_coe] at he
    change localReward*(S.card:ℝ)-localReward*((9-1:ℕ):ℝ) -
      2*η*16*(S.card:ℝ) ≤
      offDiagSqOn (G.submatrix (Subtype.val : S→ retained Z (mtParams T) T)
        Subtype.val) univ+W.B*R at he
    rw [offDiagSqOn_submatrix,hB] at he
    norm_num only [Nat.cast_ofNat] at he
    linarith
  have h := defect_gain_from_separated_subsets
    (gram_isHermitian Z (mtParams T) T) x
    (by norm_num [localReward] : localReward≤1/2) hη.le
    (by norm_num : (2:ℝ)≤32)
    hnear (fun i j _ _=>hclose i j) hsep
  rw [Fintype.card_coe] at h
  exact h

/-- All endpoint, deleted-strip and normalized-span errors are absorbed in
the true all-zero count. This has no additional spectral or numerical axiom. -/
theorem am_lossless_defect_of_nine_point_certificate
    (Z : ZeroConfig) (H : PaperInputs Z)
    (W : WCert 9) (hW : W.Adm) (hB : W.B=gapPressure)
    (hmass : (∑ a : Fin 9,∑ b : Fin 9,
      if (a:ℕ)<(b:ℕ) then W.a a b else 0)≤16)
    (hcert : ∀ g : Fin 8→ℝ,(∀ r,4/5≤ g r)→ localReward≤ Fw W g) :
    ∀ d>0, ∀ᶠ T in atTop,
      localReward*(Z.N0s T (2*T):ℝ)-gapPressure*(Z.N T (2*T):ℝ) -
        d*(Z.N T (2*T):ℝ) ≤ Dcirc Z (mtParams T) T := by
  intro d hd
  let η : ℝ := min (d/128) (localReward/64)
  have hη : 0<η := by
    dsimp [η]
    exact lt_min (by positivity) (by norm_num [localReward])
  have hηd : η≤ d/128 := min_le_left _ _
  have hηc : η≤ localReward/64 := min_le_right _ _
  have hcoef : 0≤ localReward-32*η := by linarith
  have hconstant := (Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop
    (16*localReward/d)
  filter_upwards [eventually_am_retained_lossless_defect Z H W hW hB hmass hcert η hη,
    deleted_strips Z H η hη,span_retained_le Z H η hη,hconstant]
    with T hg hstrip hspan hNlarge
  have hN : 0≤(Z.N T (2*T):ℝ) := Nat.cast_nonneg _
  have hnN : (Z.N0s T (2*T):ℝ)≤(Z.N T (2*T):ℝ) := by
    have h := (Z.trivial_chain T (2*T)).1.trans
      ((Z.trivial_chain T (2*T)).2.1.trans (Z.trivial_chain T (2*T)).2.2.1)
    exact_mod_cast h
  have hs := mul_le_mul_of_nonneg_left hstrip hcoef
  have hB0 : 0≤ gapPressure := gapPressure_nonneg
  have hp := mul_le_mul_of_nonneg_left hspan hB0
  have hc0 : 8*localReward≤(d/2)*(Z.N T (2*T):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hNlarge (by positivity : 0≤ d/2)
    have he : (d/2)*(16*localReward/d)=8*localReward := by field_simp; ring
    rw [he] at h
    exact h
  have hnη := mul_le_mul_of_nonneg_left hnN (by positivity : 0≤32*η)
  have hηN := mul_le_mul_of_nonneg_right hηd hN
  have hcoefupper : localReward+gapPressure≤1 := by
    norm_num [localReward,gapPressure]
  have hpη := mul_le_mul_of_nonneg_right hcoefupper (mul_nonneg hη.le hN)
  have hquad : 0≤32*η^2*(Z.N T (2*T):ℝ) := by positivity
  nlinarith

end RHWeilRecord

#print axioms RHWeilRecord.eventually_am_retained_lossless_defect
#print axioms RHWeilRecord.am_lossless_defect_of_nine_point_certificate

namespace RHWeilRecord

open Zeta23Ext.BridgeW Zeta23Ext.Bridge

theorem am_distinct_dyadic_of_nine_point_certificate
    (W : WCert 9) (hW : W.Adm) (hB : W.B=gapPressure)
    (hmass : (∑ a : Fin 9,∑ b : Fin 9,
      if (a:ℕ)<(b:ℕ) then W.a a b else 0)≤16)
    (hcert : ∀ g : Fin 8→ℝ,(∀ r,4/5≤ g r)→ localReward≤ Fw W g) :
    ∀ e>0,∃ T₀ : ℝ,∀ T≥ T₀,
      (recordRatio-e)*(Zeta23.Ncount T (2*T):ℝ)≤ Zeta23.N0star T (2*T) := by
  apply am_distinct_dyadic_of_lossless_defect
  simpa only [zetaZeroConfig_N,zetaZeroConfig_N0s] using
    am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W hW hB hmass hcert

theorem am_distinct_cumulative_of_nine_point_certificate
    (W : WCert 9) (hW : W.Adm) (hB : W.B=gapPressure)
    (hmass : (∑ a : Fin 9,∑ b : Fin 9,
      if (a:ℕ)<(b:ℕ) then W.a a b else 0)≤16)
    (hcert : ∀ g : Fin 8→ℝ,(∀ r,4/5≤ g r)→ localReward≤ Fw W g) :
    ∀ e>0,∃ T₀ : ℝ,∀ T≥ T₀,
      (recordRatio-e)*(Zeta23.Ncount 0 T:ℝ)≤ Zeta23.N0star 0 T := by
  apply am_distinct_cumulative_of_lossless_defect
  simpa only [zetaZeroConfig_N,zetaZeroConfig_N0s] using
    am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W hW hB hmass hcert

end RHWeilRecord

#print axioms RHWeilRecord.am_distinct_dyadic_of_nine_point_certificate
#print axioms RHWeilRecord.am_distinct_cumulative_of_nine_point_certificate

#print axioms RHWeilRecord.sinc_pi_near
#print axioms RHWeilRecord.am_near_weight_ge_reward
#print axioms RHWeilRecord.eventually_am_separated_offdiag_le_defect
#print axioms RHWeilRecord.finite_count_transport
#print axioms RHWeilRecord.c260_finite_count_transport
#print axioms RHWeilRecord.error_div_small
#print axioms RHWeilRecord.asymptotic_count_transport
#print axioms RHWeilRecord.asymptotic_mono_counts
#print axioms RHWeilRecord.eigenvalues_le_of_real_form
#print axioms RHWeilRecord.offdiag_le_defect_of_real_form
#print axioms RHWeilRecord.near_pair_defect_gain
#print axioms RHWeilRecord.defect_gain_of_partition
#print axioms RHWeilRecord.am_distinct_dyadic_of_lossless_defect
#print axioms RHWeilRecord.am_distinct_cumulative_of_lossless_defect
#print axioms RHWeilRecord.Matching.exists_maximal_matching
#print axioms RHWeilRecord.pair_defect_from_am_kernel
#print axioms RHWeilRecord.defect_gain_from_separated_subsets

#print axioms RHWeilRecord.window_pair_weights_le_energy
#print axioms RHWeilRecord.sparse_window_lossless_reward
#print axioms RHWeilRecord.sparse_frame_kernel_transfer
