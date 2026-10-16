/- SPDX-License-Identifier: Apache-2.0
Actual new-window separated Gram and spectral bounds.
Adapted from Opeth.AMSeparatedGram and Opeth.AMSeparatedSpectrum in the
attributed Core. Actual new-profile domination and normalization replace the
old fixed cosine coefficients. No local floor or new proportion is assumed.
-/
import StructuralGoal20261016.WindowCountingBase
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg Filter MeasureTheory Real Set
open scoped ComplexOrder BigOperators Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
open Zeta23Ext.Bridge Opeth
namespace StructuralGoal20261016.WindowSeparated

@[simp] theorem at24_L (P : Params) (T : ℝ) : (WindowRealization.at24 P T).L = P.L := rfl
theorem at24_phiHatR_eq {P : Params} (hP : P.Valid) (T : ℝ) :
 (WindowRealization.at24 P T).phiHatR T = AdmWindow.vHatR (WindowRealization.W P T) :=
 AMW.atW_phiHatR T hP (WindowRealization.W_even P T)
theorem phiHatReal_at24 {P : Params} (hP : P.Valid) (T : ℝ) :
 PhiHatReal T (WindowRealization.at24 P T) := fun r => GzGp.phiHat_ofReal _ T r
theorem normalized_profile_le_scaled_majorant {s : ℝ} (hs : |s| ≤ 1/2) :
 AMW.rhoAM * WindowProfile.V s ≤ Opeth.AMMajorant.scaledMajorant s := by
 rw [WindowProfile.V_eq_v24]
 exact StructuralW10Followup20261016.NewWindows.v24_dominated hs

private lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * cos (r * u) := by
  have hint : Integrable (fun u : ℝ =>
      (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp hg).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    · refine hs.mono fun u hu => ?_
      rw [Function.mem_support] at hu ⊢
      intro h0
      apply hu
      rw [h0, Complex.ofReal_zero, zero_mul]
  have h := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at h
  rw [paperFT_def, ← h]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  show ((g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re =
    g u * cos (r * u)
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
private lemma VPhiR_eq_integral {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (r : ℝ) :
    AdmWindow.VPhiR v r = ∫ u, v u ^ 2 * cos (r * u) :=
  re_paperFT_ofReal hW.sq_continuous hW.sq_hasCompactSupport r
private lemma integrable_sq_mul_cos {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (r : ℝ) :
    Integrable (fun u => v u ^ 2 * cos (r * u)) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hW.sq_continuous.mul (continuous_cos.comp (continuous_const.mul continuous_id))) ?_
  refine hW.sq_hasCompactSupport.mono fun u hu => ?_
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  rw [h0, zero_mul]
private lemma finite_sum_le_hasSum {f : ℤ → ℝ} {S : ℝ} (d : ℕ)
    (hf : HasSum f S) (h0 : ∀ k, 0 ≤ f k) :
    ∑ k : Fin d, f ((k : ℕ) : ℤ) ≤ S := by
  classical
  have he : ∑ k : Fin d, f ((k : ℕ) : ℤ) =
      ∑ k ∈ (Finset.range d).map Nat.castEmbedding, f k := by
    rw [Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d
  rw [he]
  exact sum_le_hasSum _ (fun k _ => h0 k) hf
private lemma poisson_square {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (T : ℝ) {ι : Type} [Fintype ι]
    (γ z : ι → ℝ) :
    HasSum (fun k : ℤ =>
        (∑ i, z i * AdmWindow.vHatR v (γ i - (T + k * (2 * π / L)))) ^ 2)
      (L * ∑ i, ∑ j, z i * z j * AdmWindow.VPhiR v (γ i - γ j)) := by
  have h : HasSum (fun k : ℤ => ∑ i, ∑ j, z i * z j *
        (AdmWindow.vHatR v (γ i - (T + k * (2 * π / L))) *
          AdmWindow.vHatR v (γ j - (T + k * (2 * π / L)))))
      (∑ i, ∑ j, z i * z j * (L * AdmWindow.VPhiR v (γ i - γ j))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (hW.hasSum_vHatR_mul T (γ i) (γ j)).mul_left (z i * z j)
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
private lemma cosine_integral {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) {ι : Type} [Fintype ι] (γ z : ι → ℝ) :
    ∑ i, ∑ j, z i * z j * AdmWindow.VPhiR v (γ i - γ j) =
      ∫ u, v u ^ 2 * ∑ i, ∑ j, z i * z j * cos ((γ i - γ j) * u) := by
  have hint : ∀ i j,
      Integrable (fun u => z i * z j * (v u ^ 2 * cos ((γ i - γ j) * u))) :=
    fun i j => (integrable_sq_mul_cos hW (γ i - γ j)).const_mul _
  calc
    _ = ∑ i, ∑ j, ∫ u, z i * z j * (v u ^ 2 * cos ((γ i - γ j) * u)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [VPhiR_eq_integral hW, integral_const_mul]
    _ = ∫ u, ∑ i, ∑ j, z i * z j * (v u ^ 2 * cos ((γ i - γ j) * u)) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hint i j]
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
private lemma change_scale (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u, f u = L * ∫ s, f (L * s) := by
  rw [Measure.integral_comp_mul_left f L, smul_eq_mul,
    abs_of_pos (inv_pos.mpr hL), ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
theorem scaled_separated_bound (ι : Type) [Fintype ι] (y z : ι → ℝ)
    (w : ℝ → ℝ) (hsep : ∀ i j, i ≠ j → 17 / 20 ≤ |y i - y j|)
    (hw : Measurable w) (hw0 : ∀ s, 0 ≤ w s)
    (hwM : ∀ s, w s ≤ AMMajorant.scaledMajorant s) :
    (∫ s, w s * ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s))
      ≤ (1253 / 650) * ∑ i, z i ^ 2 := by
  have hsmall : ∀ s, (13 / 14 : ℝ) * w s ≤ Pantera.gMaj s := by
    intro s
    have h := hwM s
    unfold AMMajorant.scaledMajorant at h
    linarith
  have hs : ∀ i j, i ≠ j → Pantera.sep ≤ |y i - y j| := by
    simpa only [Pantera.sep] using hsep
  have h := Pantera.separatedBound ι y z (fun s => (13 / 14) * w s) hs
    (measurable_const.mul hw) (fun s => mul_nonneg (by norm_num) (hw0 s)) hsmall
  have hscale :
      (∫ s, ((13 / 14 : ℝ) * w s) *
        ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s)) =
      (13 / 14 : ℝ) *
        ∫ s, w s * ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun s => by ring)
  rw [hscale] at h
  have hmass : Pantera.LMaj ≤ (179 / 100 : ℝ) := Pantera.lMajBound
  have hn : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right hmass hn
  linarith
def realizedWeight (P : Params) (T s : ℝ) : ℝ :=
  AMW.rhoAM * AMW.MAM * WindowRealization.W P T (P.L T * s) ^ 2
theorem realizedWeight_nonneg (P : Params) (T s : ℝ) :
    0 ≤ realizedWeight P T s :=
  mul_nonneg (mul_nonneg AMMajorant.rho_pos.le AMW.MAM_pos.le) (sq_nonneg _)
theorem realizedWeight_measurable {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T) : Measurable (realizedWeight P T) := by
  have hW := WindowRealization.admWindow hP T h8
  exact (continuous_const.mul
    ((hW.continuous.comp (continuous_const.mul continuous_id)).pow 2)).measurable
theorem realizedWeight_le {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T) (s : ℝ) :
    realizedWeight P T s ≤ AMMajorant.scaledMajorant s := by
  have hW := WindowRealization.admWindow hP T h8
  have hL := hW.L_pos
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  by_cases hs : |s| ≤ 1 / 2
  · have hsq : WindowRealization.W P T (P.L T * s) ^ 2 =
        (WindowProfile.V s / AMW.MAM) * Taper.phi P.ϱ (P.L T) P.w (P.L T * s) ^ 2 := by
      change WindowAsymptotic.phiW P.ϱ (P.L T) P.w (P.L T * s) ^ 2 = _
      rw [WindowAsymptotic.phiW_sq_eq hP.taper hw hL, WindowAsymptotic.hW,
        mul_div_cancel_left₀ s hL.ne']
    have ht0 : 0 ≤ Taper.phi P.ϱ (P.L T) P.w (P.L T * s) :=
      Taper.phi_nonneg hP.taper _
    have ht1 : Taper.phi P.ϱ (P.L T) P.w (P.L T * s) ≤ 1 :=
      Taper.phi_le_one hP.taper _
    have hv : 0 ≤ WindowProfile.V s := (by norm_num : (0 : ℝ) ≤ 67 / 100).trans
      (WindowProfile.V_ge_core hs)
    have he : realizedWeight P T s = AMW.rhoAM * WindowProfile.V s *
        Taper.phi P.ϱ (P.L T) P.w (P.L T * s) ^ 2 := by
      rw [realizedWeight, hsq]
      field_simp [AMW.MAM_pos.ne'] <;> ring
    rw [he]
    exact (mul_le_of_le_one_right (mul_nonneg AMMajorant.rho_pos.le hv)
      (pow_le_one₀ ht0 ht1)).trans (normalized_profile_le_scaled_majorant hs)
  · have hfar : P.L T / 2 ≤ |P.L T * s| := by
      rw [abs_mul, abs_of_pos hL]
      have := lt_of_not_ge hs
      nlinarith
    have hzero := hW.support (P.L T * s) hfar
    rw [realizedWeight, hzero, zero_pow (by omega : 2 ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (Pantera.gMaj_nonneg s)
def realKernel (P : Params) (T γ γ' : ℝ) : ℝ :=
  ((WindowRealization.at24 P T).a T * P.L T ^ 2)⁻¹ *
    ∑ k : Fin (P.d T),
      AdmWindow.vHatR (WindowRealization.W P T)
        (γ - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / P.L T))) *
      AdmWindow.vHatR (WindowRealization.W P T)
        (γ' - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / P.L T)))
theorem realKernel_form_le {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T) (ha : 0 < (WindowRealization.at24 P T).a T)
    (ι : Type) [Fintype ι] (γ z : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 17 / 20 ≤
      |P.L T * (γ i - T) / (2 * π) - P.L T * (γ j - T) / (2 * π)|) :
    (∑ i, ∑ j, z i * realKernel P T (γ i) (γ j) * z j) ≤
      (AMW.rhoAM * AMW.MAM * (WindowRealization.at24 P T).a T)⁻¹ *
        (1253 / 650) * ∑ i, z i ^ 2 := by
  have hW := WindowRealization.admWindow hP T h8
  set L := P.L T with hLdef
  set a := (WindowRealization.at24 P T).a T with hadef
  have hL : 0 < L := hW.L_pos
  have hc : 0 < a * L ^ 2 := by positivity
  set F : ι → ℤ → ℝ := fun i k =>
    AdmWindow.vHatR (WindowRealization.W P T) (γ i - (T + k * (2 * π / L))) with hFdef
  set y : ι → ℝ := fun i => L * (γ i - T) / (2 * π) with hydef
  have hA : (∑ i, ∑ j, z i * realKernel P T (γ i) (γ j) * z j) =
      (a * L ^ 2)⁻¹ * ∑ k : Fin (P.d T), (∑ i, z i * F i ((k : ℕ) : ℤ)) ^ 2 := by
    have hpt : ∀ i j, z i * realKernel P T (γ i) (γ j) * z j =
        ∑ k : Fin (P.d T), (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) := by
      intro i j
      simp only [realKernel, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [F, a, L]
      push_cast
      ring
    rw [Finset.mul_sum]
    calc
      _ = ∑ i, ∑ j, ∑ k : Fin (P.d T), (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
      _ = ∑ i, ∑ k : Fin (P.d T), ∑ j, (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k : Fin (P.d T), ∑ i, ∑ j, (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) :=
        Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sq (∑ i, z i * F i ((k : ℕ) : ℤ)), Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
  have hB : (∑ k : Fin (P.d T), (∑ i, z i * F i ((k : ℕ) : ℤ)) ^ 2) ≤
      L * ∑ i, ∑ j, z i * z j * AdmWindow.VPhiR (WindowRealization.W P T) (γ i - γ j) :=
    finite_sum_le_hasSum (P.d T) (poisson_square hW T γ z) (fun k => sq_nonneg _)
  have hD : (∑ i, ∑ j, z i * z j * AdmWindow.VPhiR (WindowRealization.W P T) (γ i - γ j)) =
      L * ((AMW.rhoAM * AMW.MAM)⁻¹ *
        ∫ s, realizedWeight P T s *
          ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s)) := by
    rw [cosine_integral hW γ z,
      change_scale (fun u => WindowRealization.W P T u ^ 2 *
        ∑ i, ∑ j, z i * z j * cos ((γ i - γ j) * u)) hL]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    have harg : ∀ i j, (γ i - γ j) * (L * s) = 2 * π * (y i - y j) * s := by
      intro i j
      dsimp [y]
      field_simp <;> ring
    simp only [harg, realizedWeight]
    change _ = (AMW.rhoAM * AMW.MAM)⁻¹ *
      (AMW.rhoAM * AMW.MAM * WindowRealization.W P T (L * s) ^ 2 * _)
    field_simp [AMMajorant.rho_pos.ne', AMW.MAM_pos.ne'] <;> ring
  have hE := scaled_separated_bound ι y z (realizedWeight P T) hsep
    (realizedWeight_measurable hP T h8) (realizedWeight_nonneg P T)
    (realizedWeight_le hP T h8)
  rw [hA]
  calc
    _ ≤ (a * L ^ 2)⁻¹ * (L * (L * ((AMW.rhoAM * AMW.MAM)⁻¹ *
        ((1253 / 650) * ∑ i, z i ^ 2)))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      refine hB.trans ?_
      rw [hD]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr
            (mul_nonneg AMMajorant.rho_pos.le AMW.MAM_pos.le))) hL.le) hL.le
    _ = _ := by
      dsimp [a]
      field_simp [hL.ne', ha.ne', AMMajorant.rho_pos.ne', AMW.MAM_pos.ne']
      <;> ring
lemma normalization_limit_identity : AMW.rhoAM * AMW.MAM * WindowAsymptotic.aInf = 1 := by
  rw [WindowAsymptotic.aInf_eq]
  change (1 / AMW.K0AM) * AMW.MAM * (AMW.K0AM / AMW.MAM) = 1
  field_simp [AMW.K0AM_pos.ne', AMW.MAM_pos.ne']
/-- The finite-height normalization tends to one; retain explicit slack51/50. -/
theorem eventually_normalization {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 0 < (WindowRealization.at24 P T).a T ∧
      (AMW.rhoAM * AMW.MAM * (WindowRealization.at24 P T).a T)⁻¹ ≤ (51 / 50 : ℝ) := by
  have ht : Tendsto (fun T => (WindowRealization.at24 P T).a T) atTop (𝓝 WindowAsymptotic.aInf) := by
    convert WindowAsymptotic.tendsto_aW hP using 1
    funext T
    rw [WindowRealization.at_a hP T] <;> rfl
  have hnear : (50 / 51 : ℝ) * WindowAsymptotic.aInf < WindowAsymptotic.aInf := by
    nlinarith [WindowAsymptotic.aInf_pos]
  filter_upwards [ht.eventually (lt_mem_nhds hnear)] with T hT
  have ha : 0 < (WindowRealization.at24 P T).a T :=
    lt_trans (mul_pos (by norm_num) WindowAsymptotic.aInf_pos) hT
  refine ⟨ha, ?_⟩
  have hr : 0 < AMW.rhoAM * AMW.MAM := mul_pos AMMajorant.rho_pos AMW.MAM_pos
  have hh := mul_le_mul_of_nonneg_left hT.le hr.le
  have hi := normalization_limit_identity
  rw [inv_eq_one_div, div_le_iff₀ (mul_pos hr ha)]
  nlinarith only [hh, hi]
theorem eventually_realKernel_form_le {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 0 < (WindowRealization.at24 P T).a T ∧
      ∀ (ι : Type) [Fintype ι] (γ z : ι → ℝ),
        (∀ i j, i ≠ j → 17 / 20 ≤
          |P.L T * (γ i - T) / (2 * π) - P.L T * (γ j - T) / (2 * π)|) →
        (∑ i, ∑ j, z i * realKernel P T (γ i) (γ j) * z j) ≤
          (63903 / 32500) * ∑ i, z i ^ 2 := by
  filter_upwards [Zeta23.ThmD.eventually_w8 hP, eventually_normalization hP] with T h8 hnorm
  refine ⟨hnorm.1, ?_⟩
  intro ι _ γ z hsep
  have h := realKernel_form_le hP T h8 hnorm.1 ι γ z hsep
  have hn : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm' := mul_le_mul_of_nonneg_right hnorm.2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1253 / 650) hn)
  calc
    _ ≤ _ := h
    _ ≤ (51 / 50 : ℝ) * ((1253 / 650) * ∑ i, z i ^ 2) := by
      simpa only [mul_assoc] using hnorm'
    _ = (63903 / 32500) * ∑ i, z i ^ 2 := by ring
/-- Exact identification with the retained matrix used by the AM counting consumer. -/
theorem gram_re_eq (Z : ZeroConfig) {P : Params} (hP : P.Valid) (T : ℝ)
    (ha : 0 < (WindowRealization.at24 P T).a T)
    (u v : Zeta23Ext.Bridge.retained Z (WindowRealization.at24 P T) T) :
    (Zeta23Ext.Bridge.gram Z (WindowRealization.at24 P T) T u v).re =
      realKernel P T (u.1 : ℂ).im (v.1 : ℂ).im := by
  have hc : 0 ≤ Zeta23Ext.Bridge.aL2 (WindowRealization.at24 P T) T := by
    unfold Zeta23Ext.Bridge.aL2
    exact mul_nonneg ha.le (sq_nonneg _)
  rw [Zeta23Ext.Bridge.gram_apply Z (WindowRealization.at24 P T) T
    (phiHatReal_at24 hP T) hc, Complex.ofReal_re]
  simp only [Zeta23Ext.Bridge.aL2, at24_L,
    at24_phiHatR_eq hP T] <;> rfl
theorem eventually_gram_form_le (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι]
      (e : ι → Zeta23Ext.Bridge.retained Z (WindowCountingBase.mtParams T) T)
      (z : ι → ℝ),
      (∀ i j, i ≠ j → 17 / 20 ≤
        |Zeta23Ext.Bridge.xret Z (WindowCountingBase.mtParams T) T (e i) -
          Zeta23Ext.Bridge.xret Z (WindowCountingBase.mtParams T) T (e j)|) →
      (∑ i, ∑ j, z i *
        (Zeta23Ext.Bridge.gram Z (WindowCountingBase.mtParams T) T (e i) (e j)).re * z j)
        ≤ (63903 / 32500) * ∑ i, z i ^ 2 := by
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  filter_upwards [eventually_realKernel_form_le hP] with T hT
  intro ι _ e z hsep
  have hs : ∀ i j, i ≠ j → 17 / 20 ≤
      |(paramsOf stdProfile 1).L T * ((e i).1.val.im - T) / (2 * π) -
        (paramsOf stdProfile 1).L T * ((e j).1.val.im - T) / (2 * π)| := hsep
  have h := hT.2 ι (fun i => ((e i).1 : ℂ).im) z hs
  have heq : ∀ i j,
      (Zeta23Ext.Bridge.gram Z (WindowCountingBase.mtParams T) T (e i) (e j)).re =
        realKernel (paramsOf stdProfile 1) T ((e i).1 : ℂ).im ((e j).1 : ℂ).im :=
    fun i j => gram_re_eq Z hP T hT.1 (e i) (e j)
  simpa only [heq] using h
#print axioms eventually_gram_form_le
end StructuralGoal20261016.WindowSeparated
namespace StructuralGoal20261016.WindowSeparatedSpectrum
open WindowSeparated
open Classical
theorem gram_entry_eq_re (Z : ZeroConfig) {P : Params} (hP : P.Valid)
    (T : ℝ) (ha : 0 < (WindowRealization.at24 P T).a T)
    (u v : retained Z (WindowRealization.at24 P T) T) :
    gram Z (WindowRealization.at24 P T) T u v =
      ((gram Z (WindowRealization.at24 P T) T u v).re : ℂ) := by
  have hc : 0 ≤ aL2 (WindowRealization.at24 P T) T := by
    unfold aL2
    exact mul_nonneg ha.le (sq_nonneg _)
  simp only [gram_apply Z (WindowRealization.at24 P T) T (phiHatReal_at24 hP T) hc,
    Complex.ofReal_re]
theorem eventually_submatrix_eigenvalues_le (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (e : ι → retained Z (WindowCountingBase.mtParams T) T),
      (∀ i j, i ≠ j → 17 / 20 ≤
        |xret Z (WindowCountingBase.mtParams T) T (e i) - xret Z (WindowCountingBase.mtParams T) T (e j)|) →
      ∀ k : ι,
        ((gram_isHermitian Z (WindowCountingBase.mtParams T) T).submatrix e).eigenvalues k ≤
          (63903 / 32500 : ℝ) := by
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  filter_upwards [WindowSeparated.eventually_normalization hP,
    WindowSeparated.eventually_gram_form_le Z] with T hnorm hform
  intro ι _ _ e hsep k
  have hreal : ∀ i j : ι,
      ((gram Z (WindowCountingBase.mtParams T) T).submatrix e e) i j =
        ((gram Z (WindowCountingBase.mtParams T) T (e i) (e j)).re : ℂ) :=
    fun i j => gram_entry_eq_re Z hP T hnorm.1 (e i) (e j)
  exact Meshuggah.Gram.eigenvalues_le_of_real_form
    ((gram_isHermitian Z (WindowCountingBase.mtParams T) T).submatrix e) hreal
    (fun z => hform ι e z hsep) k
theorem eventually_submatrix_eigenvalues_le_two (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (e : ι → retained Z (WindowCountingBase.mtParams T) T),
      (∀ i j, i ≠ j → 17 / 20 ≤
        |xret Z (WindowCountingBase.mtParams T) T (e i) - xret Z (WindowCountingBase.mtParams T) T (e j)|) →
      ∀ k : ι,
        ((gram_isHermitian Z (WindowCountingBase.mtParams T) T).submatrix e).eigenvalues k ≤ 2 := by
  filter_upwards [eventually_submatrix_eigenvalues_le Z] with T hT
  intro ι _ _ e hsep k
  exact (hT ι e hsep k).trans (by norm_num)
theorem eventually_principal_eigenvalues_le_two (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ S : Finset (retained Z (WindowCountingBase.mtParams T) T),
      (∀ i j : S, i ≠ j → 17 / 20 ≤
        |xret Z (WindowCountingBase.mtParams T) T i.1 - xret Z (WindowCountingBase.mtParams T) T j.1|) →
      ∀ k : S,
        ((gram_isHermitian Z (WindowCountingBase.mtParams T) T).submatrix
          (Subtype.val : S → retained Z (WindowCountingBase.mtParams T) T)).eigenvalues k ≤ 2 := by
  filter_upwards [eventually_submatrix_eigenvalues_le_two Z] with T hT
  intro S hsep k
  exact hT S Subtype.val hsep k
#print axioms eventually_principal_eigenvalues_le_two
end StructuralGoal20261016.WindowSeparatedSpectrum
end
