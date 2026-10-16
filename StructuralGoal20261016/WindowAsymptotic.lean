/- SPDX-License-Identifier: Apache-2.0
Actual v24 taper limits and limiting cRatio.
Adapted from AMW.abs_hW_le through AMW.cRatio_W_pos, and the subsequent
AMW.bInf_gt_half argument, in the attributed Core. This replaces the fixed
profile only, without asserting any unproved local floor or proportion.
-/
import StructuralGoal20261016.WindowRealization
import StructuralGoal20261016.WindowEnergyBound
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter Topology
open scoped BigOperators
open Zeta23 AMW
namespace StructuralGoal20261016.WindowAsymptotic
open WindowProfile

def hW (L u : ℝ) : ℝ := V (u/L) / MAM
def phiW (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ := WindowProfile.phi ϱ L w
def localFunW (P : Params) (T : ℝ) : PrimeSide.LocalFun :=
 AdmWindow.localFun (phiW P.ϱ (P.L T) P.w) (P.L T)
def vConv (r : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2-r), V s * V (s+r)
def aInf : ℝ := (∫ s in (-(1:ℝ)/2)..(1/2), V s) / MAM
def bInf : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), (V s / MAM)^2
def JInf : ℝ := 2 * (∫ r in (0:ℝ)..1, vConv r * r) / MAM^2

theorem abs_V_le (s : ℝ) : |V s| ≤ 5/4 := by
 rw [V_eq_v24]
 have hp := StructuralW10Followup20261016.WindowProfileGeneral.abs_perturb_le _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 s
 have hc := Real.abs_cos_le_one (Real.sqrt 2*s)
 unfold StructuralW10Followup20261016.NewWindows.v24
   StructuralW10Followup20261016.WindowProfileGeneral.profile
 exact (abs_add_le _ _).trans (by linarith)

theorem hW_core_ge {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L/2) :
 (67/125 : ℝ) ≤ hW L u := by
 have h := V_ge_core (AMW.abs_div_le_half hL hu)
 unfold hW MAM
 rw [le_div_iff₀ (by norm_num)]
 linarith

theorem phiW_nonneg {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (u : ℝ) :
 0 ≤ phiW ϱ L w u := by
 unfold phiW WindowProfile.phi AMW.phiM AMW.fP
 exact mul_nonneg (Real.sqrt_nonneg _) (Taper.phi_nonneg hϱ u)

theorem phiW_le_one {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (u : ℝ) :
 phiW ϱ L w u ≤ 1 := by
 have hf : Real.sqrt (V (u/L)/MAM) ≤ 1 := by
   rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
   apply Real.sqrt_le_sqrt
   rw [div_le_one MAM_pos]
   exact V_le _
 unfold phiW WindowProfile.phi AMW.phiM AMW.fP
 exact (mul_le_mul hf (Taper.phi_le_one hϱ u)
   (Taper.phi_nonneg hϱ u) zero_le_one).trans (by norm_num)

theorem phiW_eq_zero {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L/2 ≤ |u|) :
 phiW ϱ L w u = 0 := AMW.phiM_eq_zero hϱ hw hu

theorem phiW_sq_eq {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) :
 phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := by
 rcases le_or_gt (L/2) |u| with hu | hu
 · rw [phiW_eq_zero hϱ hw hu, Taper.phi_eq_zero hϱ hw hu]
   simp
 · have hv : 0 ≤ V (u/L)/MAM :=
     (by norm_num : (0:ℝ) ≤ 67/125).trans (hW_core_ge hL hu.le)
   unfold phiW WindowProfile.phi AMW.phiM AMW.fP hW
   rw [mul_pow, Real.sq_sqrt hv]

theorem phiW_continuous {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2*w ≤ L) :
 Continuous (phiW ϱ L w) :=
 (AMW.phiM_contDiff (AMW.pvFactor_fP actual_profile (by linarith)) hϱ hw hwL).continuous

theorem abs_hW_le (L u : ℝ) : |hW L u| ≤ 1 := by
 unfold hW
 rw [abs_div, abs_of_pos MAM_pos, div_le_one MAM_pos]
 exact abs_V_le _
theorem hW_continuous (L : ℝ) : Continuous (hW L) :=
 (V_continuous.comp (continuous_id.div_const L)).div_const MAM
variable {ϱ : ℝ → ℝ} {L w : ℝ}
theorem integral_hW (hL : 0 < L) :
   ∫ u in Set.Icc (-(L/2)) (L/2), hW L u = L * aInf := by
 rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
 unfold hW aInf
 rw [integral_scale (v := fun s => V s / MAM) hL, intervalIntegral.integral_div]
theorem integral_hW_sq (hL : 0 < L) :
   ∫ u in Set.Icc (-(L/2)) (L/2), hW L u ^ 2 = L * bInf := by
 rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2)]
 unfold hW bInf
 exact integral_scale (v := fun s => (V s / MAM) ^ 2) hL
theorem aW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   |L⁻¹ * (∫ u, phiW ϱ L w u ^ 2) - aInf| ≤ 2 * w / L := by
 have hw0 : 0 < w := by linarith
 have hwL' : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 have hwin : ∫ u, phiW ϱ L w u ^ 2 = ∫ u, hW L u * Taper.phi ϱ L w u ^ 2 := by
   congr 1; funext u; exact phiW_sq_eq hϱ hw0 hL u
 have hcore := edge_est (h := hW L) (p := fun u => Taper.phi ϱ L w u ^ 2) hw0 hwL'
   (abs_hW_le L) (fun u => sq_nonneg _)
   (fun u => by
     calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 :=
           pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
       _ = 1 := one_pow 2)
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 2 = 1
     rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 2 = 0
     rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
   ((Taper.phi_continuous hϱ hw0 hwL').pow 2) (hW_continuous L)
 rw [integral_hW hL] at hcore
 rw [hwin]
 have e : L⁻¹ * (∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - aInf
     = L⁻¹ * ((∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - L * aInf) := by
   field_simp
 rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
 calc L⁻¹ * |(∫ u, hW L u * Taper.phi ϱ L w u ^ 2) - L * aInf| ≤ L⁻¹ * (2 * w) :=
       mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
   _ = 2 * w / L := by field_simp
theorem bW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   |L⁻¹ * (∫ u, phiW ϱ L w u ^ 4) - bInf| ≤ 2 * w / L := by
 have hw0 : 0 < w := by linarith
 have hwL' : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 have hwin : ∫ u, phiW ϱ L w u ^ 4 = ∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by
   congr 1; funext u
   have := phiW_sq_eq hϱ hw0 hL u (ϱ := ϱ) (w := w)
   calc phiW ϱ L w u ^ 4 = (phiW ϱ L w u ^ 2) ^ 2 := by ring
     _ = (hW L u * Taper.phi ϱ L w u ^ 2) ^ 2 := by rw [this]
     _ = hW L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by ring
 have hcore := edge_est (h := fun u => hW L u ^ 2) (p := fun u => Taper.phi ϱ L w u ^ 4) hw0 hwL'
   (fun u => by
     rw [abs_pow]
     calc |hW L u| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_hW_le L u) 2
       _ = 1 := one_pow 2)
   (fun u => by positivity)
   (fun u => by
     calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 :=
           pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
       _ = 1 := one_pow 4)
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 4 = 1
     rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
   (fun u hu => by
     show Taper.phi ϱ L w u ^ 4 = 0
     rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow (by norm_num : (4:ℕ) ≠ 0)])
   ((Taper.phi_continuous hϱ hw0 hwL').pow 4) ((hW_continuous L).pow 2)
 rw [integral_hW_sq hL] at hcore
 rw [hwin]
 have e : L⁻¹ * (∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - bInf
     = L⁻¹ * ((∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L * bInf) := by
   field_simp
 rw [e, abs_mul, abs_of_pos (inv_pos.mpr hL)]
 calc L⁻¹ * |(∫ u, hW L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L * bInf| ≤ L⁻¹ * (2 * w) :=
       mul_le_mul_of_nonneg_left hcore (inv_pos.mpr hL).le
   _ = 2 * w / L := by field_simp
def sW (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (hW L) u
theorem sW_nonneg (hL : 0 < L) (u : ℝ) : 0 ≤ sW L u := by
 unfold sW
 apply Set.indicator_nonneg
 intro x hx
 have := hW_core_ge hL (abs_le.mpr ⟨hx.1, hx.2⟩)
 linarith
theorem abs_sW_le (L u : ℝ) : |sW L u| ≤ 1 := by
 unfold sW
 by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
 · rw [Set.indicator_of_mem hm]; exact abs_hW_le L u
 · rw [Set.indicator_of_notMem hm, abs_zero]; exact zero_le_one
theorem sW_measurable (L : ℝ) : Measurable (sW L) :=
 Measurable.indicator (hW_continuous L).measurable measurableSet_Icc
theorem sW_integrable (L : ℝ) : Integrable (sW L) :=
 (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
   ((hW_continuous L).continuousOn.integrableOn_compact isCompact_Icc)
theorem integral_abs_phiWsq_sub_sharp (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
   ∫ u, |phiW ϱ L w u ^ 2 - sW L u| ≤ 2 * w := by
 have hL : 0 < L := by linarith
 set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
     + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
 have hImaj : Integrable maj := by
   apply Integrable.add <;>
     exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
       (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
 have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
   Set.indicator_nonneg (fun _ _ => zero_le_one) u
 have hpt : ∀ u : ℝ, |phiW ϱ L w u ^ 2 - sW L u| ≤ maj u := by
   intro u
   have hmaj0 : 0 ≤ maj u := by
     rw [hmaj]
     exact add_nonneg (hind0 _ u) (hind0 _ u)
   have hval : phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := phiW_sq_eq hϱ hw hL u
   rcases le_or_gt |u| (L/2 - w) with hpl | hedge
   · have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
       rw [abs_le] at hpl
       constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
     rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one]
     unfold sW
     rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
     exact hmaj0
   · rcases le_or_gt |u| (L/2) with hin | hout
     · have hbound : |phiW ϱ L w u ^ 2 - sW L u| ≤ 1 := by
         have h1' : 0 ≤ phiW ϱ L w u ^ 2 := sq_nonneg _
         have h2' : phiW ϱ L w u ^ 2 ≤ 1 := by
           calc phiW ϱ L w u ^ 2 ≤ 1 ^ 2 :=
                 pow_le_pow_left₀ (phiW_nonneg hϱ u) (phiW_le_one hϱ u) 2
             _ = 1 := one_pow 2
         have h3' : 0 ≤ sW L u := sW_nonneg hL u
         have h4' : sW L u ≤ 1 := (abs_le.mp (abs_sW_le L u)).2
         rw [abs_le]
         constructor <;> linarith
       have hone : (1:ℝ) ≤ maj u := by
         rw [hmaj]
         show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
           + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
         rcases le_or_gt u 0 with hneg | hpos
         · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
             have : |u| = -u := abs_of_nonpos hneg
             rw [this] at hin hedge
             exact ⟨by linarith, by linarith⟩
           have := hind0 (Set.Icc (L/2 - w) (L/2)) u
           rw [Set.indicator_of_mem hu1, Pi.one_apply]
           linarith
         · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
             have : |u| = u := abs_of_pos hpos
             rw [this] at hin hedge
             exact ⟨by linarith, by linarith⟩
           have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
           rw [Set.indicator_of_mem hu1, Pi.one_apply]
           linarith
       linarith
     · have h1' : phiW ϱ L w u = 0 := phiW_eq_zero hϱ hw (le_of_lt hout)
       have h2' : sW L u = 0 := by
         unfold sW
         apply Set.indicator_of_notMem
         intro hm
         have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
         linarith
       rw [h1', h2']
       norm_num
       exact hmaj0
 calc ∫ u, |phiW ϱ L w u ^ 2 - sW L u|
     ≤ ∫ u, maj u := by
       apply MeasureTheory.integral_mono_of_nonneg
         (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
         (MeasureTheory.ae_of_all _ hpt)
   _ = 2 * w := by
       rw [hmaj]
       rw [MeasureTheory.integral_add
         ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
           (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
         ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
           (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
         MeasureTheory.integral_indicator_one measurableSet_Icc,
         MeasureTheory.integral_indicator_one measurableSet_Icc,
         MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
         Real.volume_Icc, Real.volume_Icc,
         ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
       ring
theorem phiW_sq_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) :
   HasCompactSupport (fun u => phiW ϱ L w u ^ 2) := by
 apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -(L/2)) (b := L/2))
 intro x hx
 rw [Function.mem_support] at hx
 by_contra hmem
 apply hx
 show phiW ϱ L w x ^ 2 = 0
 rw [Set.mem_Icc, not_and_or, not_le, not_le] at hmem
 have : L / 2 ≤ |x| := by
   rcases hmem with hc | hc
   · rw [abs_of_neg (by linarith : x < 0)]; linarith
   · rw [abs_of_pos (by linarith : 0 < x)]; linarith
 rw [phiW_eq_zero hϱ hw this, zero_pow two_ne_zero]
theorem autocorr_phiWsq_close (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
   |Params.autocorr (fun u => phiW ϱ L w u ^ 2) y - ∫ u, sW L u * sW L (u + y)| ≤ 4 * w := by
 set h : ℝ → ℝ := fun u => phiW ϱ L w u ^ 2 with hhdef
 set k : ℝ → ℝ := sW L with hkdef
 have hh_cont : Continuous h := (phiW_continuous hϱ hw hwL).pow 2
 have hh1 : ∀ u, |h u| ≤ 1 := by
   intro u
   rw [hhdef]
   simp only
   rw [abs_of_nonneg (sq_nonneg _)]
   calc phiW ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (phiW_nonneg hϱ u) (phiW_le_one hϱ u) 2
     _ = 1 := one_pow 2
 have hk_meas : Measurable k := sW_measurable L
 have hk1 : ∀ u, |k u| ≤ 1 := abs_sW_le L
 have hint_h : Integrable h :=
   hh_cont.integrable_of_hasCompactSupport (phiW_sq_hasCompactSupport hϱ hw (by linarith))
 have hint_k : Integrable k := sW_integrable L
 have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
 have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
 have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
 have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
 have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
   hint_hy.aestronglyMeasurable
 have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
   have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hh1 (u + y))
   exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
 have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
   exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hk1 u)
 have hint_hh : Integrable (fun u => h u * h (u + y)) := by
   have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hh1 (u + y))
   exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
 have hint_kk : Integrable (fun u => k u * k (u + y)) := by
   exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
     rw [Real.norm_eq_abs]
     exact hk1 u)
 have hdecomp : Params.autocorr h y - ∫ u, k u * k (u + y)
     = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
   have e1 : Params.autocorr h y - ∫ u, k u * k (u + y)
       = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
     rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl,
       MeasureTheory.integral_sub hint_hh hint_kk]
   rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
   apply MeasureTheory.integral_congr_ae
   apply MeasureTheory.ae_of_all
   intro u
   ring
 have hd2w := integral_abs_phiWsq_sub_sharp hϱ hw hwL
 have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
 have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
   calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
         MeasureTheory.abs_integral_le_integral_abs
     _ ≤ ∫ u, |h u - k u| := by
         apply MeasureTheory.integral_mono_of_nonneg
           (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
           (MeasureTheory.ae_of_all _ fun u => ?_)
         show |(h u - k u) * h (u + y)| ≤ |h u - k u|
         rw [abs_mul]
         calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
               mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
           _ = |h u - k u| := mul_one _
     _ ≤ 2 * w := hd2w
 have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
   have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
     MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
   calc |∫ u, k u * (h (u + y) - k (u + y))|
       ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
     _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
         apply MeasureTheory.integral_mono_of_nonneg
           (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
           (MeasureTheory.ae_of_all _ fun u => ?_)
         show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
         rw [abs_mul]
         calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
               mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
           _ = _ := one_mul _
     _ = ∫ u, |h u - k u| := htrans
     _ ≤ 2 * w := hd2w
 calc |Params.autocorr h y - ∫ u, k u * k (u + y)|
     = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by
       rw [hdecomp]
   _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
   _ ≤ 4 * w := by linarith
theorem sharp_overlap (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
   ∫ u, sW L u * sW L (u + y) = L * vConv (y / L) / MAM ^ 2 := by
 have hind : ∀ u : ℝ, sW L u * sW L (u + y)
     = (Set.Icc (-(L/2)) (L/2 - y)).indicator (fun u => hW L u * hW L (u + y)) u := by
   intro u
   unfold sW
   by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
   · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
     have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
     rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
   · rw [Set.indicator_of_notMem hu]
     rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
     rcases hu with hu | hu
     · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
         (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
     · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
         (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
 rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
   MeasureTheory.integral_indicator measurableSet_Icc,
   MeasureTheory.integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
 have hF : ∀ u, hW L u * hW L (u + y) = (fun s => V s * V (s + y / L) / MAM ^ 2) (u / L) := by
   intro u
   simp only [hW]
   rw [show (u + y) / L = u / L + y / L by ring]
   ring
 simp_rw [hF]
 rw [intervalIntegral.integral_comp_div (f := fun s => V s * V (s + y / L) / MAM ^ 2) hL.ne',
   smul_eq_mul, intervalIntegral.integral_div,
   show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
   show (L/2 - y) / L = 1/2 - y / L by field_simp]
 unfold vConv
 ring
theorem continuous_vConv : Continuous vConv := by
 unfold vConv
 have h : Continuous (Function.uncurry fun (r s : ℝ) => V s * V (s + r)) :=
   (V_continuous.comp continuous_snd).mul (V_continuous.comp (continuous_snd.add continuous_fst))
 exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous h
   (continuous_const.sub continuous_id)
theorem JW_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
   |2 / L ^ 3 * (∫ y in (0:ℝ)..L, Params.autocorr (fun u => phiW ϱ L w u ^ 2) y * y) - JInf|
     ≤ 8 * w / L := by
 have hw0 : 0 < w := by linarith
 have hwL' : 2 * w ≤ L := by linarith
 have hL : 0 < L := by linarith
 set A : ℝ → ℝ := Params.autocorr (fun u => phiW ϱ L w u ^ 2) with hAdef
 set C : ℝ → ℝ := fun y => L * vConv (y / L) / MAM ^ 2 with hCdef
 have hAcont : Continuous A := by
   rw [hAdef]
   refine Taper.autocorr_continuous_of_support _ (M := L/2) ((phiW_continuous hϱ hw0 hwL').pow 2) ?_
   intro u hu
   show phiW ϱ L w u ^ 2 = 0
   rw [phiW_eq_zero hϱ hw0 hu, zero_pow two_ne_zero]
 have hCcont : Continuous C := by
   rw [hCdef]
   exact ((continuous_const.mul (continuous_vConv.comp (continuous_id.div_const L))).div_const _)
 have hIA : IntervalIntegrable (fun y => A y * y) MeasureTheory.volume 0 L :=
   (hAcont.mul continuous_id).intervalIntegrable 0 L
 have hIC : IntervalIntegrable (fun y => C y * y) MeasureTheory.volume 0 L :=
   (hCcont.mul continuous_id).intervalIntegrable 0 L
 have hsplit : ∫ y in (0:ℝ)..L, A y * y
     = (∫ y in (0:ℝ)..L, (A y - C y) * y) + ∫ y in (0:ℝ)..L, C y * y := by
   have e1 : ∫ y in (0:ℝ)..L, (A y - C y) * y = ∫ y in (0:ℝ)..L, (A y * y - C y * y) :=
     intervalIntegral.integral_congr (fun y _ => by ring)
   rw [e1, intervalIntegral.integral_sub hIA hIC]
   ring
 have hcmp : |∫ y in (0:ℝ)..L, (A y - C y) * y| ≤ 4 * w * L * L := by
   have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := 4 * w * L)
     (f := fun y => (A y - C y) * y) (a := 0) (b := L) ?_
   · rw [Real.norm_eq_abs] at hb
     calc |∫ y in (0:ℝ)..L, (A y - C y) * y| ≤ 4 * w * L * |L - 0| := hb
       _ = 4 * w * L * L := by rw [sub_zero, abs_of_pos hL]
   · intro y hy
     rw [Set.uIoc_of_le hL.le] at hy
     rw [Real.norm_eq_abs]
     show |(A y - C y) * y| ≤ 4 * w * L
     rw [abs_mul]
     have hAC : |A y - C y| ≤ 4 * w := by
       have h1 := autocorr_phiWsq_close hϱ hw0 hwL' y (L := L)
       rw [sharp_overlap hL hy.1.le hy.2] at h1
       exact h1
     calc |A y - C y| * |y| ≤ (4 * w) * L := by
           apply mul_le_mul hAC ?_ (abs_nonneg _) (by positivity)
           rw [abs_of_pos hy.1]
           exact hy.2
       _ = 4 * w * L := rfl
 have hmain : 2 / L ^ 3 * ∫ y in (0:ℝ)..L, C y * y = JInf := by
   have hG : ∀ y, C y * y = (L ^ 2 / MAM ^ 2) * ((fun r => vConv r * r) (y / L)) := by
     intro y
     simp only [hCdef]
     field_simp
   simp_rw [hG]
   rw [intervalIntegral.integral_const_mul,
     intervalIntegral.integral_comp_div (f := fun r => vConv r * r) hL.ne', smul_eq_mul,
     zero_div, div_self hL.ne']
   unfold JInf
   field_simp
 have e : 2 / L ^ 3 * (∫ y in (0:ℝ)..L, A y * y) - JInf
     = 2 / L ^ 3 * (∫ y in (0:ℝ)..L, (A y - C y) * y) := by
   rw [hsplit, mul_add, hmain]; ring
 rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / L ^ 3)]
 calc 2 / L ^ 3 * |∫ y in (0:ℝ)..L, (A y - C y) * y|
     ≤ 2 / L ^ 3 * (4 * w * L * L) := mul_le_mul_of_nonneg_left hcmp (by positivity)
   _ = 8 * w / L := by field_simp; ring
theorem V_pos_core {s : ℝ} (hs : s ∈ Set.Icc (-(1:ℝ)/2) (1/2)) : 0 < V s :=
 lt_of_lt_of_le (by norm_num) (V_ge_core (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩))
theorem vConv_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : 0 ≤ vConv r := by
 unfold vConv
 apply intervalIntegral.integral_nonneg (by linarith)
 intro s hs
 exact mul_nonneg (V_pos_core ⟨hs.1, by linarith [hs.2]⟩).le
   (V_pos_core ⟨by linarith [hs.1], by linarith [hs.2]⟩).le
theorem JInf_nonneg : 0 ≤ JInf := by
 unfold JInf
 apply div_nonneg _ (sq_nonneg _)
 apply mul_nonneg (by norm_num)
 apply intervalIntegral.integral_nonneg zero_le_one
 intro r hr
 exact mul_nonneg (vConv_nonneg hr.1 hr.2) hr.1
theorem bInf_pos : 0 < bInf := by
 unfold bInf
 apply intervalIntegral.intervalIntegral_pos_of_pos_on
 · exact ((V_continuous.div_const _).pow 2).intervalIntegrable _ _
 · intro s hs
   have h1 := V_pos_core ⟨hs.1.le, hs.2.le⟩
   have h2 := MAM_pos
   positivity
 · norm_num
theorem aInf_pos : 0 < aInf := by
 unfold aInf
 apply div_pos _ MAM_pos
 apply intervalIntegral.intervalIntegral_pos_of_pos_on
 · exact V_continuous.intervalIntegrable _ _
 · intro s hs
   exact V_pos_core ⟨hs.1.le, hs.2.le⟩
 · norm_num
theorem tendsto_aW {P : Params} (hP : P.Valid) :
   Tendsto (fun T => (localFunW P T).a) atTop (𝓝 aInf) := by
 apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
 filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
 exact aW_close hP.taper hP.one_le_w hT
theorem tendsto_bW {P : Params} (hP : P.Valid) :
   Tendsto (fun T => (localFunW P T).b) atTop (𝓝 bInf) := by
 apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
 filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
 exact bW_close hP.taper hP.one_le_w hT
theorem tendsto_JW {P : Params} (hP : P.Valid) :
   Tendsto (fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunW P T).g y * y) atTop
     (𝓝 JInf) := by
 apply ThmD.tendsto_of_close hP.lam_pos (C := 8)
 filter_upwards [(Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop (8 * P.w)] with T hT
 exact JW_close hP.taper hP.one_le_w hT
theorem tendsto_cRatio_W {P : Params} (hP : P.Valid) :
   Tendsto (fun T => ThmD.cRatio (P.lam1 T) (localFunW P T).a (localFunW P T).b
     (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (localFunW P T).g y * y)) atTop
     (𝓝 (ThmD.cRatio P.lam aInf bInf JInf)) := by
 have hden : 0 < bInf + P.lam ^ 2 * JInf := by
   have h1 := JInf_nonneg
   have h2 := bInf_pos
   positivity
 have hl1 := ThmD.tendsto_lam1 hP.lam_pos
 have hnum := hl1.mul ((tendsto_aW hP).pow 2)
 have hdenT := (tendsto_bW hP).add ((hl1.pow 2).mul (tendsto_JW hP))
 exact hnum.div hdenT hden.ne'
theorem cRatio_W_pos {lam : ℝ} (hlam : 0 < lam) : 0 < ThmD.cRatio lam aInf bInf JInf := by
 unfold ThmD.cRatio
 have h1 := JInf_nonneg
 have h2 := bInf_pos
 have h3 := aInf_pos
 positivity
theorem integral_V : (∫ t in (-(1:ℝ)/2)..(1/2), V t) =
 Real.sqrt 2 * Real.sin (Real.sqrt 2/2) := by
 simp_rw [V_eq]
 exact WindowEnergy.integral_v 24 WindowKernel.d24

theorem aInf_eq : aInf = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) / MAM := by
 unfold aInf; rw [integral_V]
theorem aInf_gt_half : 1 / 2 < aInf := by
 rw [aInf_eq]
 have hb := sqrt2_half_bounds
 have hs := sin_theta0_ge
 unfold MAM
 rw [lt_div_iff₀ (by norm_num)]
 have h2 : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
 nlinarith
theorem aInf_sq_le_bInf : aInf ^ 2 ≤ bInf := by
 set q : ℝ → ℝ := fun s => V s / MAM with hq
 have hqc : Continuous q := V_continuous.div_const _
 have ha : aInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s := by
   unfold aInf; rw [hq, intervalIntegral.integral_div]
 have hb : bInf = ∫ s in (-(1:ℝ)/2)..(1/2), q s ^ 2 := rfl
 have h0 : 0 ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 :=
   intervalIntegral.integral_nonneg (by norm_num) fun s _ => sq_nonneg _
 have hexp : ∫ s in (-(1:ℝ)/2)..(1/2), (q s - aInf) ^ 2 = bInf - aInf ^ 2 := by
   have e : (fun s => (q s - aInf) ^ 2) = fun s => q s ^ 2 - 2 * aInf * q s + aInf ^ 2 := by
     funext s; ring
   have i1 : IntervalIntegrable (fun s => q s ^ 2 - 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
     ((hqc.pow 2).sub (continuous_const.mul hqc)).intervalIntegrable _ _
   have i2 : IntervalIntegrable (fun s => q s ^ 2) volume (-(1:ℝ)/2) (1/2) :=
     (hqc.pow 2).intervalIntegrable _ _
   have i3 : IntervalIntegrable (fun s => 2 * aInf * q s) volume (-(1:ℝ)/2) (1/2) :=
     (continuous_const.mul hqc).intervalIntegrable _ _
   rw [e, intervalIntegral.integral_add i1 intervalIntegrable_const,
     intervalIntegral.integral_sub i2 i3,
     intervalIntegral.integral_const_mul, intervalIntegral.integral_const, ← ha, ← hb]
   simp only [smul_eq_mul]
   ring
 linarith
theorem bInf_gt_half : 1 / 2 < bInf := by
 have h1 := aInf_gt_half
 have h2 := aInf_sq_le_bInf
 have hb := sqrt2_half_bounds
 have hs := sin_theta0_ge
 have ha : (734 / 1000 : ℝ) < aInf := by
   rw [aInf_eq]
   unfold MAM
   rw [lt_div_iff₀ (by norm_num)]
   have h2' : 2 * (7071067811865475244/10^19 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
   nlinarith
 nlinarith
theorem eventually_bW_ge_half {P : Params} (hP : P.Valid) :
   ∀ᶠ T in atTop, 1 / 2 ≤ (localFunW P T).b := by
 filter_upwards [(tendsto_bW hP).eventually (lt_mem_nhds bInf_gt_half)] with T h
 exact h.le
theorem JInf_eq_energy : MAM^2 * JInf =
 ∫ s in (-(1:ℝ)/2)..(1/2), V s *
   ∫ t in (-(1:ℝ)/2)..(1/2), |s-t| * V t := by
 rw [← AMW.swap_identity V_continuous abs_V_le]
 unfold JInf vConv
 field_simp [MAM_pos.ne']

theorem H24_eq_cRatio : WindowEnergy.H 24 WindowKernel.d24 =
 2 - (ThmD.cRatio 1 aInf bInf JInf)⁻¹ := by
 have ha : aInf = (∫ t in (-(1:ℝ)/2)..(1/2), V t) / MAM := rfl
 have hb : bInf = (∫ t in (-(1:ℝ)/2)..(1/2), V t^2) / MAM^2 := by
   unfold bInf
   rw [← intervalIntegral.integral_div]
   congr 1
   funext t
   ring
 have hJ := JInf_eq_energy
 have he : ∀ t : ℝ, V t = WindowEnergy.v 24 WindowKernel.d24 t := V_eq
 have hZ : (∫ t in (-(1:ℝ)/2)..(1/2), V t) ≠ 0 := by
   rw [integral_V]
   exact mul_ne_zero (by positivity) AMW.sin_theta0_pos.ne'
 unfold WindowEnergy.H ThmD.cRatio
 simp_rw [← he]
 rw [ha, hb, inv_div]
 have hJ' : JInf =
   (∫ s in (-(1:ℝ)/2)..(1/2), V s *
     ∫ t in (-(1:ℝ)/2)..(1/2), |s-t| * V t) / MAM^2 := by
   rw [← hJ]
   field_simp [MAM_pos.ne']
 rw [hJ']
 field_simp [MAM_pos.ne', hZ]
 <;> ring

theorem actual_localHypsCore {P : Params} (hP : P.Valid) :
 AMW.LocalHypsCoreWEventually P (WindowRealization.W P) (WindowRealization.c P) := by
 apply AMW.localHypsCoreW_eventually hP (WindowRealization.admWindow hP)
 exact eventually_bW_ge_half hP

theorem actual_concreteFacts (Z : ZeroConfig) (H : PaperInputs Z)
 {P : Params} (hP : P.Valid) : Zeta23.ThmD.FactsD (AMW.concreteDataW P (WindowRealization.W P) Z) := by
 apply AMW.concreteFactsW hP H (WindowRealization.admWindow hP)
 exact actual_localHypsCore hP

#print axioms tendsto_cRatio_W
#print axioms H24_eq_cRatio
#print axioms actual_concreteFacts
end StructuralGoal20261016.WindowAsymptotic
end
