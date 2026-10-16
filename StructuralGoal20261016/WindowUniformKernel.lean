/- SPDX-License-Identifier: Apache-2.0
Actual new-window uniform retained Gram-entry limit.
Adapted from Zeta23Ext.Bridge's Limit/Assembly kernel estimates and
Opeth.AMUniformKernel.kernel_limit_uniform in the attributed Core.
Every analytic window input is discharged for the actual new v24 profile;
no local floor or zero-proportion conclusion is supplied as a premise.
-/
import StructuralGoal20261016.WindowSeparated
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowUniformKernel

def Kfun (x : ℝ) : ℝ := WindowKernel.K 24 WindowKernel.d24 x
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0
theorem Kfun_zero_pos : 0 < Kfun 0 := WindowKernel.K_zero_pos 24 WindowKernel.d24
theorem abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 :=
 WindowKernel.abs_K_le 24 WindowKernel.d24 WindowKernel.v24_nonneg x

section Limit
lemma integral_sW_mul_cos {L : ℝ} (hL : 0 < L) (x : ℝ) :
   ∫ u, WindowAsymptotic.sW L u * Real.cos (2 * Real.pi * x / L * u) = L / AMW.MAM * Kfun x := by
 set f : ℝ → ℝ := fun s => WindowProfile.V s / AMW.MAM * Real.cos (2 * Real.pi * x * s) with hf
 have hind : ∀ u, WindowAsymptotic.sW L u * Real.cos (2 * Real.pi * x / L * u)
     = (Set.Icc (-(L / 2)) (L / 2)).indicator (fun u => f (u / L)) u := by
   intro u
   unfold WindowAsymptotic.sW
   by_cases hu : u ∈ Set.Icc (-(L / 2)) (L / 2)
   · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, hf]
     simp only [WindowAsymptotic.hW]
     rw [show 2 * Real.pi * x / L * u = 2 * Real.pi * x * (u / L) by ring]
   · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
 simp_rw [hind]
 rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
   ← intervalIntegral.integral_of_le (by linarith), AMW.integral_scale (v := f) hL]
 have e : (fun s => f s) = fun s => WindowProfile.V s * Real.cos (2 * Real.pi * x * s) / AMW.MAM := by
   funext s; simp only [hf]; ring
 rw [e, intervalIntegral.integral_div]
 unfold Kfun WindowKernel.K
 simp_rw [WindowProfile.V_eq]
 ring
lemma abs_integral_mul_cos_sub_le {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) (r : ℝ) :
   |(∫ u, f u * Real.cos (r * u)) - ∫ u, g u * Real.cos (r * u)| ≤ ∫ u, |f u - g u| := by
 have hcos : Continuous fun u : ℝ => Real.cos (r * u) := by fun_prop
 have hbd : ∀ u : ℝ, ‖Real.cos (r * u)‖ ≤ 1 := fun u => by
   rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _
 have hfi : Integrable fun u => f u * Real.cos (r * u) :=
   hf.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
 have hgi : Integrable fun u => g u * Real.cos (r * u) :=
   hg.mul_bdd (c := 1) hcos.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
 rw [← integral_sub hfi hgi]
 calc |∫ u, (f u * Real.cos (r * u) - g u * Real.cos (r * u))|
     ≤ ∫ u, |f u * Real.cos (r * u) - g u * Real.cos (r * u)| := abs_integral_le_integral_abs
   _ ≤ ∫ u, |f u - g u| := by
       refine integral_mono (hfi.sub hgi).abs (hf.sub hg).abs fun u => ?_
       rw [← sub_mul, abs_mul]
       exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
variable {P : Params} (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
include hP h8
lemma abs_VPhiR_sub_L_mul_Kfun_le (x : ℝ) :
   |AdmWindow.VPhiR (WindowRealization.W P T) (2 * Real.pi * x / P.L T) - P.L T / AMW.MAM * Kfun x| ≤ 2 * P.w := by
 have hW := WindowRealization.admWindow hP T h8
 have hL := hW.L_pos
 have hw : 0 < P.w := hW.w_pos
 set r := 2 * Real.pi * x / P.L T with hr
 have hV : AdmWindow.VPhiR (WindowRealization.W P T) r = ∫ u, WindowRealization.W P T u ^ 2 * Real.cos (r * u) :=
   re_paperFT_ofReal (hW.integrable_pow two_pos) r
 have hS : ∫ u, WindowAsymptotic.sW (P.L T) u * Real.cos (r * u) = P.L T / AMW.MAM * Kfun x :=
   integral_sW_mul_cos hL x
 have hL1 : ∫ u, |WindowRealization.W P T u ^ 2 - WindowAsymptotic.sW (P.L T) u| ≤ 2 * P.w :=
   WindowAsymptotic.integral_abs_phiWsq_sub_sharp hP.taper hw (by linarith)
 rw [hV, ← hS]
 exact (abs_integral_mul_cos_sub_le (hW.integrable_pow two_pos) (WindowAsymptotic.sW_integrable _) r).trans hL1
lemma abs_aL_sub_L_mul_Kfun_zero_le :
   |(WindowRealization.at24 P T).a T * P.L T - P.L T / AMW.MAM * Kfun 0| ≤ 2 * P.w := by
 have hW := WindowRealization.admWindow hP T h8
 have h := abs_VPhiR_sub_L_mul_Kfun_le hP h8 0
 rw [mul_zero, zero_div, hW.VPhiR_zero] at h
 rw [WindowRealization.at_a hP T]
 exact h
lemma abs_VPhiR_div_sub_kfun_le (h32 : 32 * P.w ≤ P.L T) (x : ℝ) :
   |AdmWindow.VPhiR (WindowRealization.W P T) (2 * Real.pi * x / P.L T) / ((WindowRealization.at24 P T).a T * P.L T) - kfun x|
     ≤ 12 * P.w / P.L T := by
 have hW := WindowRealization.admWindow hP T h8
 have hL := hW.L_pos
 have hw : 0 < P.w := hW.w_pos
 have hM := AMW.MAM_pos
 have ha : 1 / 2 ≤ (WindowRealization.at24 P T).a T := (WindowRealization.a_range_of hP h32).1
 have h1 := abs_VPhiR_sub_L_mul_Kfun_le hP h8 x
 have h2 := abs_aL_sub_L_mul_Kfun_zero_le hP h8
 have hK0 : 0 < Kfun 0 := Kfun_zero_pos
 have hK : |Kfun x| ≤ Kfun 0 := abs_Kfun_le x
 set V := AdmWindow.VPhiR (WindowRealization.W P T) (2 * Real.pi * x / P.L T) with hV
 set A := (WindowRealization.at24 P T).a T * P.L T with hA
 set K := Kfun x with hK'
 set K0 := Kfun 0 with hK0'
 set c := P.L T / AMW.MAM with hc
 have hA2 : P.L T / 2 ≤ A := by rw [hA]; nlinarith
 have hApos : 0 < A := by linarith
 have e : V / A - K / K0 = (V - c * K) / A + K * (c * K0 - A) / (A * K0) := by
   field_simp
   ring
 unfold kfun
 rw [e]
 have h2' : |c * K0 - A| ≤ 2 * P.w := by rw [abs_sub_comm]; exact h2
 calc |(V - c * K) / A + K * (c * K0 - A) / (A * K0)|
     ≤ |(V - c * K) / A| + |K * (c * K0 - A) / (A * K0)| := abs_add_le _ _
   _ = |V - c * K| / A + |K| * |c * K0 - A| / (A * K0) := by
       rw [abs_div, abs_of_pos hApos, abs_div, abs_mul, abs_of_pos (mul_pos hApos hK0)]
   _ ≤ 2 * P.w / A + K0 * (2 * P.w) / (A * K0) := by gcongr
   _ = 4 * P.w / A := by field_simp; ring
   _ ≤ 12 * P.w / P.L T := by
       rw [div_le_div_iff₀ hApos hL]
       nlinarith
end Limit
section Assembly
lemma Kfun_eq_sum {P : Params} (hP : P.Valid) (T γ γ' : ℝ) :
   PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T) γ γ'
     = ∑ k : Fin ((WindowRealization.at24 P T).d T), (WindowRealization.at24 P T).phiHatR T (γ - (WindowRealization.at24 P T).tau T k)
         * (WindowRealization.at24 P T).phiHatR T (γ' - (WindowRealization.at24 P T).tau T k) := by
 rw [WindowSeparated.at24_phiHatR_eq hP T]; rfl
lemma Kinf_eq {P : Params} (T γ γ' : ℝ) :
   PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T) γ γ'
     = P.L T * AdmWindow.VPhiR (WindowRealization.W P T) (γ - γ') := rfl
theorem gram_close_of {P : Params} (hP : P.Valid) {T : ℝ} (hT : 0 < T)
   (h8 : 8 * P.w ≤ P.L T) (h32 : 32 * P.w ≤ P.L T)
   (hF : PrimeSide.LocalHypsCoreW (WindowRealization.c P) (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T))
   (Z : ZeroConfig) (z z' : retained Z (WindowRealization.at24 P T) T) :
   ‖gram Z (WindowRealization.at24 P T) T z z'
       - (kfun (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z') : ℂ)‖
     ≤ 10 * (WindowRealization.c P / P.w) ^ 2 / P.L T ^ 4 + 12 * P.w / P.L T := by
 have hW := WindowRealization.admWindow hP T h8
 have hL := hW.L_pos
 have ha : 1 / 2 ≤ (WindowRealization.at24 P T).a T := (WindowRealization.a_range_of hP h32).1
 have hc : 0 < aL2 (WindowRealization.at24 P T) T := by
   unfold aL2; rw [WindowSeparated.at24_L]; exact mul_pos (by linarith) (pow_pos hL 2)
 set K : ℝ := (WindowRealization.c P / P.w) ^ 2 with hK
 have hK0 : 0 ≤ K := sq_nonneg _
 rw [gram_apply Z (WindowRealization.at24 P T) T (WindowSeparated.phiHatReal_at24 hP T) hc.le z z', ← Complex.ofReal_sub,
   Complex.norm_real, Real.norm_eq_abs, ← Kfun_eq_sum hP T (z.1 : ℂ).im (z'.1 : ℂ).im]
 set γ : ℝ := (z.1 : ℂ).im with hγ
 set γ' : ℝ := (z'.1 : ℂ).im with hγ'
 obtain ⟨g1, g2, g3⟩ := retained_far (Z := Z) (P := WindowRealization.at24 P T) hL hT.le z.2
 obtain ⟨g1', g2', g3'⟩ := retained_far (Z := Z) (P := WindowRealization.at24 P T) hL hT.le z'.2
 have htail : |PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T) γ γ'
     - PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T) γ γ'| ≤ 5 * K / P.L T ^ 2 :=
   abs_Kinf_sub_Kfun_le_of_far hF hT g1 g2 g3 g1' g2' g3'
 have hx : 2 * Real.pi * (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z') / P.L T
     = γ - γ' := by
   unfold xret xnorm
   rw [WindowSeparated.at24_L]
   field_simp
   ring
 have hlim := abs_VPhiR_div_sub_kfun_le hP h8 h32
   (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z')
 rw [hx] at hlim
 set A : ℝ := (WindowRealization.at24 P T).a T with hA
 set V : ℝ := AdmWindow.VPhiR (WindowRealization.W P T) (γ - γ') with hV
 set Kf : ℝ := PrimeSide.Kfun (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T) γ γ' with hKf
 have hKinf : PrimeSide.Kinf (P.toSetting T) (AMW.lfW P (WindowRealization.W P) T) γ γ' = P.L T * V :=
   Kinf_eq T γ γ'
 rw [hKinf] at htail
 have haL2 : aL2 (WindowRealization.at24 P T) T = A * P.L T ^ 2 := by unfold aL2; rw [WindowSeparated.at24_L]
 rw [haL2]
 have hApos : 0 < A := by linarith
 have hsplit : (A * P.L T ^ 2)⁻¹ * Kf - kfun (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z')
     = (A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
       + (V / (A * P.L T) - kfun (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z')) := by
   field_simp
   ring
 rw [hsplit]
 have hinv : (A * P.L T ^ 2)⁻¹ ≤ 2 / P.L T ^ 2 := by
   rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
   nlinarith [pow_pos hL 2]
 calc |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)
       + (V / (A * P.L T) - kfun (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z'))|
     ≤ |(A * P.L T ^ 2)⁻¹ * (Kf - P.L T * V)|
       + |V / (A * P.L T) - kfun (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z')| :=
         abs_add_le _ _
   _ = (A * P.L T ^ 2)⁻¹ * |P.L T * V - Kf|
       + |V / (A * P.L T) - kfun (xret Z (WindowRealization.at24 P T) T z - xret Z (WindowRealization.at24 P T) T z')| := by
       rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (A * P.L T ^ 2)⁻¹), abs_sub_comm]
   _ ≤ 2 / P.L T ^ 2 * (5 * K / P.L T ^ 2) + 12 * P.w / P.L T := by
       gcongr
   _ = 10 * K / P.L T ^ 4 + 12 * P.w / P.L T := by
       field_simp
       ring
end Assembly

theorem kernel_limit_uniform (Z : ZeroConfig) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (WindowCountingBase.mtParams T) T,
      ‖gram Z (WindowCountingBase.mtParams T) T z z' -
        (kfun
          (xret Z (WindowCountingBase.mtParams T) T z - xret Z (WindowCountingBase.mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨T₀, hT₀⟩ := WindowAsymptotic.actual_localHypsCore hP
  set K : ℝ :=
    (WindowRealization.c (paramsOf stdProfile 1) / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP, AMW.eventually_w32 hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop
      ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 h32 hTT₀ hL1 hLδ
  intro z z'
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hT h8 h32 hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T with hLdef
  have hL : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hL 2, pow_pos hL 3]
  have h1 : 10 * K / L ^ 4 ≤ 10 * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc
    10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
        ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
    _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
    _ ≤ δ := h2
#print axioms gram_close_of
#print axioms kernel_limit_uniform
end StructuralGoal20261016.WindowUniformKernel
end
