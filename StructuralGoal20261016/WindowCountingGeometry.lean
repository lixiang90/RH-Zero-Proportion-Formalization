/- SPDX-License-Identifier: Apache-2.0
Actual new-window retained-zero strip and span estimates. These arguments
adapt the generic RvM proofs in the attributed Core; they assume no gap floor.
-/
import StructuralGoal20261016.WindowCountingBase
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix RHLinalg Filter Finset
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowCountingGeometry
open Classical
theorem deleted_strips (Z : ZeroConfig) (H : PaperInputs Z) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     (Z.N0s T (2 * T) : ℝ) - ε * (Z.N T (2 * T) : ℝ)
       ≤ ((retained Z (WindowCountingBase.mtParams T) T).card : ℝ) := by
 intro ε hε
 have hP : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
 obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
 obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
 have hA0 : 0 < A₀ := by linarith
 have hπ := Real.pi_pos
 set c : ℝ := ε / (4 * Real.pi * (1600 * A₀)) with hc
 have hcpos : 0 < c := by positivity
 have hlittle : ∀ᶠ x in atTop, ‖Real.log x‖ ≤ c * ‖id x‖ :=
   Real.isLittleO_log_id_atTop.def hcpos
 filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop T₀,
   (tendsto_L hP).eventually_ge_atTop 1, hlittle,
   eventually_ge_atTop (4 * Real.pi * |C| * (1 + 2 * Real.pi))] with T hT1 hTT₀ hL1 hlog hTC
 have hT0 : 0 < T := by linarith
 set L : ℝ := (paramsOf stdProfile 1).L T with hLdef
 have hLeq : L = Real.log T - Real.log (2 * Real.pi) := by
   rw [hLdef]
   show 1 * Real.log (T / (2 * Real.pi)) = _
   rw [one_mul, Real.log_div hT0.ne' (by positivity)]
 have hlog2π0 : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
 have hlog2π : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
 have hlogT : Real.log T ≤ L + 2 * Real.pi := by linarith
 have hLlogT : L ≤ Real.log T := by linarith
 have hlogT_le : Real.log T ≤ T - 1 := Real.log_le_sub_one_of_pos hT0
 have hLT : L ≤ T := by linarith
 have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
 have hlogc : Real.log T ≤ c * T := by
   have h := hlog
   simp only [id, Real.norm_eq_abs, abs_of_pos hT0, abs_of_nonneg hlogT0] at h
   exact h
 have hLpos : 0 < (WindowCountingBase.mtParams T).L T := by show 0 < L; linarith
 have hincl := N0s_le_card_retained_add Z (WindowCountingBase.mtParams T) T hLpos
 have hstrips := strips_le Z hA₀ hloc hT1 hL1 hLT hlogT
 have hincl' : (Z.N0s T (2 * T) : ℝ) ≤ (retained Z (WindowCountingBase.mtParams T) T).card + 1600 * A₀ * L ^ 2 := by
   have e1 : (WindowCountingBase.mtParams T).L T = L := rfl
   rw [e1] at hincl
   linarith
 have hN : T * L / (2 * Real.pi) - |C| * Real.log T ≤ (Z.N T (2 * T) : ℝ) := by
   have h := hRvM T hTT₀
   have hℓ₁ : L ≤ ell1 T := by
     show 1 * l T ≤ l T + 2 * Real.log 2 - 1
     have := Real.log_two_gt_d9
     linarith
   have h1 := (abs_le.mp h).1
   have h2 : C * Real.log T ≤ |C| * Real.log T :=
     mul_le_mul_of_nonneg_right (le_abs_self C) hlogT0
   have h3 : T * L / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T := by
     rw [mul_div_right_comm]
     exact mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
   linarith
 have hkey : 1600 * A₀ * L ^ 2 + ε * |C| * Real.log T ≤ ε * (T * L / (2 * Real.pi)) := by
   have hA : 1600 * A₀ * L ^ 2 ≤ ε * T * L / (4 * Real.pi) := by
     have h1 : 1600 * A₀ * L ^ 2 ≤ 1600 * A₀ * L * (c * T) := by
       have : L * L ≤ L * (c * T) := by
         have : L ≤ c * T := hLlogT.trans hlogc
         exact mul_le_mul_of_nonneg_left this (by linarith)
       nlinarith
     have h2 : 1600 * A₀ * L * (c * T) = ε * T * L / (4 * Real.pi) := by
       rw [hc]; field_simp
     linarith
   have hB : ε * |C| * Real.log T ≤ ε * T * L / (4 * Real.pi) := by
     have h1 : |C| * Real.log T ≤ |C| * ((1 + 2 * Real.pi) * L) := by
       apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
       nlinarith
     have h2 : |C| * (1 + 2 * Real.pi) * (4 * Real.pi) ≤ T := by linarith
     have h3 : |C| * ((1 + 2 * Real.pi) * L) ≤ T * L / (4 * Real.pi) := by
       rw [le_div_iff₀ (by positivity)]
       have hL0 : 0 ≤ L := by linarith
       nlinarith
     calc ε * |C| * Real.log T = ε * (|C| * Real.log T) := by ring
       _ ≤ ε * (|C| * ((1 + 2 * Real.pi) * L)) := mul_le_mul_of_nonneg_left h1 hε.le
       _ ≤ ε * (T * L / (4 * Real.pi)) := mul_le_mul_of_nonneg_left h3 hε.le
       _ = ε * T * L / (4 * Real.pi) := by ring
   have : ε * T * L / (4 * Real.pi) + ε * T * L / (4 * Real.pi) = ε * (T * L / (2 * Real.pi)) := by
     field_simp
     ring
   linarith
 have hεN : 1600 * A₀ * L ^ 2 ≤ ε * (Z.N T (2 * T) : ℝ) := by
   have := mul_le_mul_of_nonneg_left hN hε.le
   nlinarith [hkey]
 linarith

theorem span_retained_le (Z : ZeroConfig) (H : PaperInputs Z) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     spanOf (xret Z (WindowCountingBase.mtParams T) T) univ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by
 intro ε hε
 obtain ⟨C, T₀, hRvM⟩ := H.RvM.main
 have hV : (paramsOf stdProfile 1).Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
 have hLpos : ∀ᶠ T in atTop, 0 < (WindowCountingBase.mtParams T).L T := (tendsto_L hV).eventually_gt_atTop 0
 set K : ℝ := max ((1 + ε) * C / ε) 0 with hK
 have hK0 : 0 ≤ K := le_max_right _ _
 have hc : (0 : ℝ) < 1 / (2 * Real.pi * (K + 1)) := by positivity
 have hlogT : ∀ᶠ T in atTop, ‖Real.log T‖ ≤ (1 / (2 * Real.pi * (K + 1))) * ‖id T‖ :=
   Real.isLittleO_log_id_atTop.def hc
 have hell : ∀ᶠ T in atTop, 1 ≤ ell1 T := by
   have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
     Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
   have h' : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi)) + (2 * Real.log 2 - 1))
       atTop atTop := h.atTop_add tendsto_const_nhds
   exact (h'.eventually_ge_atTop 1).mono fun T hT => by unfold ell1 l; linarith
 filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 * Real.pi), hLpos, hlogT, hell]
   with T hT₀ h2π hL hlog hel
 have hpi : 0 < 2 * Real.pi := by positivity
 have hT0 : 0 < T := lt_of_lt_of_le hpi h2π
 have hT1 : 1 ≤ T := by linarith [Real.pi_gt_three]
 have hLg0 : 0 ≤ Real.log T := Real.log_nonneg hT1
 have hl0 : 0 ≤ l T := Real.log_nonneg (by rw [le_div_iff₀ hpi]; linarith)
 have hN := abs_le.mp (hRvM T hT₀)
 have hLle : (WindowCountingBase.mtParams T).L T ≤ l T := by
   show (paramsOf stdProfile 1).lam * l T ≤ l T
   exact mul_le_of_le_one_left hl0 hV.lam_le_one
 have hl_ell : l T ≤ ell1 T := by
   unfold ell1; linarith [Real.log_two_gt_d9]
 have hd : ((WindowCountingBase.mtParams T).d T : ℝ) ≤ T / (2 * Real.pi) * ell1 T := by
   have h0 : 0 ≤ (WindowCountingBase.mtParams T).L T * T / (2 * Real.pi) := by positivity
   calc ((WindowCountingBase.mtParams T).d T : ℝ) ≤ (WindowCountingBase.mtParams T).L T * T / (2 * Real.pi) := Nat.floor_le h0
     _ = T / (2 * Real.pi) * (WindowCountingBase.mtParams T).L T := by ring
     _ ≤ T / (2 * Real.pi) * ell1 T := by gcongr; exact hLle.trans hl_ell
 have hKA : K * Real.log T ≤ T / (2 * Real.pi) * ell1 T := by
   simp only [Real.norm_eq_abs, id, abs_of_nonneg hLg0, abs_of_pos hT0] at hlog
   have h1 : K * Real.log T ≤ K * (1 / (2 * Real.pi * (K + 1)) * T) :=
     mul_le_mul_of_nonneg_left hlog hK0
   have h2 : K * (1 / (2 * Real.pi * (K + 1)) * T) ≤ T / (2 * Real.pi) := by
     rw [show K * (1 / (2 * Real.pi * (K + 1)) * T) = T / (2 * Real.pi) * (K / (K + 1)) by
       field_simp]
     have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
     exact mul_le_of_le_one_right (by positivity) this
   have h3 : T / (2 * Real.pi) ≤ T / (2 * Real.pi) * ell1 T :=
     le_mul_of_one_le_right (by positivity) hel
   linarith
 have h1 : (1 + ε) * C / ε * Real.log T ≤ T / (2 * Real.pi) * ell1 T :=
   (mul_le_mul_of_nonneg_right (le_max_left _ _) hLg0).trans hKA
 have h2 : (1 + ε) * C * Real.log T ≤ ε * (T / (2 * Real.pi) * ell1 T) := by
   have e : (1 + ε) * C * Real.log T = ε * ((1 + ε) * C / ε * Real.log T) := by
     field_simp
   rw [e]
   exact mul_le_mul_of_nonneg_left h1 hε.le
 calc spanOf (xret Z (WindowCountingBase.mtParams T) T) univ ≤ ((WindowCountingBase.mtParams T).d T : ℝ) := spanOf_xret_le_d Z _ T
   _ ≤ (1 + ε) * (Z.N T (2 * T) : ℝ) := by nlinarith [hN.1, hN.2, hd, h2]

set_option pp.fullNames true
#print axioms deleted_strips
#print axioms span_retained_le
end StructuralGoal20261016.WindowCountingGeometry
end
