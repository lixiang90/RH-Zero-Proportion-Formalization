/- SPDX-License-Identifier: Apache-2.0
The new cosine profile defines an actual admissible finite-height window.
Its exact-formula and tail packages use the existing generic W theorems,
with no added window admissibility or positive-variation assumption.
No new asymptotic energy limit or local floor is asserted in this module.
-/
import StructuralGoal20261016.WindowProfile
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped BigOperators Topology
open Zeta23
namespace StructuralGoal20261016.WindowRealization
open WindowProfile

def W (P : Params) (T : ℝ) : ℝ → ℝ := phi P.ϱ (P.L T) P.w
def at24 (P : Params) (T : ℝ) : Params := AMW.atW P (W P) T
def c (P : Params) : ℝ := AMW.cMod P.ϱ 4 (128+2*4^2)

theorem W_even (P : Params) (T u : ℝ) : W P T (-u) = W P T u := by
 simp only [W, phi, AMW.phiM, AMW.fP, neg_div, V_even, Taper.phi_even]

theorem admWindow {P : Params} (hP : P.Valid) (T : ℝ) (h8 : 8*P.w ≤ P.L T) :
 AdmWindow (W P T) (P.L T) P.w (c P) :=
 actual_admWindow hP.taper hP.one_le_w h8

theorem at_a {P : Params} (hP : P.Valid) (T : ℝ) :
 (at24 P T).a T = AdmWindow.av (W P T) (P.L T) :=
 AMW.atW_a T hP (W_even P T)

theorem W_sq_ge {P : Params} (hP : P.Valid) {T : ℝ}
 (h8 : 8*P.w ≤ P.L T) (u : ℝ) :
 (67/125 : ℝ) * Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤ W P T u ^ 2 := by
 have hw0 : 0 < P.w := by linarith [hP.one_le_w]
 have hL : 0 < P.L T := by linarith [hP.one_le_w]
 rcases le_or_gt (P.L T/2) |u| with hu | hu
 · simp only [W, phi, AMW.phiM]
   rw [Taper.phi_eq_zero hP.taper hw0 hu]
   simp
 · have hc := V_ge_core (AMW.abs_div_le_half hL hu.le)
   have hv : 0 ≤ V (u / P.L T) / AMW.MAM := by
     exact div_nonneg (by linarith) AMW.MAM_pos.le
   have hsq : W P T u ^ 2 = (V (u / P.L T)/AMW.MAM) *
       Taper.phi P.ϱ (P.L T) P.w u ^ 2 := by
     unfold W phi AMW.phiM AMW.fP
     rw [mul_pow, Real.sq_sqrt hv]
   rw [hsq]
   apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
   rw [le_div_iff₀ AMW.MAM_pos]
   norm_num [AMW.MAM] at *
   linarith

theorem a_range_of {P : Params} (hP : P.Valid) {T : ℝ}
 (h32 : 32*P.w ≤ P.L T) : 1/2 ≤ (at24 P T).a T ∧ (at24 P T).a T ≤ 1 := by
 have h8 : 8*P.w ≤ P.L T := by linarith [hP.one_le_w]
 have hW := admWindow hP T h8
 rw [at_a hP]
 refine ⟨?_, hW.av_le_one⟩
 have hw0 : 0 < P.w := by linarith [hP.one_le_w]
 have h2 : 2*P.w ≤ P.L T := by linarith
 have hL : 0 < P.L T := by linarith [hP.one_le_w]
 have hb : 1 - 2*P.w/P.L T ≤ Taper.aConst P.ϱ (P.L T) P.w :=
   (Taper.one_sub_le_bConst hP.taper hw0 h2).trans (Taper.bConst_le_aConst hP.taper hw0 h2)
 have hwL : 2*P.w/P.L T ≤ 1/16 := by rw [div_le_iff₀ hL]; linarith
 have hint : Integrable (fun u => W P T u ^ 2) := hW.integrable_pow two_pos
 have hint' : Integrable (fun u => (67/125 : ℝ) * Taper.phi P.ϱ (P.L T) P.w u ^ 2) :=
   (((Taper.phi_continuous hP.taper hw0 h2).fun_pow 2).integrable_of_hasCompactSupport
     ((Taper.phi_hasCompactSupport hP.taper hw0).comp_left (g := fun t => t^2)
       (by norm_num))).const_mul _
 have hcmp : (67/125 : ℝ) * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2 ≤
     ∫ u, W P T u ^ 2 := by
   rw [← integral_const_mul]
   exact integral_mono hint' hint (W_sq_ge hP h8)
 unfold AdmWindow.av
 unfold Taper.aConst at hb
 have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
 calc
   (1:ℝ)/2 ≤ (67/125)*(1-2*P.w/P.L T) := by nlinarith
   _ ≤ (67/125)*((P.L T)⁻¹ * ∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by gcongr
   _ = (P.L T)⁻¹*((67/125)*∫ u, Taper.phi P.ϱ (P.L T) P.w u ^ 2) := by ring
   _ ≤ (P.L T)⁻¹*∫ u, W P T u ^ 2 := mul_le_mul_of_nonneg_left hcmp hLi.le

theorem eventually_a_range {P : Params} (hP : P.Valid) :
 ∀ᶠ T in atTop, 1/2 ≤ (at24 P T).a T ∧ (at24 P T).a T ≤ 1 := by
 filter_upwards [AMW.eventually_w32 hP] with T h32
 exact a_range_of hP h32

theorem eventually_GzGp (Z : ZeroConfig) (H : PaperInputs Z) {P : Params} (hP : P.Valid) :
 ∀ᶠ T in atTop, Z.Gz (at24 P T) T = (at24 P T).Gp T :=
 AMW.eventually_GzGpW hP (W_even P) (admWindow hP) Z H

theorem eventually_tailPackage (Z : ZeroConfig) (H : PaperInputs Z)
 {P : Params} (hP : P.Valid) :
 ∃ θ₀ : ℝ → ℝ,
   (∀ᶠ T in atTop, Assembly.TailInputs Z (at24 P T) T (θ₀ T)) ∧
   ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * Zeta23.l T * T^(P.lam/2-1) :=
 AMW.eventually_tailPackageW hP (W_even P) (admWindow hP)
   ((eventually_a_range hP).mono fun _ h => h.1) Z H

#print axioms admWindow
#print axioms a_range_of
#print axioms eventually_GzGp
#print axioms eventually_tailPackage
end StructuralGoal20261016.WindowRealization
end
