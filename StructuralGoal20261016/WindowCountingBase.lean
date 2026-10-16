/- SPDX-License-Identifier: Apache-2.0
Actual new-window stable-rank trace-to-zero counting base.
Adapted from Zeta23Ext.Bridge.endgame_defect and eventually_h7 in the
attributed Core. The analytic inputs are discharged for the new v24 window.
The local separated/matching defect bound is deliberately not asserted here.
-/
import StructuralGoal20261016.WindowAsymptotic
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix RHLinalg Filter Asymptotics Topology Real
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23.Assembly
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowCountingBase

def P₀ : Params := paramsOf stdProfile 1
theorem P₀_valid : P₀.Valid := paramsOf_valid taperProfile_stdProfile one_pos le_rfl
def mtParams (T : ℝ) : Params := WindowRealization.at24 P₀ T

theorem endgame_defect (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
   (aT bT JT trG trG2 : ℝ → ℝ)
   (hTr : TracesBoundsD P aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
   {c : ℝ} (hc0 : 0 < c)
   (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
   (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
   (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (WindowRealization.at24 P T) T (θ₀ T))
   (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
   (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
   (hGzGp : ∀ᶠ T in atTop, Z.Gz (WindowRealization.at24 P T) T = (WindowRealization.at24 P T).Gp T)
   (hId : ∀ᶠ T in atTop, (WindowRealization.at24 P T).trGtilde T = trG T ∧ (WindowRealization.at24 P T).trGtildeSq T = trG2 T ∧
     (WindowRealization.at24 P T).a T = aT T)
   (hcalE : Tendsto P.calE atTop (𝓝 0))
   (D : ℝ → ℝ)
   (hcore : ∀ᶠ T in atTop,
     4 * rtrace ((WindowRealization.at24 P T).hat T (Z.Az (WindowRealization.at24 P T) T))
       - frobSq ((WindowRealization.at24 P T).hat T (Z.Az (WindowRealization.at24 P T) T))
       - 2 * (Z.NIprime T : ℝ) + D T ≤ (Z.s1 T : ℝ)) :
   ∀ ε > 0, ∀ᶠ T in atTop,
     (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) + D T ≤ (Z.N0s T (2 * T) : ℝ) := by
 have hlam0 := hP.lam_pos
 have hlam1 : P.lam ≤ 1 := hP.lam_le_one
 obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
 obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
 obtain ⟨Cθ, hθ⟩ := hθ₀
 obtain ⟨CII, hII⟩ := hNII
 set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
 set cinv : ℝ → ℝ := fun T => (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
 set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
 set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
 set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
 set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
     + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
 have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
 have hmain : ∀ᶠ T in atTop,
     (2 - c⁻¹) * N T - err T ≤ (Z.N0s T (2 * T) : ℝ) - D T := by
   filter_upwards [hcore, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
     eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
     eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
     with T hcoreT hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
   obtain ⟨hidtr, hidfr, hida⟩ := hid
   have hapos' : 0 < aT T := by linarith [ha2.1]
   have haposD : 0 < (WindowRealization.at24 P T).a T := by rw [hida]; exact hapos'
   have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
   have hA := seamA_mult2_defect hT0 hTl haposD hLpos hcoreT
   have hrt : rtrace ((WindowRealization.at24 P T).hat T (Z.Gz (WindowRealization.at24 P T) T)) = (aT T * P.L T)⁻¹ * trG T := by
     rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]; rfl
   have hfr : frobSq ((WindowRealization.at24 P T).hat T (Z.Gz (WindowRealization.at24 P T) T))
       = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
     rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]; rfl
   have haL : (WindowRealization.at24 P T).a T * (WindowRealization.at24 P T).L T = aT T * P.L T := by rw [hida]; rfl
   rw [hrt, hfr, haL] at hA
   have hA' : 4 * ((aT T * P.L T)⁻¹ * trG T) - ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
       - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
       - θ₀ T / (aT T * P.L T)
           * (4 + 2 * Real.sqrt (((aT T * P.L T)⁻¹) ^ 2 * trG2 T) + θ₀ T / (aT T * P.L T))
       ≤ (Z.N0s T (2 * T) : ℝ) - D T := by linarith [hA]
   have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
     trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
   have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
     have h := hfr2 T hT₂
     simp only at h
     have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
       rw [← mul_assoc] at h
       exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
     have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
       rw [inv_pow, div_eq_inv_mul]
     rw [e]; simp only [hR₂]; linarith
   have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
   have h := N0star_lower_c hB₀ hA' htr hfrb
   have hN0 : 0 ≤ N T := Nat.cast_nonneg _
   have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
     have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
     linarith [h1]
   simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
   linarith
 have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
 have o1 : R₁ =o[atTop] N := by
   have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
     refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
     filter_upwards [ha] with T ha2
     rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
     rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
   have := isLittleO_of_bdd_mul hbd
     (isLittleO_N_of_isLittleO_Tl Z H.RvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
   exact this.congr_left fun T => by simp only [hR₁]; ring
 have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
   have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
   filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
     hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
   exact ⟨h1, h2⟩
 have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
   refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
   filter_upwards [hcinv_bd] with T h
   rw [abs_of_nonneg h.1]; exact h.2
 have o2 : R₂ =o[atTop] N := by
   have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
     simpa using hcalE.const_mul C₂
   have i1 : (fun T => cinv T * N T) =O[atTop] N := by
     have := hcinvO.mul (isBigO_refl N atTop)
     simpa using this
   have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
   refine (this.congr_left fun T => ?_).congr_right fun T => by simp
   simp only [hR₂]
 have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
   have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
     refine IsBigO.of_bound CII ?_
     filter_upwards [hII, eventually_l_pos] with T h hl
     rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
       abs_of_nonneg (by positivity)]
     simpa [mul_assoc] using h
   exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
 have o4 : Tendsto B atTop (𝓝 0) := by
   have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
     simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
   refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
   · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
     have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
     exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
   · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
       with T hTl ha2 hl hθT hT0
     have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
     have hapos' : 0 < aT T := by linarith [ha2.1]
     have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
     simp only [hBdef]
     rw [div_le_iff₀ (mul_pos hapos' hLpos)]
     calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
       _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
       _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
       _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
         have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
             = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
         rw [this]; gcongr; exact ha2.1
 have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
   (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
 have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
   refine isLittleO_of_tendsto_zero_mul ?_
   have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
     simpa using hcinv_to.sub_const c⁻¹
   simpa using this.abs
 have herr_o : err =o[atTop] N := o5.add o6
 have hfin := eps_form_of_isLittleO (lower := fun T => (Z.N0s T (2 * T) : ℝ) - D T) hmain
   (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
 intro ε hε
 obtain ⟨T₀, hT₀⟩ := hfin ε hε
 filter_upwards [eventually_ge_atTop T₀] with T hT
 have := hT₀ T hT
 simp only [hNdef] at this
 linarith
theorem eventually_h7 (Z : ZeroConfig) :
   ∀ᶠ T in atTop,
     4 * rtrace ((mtParams T).hat T (Z.Az (mtParams T) T))
       - frobSq ((mtParams T).hat T (Z.Az (mtParams T) T))
       - 2 * (Z.NIprime T : ℝ) + Dcirc Z (mtParams T) T ≤ (Z.s1 T : ℝ) := by
 filter_upwards [eventually_w8 P₀_valid, AMW.eventually_w32 P₀_valid] with T h8 h32
 set P := mtParams T with hP
 have hconj : PhiHatConj T P := phiHatConj
 have hL : 0 < P.L T := by
   change 0 < P₀.L T; linarith [P₀_valid.one_le_w]
 have ha : 1 / 2 ≤ P.a T := (WindowRealization.a_range_of P₀_valid h32).1
 have hc : 0 < aL2 P T := mul_pos (by linarith) (pow_pos hL 2)
 have hPois : PoissonSq T P := AMW.poissonSqW P₀_valid (WindowRealization.W_even P₀) (WindowRealization.admWindow P₀_valid) h8
 have h7 := count_defect (bdata Z P T) (mkPairReps Z T _ (evalVec_reflect hconj)) hc
   (sum_normSq_v_le Z T P hconj phiHatReal hPois)
 have hD : Dcirc Z P T ≤ defect (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) :=
   pinching_submatrix (gramS₁_isHermitian (bdata Z P T) (aL2 P T)) (toS₁ Z P T)
     (toS₁_injective Z P T)
 have hA : P.hat T (Z.Az P T) = (bdata Z P T).blockP (aL2 P T) + (bdata Z P T).blockQ (aL2 P T) :=
   hat_Az_eq_hatP_add_hatQ Z T P hconj
 have hN : (Z.NIprime T : ℝ) = ((bdata Z P T).Ncount : ℝ) := by
   rw [NIprime_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
 have hs : (Z.s1 T : ℝ) = ((bdata Z P T).s₁ : ℝ) := by
   rw [s1_eq_mk Z T _ (evalVec_reflect hconj)]; rfl
 rw [hA, hN, hs]
 linarith [h7, hD]
theorem actual_tail_passage (Z : ZeroConfig) (H : PaperInputs Z) :
 ∀ ε > 0, ∀ᶠ T in atTop,
   (WindowEnergy.H 24 WindowKernel.d24 - ε) * (Z.N T (2*T) : ℝ) +
     Dcirc Z (mtParams T) T ≤ (Z.N0s T (2*T) : ℝ) := by
 let P : Params := P₀
 have hP : P.Valid := P₀_valid
 have hFacts := WindowAsymptotic.actual_concreteFacts Z H hP
 have hTr := tracesBoundsD_of_factsD _ hFacts
 have hc : Tendsto
   (fun T => cRatio (P.lam1 T)
     ((AMW.concreteDataW P (WindowRealization.W P) Z).aT T)
     ((AMW.concreteDataW P (WindowRealization.W P) Z).bT T)
     ((AMW.concreteDataW P (WindowRealization.W P) Z).JT T))
   atTop (𝓝 (cRatio P.lam WindowAsymptotic.aInf WindowAsymptotic.bInf WindowAsymptotic.JInf)) :=
   WindowAsymptotic.tendsto_cRatio_W hP
 have hc0 := WindowAsymptotic.cRatio_W_pos hP.lam_pos
 have ha : ∀ᶠ T in atTop,
   1/2 ≤ (AMW.concreteDataW P (WindowRealization.W P) Z).aT T ∧
   (AMW.concreteDataW P (WindowRealization.W P) Z).aT T ≤ 1 :=
   hFacts.ab_range.mono fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
 obtain ⟨θ₀, hTail, hθ₀⟩ := WindowRealization.eventually_tailPackage Z H hP
 obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
 have hNII := Tail.eventually_NII_le Z hA₀ hloc
 have hGzGp := WindowRealization.eventually_GzGp Z H hP
 have hId : ∀ᶠ T in atTop,
   (WindowRealization.at24 P T).trGtilde T =
     (AMW.concreteDataW P (WindowRealization.W P) Z).trG T ∧
   (WindowRealization.at24 P T).trGtildeSq T =
     (AMW.concreteDataW P (WindowRealization.W P) Z).trG2 T ∧
   (WindowRealization.at24 P T).a T =
     (AMW.concreteDataW P (WindowRealization.W P) Z).aT T :=
   Eventually.of_forall fun T => AMW.atW_ident Z hP (WindowRealization.W_even P) T
 have hcalE := Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
   (zero_le_one.trans hP.one_le_w)
 have h := endgame_defect Z H P hP _ _ _ _ _ hTr hc0 hc ha θ₀
   hTail hθ₀ hNII hGzGp hId hcalE (fun T => Dcirc Z (mtParams T) T) (eventually_h7 Z)
 intro ε hε
 rw [WindowAsymptotic.H24_eq_cRatio]
 exact h ε hε

#print axioms endgame_defect
#print axioms eventually_h7
#print axioms actual_tail_passage
end StructuralGoal20261016.WindowCountingBase
end
