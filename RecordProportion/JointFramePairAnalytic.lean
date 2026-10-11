/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Additive analytic transport for the joint frame-pair certificate.
The old c260 constants and corollaries remain unchanged.
-/
import RecordProportion.AnalyticBridge
import RecordProportion.NinthSpanAnalytic

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix Finset RHLinalg Filter Zeta23 Zeta23Ext.Bridge Zeta23Ext.StableRankTrace

namespace RHWeilRecord.JointFramePair

/-- Uniform reward proved by the new joint strengthened frame-pair assembly. -/
def localReward : ℝ := 805448 / 100000000

/-- Strengthened simple-zero proportion, equal to 66812491 / 99194552. -/
def recordRatio : ℝ := 66812491 / 99194552

theorem localReward_pos : 0 < localReward := by norm_num [localReward]
theorem localReward_lt_one : localReward < 1 := by norm_num [localReward]
theorem recordRatio_identity :
    recordRatio = (2 - energyUpper - gapPressure) / (1 - localReward) := by
  norm_num [recordRatio, energyUpper, gapPressure, localReward]
theorem recordRatio_original_fraction : recordRatio = 66812491 / 99194552 := by
  norm_num [recordRatio]
theorem previous_recordRatio_lt : RHWeilRecord.recordRatio < recordRatio := by
  norm_num [RHWeilRecord.recordRatio, recordRatio]

theorem ninth_span_recordRatio_lt : RHWeilRecord.NinthSpan.recordRatio < recordRatio := by
  norm_num [RHWeilRecord.NinthSpan.recordRatio, recordRatio]

theorem recordRatio_gt_67355 : (67355 : ℝ) / 100000 < recordRatio := by
  norm_num [recordRatio]

/-- The existing continuous near-pair AM kernel lower bound also pays the
stronger reward, with no numerical or asymptotic assumption. -/
theorem am_near_weight_ge_reward {x : ℝ} (hx : |x| ≤ 4/5) :
    localReward ≤ AMW.wfunAM x := by
  have hk := RHWeilRecord.am_near_kernel_lower hx
  unfold AMW.wfunAM localReward
  nlinarith [sq_nonneg (AMW.kfunAM x-51/550)]

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


/-- The existing all-zero seam transports the strengthened reward while retaining
the actual simple critical-line count and all nontrivial multiplicities. -/
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


/-- Conditional true simple dyadic conclusion. The only new input is the
unconditional local nine-point certificate, assembled in NinthSpan.lean. -/
theorem simple_dyadic_of_nine_point_certificate
    (W : WCert 9) (hW : W.Adm) (hB : W.B = gapPressure)
    (hmass : (∑ a : Fin 9, ∑ b : Fin 9,
      if (a : ℕ) < (b : ℕ) then W.a a b else 0) ≤ 16)
    (hcert : ∀ g : Fin 8 → ℝ, (∀ r, 4/5 ≤ g r) → localReward ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤
        Zeta23.N0simple T (2*T) := by
  have hs := am_simple_dyadic_of_lossless_defect zetaZeroConfig paperInputs_zeta
    (am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W hW hB hmass hcert)
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using hs

/-- Conditional cumulative simple conclusion by existing interval additivity. -/
theorem simple_cumulative_of_nine_point_certificate
    (W : WCert 9) (hW : W.Adm) (hB : W.B = gapPressure)
    (hmass : (∑ a : Fin 9, ∑ b : Fin 9,
      if (a : ℕ) < (b : ℕ) then W.a a b else 0) ≤ 16)
    (hcert : ∀ g : Fin 8 → ℝ, (∀ r, 4/5 ≤ g r) → localReward ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' zetaSeam)
    (simple_dyadic_of_nine_point_certificate W hW hB hmass hcert)

theorem distinct_dyadic_of_nine_point_certificate
    (W : WCert 9) (hW : W.Adm) (hB : W.B = gapPressure)
    (hmass : (∑ a : Fin 9, ∑ b : Fin 9,
      if (a : ℕ) < (b : ℕ) then W.a a b else 0) ≤ 16)
    (hcert : ∀ g : Fin 8 → ℝ, (∀ r, 4/5 ≤ g r) → localReward ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0star T (2*T) := by
  apply am_distinct_dyadic_of_lossless_defect
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W hW hB hmass hcert

theorem distinct_cumulative_of_nine_point_certificate
    (W : WCert 9) (hW : W.Adm) (hB : W.B = gapPressure)
    (hmass : (∑ a : Fin 9, ∑ b : Fin 9,
      if (a : ℕ) < (b : ℕ) then W.a a b else 0) ≤ 16)
    (hcert : ∀ g : Fin 8 → ℝ, (∀ r, 4/5 ≤ g r) → localReward ≤ Fw W g) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (recordRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T := by
  apply am_distinct_cumulative_of_lossless_defect
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    am_lossless_defect_of_nine_point_certificate zetaZeroConfig paperInputs_zeta
      W hW hB hmass hcert

end RHWeilRecord.JointFramePair
