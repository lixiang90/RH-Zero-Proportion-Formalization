import RecordProportion.FiniteCertificate

/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
The stronger outside-frame threshold, and transport of a complete captured-pair
bound to the actual fixed W9 objective. The old c260 theorem remains intact.
-/
noncomputable section
open scoped BigOperators

namespace RHWeil.RecordSubmission.NinthSpanLocal
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
open AMW.Cert.PCell AMW.Cert.PC8CL
open RHWeil.RecordSubmission.FiniteCertificate

theorem outside_low_cover {F0 F1 w : ℝ}
    (h0 : (805003 : ℝ) / 100000000 ≤ F0)
    (h1 : (805003 : ℝ) / 100000000 ≤ F1)
    (hw : 0 ≤ w)
    (hout : (805803 : ℝ) / 100000000 ≤ F0 ∨
      (805803 : ℝ) / 100000000 ≤ F1) :
    (805403 : ℝ) / 100000000 ≤ (F0 + F1) / 2 + 2 * w := by
  rcases hout with h | h <;> norm_num at * <;> linarith

theorem target_ratio :
    (((67216841 : ℚ) - 404350) / 100000000) /
      (1 - (805403 : ℚ) / 100000000) = 941021 / 1397107 := by
  norm_num

theorem strict_improvement :
    (66812491 : ℚ) / 99194740 < 941021 / 1397107 := by
  norm_num

/-- The outside branch is exactly the average of the old PC8 lower bound
and the stronger-frame capture threshold. Both-low frames use hpair. -/
theorem local_from_low_pairs
    (hpair : ∀ (g : Nat → Real) (left right : Nat), left < 482 → right < 482 →
      (∀ r < 8, (4:Real)/5 ≤ g r) → InCell 7 PR (lowCell left) g →
      InCell 7 PR (lowCell right) (fun r => g (r+1)) →
      (805403:Real)/100000000 ≤ scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7))
    (g : Fin 8 → Real) (hg : ∀ r, (4:Real)/5 ≤ g r) :
    (805403:Real)/100000000 ≤ Zeta23Ext.BridgeW.Fw W9 g := by
  let f := fun r : Nat => [g 0,g 1,g 2,g 3,g 4,g 5,g 6,g 7].getD r 0
  have hf : ∀ r < 8, (4:Real)/5 ≤ f r := by
    intro r hr
    have he : f r = g ⟨r,hr⟩ := by interval_cases r <;> rfl
    rw [he]
    exact hg ⟨r,hr⟩
  have hn0 : ∀ r < 7, 0 ≤ f r := by intro r hr; have := hf r (by omega); linarith
  have hn1 : ∀ r < 7, 0 ≤ f (r+1) := by intro r hr; have := hf (r+1) (by omega); linarith
  have ho0 := old_frame_lower f hn0
  have ho1 := old_frame_lower (fun r => f (r+1)) hn1
  have hnon : 0 ≤ wfun (f 0+f 1+f 2+f 3+f 4+f 5+f 6+f 7) := sq_nonneg _
  rw [W9_scalar_identity]
  change (805403:Real)/100000000 ≤
    scalarF9 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7)
  rcases strong_or_low_full f (fun r hr => hf r (by omega)) with hstrong | hlow
  · rw [scalar_from_frames]
    norm_num [SA] at ho0 ho1 hstrong ⊢
    nlinarith
  · rcases strong_or_low_full (fun r => f (r+1)) (fun r hr => hf (r+1) (by omega)) with hstrong | hlow'
    · rw [scalar_from_frames]
      norm_num [SA] at ho0 ho1 hstrong ⊢
      nlinarith
    · obtain ⟨left,hl,hcell⟩ := hlow
      obtain ⟨right,hr,hcell'⟩ := hlow'
      exact hpair f left right hl hr hf hcell hcell'

end RHWeil.RecordSubmission.NinthSpanLocal
