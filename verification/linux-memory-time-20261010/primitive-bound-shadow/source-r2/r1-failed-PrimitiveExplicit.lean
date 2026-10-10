/- Copyright 2026 Li Xiang (lixiang90). Apache-2.0.
Prepared source-only controlled shadow probe; not Lean checked.
The target proof is copied from frozen r6 source; see metadata.json. -/
import Solution.Candidate
set_option Elab.async false
section RHWeilBundleModule_11
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RHWeil.RecordSubmission.FiniteCertificate
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC8CL
open RHWeil.RecordSubmission.FiniteCertificateData
run_cmd do
  let env ← Lean.getEnv
  discard <| IO.wait env.checked
  let ms ← IO.monoMsNow
  IO.eprintln s!"PRIMITIVE_PROBE_BEGIN {ms}"
theorem primitiveBound_sound_probe_explicit {g : Nat → Real} {left right i j : Nat}
    (htheta : ∀ r < 8, (4 : Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell left) g)
    (hr : InCell 7 PR (lowCell right) (fun r => g (r+1)))
    (hi : i < 9) (hj : j < 9) :
    gapPotential g j - gapPotential g i ≤ (primitiveBound left right i j : Real) := by
  by_cases heq : i = j
  · subst j
    simp [primitiveBound]
  have hinf := pairPotential_infinity htheta hl hr hi hj
  have hfirst : gapPotential g j - gapPotential g i ≤
      (if i ≤ 7 ∧ j ≤ 7 then
        if i < j then 5*(cellUpper left i j : Int) else -5*(cellLower left j i : Int)
       else 1000000000000000000000000000000 : Int) := by
    by_cases hframe : i ≤ 7 ∧ j ≤ 7
    · rw [if_pos hframe]
      by_cases hij : i < j
      · rw [if_pos hij, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        exact (framePotential_upper hl hij hframe.2).1
      · rw [if_neg hij]
        push_cast
        norm_num
        have hrev := (framePotential_upper (i := j) (j := i) hl (by omega) hframe.1).2
        simpa only [neg_mul] using hrev
    · simpa only [if_neg hframe, Int.cast_ofNat] using hinf
  have hsecond : gapPotential g j - gapPotential g i ≤
      (if 1 ≤ i ∧ 1 ≤ j then
        if i < j then 5*(cellUpper right (i-1) (j-1) : Int)
        else -5*(cellLower right (j-1) (i-1) : Int)
       else 1000000000000000000000000000000 : Int) := by
    by_cases hframe : 1 ≤ i ∧ 1 ≤ j
    · rw [if_pos hframe]
      by_cases hij : i < j
      · rw [if_pos hij, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        have hs := (lowCell_spanbounds right (fun r => g (r+1)) hr
          (i-1) (j-1) (by omega) (by omega)).2
        rw [gsum_shift] at hs
        rw [show i-1+1=i by omega, show j-1+1=j by omega] at hs
        have hd := gapPotential_difference g i j (by omega)
        norm_num [SC] at hs hd
        linear_combination hd + 163840 * hs
      · rw [if_neg hij]
        push_cast
        norm_num
        have hs := (lowCell_spanbounds right (fun r => g (r+1)) hr
          (j-1) (i-1) (by omega) (by omega)).1
        rw [gsum_shift] at hs
        rw [show i-1+1=i by omega, show j-1+1=j by omega] at hs
        have hd := gapPotential_difference g j i (by omega)
        norm_num [SC] at hs hd
        linear_combination 163840 * hs - hd
    · simpa only [if_neg hframe, Int.cast_ofNat] using hinf
  unfold primitiveBound
  rw [if_neg heq]
  dsimp only
  by_cases hadj : i = j+1
  · rw [if_pos hadj, Int.cast_min, Int.cast_min]
    refine le_min (le_min hfirst hsecond) ?_
    rw [hadj]
    have ht := htheta j (by omega)
    have hd := gapPotential_difference g j i (by omega)
    rw [hadj] at hd
    simp only [gsum_range, Nat.add_sub_cancel, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, Nat.add_zero] at hd
    norm_num [SC] at hd ⊢
    linear_combination 163840 * ht - hd
  · rw [if_neg hadj, Int.cast_min]
    exact le_min hfirst hsecond
run_cmd do
  let env ← Lean.getEnv
  discard <| IO.wait env.checked
  let ms ← IO.monoMsNow
  IO.eprintln s!"PRIMITIVE_PROBE_END {ms}"
#check primitiveBound_sound_probe_explicit
#print axioms primitiveBound_sound_probe_explicit
end RHWeil.RecordSubmission.FiniteCertificate
end
end RHWeilBundleModule_11
