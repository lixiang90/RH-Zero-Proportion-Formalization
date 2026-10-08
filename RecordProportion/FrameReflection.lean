import RecordProportion.PointSoundness

noncomputable section
namespace CheckpointFrameReflection
open RHWeil.RecordSubmission.FiniteCertificateData
open RHWeil.RecordSubmission.PointSoundness
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option stderrAsMessages false
attribute [local irreducible] cells pairPacks catalog pointPacket AMW.Cert.PC8CLData.PT

theorem cellPacket_mirror {label : Nat} (h : label < 241) :
    cellPacket (label+241) = cellPacket label := by
  have hn : ¬ label+241 < 241 := by omega
  simp only [cellPacket, if_neg hn, if_pos h, Nat.add_sub_cancel]

theorem cellBound_mirror {label : Nat} (h : label < 241) (i j side : Nat) :
    cellBound (label+241) i j side = cellBound label (7-j) (7-i) side := by
  have hn : ¬ label+241 < 241 := by omega
  simp only [cellBound, if_neg hn, if_pos h, cellPacket_mirror h]

theorem termAtom_mirror {label : Nat} (h : label < 241) (i j : Nat) :
    termAtom (label+241) i j = termAtom label (7-j) (7-i) := by
  have hn : ¬ label+241 < 241 := by omega
  simp only [termAtom, if_neg hn, if_pos h, cellPacket_mirror h]

theorem sum_range_reflect (f : Nat → Nat) (n : Nat) :
    ((List.range n).map (fun k => f (n-1-k))).sum =
      ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.sum_range_succ' (fun k => f ((n+1)-1-k)) n]
    simp only [Nat.add_sub_cancel]
    have hf : (fun k => f (n-k.succ)) = (fun k => f (n-1-k)) := by
      funext k
      congr 1
      omega
    rw [hf, ih, List.sum_range_succ]
    exact Nat.add_comm _ _

theorem adjacent_sum_reflect (f : Nat → Nat) {i j : Nat}
    (hij : i ≤ j) (hj : j ≤ 7) :
    ((List.range (j-i)).map (fun k => f (7-(i+k+1)))).sum =
      ((List.range ((7-i)-(7-j))).map (fun k => f ((7-j)+k))).sum := by
  have hd : (7-i)-(7-j) = j-i := by omega
  rw [hd]
  have hm : (List.range (j-i)).map (fun k => f (7-(i+k+1))) =
      (List.range (j-i)).map (fun k => f ((7-j)+(j-i-1-k))) := by
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    congr 1
    omega
  rw [hm]
  exact sum_range_reflect (fun k => f ((7-j)+k)) (j-i)

theorem adjacent_bound_sum_mirror {label i j : Nat} (h : label < 241)
    (hij : i ≤ j) (hj : j ≤ 7) (side : Nat) :
    ((List.range (j-i)).map (fun k => cellBound (label+241) (i+k) (i+k+1) side)).sum =
      ((List.range ((7-i)-(7-j))).map
        (fun k => cellBound label ((7-j)+k) ((7-j)+k+1) side)).sum := by
  have hm : (List.range (j-i)).map (fun k => cellBound (label+241) (i+k) (i+k+1) side) =
      (List.range (j-i)).map (fun k => cellBound label (7-(i+k+1)) (7-(i+k+1)+1) side) := by
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [cellBound_mirror h]
    congr 1
    omega
  rw [hm]
  exact adjacent_sum_reflect (fun k => cellBound label k (k+1) side) hij hj

theorem tightLower_mirror {label i j : Nat} (h : label < 241)
    (hij : i ≤ j) (hj : j ≤ 7) :
    tightLower (label+241) i j = tightLower label (7-j) (7-i) := by
  simp only [tightLower, cellLower]
  rw [cellBound_mirror h, adjacent_bound_sum_mirror h hij hj]

theorem tightUpper_mirror {label i j : Nat} (h : label < 241)
    (hij : i ≤ j) (hj : j ≤ 7) :
    tightUpper (label+241) i j = tightUpper label (7-j) (7-i) := by
  simp only [tightUpper, cellUpper]
  rw [cellBound_mirror h, adjacent_bound_sum_mirror h hij hj]

theorem termCheck_mirror {label i j : Nat} (h : label < 241)
    (hij : i ≤ j) (hj : j ≤ 7) :
    termCheck (label+241) i j = termCheck label (7-j) (7-i) := by
  simp only [termCheck, constantCheck]
  rw [termAtom_mirror h, tightLower_mirror h hij hj, tightUpper_mirror h hij hj]

def mirrorTerm (t : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (7-t.2.1,7-t.1,t.2.2)

theorem mirror_terms_perm : (terms.map mirrorTerm).Perm terms := by decide +kernel

theorem terms_range_check : terms.all (fun t => decide (t.1 < t.2.1 ∧ t.2.1 ≤ 7)) = true :=
  by decide +kernel

theorem term_ranges {t : Nat × Nat × Nat} (ht : t ∈ terms) :
    t.1 < t.2.1 ∧ t.2.1 ≤ 7 := by
  exact of_decide_eq_true (List.all_eq_true.mp terms_range_check t ht)

theorem frameCheck_mirror {label : Nat} (h : label < 241) :
    frameCheck (label+241) = frameCheck label := by
  unfold frameCheck
  rw [← mirror_terms_perm.all_eq (f := fun t => termCheck label t.1 t.2.1), List.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro hall t ht
    have hb := term_ranges ht
    simpa only [Function.comp_apply, mirrorTerm, termCheck_mirror h (Nat.le_of_lt hb.1) hb.2]
      using hall t ht
  · intro hall t ht
    have hb := term_ranges ht
    simpa only [Function.comp_apply, mirrorTerm, termCheck_mirror h (Nat.le_of_lt hb.1) hb.2]
      using hall t ht

#print axioms frameCheck_mirror
end CheckpointFrameReflection
