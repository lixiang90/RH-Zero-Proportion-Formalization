import RecordProportion.FloydWeakening

/- Generic two-edge weakening of the exact simultaneous nine-pivot closure.
No array-size, diagonal, potential, cycle or certificate-data hypothesis. -/
namespace RHWeilRecord.FloydTwoEdge
open RHWeilRecord.FloydSoundness RHWeilRecord.FloydWeakening

/-- Later pivots can only decrease any valid slot. -/
theorem closure_le_prefix (d : Array Int) (n slot : Nat)
    (hn : n ≤ 9) (hs : slot < 81) :
    ((closure d)[slot]?).getD 0 ≤
      (((List.range n).foldl floydStep d)[slot]?).getD 0 := by
  have hsum : n + (9 - n) = 9 := by omega
  unfold RHWeilRecord.FloydSoundness.closure
  rw [← hsum, List.range_add, List.foldl_append]
  exact foldl_le _ _ slot hs

/-- The next prefix is the actual update with that single pivot. -/
theorem prefix_succ (d : Array Int) (k : Nat) :
    (List.range (k+1)).foldl floydStep d =
      floydStep ((List.range k).foldl floydStep d) k := by
  rw [List.range_succ, List.foldl_append]
  rfl

/-- Every two-edge path is an upper bound for the full closure entry.
This remains valid in the presence of negative cycles. -/
theorem closure_le_two_edge (d : Array Int) (i j k : Nat)
    (hi : i < 9) (hj : j < 9) (hk : k < 9) :
    ((closure d)[9*i+j]?).getD 0 ≤
      (d[9*i+k]?).getD 0 + (d[9*k+j]?).getD 0 := by
  let p := (List.range k).foldl floydStep d
  have hpost := closure_le_prefix d (k+1) (9*i+j) (by omega) (by omega)
  rw [prefix_succ] at hpost
  have hstep : ((floydStep p k)[9*i+j]?).getD 0 ≤
      (p[9*i+k]?).getD 0 + (p[9*k+j]?).getD 0 := by
    rw [floydStep_entry_ij p k i j hi hj]
    exact min_le_right _ _
  have hik : (p[9*i+k]?).getD 0 ≤ (d[9*i+k]?).getD 0 :=
    foldl_le (List.range k) d (9*i+k) (by omega)
  have hkj : (p[9*k+j]?).getD 0 ≤ (d[9*k+j]?).getD 0 :=
    foldl_le (List.range k) d (9*k+j) (by omega)
  exact (hpost.trans hstep).trans (add_le_add hik hkj)

/-- A common lower bound lies below a seeded finite minimum. -/
theorem lower_le_foldl_min (ks : List Nat) (f : Nat → Int) (x b : Int)
    (hb : x ≤ b) (hf : ∀ k ∈ ks, x ≤ f k) :
    x ≤ ks.foldl (fun best k => min best (f k)) b := by
  induction ks generalizing b with
  | nil => simpa using hb
  | cons k ks ih =>
      simp only [List.foldl_cons]
      exact ih (min b (f k)) (le_min hb (hf k (by simp)))
        (fun a ha => hf a (by simp [ha]))

/-- The original edge and all nine original two-edge candidates, with no
feedback of newly tightened entries into other candidates. -/
def twoEdgeEntry (d : Array Int) (i j : Nat) : Int :=
  (List.range 9).foldl
    (fun best k => min best ((d[9*i+k]?).getD 0 + (d[9*k+j]?).getD 0))
    ((d[9*i+j]?).getD 0)

/-- The exact full closure is bounded by the ten-candidate seeded minimum. -/
theorem closure_le_twoEdgeEntry (d : Array Int) (i j : Nat)
    (hi : i < 9) (hj : j < 9) :
    ((closure d)[9*i+j]?).getD 0 ≤ twoEdgeEntry d i j := by
  apply lower_le_foldl_min
  · exact closure_entry_le d i j hi hj
  · intro k hk
    exact closure_le_two_edge d i j k hi hj (List.mem_range.mp hk)

end RHWeilRecord.FloydTwoEdge
