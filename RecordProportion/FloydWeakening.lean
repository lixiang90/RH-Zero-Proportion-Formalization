import RecordProportion.FloydSoundness

/-
Entrywise weakening under the simultaneous Int Floyd closure, and the
monotonicity of the signed box-residual correction.  No certificate data
or finite verification result is assumed in these generic statements.
-/

namespace RHWeilRecord.FloydWeakening

open RHWeilRecord.FloydSoundness

/-- A single true Floyd minimum never increases a valid slot. -/
theorem floydStep_le (d : Array Int) (k slot : Nat) (hs : slot < 81) :
    ((floydStep d k)[slot]?).getD 0 ≤ (d[slot]?).getD 0 := by
  rw [floydStep_entry d k slot hs]
  exact min_le_left _ _

/-- Any number of simultaneous Floyd updates only tightens each valid slot. -/
theorem foldl_le : ∀ (ks : List Nat) (d : Array Int) (slot : Nat),
    slot < 81 → ((ks.foldl floydStep d)[slot]?).getD 0 ≤ (d[slot]?).getD 0 := by
  intro ks
  induction ks with
  | nil => intro d slot hs; exact le_rfl
  | cons k ks ih =>
      intro d slot hs
      simpa only [List.foldl_cons] using
        (ih (floydStep d k) slot hs).trans (floydStep_le d k slot hs)

/-- The nine-pivot closure is bounded above by the primitive edge array. -/
theorem closure_le_primitive (d : Array Int) (slot : Nat) (hs : slot < 81) :
    ((closure d)[slot]?).getD 0 ≤ (d[slot]?).getD 0 :=
  foldl_le (List.range 9) d slot hs

/-- The i,j form used by the actual 9-by-9 certificate array. -/
theorem closure_entry_le (d : Array Int) (i j : Nat) (hi : i < 9) (hj : j < 9) :
    ((closure d)[9*i+j]?).getD 0 ≤ (d[9*i+j]?).getD 0 := by
  exact closure_le_primitive d (9*i+j) (by omega)

/-- Raising a box lower bound or lowering its upper bound improves its
signed residual correction, independently of whether either box is empty. -/
theorem residual_lower_mono (r basicLo basicHi fullLo fullHi : Int)
    (hlo : basicLo ≤ fullLo) (hhi : fullHi ≤ basicHi) :
    r * (if 0 ≤ r then basicLo else basicHi) ≤
      r * (if 0 ≤ r then fullLo else fullHi) := by
  by_cases hr : 0 ≤ r
  · simp only [if_pos hr]
    exact mul_le_mul_of_nonneg_left hlo hr
  · simp only [if_neg hr]
    exact mul_le_mul_of_nonpos_left hhi (le_of_lt (lt_of_not_ge hr))

/-- The lower bounds used for gap coordinates improve under closure. -/
theorem max_neg_mono (theta primitive closed : Int) (h : closed ≤ primitive) :
    max theta (-primitive) ≤ max theta (-closed) := by
  exact max_le_max le_rfl (neg_le_neg h)

/-- Pointwise monotonicity transports the full finite residual sum. -/
theorem residual_sum_mono (columns : List Nat)
    (residual basicLo basicHi fullLo fullHi : Nat → Int)
    (hlo : ∀ column ∈ columns, basicLo column ≤ fullLo column)
    (hhi : ∀ column ∈ columns, fullHi column ≤ basicHi column) :
    (columns.map fun column => residual column *
      (if 0 ≤ residual column then basicLo column else basicHi column)).sum ≤
    (columns.map fun column => residual column *
      (if 0 ≤ residual column then fullLo column else fullHi column)).sum := by
  apply List.sum_le_sum
  intro column hcolumn
  exact residual_lower_mono _ _ _ _ _ (hlo column hcolumn) (hhi column hcolumn)

end RHWeilRecord.FloydWeakening

#print axioms RHWeilRecord.FloydWeakening.closure_le_primitive
#print axioms RHWeilRecord.FloydWeakening.closure_entry_le
#print axioms RHWeilRecord.FloydWeakening.residual_lower_mono
#print axioms RHWeilRecord.FloydWeakening.residual_sum_mono
