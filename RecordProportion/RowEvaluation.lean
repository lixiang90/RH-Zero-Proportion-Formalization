import Mathlib
import RecordProportion.FiniteCertificateData

/- Evaluation of the fixed sparse row shape, with an arbitrary scalar kernel w.
The consuming module supplies the actual imported AM kernel and row constraints. -/
namespace RHWeilRecord.RowEvaluation
open RHWeil.RecordSubmission.FiniteCertificateData
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def kernelScale : ℝ := 5*10000000000*32768

def gsum (g : Nat → ℝ) (first last : Nat) : ℝ :=
  ∑ k ∈ Finset.range (last-first), g (first+k)

def actualValue (w : ℝ → ℝ) (g : Nat → ℝ) (column : Nat) : ℝ :=
  if column < 8 then 5*32768*g column else
    let span := squareSpans.getD (column-8) (0,0)
    kernelScale*w (gsum g span.1 span.2)

theorem sum_interval (g : Nat → ℝ) (first last : Nat) (hl : last ≤ 8) :
    (∑ i ∈ Finset.range 8, if first ≤ i ∧ i < last then g i else 0) =
      gsum g first last := by
  have hs : (Finset.range 8).filter (fun i => first ≤ i ∧ i < last) =
      Finset.Ico first last := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [←Finset.sum_filter,hs,Finset.sum_Ico_eq_sum_range]
  rfl

theorem rowDot_eval (w : ℝ → ℝ) (g : Nat → ℝ) (row : IntegerRow)
    (hl : row.last ≤ 8)
    (hs : row.zcoef = 0 ∨ 8 ≤ row.square ∧ row.square < 42) :
    (∑ i ∈ Finset.range 42, (row.coeff i : ℝ)*actualValue w g i) =
      (row.slope:ℝ)*5*32768*gsum g row.first row.last +
        (row.zcoef:ℝ)*actualValue w g row.square := by
  have hfirst : (∑ i ∈ Finset.range 8, (row.coeff i:ℝ)*actualValue w g i) =
      (row.slope:ℝ)*5*32768*gsum g row.first row.last := by
    calc
      _ = ∑ i ∈ Finset.range 8, ((row.slope:ℝ)*5*32768)*
          (if row.first ≤ i ∧ i < row.last then g i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi8 : i < 8 := Finset.mem_range.mp hi
        by_cases ht : row.first ≤ i ∧ i < row.last
        · simp only [IntegerRow.coeff,actualValue,if_pos hi8,if_pos ht]
          ring
        · simp [IntegerRow.coeff,actualValue,hi8,ht]
      _ = ((row.slope:ℝ)*5*32768)*
          (∑ i ∈ Finset.range 8, if row.first ≤ i ∧ i < row.last then g i else 0) :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [sum_interval g row.first row.last hl]
  have hlast : (∑ i ∈ Finset.range 34, (row.coeff (8+i):ℝ)*actualValue w g (8+i)) =
      (row.zcoef:ℝ)*actualValue w g row.square := by
    rcases hs with hz | hs
    · simp [IntegerRow.coeff,hz,show ∀ i : Nat, ¬8+i < 8 by omega]
    · have hindex : row.square-8 ∈ Finset.range 34 := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (row.square-8)]
      · have he : 8+(row.square-8)=row.square := by omega
        simp [he,IntegerRow.coeff,show ¬row.square < 8 by omega]
      · intro i hi hne
        have he : 8+i ≠ row.square := by omega
        simp [IntegerRow.coeff,show ¬8+i < 8 by omega,he]
      · exact fun h => False.elim (h hindex)
  change (∑ i ∈ Finset.range (8+34), (row.coeff i:ℝ)*actualValue w g i) = _
  rw [Finset.sum_range_add,hfirst,hlast]

/-- Membership gives the actual lookup position and the retained scalar-kernel value. -/
theorem squareColumn_eval (w : ℝ → ℝ) (g : Nat → ℝ) (i j : Nat)
    (hm : (i,j) ∈ squareSpans) :
    8 ≤ squareColumn i j ∧ squareColumn i j < 42 ∧
      actualValue w g (squareColumn i j) = kernelScale*w (gsum g i j) := by
  let k := squareSpans.findIdx (fun p => p == (i,j))
  have hk : k < squareSpans.length :=
    List.findIdx_lt_length_of_exists ⟨(i,j),hm,by simp⟩
  have hlen : squareSpans.length = 34 := by decide
  have hgot : squareSpans[k]'hk = (i,j) := by
    have hb := List.findIdx_getElem (xs:=squareSpans) (p:=fun p => p == (i,j)) (w:=hk)
    simpa only [beq_iff_eq] using hb
  have hsome : squareSpans[k]? = some (i,j) := by
    rw [List.getElem?_eq_getElem hk,hgot]
  have he : squareColumn i j = 8+k := rfl
  have hge : 8 ≤ squareColumn i j := by omega
  refine ⟨hge,by omega,?_⟩
  simp [actualValue,he,show ¬8+k < 8 by omega,hsome]

end
end RHWeilRecord.RowEvaluation
#print axioms RHWeilRecord.RowEvaluation.rowDot_eval
#print axioms RHWeilRecord.RowEvaluation.squareColumn_eval
