import RecordProportion.FiniteCertificate

/- Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
A literal 33-column frame embedding into the retained 42-column row semantics.
The frame certificate uses only seven gaps and the original 26 square spans. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 0

namespace RHWeil.RecordSubmission.JointFramePairFrame
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
open AMW.Cert.PCell AMW.Cert.PC8CL
open RHWeil.RecordSubmission.FiniteCertificateData
open RHWeil.RecordSubmission.FiniteCertificate

def FramePotentialBound (p : Nat → Real) (bounds : Array Int) : Prop :=
  ∀ i < 8, ∀ j < 8, p j-p i ≤ (((bounds[8*i+j]?).getD 0:Int):Real)

def frameEmbed (column : Nat) : Nat :=
  if column < 7 then column else column+1

def frameCoeff (row : IntegerRow) (column : Nat) : Int :=
  row.coeff (frameEmbed column)

def frameValue (g : Nat → Real) (column : Nat) : Real :=
  actualValue g (frameEmbed column)

def frameObjectiveCoeff (column : Nat) : Int :=
  if column < 7 then 10000000000 * (BS.getD column 0 : Int)
  else ((terms.getD (column-7) (0,0,0)).2.2 : Int)

theorem frame_rowDot_transport42 (g : Nat → Real) (row : IntegerRow)
    (hlast : row.last ≤ 7)
    (hz : row.zcoef = 0 ∨ 8 ≤ row.square ∧ row.square < 34) :
    (∑ c ∈ Finset.range 33, (frameCoeff row c:Real)*frameValue g c) =
      ∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c := by
  have hseven : row.coeff 7 = 0 := by
    simp only [IntegerRow.coeff,show 7 < 8 by decide,if_pos]
    rw [if_neg (by omega : ¬(row.first ≤ 7 ∧ 7 < row.last))]
  have htail : ∀ i < 8, row.coeff (34+i) = 0 := by
    intro i hi
    simp only [IntegerRow.coeff,show ¬34+i < 8 by omega,if_neg]
    rcases hz with hz | hs
    · simp [hz]
    · rw [if_neg (by omega : 34+i ≠ row.square)]
      simp
  have h33 :
      (∑ c ∈ Finset.range 33, (frameCoeff row c:Real)*frameValue g c) =
      (∑ c ∈ Finset.range 7, (row.coeff c:Real)*actualValue g c) +
      ∑ c ∈ Finset.range 26, (row.coeff (8+c):Real)*actualValue g (8+c) := by
    change (∑ c ∈ Finset.range (7+26), (frameCoeff row c:Real)*frameValue g c) = _
    rw [Finset.sum_range_add]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro c hc
      have hc7 := Finset.mem_range.mp hc
      simp [frameCoeff,frameValue,frameEmbed,hc7]
    · apply Finset.sum_congr rfl
      intro c hc
      have hc7 : ¬7+c < 7 := by omega
      have he : 7+c+1=8+c := by omega
      simp [frameCoeff,frameValue,frameEmbed,hc7,he]
  rw [h33]
  change _ = ∑ c ∈ Finset.range (34+8), (row.coeff c:Real)*actualValue g c
  rw [Finset.sum_range_add]
  have hzsum : (∑ c ∈ Finset.range 8, (row.coeff (34+c):Real)*actualValue g (34+c))=0 := by
    apply Finset.sum_eq_zero
    intro c hc
    rw [htail c (Finset.mem_range.mp hc)]
    simp
  rw [hzsum,add_zero]
  change _ = ∑ c ∈ Finset.range (8+26), (row.coeff c:Real)*actualValue g c
  rw [Finset.sum_range_add]
  congr 1
  change _ = ∑ c ∈ Finset.range (7+1), (row.coeff c:Real)*actualValue g c
  rw [Finset.sum_range_add]
  simp [hseven]

theorem frame_row_sound {g : Nat → Real} {row : IntegerRow}
    (hlast : row.last ≤ 7)
    (hz : row.zcoef = 0 ∨ 8 ≤ row.square ∧ row.square < 34)
    (hrow : (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real)) :
    (∑ c ∈ Finset.range 33, (frameCoeff row c:Real)*frameValue g c) ≤ (row.bound:Real) := by
  rw [frame_rowDot_transport42 g row hlast hz]
  exact hrow

theorem frameObjective_identity (g : Nat → Real) :
    (∑ c ∈ Finset.range 33, (frameObjectiveCoeff c:Real)*frameValue g c) =
      kernelScale * Fg 7 BS TS g := by
  simp [frameObjectiveCoeff,frameValue,frameEmbed,actualValue,
    RHWeilRecord.RowEvaluation.actualValue,kernelScale,
    RHWeilRecord.RowEvaluation.kernelScale,
    Fg,BS,TS,tA,tI,tJ,terms,squareSpans,gsum_range,
    RHWeilRecord.RowEvaluation.gsum,Finset.sum_range_succ]
  ring

end RHWeil.RecordSubmission.JointFramePairFrame

#print axioms RHWeil.RecordSubmission.JointFramePairFrame.frame_rowDot_transport42
#print axioms RHWeil.RecordSubmission.JointFramePairFrame.frameObjective_identity
