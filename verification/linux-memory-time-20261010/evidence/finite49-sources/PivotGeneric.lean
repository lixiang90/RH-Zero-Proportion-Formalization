import «tmp».«two-edge-high».twoedge
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option stderrAsMessages false
namespace RHWeil.RecordSubmission.FiniteCertificateData
noncomputable def chosenBound (left right i j k : Nat) : Int :=
  primitiveBound left right i k + primitiveBound left right k j

theorem chosen_bound_le (left right i j k : Nat) (hi : i < 9) (hj : j < 9) (hk : k < 9) :
    ((pairClosure left right)[9*i+j]?).getD 0 ≤ chosenBound left right i j k := by
  have h := RHWeilRecord.FloydTwoEdge.closure_le_two_edge
    (primitiveBounds left right) i j k hi hj hk
  change ((pairClosure left right)[9*i+j]?).getD 0 ≤
    ((primitiveBounds left right)[9*i+k]?).getD 0 +
    ((primitiveBounds left right)[9*k+j]?).getD 0 at h
  rw [primitiveBounds_entry left right i k hi hk,
      primitiveBounds_entry left right k j hk hj] at h
  exact h

noncomputable def chosenLower (index lowWord highWord : Nat) : Int :=
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let left := packet.1
  let right := packet.2.1
  let count := packet.2.2.1
  let word := packet.2.2.2.1
  let extraCount := packet.2.2.2.2.1
  let extraWord := packet.2.2.2.2.2
  let rows := frameRows left 0 ++ frameRows right 1 ++ extraRows left right extraCount extraWord
  let multipliers := (decodeMultipliers count word).map fun p =>
    let row := rows.getD p.1 default
    let lambda : Int := p.2 * (if row.geometric then 10000000000 else 1)
    (row,lambda)
  let value := multipliers.foldl (fun total p =>
    total - p.2 * p.1.bound) 0
  value + ((List.range 42).map fun column =>
    let residual := multipliers.foldl (fun total p =>
      total + p.2 * p.1.coeff column) (1000000000*objectiveCoeff column)
    let lo := if column < 8 then max (4*32768) (-(chosenBound left right (column+1) column (bits lowWord (4*column) 4 % 9))) else 0
    let hi := if column < 8 then chosenBound left right column (column+1) (bits highWord (4*column) 4 % 9)
      else 5*10000000000*32768
    residual * (if 0 ≤ residual then lo else hi)).sum


 theorem chosen_lower_le (index lowWord highWord : Nat) :
    chosenLower index lowWord highWord ≤ integerCertificateLower index := by
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  have hentry := chosen_bound_le packet.1 packet.2.1
  unfold chosenLower integerCertificateLower
  dsimp only
  apply add_le_add le_rfl
  apply List.sum_le_sum
  intro column hcolumn
  have hc : column < 42 := List.mem_range.mp hcolumn
  apply RHWeilRecord.FloydWeakening.residual_lower_mono
  · by_cases hs : column < 8
    · simp only [if_pos hs]
      apply RHWeilRecord.FloydWeakening.max_neg_mono
      exact hentry (column+1) column (bits lowWord (4*column) 4 % 9) (by omega) (by omega) (by omega)
    · simp only [if_neg hs]
      exact le_rfl
  · by_cases hs : column < 8
    · simp only [if_pos hs]
      exact hentry column (column+1) (bits highWord (4*column) 4 % 9) (by omega) (by omega) (by omega)
    · simp only [if_neg hs]
      exact le_rfl

theorem integerCheck_of_chosen (index lowWord highWord : Nat)
    (h : decide (2*805260*(5*10000000000*32768)*1000000000 ≤ chosenLower index lowWord highWord) = true) :
    integerCertificateCheck index = true := by
  apply decide_eq_true
  exact (of_decide_eq_true h).trans (chosen_lower_le index lowWord highWord)
end RHWeil.RecordSubmission.FiniteCertificateData
