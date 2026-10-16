/- SPDX-License-Identifier: Apache-2.0
Fail-closed dispatch of reflected, inconsistent and numerical cells. -/
import StructuralW10Cert20261016.FloorTransfer
import StructuralW10Cert20261016.TreeCoverage
import StructuralW10Cert20261016.EncodedLiteral

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
namespace StructuralW10Cert20261016.LeafDispatch

/-- 0: reflection; 1..9: empty coordinate; 10..45: empty span;
46 and above: numerical certificate from a printable exact payload. -/
def check (payload : ℕ → ℕ) (c : Cl) (id : ℕ) : Bool :=
  if id = 0 then decide (c.U.getD 8 0 < c.L.getD 0 0)
  else if id ≤ 9 then decide (c.U.getD (id-1) 0 < c.L.getD (id-1) 0)
  else if id ≤ 45 then decide (c.B.getD (id-10) 0 < c.A.getD (id-10) 0)
  else EncodedLiteral.checkPacked c (payload (id-46))

theorem check_sound (payload : ℕ → ℕ) (c : Cl) (id : ℕ)
    (h : check payload c id = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  unfold check at h
  split_ifs at h with h0 h9 h45
  · exact FloorTransfer.reflection_leaf (of_decide_eq_true h)
  · exact TreeCoverage.cov_of_coordinate_empty (by omega) (of_decide_eq_true h)
  · have hk : id - 10 < PR.length := by
      norm_num only [PR, List.length_cons, List.length_nil] at ⊢
      omega
    exact TreeCoverage.cov_of_span_empty (Q := 9) (PR := PR)
      (P := Pg cN 9 BS TS) hk (of_decide_eq_true h)
  · exact EncodedLiteral.checkPacked_sound h

#print axioms check_sound
end StructuralW10Cert20261016.LeafDispatch
end
