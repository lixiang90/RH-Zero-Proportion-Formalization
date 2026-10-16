/- SPDX-License-Identifier: Apache-2.0
Generated fixed-field geometry. Equality theorems retain the inherited semantics. -/
import StructuralW10Unconditional20261016.FastGeometry
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
namespace StructuralW10Unconditional20261016.FixedGeometry
structure Cell where
  L0 : ℕ
  L1 : ℕ
  L2 : ℕ
  L3 : ℕ
  L4 : ℕ
  L5 : ℕ
  L6 : ℕ
  L7 : ℕ
  L8 : ℕ
  U0 : ℕ
  U1 : ℕ
  U2 : ℕ
  U3 : ℕ
  U4 : ℕ
  U5 : ℕ
  U6 : ℕ
  U7 : ℕ
  U8 : ℕ
  A0 : ℕ
  A1 : ℕ
  A2 : ℕ
  A3 : ℕ
  A4 : ℕ
  A5 : ℕ
  A6 : ℕ
  A7 : ℕ
  A8 : ℕ
  A9 : ℕ
  A10 : ℕ
  A11 : ℕ
  A12 : ℕ
  A13 : ℕ
  A14 : ℕ
  A15 : ℕ
  A16 : ℕ
  A17 : ℕ
  A18 : ℕ
  A19 : ℕ
  A20 : ℕ
  A21 : ℕ
  A22 : ℕ
  A23 : ℕ
  A24 : ℕ
  A25 : ℕ
  A26 : ℕ
  A27 : ℕ
  A28 : ℕ
  A29 : ℕ
  A30 : ℕ
  A31 : ℕ
  A32 : ℕ
  A33 : ℕ
  A34 : ℕ
  A35 : ℕ
  B0 : ℕ
  B1 : ℕ
  B2 : ℕ
  B3 : ℕ
  B4 : ℕ
  B5 : ℕ
  B6 : ℕ
  B7 : ℕ
  B8 : ℕ
  B9 : ℕ
  B10 : ℕ
  B11 : ℕ
  B12 : ℕ
  B13 : ℕ
  B14 : ℕ
  B15 : ℕ
  B16 : ℕ
  B17 : ℕ
  B18 : ℕ
  B19 : ℕ
  B20 : ℕ
  B21 : ℕ
  B22 : ℕ
  B23 : ℕ
  B24 : ℕ
  B25 : ℕ
  B26 : ℕ
  B27 : ℕ
  B28 : ℕ
  B29 : ℕ
  B30 : ℕ
  B31 : ℕ
  B32 : ℕ
  B33 : ℕ
  B34 : ℕ
  B35 : ℕ
structure Vec where
  v0 : ℕ
  v1 : ℕ
  v2 : ℕ
  v3 : ℕ
  v4 : ℕ
  v5 : ℕ
  v6 : ℕ
  v7 : ℕ
  v8 : ℕ
  v9 : ℕ
def Cell.toCl (c : Cell) : Cl := ⟨[c.L0, c.L1, c.L2, c.L3, c.L4, c.L5, c.L6, c.L7, c.L8],
  [c.U0, c.U1, c.U2, c.U3, c.U4, c.U5, c.U6, c.U7, c.U8],
  [c.A0, c.A1, c.A2, c.A3, c.A4, c.A5, c.A6, c.A7, c.A8, c.A9, c.A10, c.A11, c.A12, c.A13, c.A14, c.A15, c.A16, c.A17, c.A18, c.A19, c.A20, c.A21, c.A22, c.A23, c.A24, c.A25, c.A26, c.A27, c.A28, c.A29, c.A30, c.A31, c.A32, c.A33, c.A34, c.A35],
  [c.B0, c.B1, c.B2, c.B3, c.B4, c.B5, c.B6, c.B7, c.B8, c.B9, c.B10, c.B11, c.B12, c.B13, c.B14, c.B15, c.B16, c.B17, c.B18, c.B19, c.B20, c.B21, c.B22, c.B23, c.B24, c.B25, c.B26, c.B27, c.B28, c.B29, c.B30, c.B31, c.B32, c.B33, c.B34, c.B35]⟩
def Cell.ofCl (c : Cl) : Cell := ⟨c.L.getD 0 0, c.L.getD 1 0, c.L.getD 2 0, c.L.getD 3 0, c.L.getD 4 0, c.L.getD 5 0, c.L.getD 6 0, c.L.getD 7 0, c.L.getD 8 0, c.U.getD 0 0, c.U.getD 1 0, c.U.getD 2 0, c.U.getD 3 0, c.U.getD 4 0, c.U.getD 5 0, c.U.getD 6 0, c.U.getD 7 0, c.U.getD 8 0, c.A.getD 0 0, c.A.getD 1 0, c.A.getD 2 0, c.A.getD 3 0, c.A.getD 4 0, c.A.getD 5 0, c.A.getD 6 0, c.A.getD 7 0, c.A.getD 8 0, c.A.getD 9 0, c.A.getD 10 0, c.A.getD 11 0, c.A.getD 12 0, c.A.getD 13 0, c.A.getD 14 0, c.A.getD 15 0, c.A.getD 16 0, c.A.getD 17 0, c.A.getD 18 0, c.A.getD 19 0, c.A.getD 20 0, c.A.getD 21 0, c.A.getD 22 0, c.A.getD 23 0, c.A.getD 24 0, c.A.getD 25 0, c.A.getD 26 0, c.A.getD 27 0, c.A.getD 28 0, c.A.getD 29 0, c.A.getD 30 0, c.A.getD 31 0, c.A.getD 32 0, c.A.getD 33 0, c.A.getD 34 0, c.A.getD 35 0, c.B.getD 0 0, c.B.getD 1 0, c.B.getD 2 0, c.B.getD 3 0, c.B.getD 4 0, c.B.getD 5 0, c.B.getD 6 0, c.B.getD 7 0, c.B.getD 8 0, c.B.getD 9 0, c.B.getD 10 0, c.B.getD 11 0, c.B.getD 12 0, c.B.getD 13 0, c.B.getD 14 0, c.B.getD 15 0, c.B.getD 16 0, c.B.getD 17 0, c.B.getD 18 0, c.B.getD 19 0, c.B.getD 20 0, c.B.getD 21 0, c.B.getD 22 0, c.B.getD 23 0, c.B.getD 24 0, c.B.getD 25 0, c.B.getD 26 0, c.B.getD 27 0, c.B.getD 28 0, c.B.getD 29 0, c.B.getD 30 0, c.B.getD 31 0, c.B.getD 32 0, c.B.getD 33 0, c.B.getD 34 0, c.B.getD 35 0⟩
def Vec.toList (v : Vec) : List ℕ := [v.v0, v.v1, v.v2, v.v3, v.v4, v.v5, v.v6, v.v7, v.v8, v.v9]
def forceCell {α : Sort _} (c : Cell) (k : Cell → α) : α :=
  forceT c.L0 fun L0 =>
  forceT c.L1 fun L1 =>
  forceT c.L2 fun L2 =>
  forceT c.L3 fun L3 =>
  forceT c.L4 fun L4 =>
  forceT c.L5 fun L5 =>
  forceT c.L6 fun L6 =>
  forceT c.L7 fun L7 =>
  forceT c.L8 fun L8 =>
  forceT c.U0 fun U0 =>
  forceT c.U1 fun U1 =>
  forceT c.U2 fun U2 =>
  forceT c.U3 fun U3 =>
  forceT c.U4 fun U4 =>
  forceT c.U5 fun U5 =>
  forceT c.U6 fun U6 =>
  forceT c.U7 fun U7 =>
  forceT c.U8 fun U8 =>
  forceT c.A0 fun A0 =>
  forceT c.A1 fun A1 =>
  forceT c.A2 fun A2 =>
  forceT c.A3 fun A3 =>
  forceT c.A4 fun A4 =>
  forceT c.A5 fun A5 =>
  forceT c.A6 fun A6 =>
  forceT c.A7 fun A7 =>
  forceT c.A8 fun A8 =>
  forceT c.A9 fun A9 =>
  forceT c.A10 fun A10 =>
  forceT c.A11 fun A11 =>
  forceT c.A12 fun A12 =>
  forceT c.A13 fun A13 =>
  forceT c.A14 fun A14 =>
  forceT c.A15 fun A15 =>
  forceT c.A16 fun A16 =>
  forceT c.A17 fun A17 =>
  forceT c.A18 fun A18 =>
  forceT c.A19 fun A19 =>
  forceT c.A20 fun A20 =>
  forceT c.A21 fun A21 =>
  forceT c.A22 fun A22 =>
  forceT c.A23 fun A23 =>
  forceT c.A24 fun A24 =>
  forceT c.A25 fun A25 =>
  forceT c.A26 fun A26 =>
  forceT c.A27 fun A27 =>
  forceT c.A28 fun A28 =>
  forceT c.A29 fun A29 =>
  forceT c.A30 fun A30 =>
  forceT c.A31 fun A31 =>
  forceT c.A32 fun A32 =>
  forceT c.A33 fun A33 =>
  forceT c.A34 fun A34 =>
  forceT c.A35 fun A35 =>
  forceT c.B0 fun B0 =>
  forceT c.B1 fun B1 =>
  forceT c.B2 fun B2 =>
  forceT c.B3 fun B3 =>
  forceT c.B4 fun B4 =>
  forceT c.B5 fun B5 =>
  forceT c.B6 fun B6 =>
  forceT c.B7 fun B7 =>
  forceT c.B8 fun B8 =>
  forceT c.B9 fun B9 =>
  forceT c.B10 fun B10 =>
  forceT c.B11 fun B11 =>
  forceT c.B12 fun B12 =>
  forceT c.B13 fun B13 =>
  forceT c.B14 fun B14 =>
  forceT c.B15 fun B15 =>
  forceT c.B16 fun B16 =>
  forceT c.B17 fun B17 =>
  forceT c.B18 fun B18 =>
  forceT c.B19 fun B19 =>
  forceT c.B20 fun B20 =>
  forceT c.B21 fun B21 =>
  forceT c.B22 fun B22 =>
  forceT c.B23 fun B23 =>
  forceT c.B24 fun B24 =>
  forceT c.B25 fun B25 =>
  forceT c.B26 fun B26 =>
  forceT c.B27 fun B27 =>
  forceT c.B28 fun B28 =>
  forceT c.B29 fun B29 =>
  forceT c.B30 fun B30 =>
  forceT c.B31 fun B31 =>
  forceT c.B32 fun B32 =>
  forceT c.B33 fun B33 =>
  forceT c.B34 fun B34 =>
  forceT c.B35 fun B35 =>
  k ⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, U0, U1, U2, U3, U4, U5, U6, U7, U8, A0, A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32, A33, A34, A35, B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, B27, B28, B29, B30, B31, B32, B33, B34, B35⟩
theorem forceCell_eq {α : Sort _} (c : Cell) (k : Cell → α) : forceCell c k = k c := by
  cases c
  simp only [forceCell, forceT_eq]
def forceVec {α : Sort _} (c : Vec) (k : Vec → α) : α :=
  forceT c.v0 fun v0 =>
  forceT c.v1 fun v1 =>
  forceT c.v2 fun v2 =>
  forceT c.v3 fun v3 =>
  forceT c.v4 fun v4 =>
  forceT c.v5 fun v5 =>
  forceT c.v6 fun v6 =>
  forceT c.v7 fun v7 =>
  forceT c.v8 fun v8 =>
  forceT c.v9 fun v9 =>
  k ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9⟩
theorem forceVec_eq {α : Sort _} (c : Vec) (k : Vec → α) : forceVec c k = k c := by
  cases c
  simp only [forceVec, forceT_eq]
def update (c : Cell) (X Y : Vec) : Cell := ⟨nmax c.L0 (Nat.sub TB (Nat.add X.v1 Y.v0)),
  nmax c.L1 (Nat.sub TB (Nat.add X.v2 Y.v1)),
  nmax c.L2 (Nat.sub TB (Nat.add X.v3 Y.v2)),
  nmax c.L3 (Nat.sub TB (Nat.add X.v4 Y.v3)),
  nmax c.L4 (Nat.sub TB (Nat.add X.v5 Y.v4)),
  nmax c.L5 (Nat.sub TB (Nat.add X.v6 Y.v5)),
  nmax c.L6 (Nat.sub TB (Nat.add X.v7 Y.v6)),
  nmax c.L7 (Nat.sub TB (Nat.add X.v8 Y.v7)),
  nmax c.L8 (Nat.sub TB (Nat.add X.v9 Y.v8)),
  nmin c.U0 (Nat.sub (Nat.add X.v0 Y.v1) TB),
  nmin c.U1 (Nat.sub (Nat.add X.v1 Y.v2) TB),
  nmin c.U2 (Nat.sub (Nat.add X.v2 Y.v3) TB),
  nmin c.U3 (Nat.sub (Nat.add X.v3 Y.v4) TB),
  nmin c.U4 (Nat.sub (Nat.add X.v4 Y.v5) TB),
  nmin c.U5 (Nat.sub (Nat.add X.v5 Y.v6) TB),
  nmin c.U6 (Nat.sub (Nat.add X.v6 Y.v7) TB),
  nmin c.U7 (Nat.sub (Nat.add X.v7 Y.v8) TB),
  nmin c.U8 (Nat.sub (Nat.add X.v8 Y.v9) TB),
  nmax c.A0 (Nat.sub TB (Nat.add X.v2 Y.v0)),
  nmax c.A1 (Nat.sub TB (Nat.add X.v3 Y.v0)),
  nmax c.A2 (Nat.sub TB (Nat.add X.v4 Y.v0)),
  nmax c.A3 (Nat.sub TB (Nat.add X.v5 Y.v0)),
  nmax c.A4 (Nat.sub TB (Nat.add X.v6 Y.v0)),
  nmax c.A5 (Nat.sub TB (Nat.add X.v7 Y.v0)),
  nmax c.A6 (Nat.sub TB (Nat.add X.v8 Y.v0)),
  nmax c.A7 (Nat.sub TB (Nat.add X.v9 Y.v0)),
  nmax c.A8 (Nat.sub TB (Nat.add X.v3 Y.v1)),
  nmax c.A9 (Nat.sub TB (Nat.add X.v4 Y.v1)),
  nmax c.A10 (Nat.sub TB (Nat.add X.v5 Y.v1)),
  nmax c.A11 (Nat.sub TB (Nat.add X.v6 Y.v1)),
  nmax c.A12 (Nat.sub TB (Nat.add X.v7 Y.v1)),
  nmax c.A13 (Nat.sub TB (Nat.add X.v8 Y.v1)),
  nmax c.A14 (Nat.sub TB (Nat.add X.v9 Y.v1)),
  nmax c.A15 (Nat.sub TB (Nat.add X.v4 Y.v2)),
  nmax c.A16 (Nat.sub TB (Nat.add X.v5 Y.v2)),
  nmax c.A17 (Nat.sub TB (Nat.add X.v6 Y.v2)),
  nmax c.A18 (Nat.sub TB (Nat.add X.v7 Y.v2)),
  nmax c.A19 (Nat.sub TB (Nat.add X.v8 Y.v2)),
  nmax c.A20 (Nat.sub TB (Nat.add X.v9 Y.v2)),
  nmax c.A21 (Nat.sub TB (Nat.add X.v5 Y.v3)),
  nmax c.A22 (Nat.sub TB (Nat.add X.v6 Y.v3)),
  nmax c.A23 (Nat.sub TB (Nat.add X.v7 Y.v3)),
  nmax c.A24 (Nat.sub TB (Nat.add X.v8 Y.v3)),
  nmax c.A25 (Nat.sub TB (Nat.add X.v9 Y.v3)),
  nmax c.A26 (Nat.sub TB (Nat.add X.v6 Y.v4)),
  nmax c.A27 (Nat.sub TB (Nat.add X.v7 Y.v4)),
  nmax c.A28 (Nat.sub TB (Nat.add X.v8 Y.v4)),
  nmax c.A29 (Nat.sub TB (Nat.add X.v9 Y.v4)),
  nmax c.A30 (Nat.sub TB (Nat.add X.v7 Y.v5)),
  nmax c.A31 (Nat.sub TB (Nat.add X.v8 Y.v5)),
  nmax c.A32 (Nat.sub TB (Nat.add X.v9 Y.v5)),
  nmax c.A33 (Nat.sub TB (Nat.add X.v8 Y.v6)),
  nmax c.A34 (Nat.sub TB (Nat.add X.v9 Y.v6)),
  nmax c.A35 (Nat.sub TB (Nat.add X.v9 Y.v7)),
  nmin c.B0 (Nat.sub (Nat.add X.v0 Y.v2) TB),
  nmin c.B1 (Nat.sub (Nat.add X.v0 Y.v3) TB),
  nmin c.B2 (Nat.sub (Nat.add X.v0 Y.v4) TB),
  nmin c.B3 (Nat.sub (Nat.add X.v0 Y.v5) TB),
  nmin c.B4 (Nat.sub (Nat.add X.v0 Y.v6) TB),
  nmin c.B5 (Nat.sub (Nat.add X.v0 Y.v7) TB),
  nmin c.B6 (Nat.sub (Nat.add X.v0 Y.v8) TB),
  nmin c.B7 (Nat.sub (Nat.add X.v0 Y.v9) TB),
  nmin c.B8 (Nat.sub (Nat.add X.v1 Y.v3) TB),
  nmin c.B9 (Nat.sub (Nat.add X.v1 Y.v4) TB),
  nmin c.B10 (Nat.sub (Nat.add X.v1 Y.v5) TB),
  nmin c.B11 (Nat.sub (Nat.add X.v1 Y.v6) TB),
  nmin c.B12 (Nat.sub (Nat.add X.v1 Y.v7) TB),
  nmin c.B13 (Nat.sub (Nat.add X.v1 Y.v8) TB),
  nmin c.B14 (Nat.sub (Nat.add X.v1 Y.v9) TB),
  nmin c.B15 (Nat.sub (Nat.add X.v2 Y.v4) TB),
  nmin c.B16 (Nat.sub (Nat.add X.v2 Y.v5) TB),
  nmin c.B17 (Nat.sub (Nat.add X.v2 Y.v6) TB),
  nmin c.B18 (Nat.sub (Nat.add X.v2 Y.v7) TB),
  nmin c.B19 (Nat.sub (Nat.add X.v2 Y.v8) TB),
  nmin c.B20 (Nat.sub (Nat.add X.v2 Y.v9) TB),
  nmin c.B21 (Nat.sub (Nat.add X.v3 Y.v5) TB),
  nmin c.B22 (Nat.sub (Nat.add X.v3 Y.v6) TB),
  nmin c.B23 (Nat.sub (Nat.add X.v3 Y.v7) TB),
  nmin c.B24 (Nat.sub (Nat.add X.v3 Y.v8) TB),
  nmin c.B25 (Nat.sub (Nat.add X.v3 Y.v9) TB),
  nmin c.B26 (Nat.sub (Nat.add X.v4 Y.v6) TB),
  nmin c.B27 (Nat.sub (Nat.add X.v4 Y.v7) TB),
  nmin c.B28 (Nat.sub (Nat.add X.v4 Y.v8) TB),
  nmin c.B29 (Nat.sub (Nat.add X.v4 Y.v9) TB),
  nmin c.B30 (Nat.sub (Nat.add X.v5 Y.v7) TB),
  nmin c.B31 (Nat.sub (Nat.add X.v5 Y.v8) TB),
  nmin c.B32 (Nat.sub (Nat.add X.v5 Y.v9) TB),
  nmin c.B33 (Nat.sub (Nat.add X.v6 Y.v8) TB),
  nmin c.B34 (Nat.sub (Nat.add X.v6 Y.v9) TB),
  nmin c.B35 (Nat.sub (Nat.add X.v7 Y.v9) TB)⟩
theorem update_eq (c : Cell) (X Y : Vec) :
    (update c X Y).toCl = cuB 9 PR c.toCl X.toList Y.toList := by
  simp [update, Cell.toCl, Vec.toList, cuB, PR, pI, pJ, List.range_succ, List.range_zero]
def column (SL : List ℕ) (c : Cell) (s : ℕ) : Vec := ⟨dE 9 SL c.toCl BB 0 s, dE 9 SL c.toCl BB 1 s, dE 9 SL c.toCl BB 2 s, dE 9 SL c.toCl BB 3 s, dE 9 SL c.toCl BB 4 s, dE 9 SL c.toCl BB 5 s, dE 9 SL c.toCl BB 6 s, dE 9 SL c.toCl BB 7 s, dE 9 SL c.toCl BB 8 s, dE 9 SL c.toCl BB 9 s⟩
def row (SL : List ℕ) (c : Cell) (E t : ℕ) : Vec := ⟨dE 9 SL c.toCl E t 0, dE 9 SL c.toCl E t 1, dE 9 SL c.toCl E t 2, dE 9 SL c.toCl E t 3, dE 9 SL c.toCl E t 4, dE 9 SL c.toCl E t 5, dE 9 SL c.toCl E t 6, dE 9 SL c.toCl E t 7, dE 9 SL c.toCl E t 8, dE 9 SL c.toCl E t 9⟩
theorem column_eq (SL : List ℕ) (c : Cell) (s : ℕ) : (column SL c s).toList = colB 9 SL c.toCl s := by rfl
theorem row_eq (SL : List ℕ) (c : Cell) (E t : ℕ) : (row SL c E t).toList = rowB 9 SL c.toCl E t := by rfl
def child (c : Cell) (X Y : Vec) : Cell := forceVec X fun X => forceVec Y fun Y => update c X Y
theorem child_eq (c : Cell) (X Y : Vec) : (child c X Y).toCl = cuB 9 PR c.toCl X.toList Y.toList := by
  simp only [child, forceVec_eq, update_eq]
def left (SL : List ℕ) (c : Cell) (i j q : ℕ) : Cell := child c (column SL c i) (row SL c (Nat.add BB q) j)
def right (SL : List ℕ) (c : Cell) (i j q : ℕ) : Cell := child c (column SL c j) (row SL c (Nat.sub BB q) i)
theorem left_eq (SL : List ℕ) (c : Cell) (i j q : ℕ) : (left SL c i j q).toCl = leftChild 9 PR SL c.toCl i j q := by
  simp only [left, child_eq, column_eq, row_eq, leftChild]
theorem right_eq (SL : List ℕ) (c : Cell) (i j q : ℕ) : (right SL c i j q).toCl = rightChild 9 PR SL c.toCl i j q := by
  simp only [right, child_eq, column_eq, row_eq, rightChild]
def step (SL : List ℕ) (c : Cell) : Cell := forceCell (left SL c 0 1 c.U8) fun c => forceCell (right SL c 8 9 c.L0) id
theorem step_eq (SL : List ℕ) (c : Cell) : (step SL c).toCl = StructuralW10Cert20261016.OrderCoverage.step SL c.toCl := by
  simp only [step, forceCell_eq, id_eq]
  rw [right_eq]
  change rightChild 9 PR SL (left SL c 0 1 c.U8).toCl 8 9 ((left SL c 0 1 c.U8).toCl.L.getD 0 0) = _
  rw [left_eq]
  rfl
def rounds (SL : List ℕ) : ℕ → Cell → Cell
  | 0, c => c
  | n+1, c => forceCell (step SL c) (rounds SL n)
theorem rounds_eq (SL : List ℕ) (n : ℕ) (c : Cell) : (rounds SL n c).toCl = StructuralW10Cert20261016.OrderCoverage.normalize SL n c.toCl := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [rounds, forceCell_eq, ih, step_eq, StructuralW10Cert20261016.OrderCoverage.normalize]
def normalize (SL : List ℕ) (c : Cell) : Cell := if c.U0 ≤ c.U8 ∧ c.L0 ≤ c.L8 then c else rounds SL 2 c
theorem normalize_eq (SL : List ℕ) (c : Cell) : (normalize SL c).toCl = StructuralW10Cert20261016.AdaptiveCoverage.normalize SL c.toCl := by
  unfold normalize StructuralW10Cert20261016.AdaptiveCoverage.normalize
  change (if c.U0 ≤ c.U8 ∧ c.L0 ≤ c.L8 then c else rounds SL 2 c).toCl = if c.U0 ≤ c.U8 ∧ c.L0 ≤ c.L8 then c.toCl else _
  split_ifs <;> simp only [rounds_eq, StructuralW10Cert20261016.ForcedCoverage.normalize_eq]
def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) : ℕ → ℕ → Cell → ℕ
  | 0, _, _ => 0
  | fuel+1, pos, c => forceCell c fun c => forceCell (normalize SL c) fun c => forceT (read pos) fun w =>
    if w % 2 = 1 then
      let ax := (w / 2) % 64
      let i := sI 9 PR ax
      let j := sJ 9 PR ax
      let q := w / 128
      if i < j ∧ j ≤ 9 then
        let next := walk SL read leafCheck fuel (pos+1) (left SL c i j q)
        forceT next fun next => if next = 0 then 0 else walk SL read leafCheck fuel next (right SL c i j q)
      else 0
    else StructuralW10Cert20261016.ForcedCoverage.forceCell c.toCl fun lc =>
      if leafCheck lc (w / 2) then pos+1 else 0
theorem walk_sound {SL : List ℕ} (hSL : SLok 9 PR SL) (n : ℕ)
    (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool)
    (hleaf : ∀ c id, leafCheck c id = true → CovBy 9 PR (Pg n 9 BS TS) c) :
    ∀ fuel pos c, walk SL read leafCheck fuel pos c ≠ 0 → CovBy 9 PR (Pg n 9 BS TS) c.toCl := by
  intro fuel
  induction fuel with
  | zero => intro pos c h; exact False.elim (h rfl)
  | succ fuel ih =>
    intro pos c h g hg
    by_cases ho : g 0 ≤ g 8
    · have hn : InCell 9 PR (normalize SL c).toCl g := by
        rw [normalize_eq]
        exact StructuralW10Cert20261016.AdaptiveCoverage.normalize_in hSL hg ho
      simp only [walk, forceCell_eq, forceT_eq, StructuralW10Cert20261016.ForcedCoverage.forceCell_eq] at h
      split_ifs at h with hsplit hvalid hnext hcheck
      · exact False.elim (h rfl)
      · have hl := ih (pos+1) _ hnext
        have hr := ih _ _ h
        rw [left_eq] at hl
        rw [right_eq] at hr
        exact cov_splitB hSL hPR hvalid.1 hvalid.2 (read pos / 128) hl hr g hn
      · exact False.elim (h rfl)
      · exact hleaf _ (read pos / 2) hcheck g hn
      · exact False.elim (h rfl)
    · exact Or.inr (lt_of_not_ge ho)
#print axioms update_eq
#print axioms walk_sound
end StructuralW10Unconditional20261016.FixedGeometry
end
