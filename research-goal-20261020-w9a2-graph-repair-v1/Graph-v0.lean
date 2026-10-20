/-
SPDX-License-Identifier: Apache-2.0
Prepared finite geometry and potential consumer for frozen W9A2.
This file has not yet been compiled. Only ordinary kernel-reduced decidable
integer statements are used for the literal certificate. No native_decide.
-/
import StructuralW9A220261020.Core

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

noncomputable section
open Finset
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PCell AMW.Cert.PC9QB6M

namespace StructuralW9A220261020.Graph

abbrev State := Fin 49
def good : State := ⟨48, by decide⟩
def natGaps (g : Fin 8 → ℝ) : ℕ → ℝ :=
  fun r => [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7].getD r 0
def reverse8 (g : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun r => g ⟨7-r.val, by omega⟩
def leftGaps (g : Fin 9 → ℝ) : Fin 8 → ℝ :=
  fun r => g ⟨r.val, by omega⟩
def rightGaps (g : Fin 9 → ℝ) : Fin 8 → ℝ :=
  fun r => g ⟨r.val+1, by omega⟩

theorem natGaps_apply (g : Fin 8 → ℝ) {r : ℕ} (hr : r < 8) :
    natGaps g r = g ⟨r, hr⟩ := by
  interval_cases r <;> rfl

def cost (v : State) : ℤ :=
  if v.val < 48 then (qCost (v.val/2) : ℤ) else (qGoodIncrement : ℤ)
def StateAt (g : Fin 8 → ℝ) (v : State) : Prop :=
  if v.val < 48 then InCell 8 PR (qCell (v.val/2))
    (natGaps (if v.val%2 = 1 then reverse8 g else g)) else True

-- Frozen literal packet: first published direct exclusion in each old row.
def badEdges : List (ℕ × ℕ) := [(1, 10), (3, 10), (4, 5), (5, 8), (5, 30), (9, 4), (10, 14), (10, 15), (10, 39), (10, 43), (11, 0), (11, 2), (11, 19), (11, 25), (12, 21), (12, 23), (12, 36), (12, 46), (14, 11), (15, 11), (18, 10), (19, 18), (20, 13), (22, 13), (24, 10), (27, 44), (29, 44), (31, 4), (34, 44), (37, 13), (38, 11), (40, 41), (42, 11), (45, 26), (45, 28), (45, 35), (47, 13)]
def sharedSpans : List (ℕ × ℕ) := [(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 4), (3, 5), (3, 6), (3, 7), (3, 8), (4, 5), (4, 6), (4, 7), (4, 8), (5, 6), (5, 7), (5, 8), (6, 7), (6, 8), (7, 8)]
def witnessRows : List (List ℕ) := [
  [0, 0, 0, 0, 2, 0, 8, 5, 4, 0, 2, 2, 2, 2, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 4, 0, 10, 0, 2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 56, 7, 10, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 10, 3, 10, 3, 0, 3, 0, 10, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 2, 0, 8, 5, 4, 0, 2, 2, 2, 2, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 4, 0, 10, 0, 2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 56, 7, 10, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 10, 3, 10, 3, 0, 3, 0, 10, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [7, 0, 7, 4, 1, 56, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 4, 7, 1, 7, 4, 4, 4, 4, 4, 7, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4, 1, 4, 2, 2, 4, 4, 4, 10, 4, 4],
  [0, 0, 0, 0, 2, 0, 5, 5, 56, 0, 2, 2, 2, 2, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 8, 2, 8, 2, 56, 0, 5, 0, 2, 8, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 7, 3, 3, 0, 7, 7, 7, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 7, 3, 7, 3, 0, 3, 0, 7, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 2, 0, 17, 5, 9, 0, 2, 2, 2, 2, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 12, 2, 42, 2, 9, 0, 5, 0, 2, 12, 0, 0, 5, 0, 2, 2, 0, 0, 17, 6, 0, 0],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 56, 0, 3, 3, 3, 0, 6, 9, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [5, 0, 5, 8, 1, 5, 1, 1, 1, 10, 1, 1, 1, 1, 56, 56, 8, 5, 1, 5, 6, 8, 6, 8, 8, 5, 1, 1, 1, 1, 1, 10, 1, 6, 1, 1, 8, 4, 1, 56, 2, 2, 54, 56, 8, 5, 8, 4],
  [56, 0, 56, 4, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 4, 4, 4, 0, 1, 56, 4, 4, 4, 4, 4, 56, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 4, 0, 1, 4, 2, 2, 4, 4, 4, 6, 4, 0],
  [5, 11, 5, 11, 1, 5, 1, 1, 1, 9, 1, 1, 1, 1, 9, 9, 11, 5, 1, 5, 6, 56, 6, 56, 11, 5, 1, 1, 1, 1, 1, 9, 1, 6, 1, 1, 56, 6, 1, 9, 2, 2, 9, 9, 8, 5, 56, 6],
  [3, 3, 3, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 16, 7, 3, 3, 3, 3, 3, 3],
  [0, 0, 0, 0, 8, 0, 3, 3, 3, 0, 6, 56, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 8, 0, 3, 3, 3, 0, 6, 56, 6, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 10, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 10, 3, 10, 3, 0, 3, 0, 10, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 2, 0, 8, 5, 4, 0, 2, 2, 2, 2, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 4, 0, 10, 0, 2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 56, 7, 10, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 10, 3, 10, 3, 0, 3, 0, 10, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 2, 0, 8, 5, 4, 0, 2, 2, 2, 2, 0, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 4, 0, 10, 0, 2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 5, 56, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 5, 3, 5, 3, 0, 3, 0, 5, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 7, 3, 9, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 9, 3, 9, 3, 0, 3, 0, 9, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 5, 56, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 5, 3, 5, 3, 0, 3, 0, 5, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 9, 7, 9, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 9, 3, 9, 3, 0, 3, 0, 9, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 56, 5, 10, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 10, 3, 10, 3, 0, 3, 0, 10, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 2, 0, 8, 5, 4, 0, 2, 2, 2, 2, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0, 4, 2, 4, 2, 4, 0, 10, 0, 2, 4, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [5, 0, 5, 9, 1, 5, 1, 1, 1, 9, 1, 1, 1, 1, 9, 9, 9, 5, 1, 5, 6, 9, 6, 9, 9, 5, 1, 1, 1, 1, 1, 9, 1, 6, 1, 1, 9, 6, 1, 9, 2, 2, 9, 9, 56, 5, 9, 6],
  [0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [5, 9, 5, 9, 1, 5, 1, 1, 1, 9, 1, 1, 1, 1, 9, 9, 9, 5, 1, 5, 6, 9, 6, 9, 9, 5, 1, 1, 1, 1, 1, 9, 1, 6, 1, 1, 9, 6, 1, 9, 2, 2, 9, 9, 56, 5, 9, 6],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 3, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 56, 0, 3, 3, 3, 0, 6, 9, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 9, 7, 9, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 9, 3, 9, 3, 0, 3, 0, 9, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 5, 0, 3, 3, 3, 0, 5, 5, 5, 12, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 5, 3, 5, 3, 0, 3, 0, 5, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [5, 9, 5, 9, 1, 5, 1, 1, 1, 9, 1, 1, 1, 1, 9, 9, 9, 5, 1, 5, 6, 9, 6, 9, 9, 5, 1, 1, 1, 1, 1, 9, 1, 6, 1, 1, 9, 6, 1, 9, 2, 2, 9, 9, 56, 5, 9, 6],
  [0, 0, 0, 0, 3, 0, 3, 3, 3, 0, 3, 3, 3, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 0, 3, 0, 3, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 9, 7, 9, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 9, 3, 9, 3, 0, 3, 0, 9, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 5, 0, 3, 3, 3, 0, 5, 3, 5, 56, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 5, 3, 5, 3, 0, 3, 0, 5, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 8, 0, 3, 3, 3, 0, 6, 56, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 8, 0, 3, 3, 3, 0, 6, 12, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [13, 8, 3, 3, 1, 3, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 3, 3, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3, 6, 56, 3, 3, 8, 6, 3, 3],
  [13, 4, 6, 4, 1, 6, 8, 3, 1, 4, 1, 1, 1, 1, 4, 4, 4, 6, 1, 6, 4, 4, 4, 4, 4, 6, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 4, 1, 4, 4, 4, 4, 4, 4, 6, 4, 4],
  [0, 0, 0, 0, 8, 0, 3, 3, 3, 0, 6, 56, 6, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 3, 3, 3, 0, 1, 1, 6, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 6, 3, 6, 3, 0, 3, 0, 6, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 7, 7, 7, 4, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 7, 3, 7, 3, 0, 3, 0, 7, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 2, 0, 17, 5, 9, 0, 2, 2, 2, 2, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 56, 2, 56, 2, 9, 0, 5, 0, 2, 56, 0, 0, 5, 0, 2, 2, 0, 0, 0, 6, 0, 0],
  [0, 0, 0, 0, 7, 0, 3, 3, 3, 0, 7, 3, 9, 4, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 9, 3, 9, 3, 0, 3, 0, 9, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 5, 0, 3, 3, 3, 0, 5, 3, 5, 56, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 3, 5, 3, 5, 3, 0, 3, 0, 5, 3, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0]
]
def potentialValues : List ℤ := [622324546221, 2504722000690, 622324546221, 2504722000690, 1882402448569, 1260078591593, 2504722000690, 2504722000690, 637754734617, 2504722000690, 1882397454469, 1244643614792, 2504722000690, 2504722000690, 1260078385898, 1260078385898, 2504722000690, 2504722000690, 1252361000345, 622324546221, 2504722000690, 1882403171114, 2504722000690, 1882403171114, 2504722000690, 622324546221, 2504722000690, 2504722000690, 2504722000690, 2504722000690, 637754734617, 2504722000690, 2504722000690, 2504722000690, 2504722000690, 2504722000690, 1882403171114, 2504722000690, 2504722000690, 1260078385898, 2504722000690, 2504722000690, 2504722000690, 1260078385898, 2504722000690, 2504722000690, 1882403171114, 2504722000690, 0]
def originalCosts : List ℕ := [12638501, 12638501, 12739397, 12739397, 12776350, 12776350, 12893326, 12893326, 13637321, 13637321, 13734031, 13734031, 13781830, 13781830, 121390593524, 121390593524, 192129366775, 192129366775, 250484838570, 250484838570, 265453806080, 265453806080, 380598201950, 380598201950, 393062824419, 393062824419, 439727321655, 439727321655, 481742360239, 481742360239, 524597733122, 524597733122, 560453404818, 560453404818, 587098913641, 587098913641, 599413154315, 599413154315, 623361329333, 623361329333, 656866170127, 656866170127, 723180799754, 723180799754, 783349429541, 783349429541, 817785857206, 817785857206, 1000000000000]

def potential (v : State) : ℤ := potentialValues.getD v.val 0
def Edge (u v : State) : Prop :=
  u = good ∨ v = good ∨ (u.val,v.val) ∈ badEdges
instance (u v : State) : Decidable (Edge u v) := by
  unfold Edge; infer_instance

theorem all_to_good (u : State) : Edge u good := Or.inr (Or.inl rfl)
theorem all_from_good (u : State) : Edge good u := Or.inl rfl
theorem good_StateAt (g : Fin 8 → ℝ) : StateAt g good := by
  simp [StateAt, good]
theorem cost_nonneg (u : State) : 0 ≤ cost u := by
  unfold cost; split_ifs <;> positivity
theorem potential_nonneg : ∀ u : State, 0 ≤ potential u := by decide
theorem potential_le : ∀ u : State, potential u ≤ 2504722000690 := by decide
theorem potential_good : potential good = 0 := by rfl
theorem costs_match : ∀ u : State, cost u = (originalCosts.getD u.val 0 : ℤ) := by decide

theorem edge_potential : ∀ u v : State, Edge u v →
    (622387738726 : ℤ) + potential v - potential u ≤ 5 * cost u := by
  decide

-- Closed bounds. Equality or mere touching is never an exclusion.
def prIndex (i j : ℕ) : ℕ := i*(15-i)/2+(j-i-2)
def cellLower (c : Cl) (i j : ℕ) : ℕ :=
  if j = i+1 then c.L.getD i 0 else c.A.getD (prIndex i j) 0
def cellUpper (c : Cl) (i j : ℕ) : ℕ :=
  if j = i+1 then c.U.getD i 0 else c.B.getD (prIndex i j) 0
def lower (v : State) (i j : ℕ) : ℕ :=
  if v.val%2 = 1 then cellLower (qCell (v.val/2)) (8-j) (8-i)
  else cellLower (qCell (v.val/2)) i j
def upper (v : State) (i j : ℕ) : ℕ :=
  if v.val%2 = 1 then cellUpper (qCell (v.val/2)) (8-j) (8-i)
  else cellUpper (qCell (v.val/2)) i j

theorem prIndex_sound (i j : ℕ) (hi : i < 8) (hj : j ≤ 8) (hij : i+2 ≤ j) :
    prIndex i j < PR.length ∧ pI PR (prIndex i j) = i ∧ pJ PR (prIndex i j) = j := by
  have hcheck : ∀ a : Fin 8, ∀ b : Fin 9, a.val+2 ≤ b.val →
      prIndex a.val b.val < PR.length ∧ pI PR (prIndex a.val b.val) = a.val ∧
      pJ PR (prIndex a.val b.val) = b.val := by decide
  exact hcheck ⟨i,hi⟩ ⟨j,by omega⟩ hij

theorem cell_span_bounds {c : Cl} {g : ℕ → ℝ} (h : InCell 8 PR c g)
    {i j : ℕ} (hij : i < j) (hj : j ≤ 8) :
    (cellLower c i j : ℝ)/SC ≤ gsum g i j ∧
      gsum g i j ≤ (cellUpper c i j : ℝ)/SC := by
  by_cases ha : j = i+1
  · subst j
    simpa [cellLower, cellUpper, gsum_single] using h.1 i (by omega)
  · obtain ⟨hk,hi',hj'⟩ := prIndex_sound i j (by omega) hj (by omega)
    simpa [cellLower, cellUpper, ha, hi', hj'] using h.2 (prIndex i j) hk

theorem reverse_span (g : Fin 8 → ℝ) {i j : ℕ} (hij : i < j) (hj : j ≤ 8) :
    gsum (natGaps (reverse8 g)) i j = gsum (natGaps g) (8-j) (8-i) := by
  have hi : i ≤ 7 := by omega
  interval_cases i <;> interval_cases j <;> try omega
  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> ring

theorem located_span {g : Fin 8 → ℝ} {v : State}
    (hv : v.val < 48) (h : StateAt g v) {i j : ℕ} (hij : i < j) (hj : j ≤ 8) :
    (lower v i j : ℝ)/SC ≤ gsum (natGaps g) i j ∧
      gsum (natGaps g) i j ≤ (upper v i j : ℝ)/SC := by
  have hc : InCell 8 PR (qCell (v.val/2))
      (natGaps (if v.val%2 = 1 then reverse8 g else g)) := by
    simpa only [StateAt, if_pos hv] using h
  by_cases ho : v.val%2 = 1
  · simp only [if_pos ho] at hc
    have hb := cell_span_bounds hc (i := 8-j) (j := 8-i) (by omega) (by omega)
    have hi8 : 8-(8-i) = i := by omega
    have hj8 : 8-(8-j) = j := by omega
    have hr := reverse_span g (i := 8-j) (j := 8-i) (by omega) (by omega)
    simpa only [lower, upper, if_pos ho, hr, hi8, hj8] using hb
  · simp only [if_neg ho] at hc
    simpa only [lower, upper, if_neg ho] using cell_span_bounds hc hij hj

theorem shared_span (g : Fin 9 → ℝ) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ 8) :
    gsum (natGaps (leftGaps g)) i j =
      gsum (natGaps (rightGaps g)) (i-1) (j-1) := by
  have hi8 : i ≤ 7 := by omega
  interval_cases i <;> interval_cases j <;> try omega
  all_goals norm_num [gsum_range, natGaps, leftGaps, rightGaps, Finset.sum_range_succ]

def witness (u v : State) : ℕ := (witnessRows.getD u.val []).getD v.val 56
def witnessSpan (u v : State) : ℕ × ℕ := sharedSpans.getD (witness u v / 2) (0,0)
def Conflict (u v : State) : Prop :=
  let i := (witnessSpan u v).1
  let j := (witnessSpan u v).2
  if witness u v % 2 = 0 then upper u i j < lower v (i-1) (j-1)
  else upper v (i-1) (j-1) < lower u i j
instance (u v : State) : Decidable (Conflict u v) := by unfold Conflict; infer_instance

/-- The 2267 strict witnesses are extracted from the old packet, and are
checked against qCell including both independently chosen orientations. -/
theorem exclusion_checked : ∀ u v : State, ¬ Edge u v →
    u.val < 48 ∧ v.val < 48 ∧
    1 ≤ (witnessSpan u v).1 ∧ (witnessSpan u v).1 < (witnessSpan u v).2 ∧
    (witnessSpan u v).2 ≤ 8 ∧ Conflict u v := by
  decide

/-- A real nine-gap path gives an edge of the 49-state outer graph. The
seven gaps shared by the two windows are equal by construction. The G
state has no geometric restriction and every edge incident to it remains. -/
theorem edge_from_locations (g : Fin 9 → ℝ) (u v : State)
    (hu : StateAt (leftGaps g) u) (hv : StateAt (rightGaps g) v) : Edge u v := by
  by_contra he
  obtain ⟨hu48,hv48,hi,hij,hj,hc⟩ := exclusion_checked u v he
  let i := (witnessSpan u v).1
  let j := (witnessSpan u v).2
  have hl := located_span hu48 hu hij hj
  have hr := located_span hv48 hv (i := i-1) (j := j-1) (by omega) (by omega)
  have hs := shared_span g hi hij hj
  change (lower u i j : ℝ)/SC ≤ _ ∧ _ ≤ (upper u i j : ℝ)/SC at hl
  change (lower v (i-1) (j-1) : ℝ)/SC ≤ _ ∧ _ ≤ (upper v (i-1) (j-1) : ℝ)/SC at hr
  change gsum (natGaps (leftGaps g)) i j =
      gsum (natGaps (rightGaps g)) (i-1) (j-1) at hs
  unfold Conflict at hc
  change (if witness u v % 2 = 0 then upper u i j < lower v (i-1) (j-1)
    else upper v (i-1) (j-1) < lower u i j) at hc
  split_ifs at hc
  · have hstrict : (upper u i j : ℝ)/SC < (lower v (i-1) (j-1) : ℝ)/SC :=
      div_lt_div_of_pos_right (by exact_mod_cast hc) SC_pos
    linarith [hl.2, hr.1]
  · have hstrict : (upper v (i-1) (j-1) : ℝ)/SC < (lower u i j : ℝ)/SC :=
      div_lt_div_of_pos_right (by exact_mod_cast hc) SC_pos
    linarith [hl.1, hr.2]

end StructuralW9A220261020.Graph
