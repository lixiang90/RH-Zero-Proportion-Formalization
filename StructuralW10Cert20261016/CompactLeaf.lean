/-
SPDX-License-Identifier: Apache-2.0
Compact integer input format for the proved W10 local checker.
The decoder has no mathematical premises: whatever natural words are supplied,
a successful inherited check has the already proved local meaning.
-/
import StructuralW10Cert20261016.LocalChecker

noncomputable section

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
namespace StructuralW10Cert20261016.CompactLeaf
open LocalChecker

/-- A low zero bit stores a point divided by 32 in fourteen bits. A low one
bit stores an arbitrary point in nineteen bits. The second output is the tail. -/
def readPoint (w : ℕ) : ℕ × ℕ :=
  if w % 2 = 0 then ((w / 2 % 16384) * 32, w / 32768)
  else (w / 2 % 524288, w / 1048576)

/-- Ragged support word: kind 0 has no payload; kind 1 has one point;
kind 2 has ten mixture bits and a point; kind 3 has ten bits and two points. -/
def readTerm (w : ℕ) : Term × ℕ :=
  let k := w % 4
  let x := w / 4
  if k = 0 then ((0, 0, 0, 0), x)
  else if k = 1 then
    let p := readPoint x
    ((1, 0, p.1, 0), p.2)
  else if k = 2 then
    let p := readPoint (x / 1024)
    ((2, x % 1024, p.1, 0), p.2)
  else
    let p := readPoint (x / 1024)
    let r := readPoint p.2
    ((3, x % 1024, p.1, r.1), r.2)

def decodeTerms : ℕ → ℕ → List Term
  | 0, _ => []
  | n + 1, w =>
    let t := readTerm w
    t.1 :: decodeTerms n t.2

/-- Optional variable-length dual word. Six slot bits, one side bit,
seven length bits, then that many multiplier bits. -/
def readMove (w : ℕ) : DualMove × ℕ :=
  let k := w % 64
  let upper := (w / 64) % 2
  let bits := (w / 128) % 128
  let y := (w / 16384) % (2 ^ bits)
  let tail := w / (2 ^ (14 + bits))
  if upper = 1 then ((k, 0, y), tail) else ((k, y, 0), tail)

def decodeMoves : ℕ → ℕ → List DualMove
  | 0, _ => []
  | n + 1, w =>
    let m := readMove w
    m.1 :: decodeMoves n m.2

structure Leaf where
  support : ℕ
  moves : List DualMove
  deriving Inhabited

/-- The ordinary-list variant avoids committing to any multiplier quantization. -/
def check (c : Cl) (d : Leaf) : Bool :=
  checkLeaf c (decodeTerms 39 d.support) d.moves

/-- Both support and dual payloads may instead be supplied as natural words. -/
def checkWords (c : Cl) (support count moves : ℕ) : Bool :=
  checkLeaf c (decodeTerms 39 support) (decodeMoves count moves)

theorem check_sound {c : Cl} {d : Leaf} (h : check c d = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkLeaf_sound h

theorem checkWords_sound {c : Cl} {support count moves : ℕ}
    (h : checkWords c support count moves = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkLeaf_sound h

/-- The affine coefficient in gap coordinates, in the inherited integer scale. -/
def gapCoeff (FS : List Term) (r : ℕ) : ℤ :=
  1024000000000 * (BS.getD r 0 : ℤ) +
    (List.range 39).foldl (fun acc t =>
      if tI TS t ≤ r ∧ r < tJ TS t then
        let k := tI FS t
        let m := tJ FS t
        let p := tA FS t
        let q := tK FS t
        let sp : ℤ := (lo32 (hi32 (tf AMW.Cert.PC9QB6MData.PT p)) : ℤ) - 2000000000
        let sq : ℤ := (lo32 (hi32 (tf AMW.Cert.PC9QB6MData.PT q)) : ℤ) - 2000000000
        acc + (tA TS t : ℤ) * ((mw1 k m : ℤ) * sp + (mw2 k m : ℤ) * sq)
      else acc) 0

def vertexCoeff (FS : List Term) (v : ℕ) : ℤ :=
  if v = 0 then -gapCoeff FS 0
  else if v = 9 then gapCoeff FS 8
  else gapCoeff FS (v-1) - gapCoeff FS v

/-- Standard labelled-tree decoding, choosing the least available leaf. -/
def prueferEdges : List ℕ → List ℕ → List (ℕ × ℕ)
  | [], i :: j :: _ => [(i, j)]
  | [], _ => []
  | p :: ps, verts =>
    let leaf := (verts.find? (fun v => !(p :: ps).contains v)).getD 0
    (leaf, p) :: prueferEdges ps (verts.erase leaf)

def treeEdges (code : ℕ) : List (ℕ × ℕ) :=
  prueferEdges ((List.range 8).map (fun i => (code / (10 ^ i)) % 10))
    (List.range 10)

/-- One finite reachability sweep, using a ten-bit visited mask. -/
def reachStep (es : List (ℕ × ℕ)) (a b mask : ℕ) : ℕ :=
  es.foldl (fun seen edge =>
    let i := edge.1
    let j := edge.2
    if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then seen
    else
      let next := if seen.testBit i then seen ||| (2 ^ j) else seen
      if next.testBit j then next ||| (2 ^ i) else next) mask

def reachMask (es : List (ℕ × ℕ)) (a b : ℕ) : ℕ → ℕ
  | 0 => 2 ^ a
  | n+1 => reachStep es a b (reachMask es a b n)

/-- A cut sum determines the signed flow on each tree edge. The ordinary
leaf checker still verifies the resulting payment without trusting this rule. -/
def treeMoves (FS : List Term) (code : ℕ) : List DualMove :=
  let es := treeEdges code
  let coeffs := (List.range 9).map (gapCoeff FS)
  let div := (List.range 10).map (fun v =>
    if v = 0 then -(coeffs.getD 0 0)
    else if v = 9 then coeffs.getD 8 0
    else coeffs.getD (v-1) 0 - coeffs.getD v 0)
  es.filterMap (fun edge =>
    let i := min edge.1 edge.2
    let j := max edge.1 edge.2
    if i + 1 < j then
      let mask := reachMask es i j 9
      let signed := (List.range 10).foldl (fun acc v =>
        if mask.testBit v then acc + div.getD v 0 else acc) (0 : ℤ)
      let k := PR.idxOf (i, j)
      if 0 ≤ signed then some (k, 0, signed.toNat)
      else some (k, (-signed).toNat, 0)
    else none)

def checkTreeCode (c : Cl) (support treecode : ℕ) : Bool :=
  let FS := decodeTerms 39 support
  checkLeaf c FS (treeMoves FS treecode)

theorem checkTreeCode_sound {c : Cl} {support treecode : ℕ}
    (h : checkTreeCode c support treecode = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkLeaf_sound h

/-- The printable alphabet is ASCII 33 through 126, omitting quote and backslash.
Ninety-two digits use substantially fewer source bytes than hexadecimal. -/
def textDigit (ch : Char) : ℕ :=
  ch.toNat - 33 - (if 34 < ch.toNat then 1 else 0) -
    (if 92 < ch.toNat then 1 else 0)

def decodeText (text : String) : ℕ :=
  text.foldl (fun acc ch => acc * 92 + textDigit ch) 0

def checkText (c : Cl) (text : String) : Bool :=
  let word := decodeText text
  checkTreeCode c (word / 100000000) (word % 100000000)

theorem checkText_sound {c : Cl} {text : String}
    (h : checkText c text = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkTreeCode_sound h

#print axioms check_sound
#print axioms checkWords_sound
#print axioms checkTreeCode_sound
#print axioms checkText_sound
end StructuralW10Cert20261016.CompactLeaf

end
