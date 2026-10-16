/- SPDX-License-Identifier: Apache-2.0
Cell-relative support input for the same proved W10 checker.
A 39-bit presence mask and short nonzero-kind codes replace fixed kind tags.
The point grid has exactly the bit width of the current certified span.
-/
import StructuralW10Cert20261016.CompactLeaf
noncomputable section

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
namespace StructuralW10Cert20261016.RelCompactLeaf
open LocalChecker

/-- A singleton grid consumes zero payload bits. -/
def pointBits (c : Cl) (t : ℕ) : ℕ :=
  let n := eU TS c t / 32 - (eL TS c t + 31) / 32
  if n = 0 then 0 else n.log2 + 1

def readPoint (c : Cl) (t w : ℕ) : ℕ × ℕ :=
  let bits := pointBits c t
  let base := (eL TS c t + 31) / 32
  ((base + w % (2 ^ bits)) * 32, w / (2 ^ bits))

/-- Two common neighboring table points have a two-bit representation. -/
def readSecondPoint (c : Cl) (t p w : ℕ) : ℕ × ℕ :=
  let tag := w % 4
  let tail := w / 4
  if tag = 0 then (p - 32, tail)
  else if tag = 1 then (p + 32, tail)
  else if tag = 2 then (p - 256, tail)
  else readPoint c t tail

/-- Nonzero kind: bit 0 is a single tangent; bits 10 and 11 select the two
mixture kinds. The remaining payload is the inherited ten-bit mixture mass. -/
def readNonzero (c : Cl) (t w : ℕ) : Term × ℕ :=
  if w % 2 = 0 then
    let p := readPoint c t (w / 2)
    ((1, 0, p.1, 0), p.2)
  else
    let kind := if (w / 2) % 2 = 0 then 2 else 3
    let x := w / 4
    let p := readPoint c t (x / 1024)
    if kind = 2 then ((2, x % 1024, p.1, 0), p.2)
    else
      let r := readSecondPoint c t p.1 p.2
      ((3, x % 1024, p.1, r.1), r.2)

def decodeAux (c : Cl) : ℕ → ℕ → ℕ → ℕ → List Term
  | 0, _, _, _ => []
  | n + 1, t, mask, w =>
    if mask % 2 = 0 then (0, 0, 0, 0) :: decodeAux c n (t+1) (mask/2) w
    else
      let term := readNonzero c t w
      term.1 :: decodeAux c n (t+1) (mask/2) term.2

def decodeTerms (c : Cl) (support : ℕ) : List Term :=
  decodeAux c 39 0 (support % (2 ^ 39)) (support / (2 ^ 39))

def checkTreeCode (c : Cl) (support treecode : ℕ) : Bool :=
  let FS := decodeTerms c support
  checkLeaf c FS (CompactLeaf.treeMoves FS treecode)

theorem checkTreeCode_sound {c : Cl} {support treecode : ℕ}
    (h : checkTreeCode c support treecode = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkLeaf_sound h

/-- Text stores support*10^8 + the eight-digit labelled-tree code. -/
def checkText (c : Cl) (text : String) : Bool :=
  let word := CompactLeaf.decodeText text
  checkTreeCode c (word / 100000000) (word % 100000000)

theorem checkText_sound {c : Cl} {text : String}
    (h : checkText c text = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkTreeCode_sound h

#print axioms checkTreeCode_sound
#print axioms checkText_sound
end StructuralW10Cert20261016.RelCompactLeaf

end
