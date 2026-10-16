/- SPDX-License-Identifier: Apache-2.0
An encoded source literal expands to an ordinary natural-number literal.
The kernel checks the full numeric certificate after expansion; no theorem
about a string primitive, macro implementation, or external computation is used.
-/
import StructuralW10Cert20261016.RelCompactLeaf
import StructuralW10Cert20261016.NumeralCodec

open AMW.Cert.PCell
namespace StructuralW10Cert20261016.EncodedLiteral
open LocalChecker

noncomputable def checkPacked (c : Cl) (word : ℕ) : Bool :=
  RelCompactLeaf.checkTreeCode c (word / 100000000) (word % 100000000)

theorem checkPacked_sound {c : Cl} {word : ℕ}
    (h : checkPacked c word = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := RelCompactLeaf.checkTreeCode_sound h

#print axioms checkPacked_sound
end StructuralW10Cert20261016.EncodedLiteral
