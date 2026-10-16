/- SPDX-License-Identifier: Apache-2.0
Printable base92 source literals expand to ordinary natural-number literals.
The macro supplies data only; subsequent proofs remain kernel checked. -/
import Lean

syntax (name := w10EncodedLiteral) "w10%" str : term
macro_rules
  | `(w10% $text:str) => do
    let digit (ch : Char) : Nat :=
      ch.toNat - 33 - (if 34 < ch.toNat then 1 else 0) -
        (if 92 < ch.toNat then 1 else 0)
    let n := text.getString.foldl (fun acc ch => acc * 92 + digit ch) 0
    pure (Lean.Syntax.mkNumLit (toString n))


/-- Short spelling for dense certificate tables. -/
syntax:max "~" str : term
macro_rules
  | `(~ $text:str) => `(w10% $text)
