/- SPDX-License-Identifier: Apache-2.0
Materialize every intermediate nine-coordinate dual state. The previous
eager wrapper materialized only the final state of the entire move list.
-/
import StructuralW10Unconditional20261016.GenericFloor
import StructuralW10Cert20261016.EagerLeaf

set_option Elab.async false
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016
open LocalChecker
namespace StructuralW10Unconditional20261016.StreamingDual

def run (c : Cl) : List DualMove → DualState → DualState
  | [], s => s
  | m :: ms, s => EagerLeaf.forceDual (dualStep c s m) (run c ms)

theorem run_eq (c : Cl) (ms : List DualMove) (s : DualState) :
    run c ms s = runDual c ms s := by
  induction ms generalizing s with
  | nil => rfl
  | cons m ms ih => simp only [run, EagerLeaf.forceDual_eq, ih, runDual]

def checkLeaf (n : ℕ) (c : Cl) (FS : List Term) (moves : List DualMove) : Bool :=
  let s := run c moves initialDual
  mcheckGX (mokI PC9QB6MData.PT) PC9QB6MData.TOP PC9QB6MData.BK
    (tf PC9QB6MData.PT) 9 BS TS n c FS s.P s.S s.Cp s.Cm

theorem checkLeaf_eq (n : ℕ) (c : Cl) (FS : List Term) (moves : List DualMove) :
    checkLeaf n c FS moves = GenericFloor.checkLeaf n c FS moves := by
  simp only [checkLeaf, run_eq, GenericFloor.checkLeaf]

def checkPacked (n : ℕ) (c : Cl) (word : ℕ) : Bool :=
  forceT word fun word =>
  FastPruefer.forceTerms (RelCompactLeaf.decodeTerms c (word / 100000000)) fun FS =>
    EagerLeaf.forceMoves (FastPruefer.moves FS (word % 100000000)) fun moves =>
      checkLeaf n c FS moves

theorem checkPacked_sound {n : ℕ} {c : Cl} {word : ℕ}
    (h : checkPacked n c word = true) : CovBy 9 PR (Pg n 9 BS TS) c := by
  simp only [checkPacked, forceT_eq, FastPruefer.forceTerms_eq,
    EagerLeaf.forceMoves_eq, checkLeaf_eq] at h
  exact GenericFloor.checkLeaf_sound h

def dispatch (n : ℕ) (payload : ℕ → ℕ) (c : Cl) (id : ℕ) : Bool :=
  if id ≤ 45 then GenericFloor.dispatch n payload c id
  else checkPacked n c (payload (id-46))

theorem dispatch_sound (n : ℕ) (payload : ℕ → ℕ) (c : Cl) (id : ℕ)
    (h : dispatch n payload c id = true) : CovBy 9 PR (Pg n 9 BS TS) c := by
  unfold dispatch at h
  split_ifs at h
  · exact GenericFloor.dispatch_sound n payload c id h
  · exact checkPacked_sound h

#print axioms dispatch_sound
end StructuralW10Unconditional20261016.StreamingDual
end
