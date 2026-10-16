/- SPDX-License-Identifier: Apache-2.0
Force reconstructed dual numerals once before the inherited integer check.
Every forcing wrapper is proved equal to the unchanged local checker.
-/
import StructuralW10Cert20261016.ForcedCoverage2

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.ForcedCoverage
namespace StructuralW10Cert20261016.EagerLeaf

def forceMoves {α : Sort _} : List DualMove → (List DualMove → α) → α
  | [], k => k []
  | (i, lo, hi) :: ms, k =>
    forceT i fun i => forceT lo fun lo => forceT hi fun hi =>
      forceMoves ms fun ms => k ((i, lo, hi) :: ms)

theorem forceMoves_eq {α : Sort _} (ms : List DualMove) (k : List DualMove → α) :
    forceMoves ms k = k ms := by
  induction ms generalizing k with
  | nil => rfl
  | cons m ms ih =>
    rcases m with ⟨i, lo, hi⟩
    simp only [forceMoves, forceT_eq, ih]

def forceDual {α : Sort _} (s : DualState) (k : DualState → α) : α :=
  forceNats s.P fun P => forceNats s.S fun S =>
    forceT s.Cp fun Cp => forceT s.Cm fun Cm => k ⟨P,S,Cp,Cm⟩

theorem forceDual_eq {α : Sort _} (s : DualState) (k : DualState → α) :
    forceDual s k = k s := by
  cases s
  simp only [forceDual, forceNats_eq, forceT_eq]

def checkLeaf (c : Cl) (FS : List Term) (moves : List DualMove) : Bool :=
  forceDual (runDual c moves initialDual) fun s =>
    mcheckGX (mokI AMW.Cert.PC9QB6MData.PT) AMW.Cert.PC9QB6MData.TOP
      AMW.Cert.PC9QB6MData.BK (tf AMW.Cert.PC9QB6MData.PT) 9 BS TS cN c FS s.P s.S s.Cp s.Cm

theorem checkLeaf_eq (c : Cl) (FS : List Term) (moves : List DualMove) :
    checkLeaf c FS moves = LocalChecker.checkLeaf c FS moves := by
  simp only [checkLeaf, forceDual_eq, LocalChecker.checkLeaf]

def checkTreeCode (c : Cl) (support treecode : ℕ) : Bool :=
  FastPruefer.forceTerms (RelCompactLeaf.decodeTerms c support) fun FS =>
    forceMoves (FastPruefer.moves FS treecode) fun moves => checkLeaf c FS moves

theorem checkTreeCode_sound {c : Cl} {support treecode : ℕ}
    (h : checkTreeCode c support treecode = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  simp only [checkTreeCode, FastPruefer.forceTerms_eq, forceMoves_eq, checkLeaf_eq] at h
  exact LocalChecker.checkLeaf_sound h

def checkPacked (c : Cl) (word : ℕ) : Bool :=
  forceT word fun word => checkTreeCode c (word / 100000000) (word % 100000000)

theorem checkPacked_sound {c : Cl} {word : ℕ} (h : checkPacked c word = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := by
  simp only [checkPacked, forceT_eq] at h
  exact checkTreeCode_sound h

def dispatch (payload : ℕ → ℕ) (c : Cl) (id : ℕ) : Bool :=
  if id ≤ 45 then LeafDispatch.check payload c id
  else checkPacked c (payload (id-46))

theorem dispatch_sound (payload : ℕ → ℕ) (c : Cl) (id : ℕ)
    (h : dispatch payload c id = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  unfold dispatch at h
  split_ifs at h
  · exact LeafDispatch.check_sound payload c id h
  · exact checkPacked_sound h

#print axioms checkTreeCode_sound
#print axioms dispatch_sound
end StructuralW10Cert20261016.EagerLeaf
end
