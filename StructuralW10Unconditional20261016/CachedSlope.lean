/- SPDX-License-Identifier: Apache-2.0
Cache the 39 term slopes before the inherited nine-coordinate arithmetic
uses them repeatedly. Every executable cache is proved extensionally equal.
-/
import StructuralW10Unconditional20261016.StreamingDual

set_option Elab.async false
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016
open LocalChecker
namespace StructuralW10Unconditional20261016.CachedSlope

def cache {α : Sort _} (N : ℕ) (f : ℕ → ℕ) (k : (ℕ → ℕ) → α) : α :=
  ForcedCoverage.forceNats ((List.range N).map f) fun xs =>
    k (fun n => if n < N then xs.getD n 0 else f n)

theorem cache_eq {α : Sort _} (N : ℕ) (f : ℕ → ℕ) (k : (ℕ → ℕ) → α) :
    cache N f k = k f := by
  simp only [cache, ForcedCoverage.forceNats_eq]
  congr 1
  funext n
  by_cases hn : n < N
  · simp only [if_pos hn, getD_map_range f hn]
  · exact if_neg hn

def ng (slopes weights : ℕ → ℕ) (P S : List ℕ) (r : ℕ) : ℕ :=
 Nat.sub (Nat.add (Nat.mul 2000000000 (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
     (Nat.mul (tA TS n) (weights n)) (inr r (tI TS n) (tJ TS n))) TS.length)) (P.getD r 0))
   (Nat.add (Nat.add (Nat.mul 1024000000000 (BS.getD r 0)) (isum (fun n => Bool.rec (motive := fun _ => ℕ) 0
     (Nat.mul (tA TS n) (slopes n)) (inr r (tI TS n) (tJ TS n))) TS.length)) (S.getD r 0))

def core (n : ℕ) (c : Cl) (FS : List Term) (P S : List ℕ) (Cp Cm : ℕ)
    (slopes weights : ℕ → ℕ) : Bool :=
 Bool.rec (motive := fun _ => Bool) false
   (Nat.ble
     (Nat.add (Nat.mul 335544320000000000 n) (Nat.mul 10 (Nat.add (Nat.add (isum (fun k => Nat.mul (tA TS k)
       (mcnT (tf PC9QB6MData.PT) (eL0 TS c k) (tI FS k) (tJ FS k) (tA FS k) (tK FS k))) TS.length) Cp)
       (isum (fun r => Nat.mul (Nat.sub (c.U.getD r 0) (c.L.getD r 0)) (ng slopes weights P S r)) 9))))
     (Nat.add (Nat.add (Nat.mul 10240000000000 (isum (fun r => Nat.mul (BS.getD r 0) (c.L.getD r 0)) 9))
       (Nat.mul 32768 (isum (fun k => Nat.mul (tA TS k) (mvT PC9QB6MData.TOP PC9QB6MData.BK (tf PC9QB6MData.PT)
         (eL TS c k) (uc (eL TS c k) (eU TS c k)) (tI FS k) (tJ FS k) (tA FS k) (tK FS k))) TS.length)))
       (Nat.mul 10 (Nat.add (isum (fun k => Nat.mul (tA TS k) (mcpT (tf PC9QB6MData.PT) (eL0 TS c k)
         (tI FS k) (tJ FS k) (tA FS k) (tK FS k))) TS.length) Cm))))
   (Bool.rec (motive := fun _ => Bool) false
     (iall (fun k => mokI PC9QB6MData.PT (eL TS c k) (eU TS c k) (tI FS k) (tJ FS k) (tA FS k) (tK FS k)) TS.length)
     (iall (fun r => Nat.ble (c.L.getD r 0) (c.U.getD r 0)) 9))

def checkLeaf (n : ℕ) (c : Cl) (FS : List Term) (moves : List DualMove) : Bool :=
  EagerLeaf.forceDual (runDual c moves initialDual) fun s =>
  cache TS.length (fun k => mslT (tf PC9QB6MData.PT) (tI FS k) (tJ FS k) (tA FS k) (tK FS k)) fun slopes =>
  cache TS.length (fun k => mwT (tI FS k) (tJ FS k)) fun weights =>
    core n c FS s.P s.S s.Cp s.Cm slopes weights

theorem checkLeaf_eq (n : ℕ) (c : Cl) (FS : List Term) (moves : List DualMove) :
    checkLeaf n c FS moves = GenericFloor.checkLeaf n c FS moves := by
  simp only [checkLeaf, EagerLeaf.forceDual_eq, cache_eq, GenericFloor.checkLeaf, core, ng, Ng, mcheckGX]

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

#print axioms checkLeaf_eq
#print axioms dispatch_sound
end StructuralW10Unconditional20261016.CachedSlope
end
