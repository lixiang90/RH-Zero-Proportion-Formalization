/- SPDX-License-Identifier: Apache-2.0
Computable leaf certificate interface for the fixed ten-point candidate.
Every analytic minorant is inherited from the proved kernel table.
This module alone asserts no finite coverage and no improved zeta bound. -/
import StructuralResearch20261016.W10RefinedCandidate

noncomputable section
open Finset AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace StructuralW10Cert20261016.LocalChecker

def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 9), (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (4, 6), (4, 7), (4, 8), (4, 9), (5, 7), (5, 8), (5, 9), (6, 8), (6, 9), (7, 9)]
def BS : List ℕ := [1960353, 3889123, 5428938, 6964154, 7513588, 6964154, 5428938, 3889123, 1960353]
def TS : List Term := [(0, 1, 856023725, 0), (0, 5, 2431155644, 3), (0, 6, 6271589178, 4), (0, 7, 6414869991, 5), (0, 8, 10000000000, 6), (0, 9, 20000000000, 7), (1, 2, 1769970138, 0), (1, 3, 1139482463, 8), (1, 4, 3005622676, 9), (1, 5, 3187144078, 10), (1, 6, 5479076134, 11), (1, 7, 3728410821, 12), (1, 8, 7170260017, 13), (1, 9, 10000000000, 14), (2, 3, 2492616294, 0), (2, 4, 3741136898, 15), (2, 5, 4658843169, 16), (2, 6, 6812855921, 17), (2, 7, 4179536443, 18), (2, 8, 3728410821, 19), (2, 9, 6414869991, 20), (3, 4, 3184724710, 0), (3, 5, 5119380638, 21), (3, 6, 4671068306, 22), (3, 7, 6812855921, 23), (3, 8, 5479076134, 24), (3, 9, 6271589178, 25), (4, 5, 3393330261, 0), (4, 6, 5119380638, 26), (4, 7, 4658843169, 27), (4, 8, 3187144078, 28), (4, 9, 2431155644, 29), (5, 6, 3184724710, 0), (5, 7, 3741136898, 30), (5, 8, 3005622676, 31), (6, 7, 2492616294, 0), (6, 8, 1139482463, 33), (7, 8, 1769970138, 0), (8, 9, 856023725, 0)]
def cN : ℕ := 86600000

theorem hPR : PRok 9 PR := by decide +kernel
theorem hTS : TSok 9 PR TS := by decide +kernel

structure DualState where
  P : List ℕ
  S : List ℕ
  Cp : ℕ
  Cm : ℕ
  deriving Inhabited

/-- (partial-span index, lower multiplier, upper multiplier). -/
abbrev DualMove := ℕ × ℕ × ℕ

def initialDual : DualState := ⟨List.replicate 9 0, List.replicate 9 0, 0, 0⟩

def dualStep (c : Cl) (s : DualState) (m : DualMove) : DualState :=
  if m.1 < PR.length then
    let i := pI PR m.1
    let j := pJ PR m.1
    let lo := m.2.1
    let hi := m.2.2
    let sl := sumR c.L i (j-i)
    ⟨imap (fun r x => x + lo * ind (inr r i j)) 0 s.P,
      imap (fun r x => x + hi * ind (inr r i j)) 0 s.S,
      s.Cp + lo * (sl - c.A.getD m.1 0) + hi * (c.B.getD m.1 0 - sl),
      s.Cm + lo * (c.A.getD m.1 0 - sl) + hi * (sl - c.B.getD m.1 0)⟩
  else s

def runDual (c : Cl) : List DualMove → DualState → DualState
  | [], s => s
  | m :: ms, s => runDual c ms (dualStep c s m)

def DualGood (c : Cl) (s : DualState) : Prop :=
  s.P.length = 9 ∧ s.S.length = 9 ∧ MulOKg 9 PR c s.P s.S s.Cp s.Cm

theorem initial_good (c : Cl) : DualGood c initialDual := by
  refine ⟨by simp [initialDual], by simp [initialDual], ?_⟩
  intro g hg
  simp [initialDual]

theorem dualStep_good (c : Cl) (s : DualState) (m : DualMove)
    (hs : DualGood c s) : DualGood c (dualStep c s m) := by
  unfold dualStep
  split_ifs with hm
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [imap_length] using hs.1
    · simpa only [imap_length] using hs.2.1
    · exact mul_step hPR hs.1 hs.2.1 hs.2.2 hm m.2.1 m.2.2
  · exact hs

theorem runDual_good (c : Cl) (ms : List DualMove) (s : DualState)
    (hs : DualGood c s) : DualGood c (runDual c ms s) := by
  induction ms generalizing s with
  | nil => exact hs
  | cons m ms ih => exact ih _ (dualStep_good c s m hs)

/-- All its inputs are naturals or finite lists; no real-valued claim is tested. -/
def checkLeaf (c : Cl) (FS : List Term) (moves : List DualMove) : Bool :=
  let s := runDual c moves initialDual
  mcheckGX (mokI AMW.Cert.PC9QB6MData.PT) AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK (tf AMW.Cert.PC9QB6MData.PT) 9 BS TS cN c FS
    s.P s.S s.Cp s.Cm

/-- Kernel-checked soundness of every successful executable leaf check. -/
theorem checkLeaf_sound {c : Cl} {FS : List Term} {moves : List DualMove}
    (h : checkLeaf c FS moves = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  exact mcheckGX_sound (mtermTI AMW.Cert.PC9QB6MData.lbS AMW.Cert.PC9QB6MData.ptS) hPR hTS
    (runDual_good c moves initialDual (initial_good c)).2.2 h

open Zeta23Ext.BridgeW Zeta23Ext.Bridge
open StructuralResearch20261016.W10RefinedCandidate

/-- The finite arithmetic objective uses the exact common weight denominator. -/
theorem fg_eq_scaled_Fw (g : ℕ → ℝ) :
    Fg 9 BS TS g = 10000000000 * Fw W (fun r : Fin 9 => g r) := by
  simp [RiemannFail.cert_wfun_eq, Fg, BS, TS, tI, tJ, tA, Fw, W, a, b, aN, bN,
    ptsN, gsum, Fin.sum_univ_succ, Finset.sum_range_succ, Finset.sum_Ico_succ_top]
  ring

/-- A leaf's ordering escape is eliminated when the endpoints have been ordered. -/
theorem checkLeaf_floor_ordered {c : Cl} {FS : List Term} {moves : List DualMove}
    (h : checkLeaf c FS moves = true) {g : ℕ → ℝ}
    (hg : InCell 9 PR c g) (horder : g 0 ≤ g 8) :
    (433 : ℝ) / 50000 ≤ Fw W (fun r : Fin 9 => g r) := by
  have hh := checkLeaf_sound h g hg
  rcases hh with hf | hf
  · rw [fg_eq_scaled_Fw] at hf
    norm_num only [cN, Nat.cast_ofNat] at hf
    nlinarith only [hf]
  · exact False.elim ((not_lt_of_ge horder) hf)

#print axioms checkLeaf_sound
#print axioms fg_eq_scaled_Fw
end StructuralW10Cert20261016.LocalChecker
end
