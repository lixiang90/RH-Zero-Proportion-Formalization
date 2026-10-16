/- SPDX-License-Identifier: Apache-2.0
Materialize the two ten-entry closure vectors before their ninety uses.
This is an evaluation change, with equality to the inherited cell geometry.
-/
import StructuralW10Cert20261016.AdaptiveCoverage

set_option Elab.async false
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralW10Cert20261016.ForcedCoverage
namespace StructuralW10Unconditional20261016.FastGeometry

def child (c : Cl) (X Y : List ℕ) : Cl :=
  forceNats X fun X => forceNats Y fun Y => cuB 9 PR c X Y

theorem child_eq (c : Cl) (X Y : List ℕ) : child c X Y = cuB 9 PR c X Y := by
  simp only [child, forceNats_eq]

def left (SL : List ℕ) (c : Cl) (i j q : ℕ) : Cl :=
  child c (colB 9 SL c i) (rowB 9 SL c (Nat.add BB q) j)

def right (SL : List ℕ) (c : Cl) (i j q : ℕ) : Cl :=
  child c (colB 9 SL c j) (rowB 9 SL c (Nat.sub BB q) i)

theorem left_eq (SL : List ℕ) (c : Cl) (i j q : ℕ) :
    left SL c i j q = leftChild 9 PR SL c i j q := by
  simp only [left, child_eq, leftChild]

theorem right_eq (SL : List ℕ) (c : Cl) (i j q : ℕ) :
    right SL c i j q = rightChild 9 PR SL c i j q := by
  simp only [right, child_eq, rightChild]

def step (SL : List ℕ) (c : Cl) : Cl :=
  forceCell (left SL c 0 1 (c.U.getD 8 0)) fun c =>
    forceCell (right SL c 8 9 (c.L.getD 0 0)) id

theorem step_eq (SL : List ℕ) (c : Cl) :
    step SL c = StructuralW10Cert20261016.OrderCoverage.step SL c := by
  simp only [step, forceCell_eq, left_eq, right_eq, id_eq,
    StructuralW10Cert20261016.OrderCoverage.step,
    StructuralW10Cert20261016.OrderCoverage.tightenUpper,
    StructuralW10Cert20261016.OrderCoverage.tightenLower]

def rounds (SL : List ℕ) : ℕ → Cl → Cl
  | 0, c => c
  | n+1, c => forceCell (step SL c) (rounds SL n)

theorem rounds_eq (SL : List ℕ) (n : ℕ) (c : Cl) :
    rounds SL n c = StructuralW10Cert20261016.OrderCoverage.normalize SL n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [rounds, forceCell_eq, step_eq,
      StructuralW10Cert20261016.OrderCoverage.normalize, ih]

def normalize (SL : List ℕ) (c : Cl) : Cl :=
  if c.U.getD 0 0 ≤ c.U.getD 8 0 ∧ c.L.getD 0 0 ≤ c.L.getD 8 0 then c
  else rounds SL 2 c

theorem normalize_eq (SL : List ℕ) (c : Cl) :
    normalize SL c = StructuralW10Cert20261016.AdaptiveCoverage.normalize SL c := by
  simp only [normalize, rounds_eq,
    StructuralW10Cert20261016.AdaptiveCoverage.normalize,
    StructuralW10Cert20261016.ForcedCoverage.normalize_eq]

def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) :
    ℕ → ℕ → Cl → ℕ
  | 0, _, _ => 0
  | fuel+1, pos, c => forceCell c fun c =>
    forceCell (normalize SL c) fun c =>
    forceT (read pos) fun w =>
    if w % 2 = 1 then
      let ax := (w / 2) % 64
      let i := sI 9 PR ax
      let j := sJ 9 PR ax
      let q := w / 128
      if i < j ∧ j ≤ 9 then
        let next := walk SL read leafCheck fuel (pos+1) (left SL c i j q)
        forceT next fun next =>
          if next = 0 then 0 else walk SL read leafCheck fuel next (right SL c i j q)
      else 0
    else if leafCheck c (w / 2) then pos+1 else 0

theorem walk_sound {SL : List ℕ} (hSL : SLok 9 PR SL) (n : ℕ)
    (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool)
    (hleaf : ∀ c id, leafCheck c id = true → CovBy 9 PR (Pg n 9 BS TS) c) :
    ∀ fuel pos c, walk SL read leafCheck fuel pos c ≠ 0 → CovBy 9 PR (Pg n 9 BS TS) c := by
  intro fuel
  induction fuel with
  | zero => intro pos c h; exact False.elim (h rfl)
  | succ fuel ih =>
    intro pos c h g hg
    by_cases ho : g 0 ≤ g 8
    · have hn : InCell 9 PR (normalize SL c) g := by
        rw [normalize_eq]
        exact StructuralW10Cert20261016.AdaptiveCoverage.normalize_in hSL hg ho
      simp only [walk, forceCell_eq, forceT_eq] at h
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

#print axioms walk_sound
end StructuralW10Unconditional20261016.FastGeometry
end
