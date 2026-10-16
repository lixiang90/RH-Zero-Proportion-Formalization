/- SPDX-License-Identifier: Apache-2.0
The same ordered cell walker, with eager numeral forcing between updates.
The forcing equations are proved, so this changes only evaluation order.
-/
import StructuralW10Cert20261016.OrderCoverage

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
namespace StructuralW10Cert20261016.ForcedCoverage

def forceNats {α : Sort _} : List ℕ → (List ℕ → α) → α
  | [], k => k []
  | n :: ns, k => forceT n fun n => forceNats ns fun ns => k (n :: ns)

theorem forceNats_eq {α : Sort _} (ns : List ℕ) (k : List ℕ → α) :
    forceNats ns k = k ns := by
  induction ns generalizing k with
  | nil => rfl
  | cons n ns ih => simp only [forceNats, forceT_eq, ih]

def forceCell {α : Sort _} (c : Cl) (k : Cl → α) : α :=
  forceNats c.L fun L => forceNats c.U fun U =>
    forceNats c.A fun A => forceNats c.B fun B => k ⟨L,U,A,B⟩

theorem forceCell_eq {α : Sort _} (c : Cl) (k : Cl → α) : forceCell c k = k c := by
  cases c
  simp only [forceCell, forceNats_eq]

/-- Force the first `cuB` result before constructing the second one. Both
updates have the same mathematical value as the unforced ordered step. -/
def step {α : Sort _} (SL : List ℕ) (c : Cl) (k : Cl → α) : α :=
  forceCell (OrderCoverage.tightenUpper SL c) fun c =>
    forceCell (OrderCoverage.tightenLower SL c) k

theorem step_eq {α : Sort _} (SL : List ℕ) (c : Cl) (k : Cl → α) :
    step SL c k = k (OrderCoverage.step SL c) := by
  simp only [step, forceCell_eq, OrderCoverage.step]

def normalize (SL : List ℕ) : ℕ → Cl → Cl
  | 0, c => c
  | n+1, c => step SL c (normalize SL n)

theorem normalize_eq (SL : List ℕ) (n : ℕ) (c : Cl) :
    normalize SL n c = OrderCoverage.normalize SL n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [normalize, step_eq, OrderCoverage.normalize, ih]

def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) :
    ℕ → ℕ → Cl → ℕ
  | 0, _, _ => 0
  | fuel+1, pos, c => forceCell c fun c =>
    forceCell (normalize SL 2 c) fun c =>
    let w := read pos
    if w % 2 = 1 then
      let ax := (w / 2) % 64
      let i := sI 9 PR ax
      let j := sJ 9 PR ax
      let q := w / 128
      if i < j ∧ j ≤ 9 then
        let next := walk SL read leafCheck fuel (pos+1) (leftChild 9 PR SL c i j q)
        if next = 0 then 0 else walk SL read leafCheck fuel next (rightChild 9 PR SL c i j q)
      else 0
    else if leafCheck c (w / 2) then pos+1 else 0

theorem walk_sound {SL : List ℕ} (hSL : SLok 9 PR SL)
    (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool)
    (hleaf : ∀ c id, leafCheck c id = true → CovBy 9 PR (Pg cN 9 BS TS) c) :
    ∀ fuel pos c, walk SL read leafCheck fuel pos c ≠ 0 → CovBy 9 PR (Pg cN 9 BS TS) c := by
  intro fuel
  induction fuel with
  | zero => intro pos c h; exact False.elim (h rfl)
  | succ fuel ih =>
    intro pos c h
    apply OrderCoverage.normalize_sound hSL 2
    simp only [walk, forceCell_eq, normalize_eq] at h
    split_ifs at h with hsplit hvalid hnext hcheck
    · exact False.elim (h rfl)
    · have hl := ih (pos+1) _ hnext
      have hr := ih _ _ h
      exact cov_splitB hSL hPR hvalid.1 hvalid.2 (read pos / 128) hl hr
    · exact False.elim (h rfl)
    · exact hleaf _ (read pos / 2) hcheck
    · exact False.elim (h rfl)

#print axioms walk_sound
end StructuralW10Cert20261016.ForcedCoverage
end
