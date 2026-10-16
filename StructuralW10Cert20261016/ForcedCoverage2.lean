/- SPDX-License-Identifier: Apache-2.0
The proved cell walker, additionally forcing each read word and successful
left-subtree cursor before reusing them. Only evaluation order changes.
-/
import StructuralW10Cert20261016.ForcedCoverage
import StructuralW10Cert20261016.FastPruefer

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralW10Cert20261016.ForcedCoverage
namespace StructuralW10Cert20261016.ForcedCoverage2

def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) :
    ℕ → ℕ → Cl → ℕ
  | 0, _, _ => 0
  | fuel+1, pos, c => forceCell c fun c =>
    forceCell (normalize SL 2 c) fun c =>
    forceT (read pos) fun w =>
    if w % 2 = 1 then
      let ax := (w / 2) % 64
      let i := sI 9 PR ax
      let j := sJ 9 PR ax
      let q := w / 128
      if i < j ∧ j ≤ 9 then
        forceT (walk SL read leafCheck fuel (pos+1) (leftChild 9 PR SL c i j q)) fun next =>
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
    simp only [walk, forceCell_eq, normalize_eq, forceT_eq] at h
    split_ifs at h with hsplit hvalid hnext hcheck
    · exact False.elim (h rfl)
    · have hl := ih (pos+1) _ hnext
      have hr := ih _ _ h
      exact cov_splitB hSL hPR hvalid.1 hvalid.2 (read pos / 128) hl hr
    · exact False.elim (h rfl)
    · exact hleaf _ (read pos / 2) hcheck
    · exact False.elim (h rfl)

/-- Force a packed payload before its quotient and remainder are read. -/
def dispatch (payload : ℕ → ℕ) (c : Cl) (id : ℕ) : Bool :=
  if id ≤ 45 then LeafDispatch.check payload c id
  else forceT (payload (id-46)) fun word => FastPruefer.checkPacked c word

theorem dispatch_sound (payload : ℕ → ℕ) (c : Cl) (id : ℕ)
    (h : dispatch payload c id = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  simp only [dispatch, forceT_eq] at h
  split_ifs at h
  · exact LeafDispatch.check_sound payload c id h
  · exact FastPruefer.checkPacked_sound h

#print axioms walk_sound
#print axioms dispatch_sound
end StructuralW10Cert20261016.ForcedCoverage2
end
