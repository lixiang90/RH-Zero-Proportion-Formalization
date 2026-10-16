/- SPDX-License-Identifier: Apache-2.0
Ordered coverage with an inexpensive redundant-bound test. Skipping the
optional tightening preserves every ordered input. All cell entries are
forced before they are used, as in ForcedCoverage.
-/
import StructuralW10Cert20261016.ForcedCoverage

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
namespace StructuralW10Cert20261016.AdaptiveCoverage

/-- Both endpoint bound updates are unnecessary when their individual
upper and lower bounds already have the required order. Soundness needs
only preservation of ordered points, and does not assume a closed cell. -/
def normalize (SL : List ℕ) (c : Cl) : Cl :=
  if c.U.getD 0 0 ≤ c.U.getD 8 0 ∧ c.L.getD 0 0 ≤ c.L.getD 8 0 then c
  else ForcedCoverage.normalize SL 2 c

theorem normalize_in {SL : List ℕ} (hSL : SLok 9 PR SL) {c : Cl} {g : ℕ → ℝ}
    (hg : InCell 9 PR c g) (ho : g 0 ≤ g 8) :
    InCell 9 PR (normalize SL c) g := by
  unfold normalize
  split_ifs
  · exact hg
  · rw [ForcedCoverage.normalize_eq]
    exact OrderCoverage.normalize_in hSL 2 hg ho

theorem normalize_sound {SL : List ℕ} (hSL : SLok 9 PR SL) {c : Cl}
    (hc : CovBy 9 PR (Pg cN 9 BS TS) (normalize SL c)) :
    CovBy 9 PR (Pg cN 9 BS TS) c := by
  intro g hg
  by_cases ho : g 0 ≤ g 8
  · exact hc g (normalize_in hSL hg ho)
  · exact Or.inr (lt_of_not_ge ho)

def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) :
    ℕ → ℕ → Cl → ℕ
  | 0, _, _ => 0
  | fuel+1, pos, c => ForcedCoverage.forceCell c fun c =>
    ForcedCoverage.forceCell (normalize SL c) fun c =>
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
    apply normalize_sound hSL
    simp only [walk, ForcedCoverage.forceCell_eq] at h
    split_ifs at h with hsplit hvalid hnext hcheck
    · exact False.elim (h rfl)
    · have hl := ih (pos+1) _ hnext
      have hr := ih _ _ h
      exact cov_splitB hSL hPR hvalid.1 hvalid.2 (read pos / 128) hl hr
    · exact False.elim (h rfl)
    · exact hleaf _ (read pos / 2) hcheck
    · exact False.elim (h rfl)

#print axioms normalize_sound
#print axioms walk_sound
end StructuralW10Cert20261016.AdaptiveCoverage
end
