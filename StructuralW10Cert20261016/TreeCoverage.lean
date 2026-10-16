/-
SPDX-License-Identifier: Apache-2.0
Generic finite coverage for the inherited polyhedral cell geometry.
The numerical leaf checker must prove its own soundness.
-/
import GramDefect20261015.Core

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell

namespace StructuralW10Cert20261016.TreeCoverage

def leftChild (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ)
    (c : Cl) (i j q : ℕ) : Cl :=
  cuB Q PR c (colB Q SL c i) (rowB Q SL c (Nat.add BB q) j)

def rightChild (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ)
    (c : Cl) (i j q : ℕ) : Cl :=
  cuB Q PR c (colB Q SL c j) (rowB Q SL c (Nat.sub BB q) i)

/-- A prefix tree in natural-number words. Even words select a numerical
leaf, odd words split a slot; the upper bits contain the integer split point.
Both children must be consumed successfully, so truncated trees fail closed. -/
def walk (Q : ℕ) (PR : List (ℕ × ℕ)) (SL : List ℕ)
    (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) :
    ℕ → ℕ → Cl → ℕ
  | 0, _, _ => 0
  | fuel + 1, pos, c =>
    let w := read pos
    if w % 2 = 1 then
      let ax := (w / 2) % 64
      let i := sI Q PR ax
      let j := sJ Q PR ax
      let q := w / 128
      if i < j ∧ j ≤ Q then
        let next := walk Q PR SL read leafCheck fuel (pos + 1) (leftChild Q PR SL c i j q)
        if next = 0 then 0 else
          walk Q PR SL read leafCheck fuel next (rightChild Q PR SL c i j q)
      else 0
    else if leafCheck c (w / 2) then pos + 1 else 0

theorem walk_sound {Q : ℕ} {PR : List (ℕ × ℕ)} {SL : List ℕ}
    (hSL : SLok Q PR SL) (hPR : PRok Q PR)
    (P : (ℕ → ℝ) → Prop) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool)
    (hleaf : ∀ c id, leafCheck c id = true → CovBy Q PR P c) :
    ∀ fuel pos c, walk Q PR SL read leafCheck fuel pos c ≠ 0 → CovBy Q PR P c := by
  intro fuel
  induction fuel with
  | zero => intro pos c h; exact False.elim (h rfl)
  | succ fuel ih =>
    intro pos c h
    simp only [walk] at h
    split_ifs at h with hsplit hvalid hnext hcheck
    · exact False.elim (h rfl)
    · have hl := ih (pos + 1)
        (leftChild Q PR SL c (sI Q PR ((read pos / 2) % 64))
          (sJ Q PR ((read pos / 2) % 64)) (read pos / 128)) hnext
      have hr := ih _ _ h
      exact cov_splitB hSL hPR hvalid.1 hvalid.2 (read pos / 128) hl hr
    · exact False.elim (h rfl)
    · exact hleaf c (read pos / 2) hcheck
    · exact False.elim (h rfl)

/-- A leaf which contradicts a coordinate interval is vacuous. -/
theorem cov_of_coordinate_empty {Q : ℕ} {PR : List (ℕ × ℕ)}
    {P : (ℕ → ℝ) → Prop} {c : Cl} {r : ℕ} (hr : r < Q)
    (hempty : c.U.getD r 0 < c.L.getD r 0) : CovBy Q PR P c := by
  intro g hg
  have h := (hg.1 r hr).1.trans (hg.1 r hr).2
  have hnat : c.L.getD r 0 ≤ c.U.getD r 0 := by
    exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp h
  exact False.elim (Nat.not_lt_of_ge hnat hempty)

/-- A leaf which contradicts a partial-span interval is also vacuous. -/
theorem cov_of_span_empty {Q : ℕ} {PR : List (ℕ × ℕ)}
    {P : (ℕ → ℝ) → Prop} {c : Cl} {k : ℕ} (hk : k < PR.length)
    (hempty : c.B.getD k 0 < c.A.getD k 0) : CovBy Q PR P c := by
  intro g hg
  have h := (hg.2 k hk).1.trans (hg.2 k hk).2
  have hnat : c.A.getD k 0 ≤ c.B.getD k 0 := by
    exact_mod_cast (div_le_div_iff_of_pos_right SC_pos).mp h
  exact False.elim (Nat.not_lt_of_ge hnat hempty)

end StructuralW10Cert20261016.TreeCoverage
end
