/- SPDX-License-Identifier: Apache-2.0
Sound endpoint ordering reduction.  Unordered inputs already satisfy Pg's
reflection alternative; every tightening preserves all ordered inputs. -/
import StructuralW10Cert20261016.LocalChecker
import StructuralW10Cert20261016.TreeCoverage

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
namespace StructuralW10Cert20261016.OrderCoverage

def tightenUpper (SL : List ℕ) (c : Cl) : Cl :=
  leftChild 9 PR SL c 0 1 (c.U.getD 8 0)

def tightenLower (SL : List ℕ) (c : Cl) : Cl :=
  rightChild 9 PR SL c 8 9 (c.L.getD 0 0)

def step (SL : List ℕ) (c : Cl) : Cl := tightenLower SL (tightenUpper SL c)
def normalize (SL : List ℕ) : ℕ → Cl → Cl
  | 0, c => c
  | n+1, c => normalize SL n (step SL c)

theorem tightenUpper_in {SL : List ℕ} (hSL : SLok 9 PR SL) {c : Cl} {g : ℕ → ℝ}
    (hg : InCell 9 PR c g) (ho : g 0 ≤ g 8) : InCell 9 PR (tightenUpper SL c) g := by
  apply cuB_ok hPR hg
  apply colB_ok hSL hg (by decide : 0 ≤ 9) (by decide : 1 ≤ 9)
  have h8 := (hg.1 8 (by decide)).2
  have hd : gsum g 0 1 - gsum g 0 0 = g 0 := by
    rw [← gsum_sub g (by decide : 0 ≤ 1), gsum_single]
  rw [cast_add_div]
  linarith only [h8, ho, hd]

theorem tightenLower_in {SL : List ℕ} (hSL : SLok 9 PR SL) {c : Cl} {g : ℕ → ℝ}
    (hg : InCell 9 PR c g) (ho : g 0 ≤ g 8) : InCell 9 PR (tightenLower SL c) g := by
  apply cuB_ok hPR hg
  apply colB_ok hSL hg (by decide : 9 ≤ 9) (by decide : 8 ≤ 9)
  have h0 := (hg.1 0 (by decide)).1
  have hd : gsum g 0 9 - gsum g 0 8 = g 8 := by
    rw [← gsum_sub g (by decide : 8 ≤ 9), gsum_single]
  have hh := natsub_ge BB (c.L.getD 0 0)
  have hb : ((BB : ℝ) - c.L.getD 0 0) / SC ≤
      ((Nat.sub BB (c.L.getD 0 0) : ℕ) : ℝ) / SC := by
    apply (div_le_div_iff_of_pos_right SC_pos).mpr
    simpa only [Nat.sub_eq] using hh
  rw [sub_div] at hb
  linarith only [h0, ho, hd, hb]

theorem normalize_in {SL : List ℕ} (hSL : SLok 9 PR SL) (n : ℕ)
    {c : Cl} {g : ℕ → ℝ} (hg : InCell 9 PR c g) (ho : g 0 ≤ g 8) :
    InCell 9 PR (normalize SL n c) g := by
  induction n generalizing c with
  | zero => exact hg
  | succ n ih => exact ih (tightenLower_in hSL (tightenUpper_in hSL hg ho) ho)

theorem normalize_sound {SL : List ℕ} (hSL : SLok 9 PR SL) (n : ℕ) {c : Cl}
    (hc : CovBy 9 PR (Pg cN 9 BS TS) (normalize SL n c)) :
    CovBy 9 PR (Pg cN 9 BS TS) c := by
  intro g hg
  by_cases ho : g 0 ≤ g 8
  · exact hc g (normalize_in hSL n hg ho)
  · exact Or.inr (lt_of_not_ge ho)

/-- Every visited cell is tightened by two sound ordered endpoint rounds.
The prefix word format is the same as TreeCoverage.walk. -/
def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) :
    ℕ → ℕ → Cl → ℕ
  | 0, _, _ => 0
  | fuel+1, pos, c =>
    let c := normalize SL 2 c
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
    apply normalize_sound hSL 2
    simp only [walk] at h
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
end StructuralW10Cert20261016.OrderCoverage
end
