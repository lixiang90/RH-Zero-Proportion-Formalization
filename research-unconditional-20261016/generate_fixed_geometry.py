"""Generate a fixed-field cell evaluator and explicit definitional equivalences."""
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
FIELDS=[(p,i) for p,n in [('L',9),('U',9),('A',36),('B',36)] for i in range(n)]
PR=[(i,j) for i in range(8) for j in range(i+2,10)]
assert len(PR)==36

def literal(xs):
    return '['+', '.join(xs)+']'

def main():
    lines=['/- SPDX-License-Identifier: Apache-2.0',
           'Generated fixed-field geometry. Equality theorems retain the inherited semantics. -/',
           'import StructuralW10Unconditional20261016.FastGeometry',
           'set_option Elab.async false', 'set_option maxRecDepth 100000',
           'set_option maxHeartbeats 0', 'noncomputable section',
           'open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell',
           'open StructuralW10Cert20261016.LocalChecker',
           'open StructuralW10Cert20261016.TreeCoverage',
           'namespace StructuralW10Unconditional20261016.FixedGeometry',
           'structure Cell where']
    lines += [f'  {p}{i} : ℕ' for p,i in FIELDS]
    lines += ['structure Vec where']+[f'  v{i} : ℕ' for i in range(10)]
    lines += ['def Cell.toCl (c : Cell) : Cl := ⟨'+',\n  '.join(literal([f'c.{p}{i}' for i in range(n)]) for p,n in [('L',9),('U',9),('A',36),('B',36)])+'⟩',
              'def Cell.ofCl (c : Cl) : Cell := ⟨'+', '.join(f'c.{p}.getD {i} 0' for p,i in FIELDS)+'⟩',
              'def Vec.toList (v : Vec) : List ℕ := '+literal([f'v.v{i}' for i in range(10)])]
    for name,typ,fs in [('forceCell','Cell',[f'{p}{i}' for p,i in FIELDS]),('forceVec','Vec',[f'v{i}' for i in range(10)])]:
        lines += [f'def {name} {{α : Sort _}} (c : {typ}) (k : {typ} → α) : α :=']
        lines += [f'  forceT c.{f} fun {f} =>' for f in fs]
        lines += ['  k ⟨'+', '.join(fs)+'⟩',f'theorem {name}_eq {{α : Sort _}} (c : {typ}) (k : {typ} → α) : {name} c k = k c := by',
                  '  cases c',f'  simp only [{name}, forceT_eq]']
    vals=[]
    for p,i in FIELDS:
        a,b=(i,i+1) if p in ('L','U') else PR[i]
        if p in ('L','A'):
            vals.append(f'nmax c.{p}{i} (Nat.sub TB (Nat.add X.v{b} Y.v{a}))')
        else:
            vals.append(f'nmin c.{p}{i} (Nat.sub (Nat.add X.v{a} Y.v{b}) TB)')
    lines += ['def update (c : Cell) (X Y : Vec) : Cell := ⟨'+',\n  '.join(vals)+'⟩',
              'theorem update_eq (c : Cell) (X Y : Vec) :',
              '    (update c X Y).toCl = cuB 9 PR c.toCl X.toList Y.toList := by',
              '  simp [update, Cell.toCl, Vec.toList, cuB, PR, pI, pJ, List.range_succ, List.range_zero]',
              'def column (SL : List ℕ) (c : Cell) (s : ℕ) : Vec := ⟨'+', '.join(f'dE 9 SL c.toCl BB {i} s' for i in range(10))+'⟩',
              'def row (SL : List ℕ) (c : Cell) (E t : ℕ) : Vec := ⟨'+', '.join(f'dE 9 SL c.toCl E t {i}' for i in range(10))+'⟩',
              'theorem column_eq (SL : List ℕ) (c : Cell) (s : ℕ) : (column SL c s).toList = colB 9 SL c.toCl s := by rfl',
              'theorem row_eq (SL : List ℕ) (c : Cell) (E t : ℕ) : (row SL c E t).toList = rowB 9 SL c.toCl E t := by rfl',
              'def child (c : Cell) (X Y : Vec) : Cell := forceVec X fun X => forceVec Y fun Y => update c X Y',
              'theorem child_eq (c : Cell) (X Y : Vec) : (child c X Y).toCl = cuB 9 PR c.toCl X.toList Y.toList := by',
              '  simp only [child, forceVec_eq, update_eq]',
              'def left (SL : List ℕ) (c : Cell) (i j q : ℕ) : Cell := child c (column SL c i) (row SL c (Nat.add BB q) j)',
              'def right (SL : List ℕ) (c : Cell) (i j q : ℕ) : Cell := child c (column SL c j) (row SL c (Nat.sub BB q) i)',
              'theorem left_eq (SL : List ℕ) (c : Cell) (i j q : ℕ) : (left SL c i j q).toCl = leftChild 9 PR SL c.toCl i j q := by',
              '  simp only [left, child_eq, column_eq, row_eq, leftChild]',
              'theorem right_eq (SL : List ℕ) (c : Cell) (i j q : ℕ) : (right SL c i j q).toCl = rightChild 9 PR SL c.toCl i j q := by',
              '  simp only [right, child_eq, column_eq, row_eq, rightChild]',
              'def step (SL : List ℕ) (c : Cell) : Cell := forceCell (left SL c 0 1 c.U8) fun c => forceCell (right SL c 8 9 c.L0) id',
              'theorem step_eq (SL : List ℕ) (c : Cell) : (step SL c).toCl = StructuralW10Cert20261016.OrderCoverage.step SL c.toCl := by',
              '  simp only [step, forceCell_eq, id_eq]',
              '  rw [right_eq]',
              '  change rightChild 9 PR SL (left SL c 0 1 c.U8).toCl 8 9 ((left SL c 0 1 c.U8).toCl.L.getD 0 0) = _',
              '  rw [left_eq]',
              '  rfl',
              'def rounds (SL : List ℕ) : ℕ → Cell → Cell',
              '  | 0, c => c',
              '  | n+1, c => forceCell (step SL c) (rounds SL n)',
              'theorem rounds_eq (SL : List ℕ) (n : ℕ) (c : Cell) : (rounds SL n c).toCl = StructuralW10Cert20261016.OrderCoverage.normalize SL n c.toCl := by',
              '  induction n generalizing c with',
              '  | zero => rfl',
              '  | succ n ih => simp only [rounds, forceCell_eq, ih, step_eq, StructuralW10Cert20261016.OrderCoverage.normalize]',
              'def normalize (SL : List ℕ) (c : Cell) : Cell := if c.U0 ≤ c.U8 ∧ c.L0 ≤ c.L8 then c else rounds SL 2 c',
              'theorem normalize_eq (SL : List ℕ) (c : Cell) : (normalize SL c).toCl = StructuralW10Cert20261016.AdaptiveCoverage.normalize SL c.toCl := by',
              '  unfold normalize StructuralW10Cert20261016.AdaptiveCoverage.normalize',
              '  change (if c.U0 ≤ c.U8 ∧ c.L0 ≤ c.L8 then c else rounds SL 2 c).toCl = if c.U0 ≤ c.U8 ∧ c.L0 ≤ c.L8 then c.toCl else _',
              '  split_ifs <;> simp only [rounds_eq, StructuralW10Cert20261016.ForcedCoverage.normalize_eq]',
              'def walk (SL : List ℕ) (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool) : ℕ → ℕ → Cell → ℕ',
              '  | 0, _, _ => 0',
              '  | fuel+1, pos, c => forceCell c fun c => forceCell (normalize SL c) fun c => forceT (read pos) fun w =>',
              '    if w % 2 = 1 then',
              '      let ax := (w / 2) % 64',
              '      let i := sI 9 PR ax',
              '      let j := sJ 9 PR ax',
              '      let q := w / 128',
              '      if i < j ∧ j ≤ 9 then',
              '        let next := walk SL read leafCheck fuel (pos+1) (left SL c i j q)',
              '        forceT next fun next => if next = 0 then 0 else walk SL read leafCheck fuel next (right SL c i j q)',
              '      else 0',
              '    else StructuralW10Cert20261016.ForcedCoverage.forceCell c.toCl fun lc =>',
              '      if leafCheck lc (w / 2) then pos+1 else 0',
              'theorem walk_sound {SL : List ℕ} (hSL : SLok 9 PR SL) (n : ℕ)',
              '    (read : ℕ → ℕ) (leafCheck : Cl → ℕ → Bool)',
              '    (hleaf : ∀ c id, leafCheck c id = true → CovBy 9 PR (Pg n 9 BS TS) c) :',
              '    ∀ fuel pos c, walk SL read leafCheck fuel pos c ≠ 0 → CovBy 9 PR (Pg n 9 BS TS) c.toCl := by',
              '  intro fuel',
              '  induction fuel with',
              '  | zero => intro pos c h; exact False.elim (h rfl)',
              '  | succ fuel ih =>',
              '    intro pos c h g hg',
              '    by_cases ho : g 0 ≤ g 8',
              '    · have hn : InCell 9 PR (normalize SL c).toCl g := by',
              '        rw [normalize_eq]',
              '        exact StructuralW10Cert20261016.AdaptiveCoverage.normalize_in hSL hg ho',
              '      simp only [walk, forceCell_eq, forceT_eq, StructuralW10Cert20261016.ForcedCoverage.forceCell_eq] at h',
              '      split_ifs at h with hsplit hvalid hnext hcheck',
              '      · exact False.elim (h rfl)',
              '      · have hl := ih (pos+1) _ hnext',
              '        have hr := ih _ _ h',
              '        rw [left_eq] at hl',
              '        rw [right_eq] at hr',
              '        exact cov_splitB hSL hPR hvalid.1 hvalid.2 (read pos / 128) hl hr g hn',
              '      · exact False.elim (h rfl)',
              '      · exact hleaf _ (read pos / 2) hcheck g hn',
              '      · exact False.elim (h rfl)',
              '    · exact Or.inr (lt_of_not_ge ho)',
              '#print axioms update_eq', '#print axioms walk_sound',
              'end StructuralW10Unconditional20261016.FixedGeometry', 'end', '']
    (ROOT/'StructuralW10Unconditional20261016/FixedGeometry.lean').write_text('\n'.join(lines),encoding='utf8')

if __name__=='__main__':
    main()
