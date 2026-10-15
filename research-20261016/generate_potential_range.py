"""Generate a pure rational Lean range proof for the fixed overlap potential."""
import hashlib,json
from pathlib import Path

FOLDER=Path(__file__).resolve().parent

def real(n,d=10**12):return f'(({n} : ℝ) / {d})'

def main():
    src=FOLDER/'overlap_rational_candidate.json';raw=src.read_bytes();j=json.loads(raw)
    den=int(j['common_denominator']);base={int(s):r for s,r in j['binary_affine_numerators'].items()}
    delta={int(s):int(v) for s,v in j['ternary_constant_numerators'].items()}
    lines=['import Mathlib.Data.Real.Basic','import Mathlib.Data.Fin.VecNotation',
        'import Mathlib.Tactic.Linarith','import Mathlib.Tactic.NormNum',
        'import Mathlib.Tactic.SplitIfs\n', '/- Pure rational research lemma. The global local-energy inequality is not claimed.',
        '   Fixed candidate SHA256: '+hashlib.sha256(raw).hexdigest()+' -/',
        'noncomputable section','namespace OverlapPotential20261016',
        'attribute [local instance] Classical.propDecidable',
        'def classes (g : Fin 7 → ℝ) : Fin 7 → Fin 3 :=',
        '  fun i => if g i ≤ 3 / 2 then 0 else if g i ≤ 5 / 2 then 1 else 2',
        'def ternaryCode (w : Fin 7 → Fin 3) : ℕ := '+ ' + '.join(f'{3**i} * (w {i}).val' for i in range(7)),
        'def delta (s : ℕ) : ℝ :=']
    for ix,(s,v) in enumerate(sorted(delta.items())):
        lines.append(f'  {"if" if ix==0 else "else if"} s = {s} then {real(v,den)}')
    lines.append('  else 0')
    lines += ['theorem delta_bounds (s : ℕ) :',
        '    -(133 / 100000 : ℝ) ≤ delta s ∧ delta s ≤ (143 / 100000 : ℝ) := by']
    for ix,s in enumerate(sorted(delta)):
        lines += [f'  by_cases h{ix} : s = {s}',f'  · subst s; norm_num [delta]']
    lines += ['  simp only [delta, '+', '.join('h'+str(ix) for ix in range(len(delta)))+', if_false]',
        '  norm_num',
        'theorem zero_bounds {g : Fin 7 → ℝ} (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)',
        '    (i : Fin 7) (h : classes g i = 0) :',
        '    (17 / 20 : ℝ) ≤ g i ∧ g i ≤ (3 / 2 : ℝ) := by',
        '  by_cases h0 : g i ≤ (3 / 2 : ℝ)',
        '  · exact ⟨hg i, h0⟩',
        '  · dsimp only [classes] at h','    rw [if_neg h0] at h',
        '    split_ifs at h with h1',
        '    · have hh := congrArg Fin.val h; norm_num at hh',
        '    · have hh := congrArg Fin.val h; norm_num at hh',
        'theorem one_bounds {g : Fin 7 → ℝ} (i : Fin 7) (h : classes g i = 1) :',
        '    (3 / 2 : ℝ) ≤ g i ∧ g i ≤ (5 / 2 : ℝ) := by',
        '  by_cases h0 : g i ≤ (3 / 2 : ℝ)',
        '  · simp [classes, h0] at h',
        '  · by_cases h1 : g i ≤ (5 / 2 : ℝ)',
        '    · exact ⟨(lt_of_not_ge h0).le, h1⟩',
        '    · simp [classes, h0, h1] at h']
    for s,row in sorted(base.items()):
        w=[(s>>i)&1 for i in range(7)];code=sum(v*3**i for i,v in enumerate(w));u=row[0]+delta.get(code,0)
        lines += [f'def state{s} : Fin 7 → Fin 3 := !['+', '.join(map(str,w))+']',
            f'def affine{s} (g : Fin 7 → ℝ) : ℝ :=']
        terms=[real(u,den)]+[real(v,den)+f' * (g {i} - '+(['(26 / 25 : ℝ)','(197 / 100 : ℝ)'][w[i]])+')' for i,v in enumerate(row[1:]) if v]
        lines.append('  '+' +\n    '.join(terms))
        lines += [f'theorem affine{s}_bounds {{g : Fin 7 → ℝ}}',
            '    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)',
            f'    (h : classes g = state{s}) :',
            f'    -(133 / 100000 : ℝ) ≤ affine{s} g ∧ affine{s} g ≤ (143 / 100000 : ℝ) := by']
        for i,v in enumerate(w):
            lines += [f'  have hc{i} : classes g {i} = ({v} : Fin 3) := by',
                f'    simpa [state{s}] using congrFun h ({i} : Fin 7)',
                (f'  have h{i} := zero_bounds hg ({i} : Fin 7) hc{i}' if v==0 else f'  have h{i} := one_bounds ({i} : Fin 7) hc{i}')]
        lines += [f'  unfold affine{s}','  constructor <;> linarith only ['+', '.join(f'h{i}.{v}' for i in range(7) for v in [1,2])+']']
    lines += ['def V (g : Fin 7 → ℝ) : ℝ :=']
    for ix,s in enumerate(sorted(base)):
        lines.append(f'  {"if" if ix==0 else "else if"} classes g = state{s} then affine{s} g')
    lines += ['  else delta (ternaryCode (classes g))',
        'theorem V_bounds (g : Fin 7 → ℝ) (hg : ∀ i, (17 / 20 : ℝ) ≤ g i) :',
        '    -(133 / 100000 : ℝ) ≤ V g ∧ V g ≤ (143 / 100000 : ℝ) := by',
        '  unfold V','  split_ifs with '+' '.join('h'+str(s) for s in sorted(base))]
    for s in sorted(base):lines.append(f'  · exact affine{s}_bounds hg h{s}')
    lines += ['  · exact delta_bounds _',
        'theorem V_oscillation {g h : Fin 7 → ℝ}',
        '    (hg : ∀ i, (17 / 20 : ℝ) ≤ g i) (hh : ∀ i, (17 / 20 : ℝ) ≤ h i) :',
        '    V g - V h ≤ (69 / 25000 : ℝ) := by',
        '  have a := V_bounds g hg','  have b := V_bounds h hh','  linarith',
        'end OverlapPotential20261016',
        '#print axioms OverlapPotential20261016.V_bounds',
        '#print axioms OverlapPotential20261016.V_oscillation','']
    out=FOLDER.parent/'StructuralResearch20261016/PotentialRange.lean'
    out.write_text('\n'.join(lines),encoding='utf-8')
    print(out)

if __name__=='__main__':main()
