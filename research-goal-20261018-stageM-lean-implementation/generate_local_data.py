"""Deterministic literal conversion of the frozen M certificate, not discovery."""
from fractions import Fraction
import hashlib
import json
from math import lcm
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
INPUT = ROOT / 'research-goal-20261018-stageM-component-envelope-preparation'
OUT = ROOT / 'StructuralS1RM20261018'
PINS = {
    'model.json': '9a47b54d54995fe8565b27c4268368f8779a2cbb9bc22b9fdbd09a7a4fc6d04a',
    'certificate.json': '8b9d10c8553c0b70ff8937145028a9cdd6226587d264f4ffd064dae7ad841fb9',
}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def emit(path, text):
    with path.open('x', encoding='utf-8', newline='\n') as f:
        f.write(text)


def nlist(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def int_lit(x):
    return '(' + str(x) + ')' if x < 0 else str(x)


def main():
    for name, h in PINS.items():
        assert sha(INPUT / name) == h
    m = json.loads((INPUT / 'model.json').read_text(encoding='utf-8'))
    c = json.loads((INPUT / 'certificate.json').read_text(encoding='utf-8'))
    mus = list(map(Fraction, c['raw_row_weights']))
    ids = [i for i, mu in enumerate(mus) if mu > 0]
    assert len(ids) == 77 and all(mu >= 0 for mu in mus)
    den = lcm(*(mus[i].denominator for i in ids))
    weights = [int(mus[i] * den) for i in ids]
    rows = [m['rows'][i] for i in ids]
    objective = m['objective_position10'] + m['objective_epigraph68']
    # Conversion identity only: no optimization or different certificate.
    for j in range(78):
        s = den * objective[j]
        for r, w in zip(rows, weights):
            a = r['position10'][j] if j < 10 else (
                r['epigraph_coefficient'] if r['epigraph_index'] == j - 10 else 0)
            s += w * a
        assert s == 0
    assert den * int(m['target']) + sum(w * r['bound'] for r, w in zip(rows, weights)) <= 0
    text = '''import StructuralS1RM20261018.Sparse78
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open StructuralS1RM20261018.Sparse78
namespace StructuralS1RM20261018.LocalData
-- Literal conversion of the independently replayed frozen M certificate only.
'''
    for k, r in enumerate(rows):
        entries = [(j, a) for j, a in enumerate(r['position10']) if a]
        if r['epigraph_index'] is not None:
            entries.append((10 + r['epigraph_index'], r['epigraph_coefficient']))
        estr = ', '.join('(⟨' + str(j) + ', by decide⟩, ' + int_lit(a) + ')' for j, a in entries)
        text += f'def row{k} : Row := ⟨[{estr}], {int_lit(r["bound"])}⟩\n'
    text += '\ndef rows (i : Fin 77) : Row :=\n  match i.val with\n'
    text += ''.join(f'  | {k} => row{k}\n' for k in range(76)) + '  | _ => row76\n'
    text += '\ndef weights (i : Fin 77) : ℕ :=\n  match i.val with\n'
    text += ''.join(f'  | {k} => {w}\n' for k, w in enumerate(weights[:-1]))
    text += f'  | _ => {weights[-1]}\n'
    text += f'\ndef den : ℕ := {den}\ndef target : ℤ := {m["target"]}\n'
    text += '\ndef objective (j : Fin 78) : ℤ :=\n  match j.val with\n'
    text += ''.join(f'  | {j} => {int_lit(a)}\n' for j, a in enumerate(objective[:-1]))
    text += f'  | _ => {int_lit(objective[-1])}\n\n'
    for j in range(78):
        text += f'theorem balance{j} : (den : ℤ) * objective ⟨{j}, by decide⟩ +\n'
        text += f'    ∑ i : Fin 77, (weights i : ℤ) * coefficient (rows i) ⟨{j}, by decide⟩ = 0 := by\n  decide +kernel\n'
    text += '\ntheorem balanced (j : Fin 78) : (den : ℤ) * objective j +\n'
    text += '    ∑ i : Fin 77, (weights i : ℤ) * coefficient (rows i) j = 0 := by\n  fin_cases j\n'
    text += ''.join(f'  · exact balance{j}\n' for j in range(78))
    text += '''
theorem cost : (den : ℤ) * target +
    ∑ i : Fin 77, (weights i : ℤ) * (rows i).rhs ≤ 0 := by
  decide +kernel
theorem checked : check rows weights den objective target = true := by
  apply of_decide_eq_true
  exact ⟨by decide, balanced, cost⟩
set_option pp.fullNames true
#print axioms balanced
#print axioms cost
#print axioms checked
end StructuralS1RM20261018.LocalData
end
'''
    emit(OUT / 'LocalData.lean', text)
    # Geometry and term identities are separate from the numerical dual check.
    t = '''import StructuralS1RM20261018.QuantizedComponent
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.PCell AMW.Cert.Pyr AMW.Cert.PyrD
namespace StructuralS1RM20261018.LocalGeometry
'''
    for w, name in [(0, 'leftCell'), (1, 'rightCell')]:
        rr = m['rows'][w * 72:(w + 1) * 72]
        lows = [-rr[2*k+1]['bound'] // 20 for k in range(36)]
        ups = [rr[2*k]['bound'] // 20 for k in range(36)]
        assert all(rr[2*k]['bound'] == 20*ups[k] and rr[2*k+1]['bound'] == -20*lows[k] for k in range(36))
        t += f'def {name} : Cl := ⟨{nlist(lows[:8])}, {nlist(ups[:8])}, {nlist(lows[8:])}, {nlist(ups[8:])}⟩\n'
    t += '''
def canonicalGap (P : ℕ → ℝ) (rev : Bool) (r : ℕ) : ℝ :=
  if rev then
    [P 9-P 8, P 8-P 7, P 7-P 6, P 6-P 5, P 5-P 4, P 4-P 3, P 3-P 2, P 2-P 1].getD r 0
  else
    [P 1-P 0, P 2-P 1, P 3-P 2, P 4-P 3, P 5-P 4, P 6-P 5, P 7-P 6, P 8-P 7].getD r 0

structure Domain (P : ℕ → ℝ) : Prop where
  left : InCell 8 AMW.Cert.PC9QB6M.PR leftCell (canonicalGap P false)
  right : InCell 8 AMW.Cert.PC9QB6M.PR rightCell (canonicalGap P true)
  separated : ∀ r < 9, (17 : ℝ)/20 ≤ P (r+1)-P r
  orderedLeft : P 1-P 0 ≤ P 8-P 7
  orderedRight : P 9-P 8 ≤ P 2-P 1

theorem canonical_span (P : ℕ → ℝ) (rev : Bool) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ 8) :
    gsum (canonicalGap P rev) i j =
      if rev then P (9-i)-P (9-j) else P j-P i := by
  have hi : i ≤ 8 := hij.trans hj
  cases rev <;> interval_cases j <;> interval_cases i <;>
    norm_num [canonicalGap, gsum_range, Finset.sum_range_succ] at * <;> ring
'''
    for term in m['terms']:
        e = term['term']; w = term['window']; i, j = term['original_span']
        cell = 'leftCell' if w == 0 else 'rightCell'
        rev = 'false' if w == 0 else 'true'
        L0 = term['original_L0']; L, U = term['original_bounds']; pi, pj = term['physical_span']
        t += f'\ntheorem numeric{e} : eL0 AMW.Cert.PC9QB6M.TS {cell} {e%34} = {L0} ∧\n'
        t += f'    eL AMW.Cert.PC9QB6M.TS {cell} {e%34} = {L} ∧\n'
        t += f'    eU AMW.Cert.PC9QB6M.TS {cell} {e%34} = {U} ∧\n'
        t += f'    tI AMW.Cert.PC9QB6M.TS {e%34} = {i} ∧ tJ AMW.Cert.PC9QB6M.TS {e%34} = {j} := by decide +kernel\n'
        t += f'theorem range{e} (P : ℕ → ℝ) (h : Domain P) :\n'
        t += f'    ({L} : ℝ)/SC ≤ P {pj}-P {pi} ∧ P {pj}-P {pi} ≤ ({U} : ℝ)/SC := by\n'
        t += f'  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.{"left" if w==0 else "right"} (n := {e%34}) (by decide)\n'
        t += f'  rcases numeric{e} with ⟨ha, hb, hc, hi, hj⟩\n  rw [ha, hb, hc, hi, hj] at hr\n'
        t += f'  rw [canonical_span P {rev} {i} {j} (by decide) (by decide)] at hr\n'
        t += '  exact hr.2\n'
    t += '\nset_option pp.fullNames true\n#print axioms canonical_span\n#print axioms range0\n#print axioms range67\nend StructuralS1RM20261018.LocalGeometry\nend\n'
    emit(OUT / 'LocalGeometry.lean', t)
    record = {
        'schema': 'M-frozen-certificate-literal-conversion-v1',
        'input_sha256': PINS, 'positive_original_row_ids': ids,
        'positive_rows': len(ids), 'denominator': str(den),
        'files': [{'path': p.relative_to(ROOT).as_posix(), 'bytes': p.stat().st_size,
                   'sha256': sha(p)} for p in [OUT/'LocalData.lean', OUT/'LocalGeometry.lean']],
        'Lean_runs': 0, 'new_solver_calls': 0, 'new_FS_or_anchor_or_kernel': 0,
        'scope': 'uncompiled local source; no full-cover claim',
    }
    emit(HERE / 'local-data-prepared.json', json.dumps(record, indent=2) + '\n')
    print(json.dumps(record['files']))


if __name__ == '__main__':
    main()
