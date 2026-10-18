"""Deterministic source-text-only tiny Core conversion, never runs Lean/math.

Separate root authorization is required before invoking --generate-once.
Frozen accepted source and payloads are read-only. No leaf parser is imported.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import difflib
import json
import os
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT / 'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_SHA = 'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
EXCEPTION = ROOT / 'research-goal-20261018-tiny-overlap-independent/unique-exception.json'
EXCEPTION_SHA = '3904ff3b5b0e4867fdb9354c6b8232ede49cde102036f513a10467ac96f0327a'
CORE = ROOT / 'StructuralS1RTiny20261018/Core.lean'

def pin(data): return sha256(data).hexdigest()
def write(path, data):
    with path.open('xb') as handle: handle.write(data); handle.flush(); os.fsync(handle.fileno())
def replace_once(text, old, new):
    assert text.count(old) == 1, ('unique_text_anchor', old[:120], text.count(old))
    return text.replace(old, new, 1)
def block(text, start, end):
    assert text.count(start) == text.count(end) == 1, (start, end)
    lo, hi = text.index(start), text.index(end)
    assert lo < hi
    return text[lo:hi]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--generate-once', action='store_true'); args = ap.parse_args()
    assert args.generate_once, 'separate root authorization is required'
    for path in [CORE, HERE/'generation.json', HERE/'Core.diff']:
        assert not path.exists(), ('no_overwrite_or_retry', str(path))
    raw = SOURCE.read_bytes(); eraw = EXCEPTION.read_bytes()
    assert pin(raw) == SOURCE_SHA and pin(eraw) == EXCEPTION_SHA
    original = raw.decode('utf-8'); text = original; exception = json.loads(eraw)
    assert exception['root'] == 11 and exception['position'] == 27229 and exception['end'] == 27674
    assert exception['exception_id'] == 462 and exception['coordinate_scale'] == 32768
    state = exception['state']; assert len(state['L']) == len(state['U']) == 8
    assert len(state['A']) == len(state['B']) == 28 and state['M'] == 0
    flat = [v for pair in zip(state['L'] + state['A'], state['U'] + state['B']) for v in pair] + [0]
    assert len(flat) == 73

    text = replace_once(text, 'noncomputable def cN : ℕ := 893616123055294719\n',
        'noncomputable def cN : ℕ := 893616123055294719\n'
        'noncomputable def tinyDeltaN : ℕ := 389500523\n'
        'noncomputable def tinyTauN : ℕ := cN + 2 * tinyDeltaN\n')
    text = replace_once(text, 'abbrev Covered : Cl → Prop := CovBy 8 PR (Pg cN 8 BS TS)\n', '')
    old_eq = block(text, 'noncomputable def stEq (a b : St)', 'theorem covered_of_walkCP')
    text = replace_once(text, old_eq, '')
    added = ('noncomputable def tinyExceptionState : St := ⟨' + ', '.join(map(str, flat)) + '⟩\n'
        'noncomputable def tinyExceptionCell : Cl := toCl tinyExceptionState\n' + old_eq +
        'noncomputable def tinyTarget (s : St) : ℕ :=\n'
        '  if stEq s tinyExceptionState = true then cN else tinyTauN\n'
        'noncomputable def TinyGoal (g : ℕ → ℝ) : Prop :=\n'
        '  Pg tinyTauN 8 BS TS g ∨ (InCell 8 PR tinyExceptionCell g ∧ Pg cN 8 BS TS g)\n'
        'abbrev Covered : Cl → Prop := CovBy 8 PR TinyGoal\n'
        'theorem tiny_forget {g : ℕ → ℝ} (h : TinyGoal g) : Pg cN 8 BS TS g := by\n'
        '  rcases h with h | h\n'
        '  · rcases h with h | h\n'
        '    · left\n'
        '      exact le_trans (by norm_num [cN, tinyTauN, tinyDeltaN]) h\n'
        '    · exact Or.inr h\n'
        '  · exact h.2\n'
        'theorem tiny_target_sound {s : St} {g : ℕ → ℝ}\n'
        '    (hg : InCell 8 PR (toCl s) g) (h : Pg (tinyTarget s) 8 BS TS g) : TinyGoal g := by\n'
        '  by_cases hs : stEq s tinyExceptionState = true\n'
        '  · have heq : s = tinyExceptionState := St_eq hs\n'
        '    right\n'
        '    refine ⟨?_, ?_⟩\n'
        '    · simpa only [tinyExceptionCell, heq] using hg\n'
        '    · simpa [tinyTarget, hs] using h\n'
        '  · left\n'
        '    simpa [tinyTarget, hs] using h\n')
    text = replace_once(text, 'abbrev ST : Type :=', added + 'abbrev ST : Type :=')
    text = replace_once(text, 'cov_splitB (P := Pg cN 8 BS TS)', 'cov_splitB (P := TinyGoal)')

    checker = block(text, 'noncomputable def mcheckP (top : ℕ)', 'theorem mcheckP_ok')
    assert len(re.findall(r'\bcN\b', checker)) == 1
    new_checker = replace_once(checker, 'def mcheckP (top : ℕ)', 'def mcheckP (goalN : ℕ) (top : ℕ)')
    new_checker = re.sub(r'\bcN\b', 'goalN', new_checker)
    text = replace_once(text, checker, new_checker)
    checker_proof = block(text, 'theorem mcheckP_ok ', 'noncomputable def mleafP ')
    new_checker_proof = replace_once(checker_proof, 'theorem mcheckP_ok ', 'theorem mcheckP_ok (goalN : ℕ) ')
    new_checker_proof = replace_once(new_checker_proof, 'mcheckP top bk', 'mcheckP goalN top bk')
    assert len(re.findall(r'\bcN\b', new_checker_proof)) == 1
    new_checker_proof = re.sub(r'\bcN\b', 'goalN', new_checker_proof)
    text = replace_once(text, checker_proof, new_checker_proof)

    leaf = block(text, 'noncomputable def mleafP ', '/- Eliminate forced decoder values')
    new_leaf = replace_once(leaf, 'def mleafP (top : ℕ)', 'def mleafP (goalN : ℕ) (top : ℕ)')
    new_leaf = replace_once(new_leaf, 'mcheckP top bk', 'mcheckP goalN top bk')
    text = replace_once(text, leaf, new_leaf)
    leaf_proof = block(text, 'theorem mleafP_ok ', 'noncomputable def fleaf ')
    generic_leaf_proof = replace_once(leaf_proof, 'theorem mleafP_ok ', 'theorem mleafP_target_ok (goalN : ℕ) ')
    generic_leaf_proof = replace_once(generic_leaf_proof, 'mleafP top bk', 'mleafP goalN top bk')
    generic_leaf_proof = replace_once(generic_leaf_proof, ': Covered (toCl s) := by', ': CovBy 8 PR (Pg goalN 8 BS TS) (toCl s) := by')
    generic_leaf_proof = replace_once(generic_leaf_proof, '(mcheckP_ok _ ', '(mcheckP_ok goalN _ ')
    wrapper = ('theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}\n'
        '    {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}\n'
        '    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x))\n'
        '    (hR : rgOk R = true) (w : ℕ) (s : St)\n'
        '    (h : mleafP (tinyTarget s) top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by\n'
        '  intro g hg\n'
        '  exact tiny_target_sound hg (mleafP_target_ok (tinyTarget s) hlb hD hpt hR w s h g hg)\n')
    text = replace_once(text, leaf_proof, generic_leaf_proof + wrapper)
    step = block(text, 'noncomputable def leafStep ', 'theorem fleaf_ok ')
    pattern = r'mleafP top bk tD bD pb R \(Nat.shiftRight w 2\) (⟨[^⟩]+⟩)'
    matches = list(re.finditer(pattern, step)); assert len(matches) == 1
    state_literal = matches[0][1]
    step_new = re.sub(pattern, lambda m: 'mleafP (tinyTarget ' + state_literal + ') top bk tD bD pb R (Nat.shiftRight w 2) ' + state_literal, step)
    text = replace_once(text, step, step_new)
    step_proof = block(text, 'theorem leafStep_ok ', 'noncomputable def WMASK ')
    step_proof_new = replace_once(step_proof, 'mleafP top bk tD bD pb R (Nat.shiftRight w 2) s',
        'mleafP (tinyTarget s) top bk tD bD pb R (Nat.shiftRight w 2) s')
    step_proof_new = replace_once(step_proof_new, '  · intro g hg\n    right\n', '  · intro g hg\n    left\n    right\n')
    text = replace_once(text, step_proof, step_proof_new)
    cert_proof = block(text, 'theorem cert_of (cov ', '\nend AMW.Cert.PC9QB6M\n')
    cert_proof_new = replace_once(cert_proof, 'hwin W hW hrun\n',
        'hwin W hW (fun idx hi g hg => tiny_forget (hrun idx hi g hg))\n')
    text = replace_once(text, cert_proof, cert_proof_new)
    header = ('/- PREPARATION ONLY: deterministic tiny-exception Core variant.\n'
        'Current s1R kernel, W9 and all payloads retained. Numeric leaves use one\n'
        'targetN check; strengthened coverage retains the old c9 in the exception.\n'
        'No Lean execution has checked this variant. This is not a new accepted\n'
        'candidate; inherited final record theorems below still describe the baseline.\n'
        'The separated root-outside/dichotomy/pair root and final counting instance\n'
        'remain to be supplied without extra assumptions or placeholders.\n-/\n')
    text = header + text
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b', text)
    assert len(re.findall(r'^\s*axiom\s', text, re.M)) == len(re.findall(r'^\s*axiom\s', original, re.M)) == 0
    # Long literal declarations and all existing numerical ready/cursor calls
    # are byte-identical. This is not a proof that the latter still evaluate.
    def protected(s):
        return [line for line in s.splitlines() if ' := zfNat64 ' in line
                or re.match(r'noncomputable def (?:WL\d\w*|WD\d\w*|PTT\w*|COV|TOP\w*|BK\w*|REG|BND|BS|TS|PR)\b', line)
                or re.match(r'theorem ready.*_(?:cursor|parent_cursor)\s*:', line)]
    assert protected(text) == protected(original)
    data = text.encode('utf-8'); CORE.parent.mkdir(exist_ok=True)
    write(CORE, data)
    diff = ''.join(difflib.unified_diff(original.splitlines(keepends=True), text.splitlines(keepends=True),
        fromfile='accepted/Solution.lean', tofile='StructuralS1RTiny20261018/Core.lean'))
    write(HERE/'Core.diff', diff.encode('utf-8'))
    report = {'schema':'tiny-core-deterministic-source-text-conversion-v1','source_sha256_start':SOURCE_SHA,
        'source_sha256_end':pin(SOURCE.read_bytes()),'unique_exception_input_sha256':EXCEPTION_SHA,
        'generated_Core':{'path':CORE.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':pin(data)},
        'byte_change_from_accepted':len(data)-len(raw),'protected_source_lines_identical':True,
        'frozen_old_source_modified':False,'source_text_generation_only':True,'leaf_or_kernel_or_optimizer_or_Lean_runs':0,
        'ordinary_Lean_elaboration_or_final_source_acceptance_passed':False,
        'proofs_not_yet_kernel_checked':['tiny_target_sound','generic target mcheckP/mleafP','E logical split/cut/walk',
            'all original 48+70 new-target cursor theorems','E-forgetting original cert_AM'],
        'absent_new_theorems_not_stubbed':['sep root-outside lift','separated raised-or-exception dichotomy',
            'actual two-window pair-floor','Counting instance/final candidate wrapper']}
    assert report['source_sha256_end'] == SOURCE_SHA
    write(HERE/'generation.json', (json.dumps(report,indent=2)+'\n').encode('utf-8'))
    print(json.dumps(report))

if __name__ == '__main__': main()
