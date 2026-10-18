"""Preserve Phase2 and prepare a Final-only, same-statement name repair."""
from pathlib import Path
import hashlib, json, difflib

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent

def row(p):
    raw = p.read_bytes()
    return dict(path=p.relative_to(ROOT).as_posix(), bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())

def put(p, raw):
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f:
        f.write(raw if isinstance(raw, bytes) else raw.encode())

def dump(p, value):
    put(p, json.dumps(value, indent=2) + '\n')

p2 = json.loads((HERE/'phase2-prepared.json').read_bytes())
terminal = ROOT/'tmp/current-s1r-tiny-20261018/phase2-v0/terminal.json'
assert json.loads(terminal.read_bytes())['passed'] is False
count = json.loads((terminal.parent/'Counting.receipt.json').read_bytes())
assert count['ordinary_compile_passed'] and count['axiom_audit_passed']
old = (ROOT/'StructuralS1RTiny20261018/Phase2/Final.lean').read_text(encoding='utf-8')
start = old.index('  simpa only [StructuralS1RTiny20261018.Counting.leftGaps,')
end = old.index('\nprivate theorem ratio_exact', start)
new_pair = '''  have hl : StructuralS1RTiny20261018.Counting.leftGaps g =
      StructuralS1RTiny20261018.Dev.Localization.leftGaps g := by
    funext r
    rfl
  have hr : StructuralS1RTiny20261018.Counting.rightGaps g =
      StructuralS1RTiny20261018.Dev.Localization.rightGaps g := by
    funext r
    rfl
  rw [hl, hr]
  exact StructuralS1RTiny20261018.Dev.Localization.pair_floor g hg
'''
new = old[:start] + new_pair + old[end:]
new = new.replace('(Ncount T (2*T) : ℝ)', '(_root_.Ncount T (2*T) : ℝ)').replace('≤ N0star T (2*T)', '≤ _root_.N0star T (2*T)')
new = new.replace('(Ncount 0 T : ℝ)', '(_root_.Ncount 0 T : ℝ)').replace('≤ N0star 0 T', '≤ _root_.N0star 0 T')
source = ROOT/'StructuralS1RTiny20261018/Phase3/Final.lean'
put(source, new)
diff = ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile='Phase2/Final.lean', tofile='Phase3/Final.lean'))
put(HERE/'phase3-final.diff', diff)
runner = (HERE/'compile_phase2.py').read_text(encoding='utf-8')
runner = runner.replace('One gated Tiny Counting let/cast API-repair compile; reuse all three proved dependencies.', 'One gated Final-only function/name repair; reuse all four proved dependencies.')
runner = runner.replace('phase2-v0', 'phase3-v0').replace('phase2-prepared.json', 'phase3-prepared.json').replace('tiny-current-s1R-counting-phase2', 'tiny-current-s1R-final-phase3')
runner = runner.replace("'all_two_modules_completed':len(receipts)==2", "'all_one_module_completed':len(receipts)==1").replace('passed and len(receipts)==2', 'passed and len(receipts)==1')
put(HERE/'compile_phase3.py', runner)
target = dict(p2['targets'][1])
target['module'] = 'StructuralS1RTiny20261018/Phase3/Final'
count_olean = ROOT/'tmp/current-s1r-tiny-20261018/phase2-v0/lib/StructuralS1RTiny20261018/Phase2/Counting.olean'
assert row(count_olean)['sha256'] == count['olean_sha256']
deps = [ROOT/x['path'] for x in p2['dependencies']]
deps += [ROOT/'StructuralS1RTiny20261018/Phase2/Final.lean', HERE/'phase2-prepared.json', terminal,
         terminal.parent/'Counting.receipt.json', terminal.parent/'Final.receipt.json',
         terminal.parent/'Final.log', count_olean]
deps = list(dict.fromkeys(deps))
reuse = list(p2['reused_oleans']) + [dict(row(count_olean), relative_module_path='StructuralS1RTiny20261018/Phase2/Counting.olean')]
gate = dict(json.loads((HERE/'phase2-gate-template.json').read_bytes()))
gate.update(task='tiny-current-s1R-final-phase3', allowed_modules=[target['module']])
dump(HERE/'phase3-gate-template.json', gate)
prep = dict(schema='tiny-final-function-and-counting-name-repair-phase3-v1',
    files=[row(p) for p in [source, Path(__file__), HERE/'compile_phase3.py', HERE/'phase3-final.diff', HERE/'phase3-gate-template.json']],
    dependencies=[row(p) for p in deps], targets=[target], reused_oleans=reuse,
    Python_executable=p2['Python_executable'], external_Linux_pins=p2['external_Linux_pins'],
    same_mathematical_statements=True, constants_tree_model_and_witnesses_changed=False,
    only_explicit_function_equality_and_root_name_qualification=True,
    automatic_repairs_or_retries=0, Lean_runs=0)
dump(HERE/'phase3-prepared.json', prep)
print(json.dumps(row(HERE/'phase3-prepared.json')))
