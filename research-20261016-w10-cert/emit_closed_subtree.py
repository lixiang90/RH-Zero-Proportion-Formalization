"""Emit an already closed numerical subtree with in-source certificate timing.

The source is an experiment only.  It never asserts the global W10 floor.
The existing closed search and compact payload files remain unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import emit_tree as emit
import ordered_generate as og

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE / 'ordered-0.json')
    parser.add_argument('--compact', type=Path, default=HERE / 'ordered-0-compact.json')
    parser.add_argument('--prefix', default='r0')
    parser.add_argument('--namespace', default='ClosedLowDomain')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = args.output or ROOT / ('StructuralW10Cert20261016/' + args.namespace + '.lean')
    raw = args.input.read_bytes()
    doc = json.loads(raw)
    packed_raw = args.compact.read_bytes()
    packed = json.loads(packed_raw)
    assert not doc['unresolved']
    assert packed['receipt']['input_closed']
    assert packed['receipt']['input_sha256'] == hashlib.sha256(raw).hexdigest()
    master = json.loads((HERE / 'ordered-master.json').read_text())
    branches = {a['path']: a for a in master['branches'] + doc['branches']}
    leaves = {a['path']: a for a in doc['accepted']}
    compact = {a['path']: a for a in packed['leaves']}
    initial = doc['root']
    path = 'r'
    for bit in args.prefix[1:]:
        normal, _ = og.normalize(initial)
        branch = branches[path]
        initial = og.rawsplit(normal, branch['axis'], branch['cut'], bit == '0')
        path += bit
    words, payloads, visited = [], [], set()
    maxdepth = 0

    def visit(path, state):
        nonlocal maxdepth
        assert path not in visited
        visited.add(path)
        maxdepth = max(maxdepth, len(path) - len(args.prefix))
        state, _ = og.normalize(state)
        if path in branches:
            branch = branches[path]
            words.append(128 * branch['cut'] + 2 * branch['axis'] + 1)
            visit(path + '0', og.rawsplit(state, branch['axis'], branch['cut'], True))
            visit(path + '1', og.rawsplit(state, branch['axis'], branch['cut'], False))
        else:
            original = leaves[path]['result']['certificate']
            assert state == (original['lower_bounds'], original['upper_bounds']), path
            leaf = compact[path]
            if leaf['kind'] == 'numeric':
                word = int(leaf['support_hex'], 16) * 10**8 + leaf['tree_code']
                ident = 46 + len(payloads)
                payloads.append(word)
            elif leaf['kind'] == 'reflection':
                ident = 0
            else:
                assert leaf['kind'] == 'empty'
                ident = 1 + leaf['violation_axis']
            words.append(2 * ident)

    visit(args.prefix, initial)
    fmt = lambda ns: '[' + ', '.join(map(str, ns)) + ']'
    sl = [og.g.LOOK.get((min(i, j), max(i, j)), 0) for i in range(10) for j in range(10)]
    out = ['''/- Closed subtree experiment only; no global W10 floor is asserted. -/
import StructuralW10Cert20261016.ForcedCoverage
import StructuralW10Cert20261016.FastPruefer
set_option Elab.async false
elab "#w10_timing" label:str : command => do
  let tick ← IO.monoMsNow
  Lean.logInfo m!"W10_TIMING {label.getString} {tick}"
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
set_option maxHeartbeats 0
set_option maxRecDepth 100000
''', 'namespace StructuralW10Cert20261016.' + args.namespace + '\n',
           '-- original subtree ' + args.prefix + '\n',
           'def initialCell : Cl := ⟨' + ', '.join(map(fmt, [initial[0][:9], initial[1][:9], initial[0][9:], initial[1][9:]])) + '⟩\n',
           'def SL : List ℕ := ' + str(sl) + '\n',
           'theorem hSL : SLok 9 PR SL := by decide +kernel\n']
    names = []
    for k, start in enumerate(range(0, len(words), 32)):
        word = sum(w << (28 * r) for r, w in enumerate(words[start:start + 32]))
        name = 'T' + str(k)
        names.append(name)
        out.append(f'def {name} : ℕ := ~"{emit.encode(word)}"\n')
    out.append(f'def treeChunk (n : ℕ) : ℕ := {emit.balanced(names)}\n')
    out.append('def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455\n')
    names = []
    for k, start in enumerate(range(0, len(payloads), 32)):
        word = offset = 0
        for n in payloads[start:start + 32]:
            bits = n.bit_length()
            assert bits < 2048
            word |= bits << offset
            offset += 11
            word |= n << offset
            offset += bits
        name = 'D' + str(k)
        names.append(name)
        out.append(f'def {name} : ℕ := ~"{emit.encode(word)}"\n')
    out.append(f'def payloadChunk (n : ℕ) : ℕ := {emit.balanced(names)}\n')
    out.append('''def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
def leafCheck := FastPruefer.dispatch payload
#w10_timing "certificate_begin"
''')
    out.append(f'''theorem checked : ForcedCoverage.walk SL read leafCheck 128 1 initialCell = {len(words)+1} := by
  decide +kernel
#w10_timing "certificate_end"
theorem covered : CovBy 9 PR (Pg cN 9 BS TS) initialCell := by
  apply ForcedCoverage.walk_sound hSL read leafCheck (FastPruefer.dispatch_sound payload) 128 1 initialCell
  rw [checked]
  decide
#w10_timing "soundness_end"
#print axioms covered
end StructuralW10Cert20261016.{args.namespace}
end
''')
    source = ''.join(out).encode('utf8')
    output.write_bytes(source)
    receipt = {'scope': 'Generated closed-subtree source; compilation and proof replay remain required.',
               'input_sha256': hashlib.sha256(raw).hexdigest(),
               'compact_input_sha256': hashlib.sha256(packed_raw).hexdigest(),
               'prefix': args.prefix, 'nodes': len(words), 'numeric_leaves': len(payloads),
               'max_relative_depth': maxdepth, 'source': str(output),
               'source_bytes': len(source), 'source_sha256': hashlib.sha256(source).hexdigest(),
               'lean_passed': False}
    (HERE / (args.namespace + '-generated.json')).write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf8')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
