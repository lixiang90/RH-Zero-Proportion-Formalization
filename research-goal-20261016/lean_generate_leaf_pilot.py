"""Emit an eight-leaf W10 checkpoint pilot from the frozen complete tree.

No discovery or optimizer is run. Literal cells are untrusted, and each
normalization, split, and numeric leaf is an independent kernel obligation.
The only unconditional coverage theorem covers the selected subtree.
"""
from pathlib import Path
import hashlib
import importlib.util
import json

from window_moment_frozen_write import write_lean

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location('frozen_w10_generator', HERE/'lean_generate.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)

PREFIX = 'r0010110010111111'
NS = 'StructuralGoal20261016.W10LeafPilot'
sha = lambda raw: hashlib.sha256(raw).hexdigest()
tree_raw = (old.OLD/'ordered-proof-input.json').read_bytes()
compact_raw = (old.OLD/'ordered-compact.json').read_bytes()
assert sha(tree_raw) == '6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e'
assert sha(compact_raw) == '5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463'
tree = json.loads(tree_raw)
compact = json.loads(compact_raw)
assert not tree['unresolved'] and compact['receipt']['input_closed']
branches = {r['path']:r for r in tree['branches']}
leaves = {r['path']:r for r in compact['leaves']}
states = {'r':tree['root']}
normal = {}
children = {}
ancestors = []


def expand(path):
    row = branches[path]
    norm = old.normalize(states[path])
    normal[path] = norm
    children[path] = (old.split(norm,row['axis'],row['cut'],True),
                      old.split(norm,row['axis'],row['cut'],False))
    states[path+'0'],states[path+'1'] = children[path]


for n in range(1,len(PREFIX)):
    p = PREFIX[:n]
    ancestors.append(p)
    expand(p)

selected_nodes = []
selected_leaves = []


def visit(path):
    selected_nodes.append(path)
    if path in branches:
        expand(path)
        visit(path+'0')
        visit(path+'1')
    else:
        assert leaves[path]['kind'] == 'numeric'
        normal[path] = old.normalize(states[path])
        selected_leaves.append(path)


visit(PREFIX)
assert len(selected_leaves) == 8 and len(selected_nodes) == 15
names = {p:f'cell{i:03d}' for i,p in enumerate(states)}
norm_names = {p:f'normal{i:03d}' for i,p in enumerate(normal)}
opts = '''set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralGoal20261016.LeanCoverBase
open StructuralW10Unconditional20261016
open StructuralW10Cert20261016
'''
modules = []


def emit(suffix,imports,body,roots=()):
    module = 'StructuralGoal20261016.W10LeafPilot'+suffix
    source = '/- Eight-leaf pilot only; complete W10 coverage is not asserted. -/\n'
    source += ''.join('import '+i+'\n' for i in imports)+opts
    source += 'namespace '+NS+'\n'+body+'\nset_option pp.fullNames true\n'
    source += ''.join('#print axioms '+r+'\n' for r in roots)
    source += 'end '+NS+'\nend\n'
    path = ROOT/(module.replace('.','/')+'.lean')
    write_lean(path,source)
    modules.append({'module':module,'source':path.relative_to(ROOT).as_posix(),
                    'source_sha256':sha(path.read_bytes()),'source_bytes':path.stat().st_size,
                    'roots':[NS+'.'+r for r in roots]})


data = []
for p,state in states.items():
    data += [f'-- Frozen path {p}\n',f'def {names[p]} : Cl := {old.cl(state)}\n']
for p,state in normal.items():
    data += [f'-- Normalized path {p}\n',f'def {norm_names[p]} : Cl := {old.cl(state)}\n']
payloads = []
for i,p in enumerate(selected_leaves):
    row = leaves[p]
    word = int(row['support_hex'],16)*10**8+row['tree_code']
    payloads.append(word)
    data.append(f'def payload{i:02d} : ℕ := {word}\n')
emit('Data',['StructuralGoal20261016.LeanCoverBase','StructuralW10Cert20261016.RootBounds'],''.join(data))


def norm_proof(p):
    c,n = names[p],norm_names[p]
    return f'''  calc
    AdaptiveCoverage.normalize SL {c} =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl {c})).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl {c})).symm
    _ = {n} := by rfl
'''


for i,p in enumerate(selected_leaves):
    c,n = names[p],norm_names[p]
    body = f'''theorem normalizedLeaf{i:02d} : AdaptiveCoverage.normalize SL {c} = {n} := by
{norm_proof(p)}
theorem numeric{i:02d} : ForcedCoverage2.dispatch (fun _ => payload{i:02d}) {n} 46 = true := by
  decide +kernel

theorem coveredLeaf{i:02d} : CovBy 9 PR (Pg cN 9 BS TS) {c} := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf{i:02d}]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload{i:02d}) {n} 46 numeric{i:02d}
'''
    emit(f'Leaf{i:02d}',['StructuralGoal20261016.W10LeafPilotData'],body,
         [f'normalizedLeaf{i:02d}',f'numeric{i:02d}',f'coveredLeaf{i:02d}'])

geo = [f'theorem root_eq : {names["r"]} = RootBounds.initialCell := by rfl\n']
branch_paths = ancestors+[p for p in selected_nodes if p in branches]
branch_ids = {p:i for i,p in enumerate(branch_paths)}
for p,k in branch_ids.items():
    c,n = names[p],norm_names[p]
    left,right = names[p+'0'],names[p+'1']
    row = branches[p]
    i,j = old.PAIRS[row['axis']]
    q = row['cut']
    geo.append(f'theorem normalized{k:02d} : AdaptiveCoverage.normalize SL {c} = {n} := by\n'+norm_proof(p))
    for hand,target,op in [('left',left,'left'),('right',right,'right')]:
        geo.append(f'''theorem {hand}{k:02d} : {op}Child 9 PR SL {n} {i} {j} {q} = {target} := by
  calc
    {op}Child 9 PR SL {n} {i} {j} {q} =
        (FixedGeometry.{op} SL (FixedGeometry.Cell.ofCl {n}) {i} {j} {q}).toCl :=
      (FixedGeometry.{op}_eq SL (FixedGeometry.Cell.ofCl {n}) {i} {j} {q}).symm
    _ = {target} := by rfl
''')
emit('Geometry',['StructuralGoal20261016.W10LeafPilotData'],''.join(geo),
     ['root_eq']+[f'{s}{k:02d}' for k in branch_ids.values() for s in ['normalized','left','right']])

coverage = {p:f'coveredLeaf{i:02d}' for i,p in enumerate(selected_leaves)}
body = []


def branch_term(p,left,right):
    k = branch_ids[p]
    row = branches[p]
    i,j = old.PAIRS[row['axis']]
    return f'branch {i} {j} {row["cut"]} (by decide) (by decide) normalized{k:02d} left{k:02d} right{k:02d} {left} {right}'


for p in reversed(selected_nodes):
    if p not in branches:
        continue
    name = f'coveredNode{branch_ids[p]:02d}'
    body.append(f'theorem {name} : CovBy 9 PR (Pg cN 9 BS TS) {names[p]} :=\n  '+branch_term(p,coverage[p+'0'],coverage[p+'1'])+'\n')
    coverage[p] = name
body.append(f'theorem selected_covered : CovBy 9 PR (Pg cN 9 BS TS) {names[PREFIX]} := {coverage[PREFIX]}\n')
# This scaffold makes the root connection explicit, leaving all other
# sibling subtrees as named hypotheses. It does not prove their coverage.
arguments = []
siblings = []
for p in ancestors:
    chosen = PREFIX[len(p)]
    other = p+('1' if chosen=='0' else '0')
    name = f'sibling{branch_ids[p]:02d}'
    arguments.append(f'    ({name} : CovBy 9 PR (Pg cN 9 BS TS) {names[other]})')
    siblings.append({'path':other,'hypothesis':name})
    coverage[other] = name
body.append('theorem root_covered_of_siblings\n'+'\n'.join(arguments)+\
            '\n    : CovBy 9 PR (Pg cN 9 BS TS) RootBounds.initialCell := by\n')
for p in reversed(ancestors):
    name = f'route{branch_ids[p]:02d}'
    body.append(f'  have {name} : CovBy 9 PR (Pg cN 9 BS TS) {names[p]} :=\n    '+branch_term(p,coverage[p+'0'],coverage[p+'1'])+'\n')
    coverage[p] = name
body.append(f'  simpa only [root_eq] using {coverage["r"]}\n')
emit('Subtree',['StructuralGoal20261016.W10LeafPilotGeometry']+
     [f'StructuralGoal20261016.W10LeafPilotLeaf{i:02d}' for i in range(8)],
     ''.join(body),['selected_covered','root_covered_of_siblings'])

manifest = {'scope':__doc__,'generator_sha256':sha(Path(__file__).read_bytes()),
            'tree_sha256':sha(tree_raw),'compact_sha256':sha(compact_raw),
            'prefix':PREFIX,'selected_nodes':15,'selected_numeric_leaves':8,
            'ancestor_branches':len(ancestors),'subtree_branches':7,
            'leaves':[{'path':p,'payload_bits':w.bit_length(),'module':f'StructuralGoal20261016.W10LeafPilotLeaf{i:02d}'}
                      for i,(p,w) in enumerate(zip(selected_leaves,payloads))],
            'unproved_sibling_hypotheses':siblings,'modules':modules,
            'ordinary_Lean_verified':False,'complete_W10_cover':False,
            'source_size_compliant':False,'new_zero_proportion_proven':False}
(HERE/'lean_leaf_pilot_generated.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
print(json.dumps({'modules':len(modules),'leaves':8,'subtree_nodes':15,'ancestor_branches':len(ancestors),
                  'source_bytes':sum(m['source_bytes'] for m in modules)}))
