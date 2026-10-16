"""Emit only the frozen r0010 subtree as independent W10 aux declarations.

127 numerical leaves are grouped in at most 32 leaves per module. Geometry
groups have at most eight branches and 26 equality declarations. No walk
over the complete subtree is evaluated in one Boolean proof.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
from window_moment_frozen_write import write_lean

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--only',action='append',help='Regenerate only a named new module; keep all siblings byte-identical.')
args=ap.parse_args()
PREFIX='r0010'
NS='StructuralGoal20261016.W10Aux127'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
seed_raw=(HERE/'lean_aux127_seed.json.gz').read_bytes()
assert sha(seed_raw)=='45daa14583de36bf9185d51413ae38804b5bcdbb188be47b790ba09f59b9137a'
seed=json.loads(gzip.decompress(seed_raw))
assert seed['prefix']==PREFIX
assert seed['provenance_tree_sha256']=='6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e'
assert seed['provenance_compact_sha256']=='5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463'
assert seed['provenance_old_source_sha256']=='d9d834f81cb334fca36dc5794f0560c611acb2ea139ce7289b933d336ecad271'


class Geometry:
    """Untrusted materializer; all its outputs are independently checked in Lean."""
    PAIRS=[(i,i+1)for i in range(9)]+[(i,j)for i in range(10)for j in range(i+2,10)]
    SLOTS={p:k for k,p in enumerate(PAIRS)}
    BB=1<<42

    @classmethod
    def split(cls,state,axis,cut,upper):
        lo,hi=state;i,j=cls.PAIRS[axis]
        a,b,w=(i,j,cut)if upper else(j,i,-cut)
        def leg(x,y):
            return 0 if x==y else hi[cls.SLOTS[x,y]]if x<y else-lo[cls.SLOTS[y,x]]
        col=[max(0,cls.BB+leg(x,a))for x in range(10)]
        row=[max(0,cls.BB+w+leg(b,x))for x in range(10)]
        return ([max(v,max(0,2*cls.BB-col[j]-row[i]))for v,(i,j)in zip(lo,cls.PAIRS)],
                [min(v,max(0,col[i]+row[j]-2*cls.BB))for v,(i,j)in zip(hi,cls.PAIRS)])

    @classmethod
    def normalize(cls,state):
        if state[1][0]<=state[1][8]and state[0][0]<=state[0][8]:
            return state
        for _ in range(2):
            state=cls.split(state,0,state[1][8],True)
            state=cls.split(state,8,state[0][0],False)
        return state

    @staticmethod
    def cl(state):
        fmt=lambda xs:'['+', '.join(map(str,xs))+']'
        return '⟨'+', '.join(map(fmt,[state[0][:9],state[1][:9],state[0][9:],state[1][9:]]))+'⟩'


old=Geometry
branches={r['path']:r for r in seed['branches']}
leaves={r['path']:r for r in seed['leaves']}
states={'r':seed['root']};normal={};children={};ancestors=[]


def expand(path):
    row=branches[path];norm=old.normalize(states[path]);normal[path]=norm
    children[path]=(old.split(norm,row['axis'],row['cut'],True),
                    old.split(norm,row['axis'],row['cut'],False))
    states[path+'0'],states[path+'1']=children[path]


for n in range(1,len(PREFIX)):
    p=PREFIX[:n];ancestors.append(p);expand(p)
nodes=[];numeric=[]


def visit(path):
    nodes.append(path)
    if path in branches:
        expand(path);visit(path+'0');visit(path+'1')
    else:
        assert leaves[path]['kind']=='numeric'
        normal[path]=old.normalize(states[path]);numeric.append(path)


visit(PREFIX)
assert len(numeric)==127 and len(nodes)==253 and len(ancestors)==4
literal=old.cl(states[PREFIX])
assert literal==seed['selected_cell_literal']
names={p:f'cell{i:03d}' for i,p in enumerate(states)}
norm_names={p:f'normal{i:03d}' for i,p in enumerate(normal)}
opts='''set_option Elab.async false
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
modules=[]


def emit(suffix,imports,body,roots=(),**extra):
    name='W10Aux127'+suffix;module='StructuralGoal20261016.'+name
    source='/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/\n'
    source+=''.join('import '+i+'\n' for i in imports)+opts+'namespace '+NS+'\n'+body
    source+='\nset_option pp.fullNames true\n'+''.join('#print axioms '+r+'\n' for r in roots)
    source+='end '+NS+'\nend\n'
    path=ROOT/(module.replace('.','/')+'.lean')
    if not args.only or name in args.only or module in args.only:
        write_lean(path,source)
    assert path.exists(),name
    modules.append({'module':module,'source':path.relative_to(ROOT).as_posix(),
        'source_sha256':sha(path.read_bytes()),'source_bytes':path.stat().st_size,
        'roots':[NS+'.'+r for r in roots],**extra})


data=[]
for p,state in states.items():
    data += [f'-- Frozen path {p}\n',f'def {names[p]} : Cl := {old.cl(state)}\n']
for p,state in normal.items():
    data += [f'-- Normalized path {p}\n',f'def {norm_names[p]} : Cl := {old.cl(state)}\n']
data.append(f'def selectedCell : Cl := {names[PREFIX]}\n')
payloads=[]
for i,p in enumerate(numeric):
    row=leaves[p];word=int(row['support_hex'],16)*10**8+row['tree_code'];payloads.append(word)
    data.append(f'def payload{i:03d} : ℕ := {word}\n')
emit('Data',['StructuralGoal20261016.LeanCoverBase','StructuralW10Cert20261016.RootBounds'],''.join(data),kind='data')


def norm_proof(p):
    c,n=names[p],norm_names[p]
    return f'''  calc
    AdaptiveCoverage.normalize SL {c} =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl {c})).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl {c})).symm
    _ = {n} := by rfl
'''


leaf_modules=[]
for group,start in enumerate(range(0,127,32)):
    body=[];roots=[]
    for i in range(start,min(start+32,127)):
        p=numeric[i];c,n=names[p],norm_names[p]
        body.append(f'''theorem normalizedLeaf{i:03d} : AdaptiveCoverage.normalize SL {c} = {n} := by
{norm_proof(p)}
theorem numeric{i:03d} : ForcedCoverage2.dispatch (fun _ => payload{i:03d}) {n} 46 = true := by
  decide +kernel

theorem coveredLeaf{i:03d} : CovBy 9 PR (Pg cN 9 BS TS) {c} := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf{i:03d}]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload{i:03d}) {n} 46 numeric{i:03d}
''')
        roots += [f'normalizedLeaf{i:03d}',f'numeric{i:03d}',f'coveredLeaf{i:03d}']
    suffix=f'Leaves{group:02d}';leaf_modules.append('StructuralGoal20261016.W10Aux127'+suffix)
    emit(suffix,['StructuralGoal20261016.W10Aux127Data'],''.join(body),roots,
         kind='numeric_aux',leaf_start=start,leaf_count=min(32,127-start))

branch_paths=ancestors+[p for p in nodes if p in branches]
branch_ids={p:i for i,p in enumerate(branch_paths)}
assert len(branch_paths)==130
geometry_modules=[]
for group,start in enumerate(range(0,len(branch_paths),8)):
    body=[];roots=[]
    if group==0:
        body += [f'theorem root_eq : {names["r"]} = RootBounds.initialCell := by rfl\n',
                 f'theorem same_frozen_cell : selectedCell = {literal} := by rfl\n']
        roots += ['root_eq','same_frozen_cell']
    for p in branch_paths[start:start+8]:
        k=branch_ids[p];c,n=names[p],norm_names[p]
        row=branches[p];i,j=old.PAIRS[row['axis']];q=row['cut']
        body.append(f'theorem normalized{k:03d} : AdaptiveCoverage.normalize SL {c} = {n} := by\n'+norm_proof(p))
        roots.append(f'normalized{k:03d}')
        for hand in ['left','right']:
            target=names[p+('0' if hand=='left' else '1')]
            body.append(f'''theorem {hand}{k:03d} : {hand}Child 9 PR SL {n} {i} {j} {q} = {target} := by
  calc
    {hand}Child 9 PR SL {n} {i} {j} {q} =
        (FixedGeometry.{hand} SL (FixedGeometry.Cell.ofCl {n}) {i} {j} {q}).toCl :=
      (FixedGeometry.{hand}_eq SL (FixedGeometry.Cell.ofCl {n}) {i} {j} {q}).symm
    _ = {target} := by rfl
''')
            roots.append(f'{hand}{k:03d}')
    suffix=f'Geometry{group:02d}';geometry_modules.append('StructuralGoal20261016.W10Aux127'+suffix)
    assert len(roots)<=26
    emit(suffix,['StructuralGoal20261016.W10Aux127Data'],''.join(body),roots,
         kind='geometry_aux',branch_start=start,branch_count=min(8,len(branch_paths)-start),
         equality_count=len(roots))

coverage={p:f'coveredLeaf{i:03d}' for i,p in enumerate(numeric)}
body=[]


def branch_term(p,left,right):
    k=branch_ids[p];row=branches[p];i,j=old.PAIRS[row['axis']]
    return f'branch {i} {j} {row["cut"]} (by decide) (by decide) normalized{k:03d} left{k:03d} right{k:03d} {left} {right}'


for p in reversed(nodes):
    if p not in branches:
        continue
    name=f'coveredNode{branch_ids[p]:03d}'
    body.append(f'theorem {name} : CovBy 9 PR (Pg cN 9 BS TS) {names[p]} :=\n  '+branch_term(p,coverage[p+'0'],coverage[p+'1'])+'\n')
    coverage[p]=name
body.append(f'theorem selected_covered : CovBy 9 PR (Pg cN 9 BS TS) selectedCell := {coverage[PREFIX]}\n')
arguments=[];siblings=[]
for p in ancestors:
    chosen=PREFIX[len(p)];other=p+('1' if chosen=='0' else '0');name=f'sibling{branch_ids[p]:03d}'
    arguments.append(f'    ({name} : CovBy 9 PR (Pg cN 9 BS TS) {names[other]})')
    siblings.append({'path':other,'hypothesis':name});coverage[other]=name
body.append('theorem root_covered_of_siblings\n'+'\n'.join(arguments)+
            '\n    : CovBy 9 PR (Pg cN 9 BS TS) RootBounds.initialCell := by\n')
for p in reversed(ancestors):
    name=f'route{branch_ids[p]:03d}'
    body.append(f'  have {name} : CovBy 9 PR (Pg cN 9 BS TS) {names[p]} :=\n    '+branch_term(p,coverage[p+'0'],coverage[p+'1'])+'\n')
    coverage[p]=name
body.append(f'  simpa only [root_eq] using {coverage["r"]}\n')
emit('Cover',leaf_modules+geometry_modules,''.join(body),['selected_covered','root_covered_of_siblings'],kind='composition')
out={'scope':__doc__,'generator_sha256':sha(Path(__file__).read_bytes()),'prefix':PREFIX,
     'old_unpassed_monolithic_source_sha256':seed['provenance_old_source_sha256'],
     'tree_sha256':seed['provenance_tree_sha256'],'compact_sha256':seed['provenance_compact_sha256'],
     'self_contained_seed_sha256':sha(seed_raw),'self_contained_seed_bytes':len(seed_raw),
     'seed_mathematical_data_trusted':False,'numeric_leaves':127,'subtree_nodes':253,
     'subtree_branches':126,'ancestor_branches':4,'max_leaf_group_size':32,
     'max_geometry_equality_count':max(m.get('equality_count',0)for m in modules),
     'unproved_root_sibling_hypotheses':siblings,'modules':modules,
     'numeric_leaf_paths':numeric,'ordinary_Lean_verified':False,
     'complete_W10_cover':False,'source_size_compliant':False,'new_zero_proportion_proven':False}
(HERE/'lean_aux127_generated.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'modules':len(modules),'numeric_leaves':127,'subtree_branches':126,
                  'max_leaf_group_size':32,'max_geometry_equalities':out['max_geometry_equality_count'],
                  'source_bytes':sum(m['source_bytes']for m in modules)}))
