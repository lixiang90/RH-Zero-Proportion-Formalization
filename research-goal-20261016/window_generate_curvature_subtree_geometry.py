"""Bounded geometry checkpoints for the 24-OBBT local curvature subtree.

Intermediate matrices are untrusted data. Each single-edge closure is
checked on 100 entries before it can be used in the final fold identity.
This prevents a 14-deep functional closure from being recomputed as a tree.
"""
from pathlib import Path
import json
from window_generate_curvature_subtree import cell_lit,matrix,a,LCA
HERE=Path(__file__).parent;ROOT=HERE.parent

def main():
    doc=json.loads((HERE/'window_curvature_subtree_generation.json').read_bytes())
    text='''/- SPDX-License-Identifier: Apache-2.0
Ordinary-kernel geometry for 24 actual OBBT cuts and two branches.
Every intermediate matrix is checked entrywise, with no rounding assumption.
-/
import StructuralGoal20261016.WindowCurvatureSubtreeData
import StructuralGoal20261016.WindowCurvatureLeafData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureSubtreeGeometry
open WindowCurvatureSubtreeData
'''
    for group,node,key,count,last in [(0,LCA,'parent_state',14,'refined'),(1,LCA+'0','left_parent_state',10,'leftRefined')]:
        bs=[b for b in doc['bounds']if b['node']==node];assert len(bs)==count
        state=doc[key];stages=[matrix(state)]
        for b in bs:
            i,j,q=b['cut'];m=stages[-1]
            nxt=[[min(m[x][y],m[x][i]+q+m[j][y])for y in range(10)]for x in range(10)]
            assert all(nxt[i][i]==0 for i in range(10));stages.append(nxt)
        for k,m in enumerate(stages[1:-1],1):
            st=[[-m[j][i]for i,j in a.PAIRS],[m[i][j]for i,j in a.PAIRS]]
            text+=f'def stage{group}_{k:02} : DifferenceCell.Cell 10 := {cell_lit(st)}\n'
        first='parent'if group==0 else'leftParent'
        text+=f'def stage{group} (i : ℕ) : DifferenceCell.Cell 10 :=\n match i with\n | 0 => {first}\n'
        for k in range(1,count):text+=f' | {k} => stage{group}_{k:02}\n'
        text+=f' | _ => {last}\n'
        text+=f'def cuts{group} : List WindowCellCuts.Cut := ['+','.join(f'bound{b["id"]:02}.cut'for b in bs)+']\n'
        text+=f'def cut{group} (i : Fin {count}) : WindowCellCuts.Cut := !['+','.join(f'bound{b["id"]:02}.cut'for b in bs)+'] i\n'
        text+=f'''theorem steps{group} : ∀ k : Fin {count}, ∀ i j : Fin 10,
 DifferenceCell.addEdge (stage{group} k) (cut{group} k).i (cut{group} k).j (cut{group} k).bound i j =
   stage{group} ((k:ℕ)+1) i j := by decide +kernel
theorem step{group} (k : Fin {count}) :
 DifferenceCell.addEdge (stage{group} k) (cut{group} k).i (cut{group} k).j (cut{group} k).bound =
   stage{group} ((k:ℕ)+1) := funext (fun i => funext (fun j => steps{group} k i j))
theorem restrict{group} : WindowCellCuts.restrict {first} cuts{group} = {last} := by
'''
        for k,b in enumerate(bs):
            v=f'bound{b["id"]:02}'
            text+=f' have h{k} : DifferenceCell.addEdge (stage{group} {k}) {v}.cut.i {v}.cut.j {v}.cut.bound = stage{group} {k+1} := step{group} {k}\n'
        text+=f' change WindowCellCuts.restrict (stage{group} 0) cuts{group} = stage{group} {count}\n'
        text+=f' simp only [WindowCellCuts.restrict,cuts{group},List.foldl_cons,List.foldl_nil]\n'
        text+=' rw ['+','.join(f'h{k}'for k in range(count))+']\n'
        text+='set_option pp.fullNames true\n'+f'#print axioms steps{group}\n#print axioms restrict{group}\n'
    # Direct finite geometry ties the post-contraction branches to the
    # already proved actual curvature cells, so no new leaf is assumed.
    facts=[('branchLeft','WindowCellCuts.left refined 78 38166','leftParent'),
        ('branchRight','WindowCellCuts.right refined 78 38166','WindowCurvatureLeafData.cell01'),
        ('branchLeftLeft','WindowCellCuts.left leftRefined 12 38810','WindowCurvatureLeafData.cell00'),
        ('branchLeftRight','WindowCellCuts.right leftRefined 12 38810','WindowCurvatureLeafData.cell02')]
    for name,l,r in facts:
        text+=f'''theorem {name}_entries : ∀ i j : Fin 10, ({l}) i j = {r} i j := by decide +kernel
theorem {name} : {l} = {r} := funext (fun i => funext (fun j => {name}_entries i j))
#print axioms {name}
'''
    text+='end StructuralGoal20261016.WindowCurvatureSubtreeGeometry\n'
    (ROOT/'StructuralGoal20261016/WindowCurvatureSubtreeGeometry.lean').write_text(text,encoding='utf8',newline='\n')
    print(json.dumps({'intermediate_matrices':22,'steps':24,'finite_entries':2800,'bytes':len(text.encode()),'ordinary_Lean_proven':False}))
if __name__=='__main__':main()
