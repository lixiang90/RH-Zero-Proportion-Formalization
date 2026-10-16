"""Assemble the exact 24-contraction/two-branch/three-leaf local tree.

The finite OBBT and curvature facts are imported checkpoints, not recomputed
inside the tree proof. Every cell transition is linked by checked geometry.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s='''/- SPDX-License-Identifier: Apache-2.0
A complete actual mixed minimizer subtree at depth 23. The local root is
the frozen LCA cell, not the global pressure root. The theorem excludes
RelevantBelow(0.0088) points in this cell and asserts no global record.
-/
import StructuralGoal20261016.WindowCurvatureOBBTAll
import StructuralGoal20261016.WindowCurvatureSubtreeGeometry
import StructuralGoal20261016.WindowCurvatureLeavesAll
import StructuralGoal20261016.WindowMixedCover
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowCurvatureSubtree
open WindowCurvatureSubtreeData WindowCurvatureSubtreeGeometry
open WindowCurvatureLeafData WindowCurvatureLeaves
open MinimizerCover
'''
for g,(start,count) in enumerate([(0,14),(14,10)]):
    s+=f'def bounds{g} : List WindowMixedContractions.OBBTBound := ['+', '.join(f'bound{k:02}'for k in range(start,start+count))+']\n'
s+='''def store : WindowMixedCover.Store where
 leaf := fun i => match i with
   | 0 => .curvature ⟨direction00,rows00,packets00,edges00⟩
   | 1 => .curvature ⟨direction01,rows01,packets01,edges01⟩
   | _ => .curvature ⟨direction02,rows02,packets02,edges02⟩
 contraction := fun i => if i = 0 then .obbt bounds0 else .obbt bounds1
def operations := WindowMixedCover.operations WindowMixedCover.target880 store
def leftSplit : Tree := .split 12 38810 (.leaf 0) (.leaf 2)
def leftTree : Tree := .contract 1 leftSplit
def topSplit : Tree := .split 78 38166 leftTree (.leaf 1)
def tree : Tree := .contract 0 topSplit

'''
for g,(start,count,parent,last) in enumerate([(0,14,'parent','refined'),(14,10,'leftParent','leftRefined')]):
    s+=f'''theorem batch{g} : WindowMixedContractions.check WindowMixedCover.target880
 {parent} (.obbt bounds{g}) = true := by
 simp only [WindowMixedContractions.check,bounds{g},List.all_cons,List.all_nil,
   Bool.and_eq_true,and_true]
 exact ⟨'''+', '.join(f'WindowCurvatureOBBTAll.checked {k}'for k in range(start,start+count))+f'''⟩
theorem contract{g}_eq : WindowMixedContractions.contract {parent} (.obbt bounds{g}) = {last} := by
 simpa only [WindowMixedContractions.contract,WindowMixedContractions.cuts,bounds{g},
   List.map_cons,List.map_nil,cuts{g}] using restrict{g}

'''
for k in range(3):
    s+=f'''theorem leaf{k}_checked : (Tree.leaf {k}).check operations cell{k:02} = true := by
 change ((WindowCurvatureScalar.allCheck cell{k:02} rows{k:02} packets{k:02} &&
   WindowCurvatureScalar.supportCheck cell{k:02} direction{k:02}) &&
   WindowCurvatureFlow.check cell{k:02} edges{k:02} direction{k:02} rows{k:02}) = true
 rw [scalar{k:02},support{k:02},flow{k:02}]
 rfl

'''
s+='''theorem leftSplit_checked : leftSplit.check operations leftRefined = true := by
 change (WindowCellCuts.branchCheck 12 &&
   ((Tree.leaf 0).check operations (WindowCellCuts.left leftRefined 12 38810) &&
    (Tree.leaf 2).check operations (WindowCellCuts.right leftRefined 12 38810))) = true
 rw [branchLeftLeft,branchLeftRight,leaf0_checked,leaf2_checked]
 decide +kernel

theorem leftTree_checked : leftTree.check operations leftParent = true := by
 change (WindowMixedContractions.check WindowMixedCover.target880 leftParent (.obbt bounds1) &&
   leftSplit.check operations (WindowMixedContractions.contract leftParent (.obbt bounds1))) = true
 rw [batch1,contract1_eq,leftSplit_checked]
 rfl

theorem topSplit_checked : topSplit.check operations refined = true := by
 change (WindowCellCuts.branchCheck 78 &&
   (leftTree.check operations (WindowCellCuts.left refined 78 38166) &&
    (Tree.leaf 1).check operations (WindowCellCuts.right refined 78 38166))) = true
 rw [branchLeft,branchRight,leftTree_checked,leaf1_checked]
 decide +kernel

theorem checked : tree.check operations parent = true := by
 change (WindowMixedContractions.check WindowMixedCover.target880 parent (.obbt bounds0) &&
   topSplit.check operations (WindowMixedContractions.contract parent (.obbt bounds0))) = true
 rw [batch0,contract0_eq,topSplit_checked]
 rfl

theorem exclude {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.RelevantBelow ((123:ℝ)/128) ((11:ℝ)/1250) g)
 (hcell : WindowDifferenceCell.Contains parent g) : False := by
 have hrel : WindowMinimizerCover.RelevantBelow ((123:ℝ)/128)
     (WindowMixedLeaves.floor WindowMixedCover.target880) g := by
   simpa only [WindowMixedCover.floor880_eq] using hg
 have h := tree.check_sound (WindowMixedCover.sound WindowMixedCover.target880 store)
   parent checked g hrel hcell
 have hf : (11:ℝ)/1250 ≤ WindowGapEnergy.Fw24 g := by
   simpa only [WindowMixedCover.floor880_eq] using h
 exact (not_lt_of_ge hf) hg.2

set_option pp.fullNames true
#print axioms batch0
#print axioms batch1
#print axioms checked
#print axioms exclude
end StructuralGoal20261016.WindowCurvatureSubtree
end
'''
(ROOT/'StructuralGoal20261016/WindowCurvatureSubtree.lean').write_text(s,encoding='utf8',newline='\n')
print('WindowCurvatureSubtree.lean written; requires the passed finite checkpoints')
