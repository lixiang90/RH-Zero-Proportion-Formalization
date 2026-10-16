/- SPDX-License-Identifier: Apache-2.0
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
def bounds0 : List WindowMixedContractions.OBBTBound := [bound00, bound01, bound02, bound03, bound04, bound05, bound06, bound07, bound08, bound09, bound10, bound11, bound12, bound13]
def bounds1 : List WindowMixedContractions.OBBTBound := [bound14, bound15, bound16, bound17, bound18, bound19, bound20, bound21, bound22, bound23]
def store : WindowMixedCover.Store where
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

theorem batch0 : WindowMixedContractions.check WindowMixedCover.target880
 parent (.obbt bounds0) = true := by
 simp only [WindowMixedContractions.check,bounds0,List.all_cons,List.all_nil,
   Bool.and_eq_true,and_true]
 exact ⟨WindowCurvatureOBBTAll.checked 0, WindowCurvatureOBBTAll.checked 1, WindowCurvatureOBBTAll.checked 2, WindowCurvatureOBBTAll.checked 3, WindowCurvatureOBBTAll.checked 4, WindowCurvatureOBBTAll.checked 5, WindowCurvatureOBBTAll.checked 6, WindowCurvatureOBBTAll.checked 7, WindowCurvatureOBBTAll.checked 8, WindowCurvatureOBBTAll.checked 9, WindowCurvatureOBBTAll.checked 10, WindowCurvatureOBBTAll.checked 11, WindowCurvatureOBBTAll.checked 12, WindowCurvatureOBBTAll.checked 13⟩
theorem contract0_eq : WindowMixedContractions.contract parent (.obbt bounds0) = refined := by
 simpa only [WindowMixedContractions.contract,WindowMixedContractions.cuts,bounds0,
   List.map_cons,List.map_nil,cuts0] using restrict0

theorem batch1 : WindowMixedContractions.check WindowMixedCover.target880
 leftParent (.obbt bounds1) = true := by
 simp only [WindowMixedContractions.check,bounds1,List.all_cons,List.all_nil,
   Bool.and_eq_true,and_true]
 exact ⟨WindowCurvatureOBBTAll.checked 14, WindowCurvatureOBBTAll.checked 15, WindowCurvatureOBBTAll.checked 16, WindowCurvatureOBBTAll.checked 17, WindowCurvatureOBBTAll.checked 18, WindowCurvatureOBBTAll.checked 19, WindowCurvatureOBBTAll.checked 20, WindowCurvatureOBBTAll.checked 21, WindowCurvatureOBBTAll.checked 22, WindowCurvatureOBBTAll.checked 23⟩
theorem contract1_eq : WindowMixedContractions.contract leftParent (.obbt bounds1) = leftRefined := by
 simpa only [WindowMixedContractions.contract,WindowMixedContractions.cuts,bounds1,
   List.map_cons,List.map_nil,cuts1] using restrict1

theorem leaf0_checked : (Tree.leaf 0).check operations cell00 = true := by
 change ((WindowCurvatureScalar.allCheck cell00 rows00 packets00 &&
   WindowCurvatureScalar.supportCheck cell00 direction00) &&
   WindowCurvatureFlow.check cell00 edges00 direction00 rows00) = true
 rw [scalar00,support00,flow00]
 rfl

theorem leaf1_checked : (Tree.leaf 1).check operations cell01 = true := by
 change ((WindowCurvatureScalar.allCheck cell01 rows01 packets01 &&
   WindowCurvatureScalar.supportCheck cell01 direction01) &&
   WindowCurvatureFlow.check cell01 edges01 direction01 rows01) = true
 rw [scalar01,support01,flow01]
 rfl

theorem leaf2_checked : (Tree.leaf 2).check operations cell02 = true := by
 change ((WindowCurvatureScalar.allCheck cell02 rows02 packets02 &&
   WindowCurvatureScalar.supportCheck cell02 direction02) &&
   WindowCurvatureFlow.check cell02 edges02 direction02 rows02) = true
 rw [scalar02,support02,flow02]
 rfl

theorem leftSplit_checked : leftSplit.check operations leftRefined = true := by
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
