/- SPDX-License-Identifier: Apache-2.0
Finite scalar packets for actual curvature certificates. Only the chosen
cell-query indices and point midpoint are inputs; each is checked against
the actual Fourier derivative tables. Inactive edges may use the global
second-derivative upper bound 40, whose contribution vanishes in the energy.
-/
import StructuralGoal20261016.WindowCurvatureOracle
import StructuralGoal20261016.WindowCurvatureGridAll
import StructuralGoal20261016.WindowCurvatureFlow
import StructuralGoal20261016.WindowScalarLine
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCurvatureScalar
open WindowDirectionalFlow (Row SC DS)
open WindowCurvatureGridData (row index)
open WindowScalarMinorant

structure Packet where
 kind : ℕ
 n : ℕ
 first : ℕ
 last : ℕ
 fourth : ℤ
def defaultPacket : Packet := ⟨0,0,0,0,0⟩
def inactiveRow : Row := ⟨0,40*DS,0,0⟩

def check (a b : ℚ) (r : Row) (p : Packet) : Bool :=
 if p.kind = 0 then decide (r.value = 40*DS ∧ r.slope = 0 ∧ r.error = 0)
 else if p.kind = 1 then decide (r.slope = 0 ∧
   WindowCurvatureGrid.secondCheck row index 331 p.first p.last a b
     (((r.value-r.error):ℚ)/(DS:ℚ)) (((r.value+r.error):ℚ)/(DS:ℚ)) = true)
 else decide (p.kind = 2 ∧
   WindowCurvatureOracle.check p.n a b ((r.anchor:ℚ)/(2*(SC:ℚ)))
     ((r.value:ℚ)/(DS:ℚ)) ((r.slope:ℚ)/(DS:ℚ))
     ((p.fourth:ℚ)/(DS:ℚ)) ((r.error:ℚ)/(DS:ℚ)) = true ∧
   WindowCurvatureGrid.fourthCheck row index 331 p.first p.last a b
     ((p.fourth:ℚ)/(DS:ℚ)) = true)

theorem global_upper (x : ℝ) : WindowSecondVariation.w2 x ≤ 40 := by
 rw [WindowSecondVariation.w2_eq_actual]
 have h := WindowTaylorBridge.w24_iterated_abs_le 2 x
 exact (le_abs_self _).trans (h.trans (by norm_num))

theorem actual {a b : ℚ} {r : Row} {p : Packet}
 (hc : check a b r p = true) {x : ℝ}
 (hx : p.kind ≠ 0 → x ∈ Icc (a:ℝ) b) :
 WindowSecondVariation.w2 x ≤
   (r.value:ℝ)/(DS:ℝ)+(r.slope:ℝ)/(DS:ℝ)*(x-(r.anchor:ℝ)/(2*(SC:ℝ)))+
     (r.error:ℝ)/(DS:ℝ) := by
 by_cases h0 : p.kind = 0
 · have hh : r.value = 40*DS ∧ r.slope = 0 ∧ r.error = 0 := by
     simpa only [check,if_pos h0,decide_eq_true_eq] using hc
   rw [hh.1,hh.2.1,hh.2.2]
   norm_num [DS]
   exact global_upper x
 · by_cases h1 : p.kind = 1
   · have hh : r.slope = 0 ∧
       WindowCurvatureGrid.secondCheck row index 331 p.first p.last a b
         (((r.value-r.error):ℚ)/(DS:ℚ)) (((r.value+r.error):ℚ)/(DS:ℚ)) = true := by
       simpa only [check,if_neg h0,if_pos h1,decide_eq_true_eq] using hc
     have hu := (WindowCurvatureGridAll.second hh.2 (hx h0)).2
     rw [← WindowSecondVariation.w2_eq_actual] at hu
     push_cast at hu
     rw [hh.1]
     simp only [Int.cast_zero,zero_div,zero_mul,add_zero]
     simpa only [add_div] using hu
   · have hh : p.kind = 2 ∧
       WindowCurvatureOracle.check p.n a b ((r.anchor:ℚ)/(2*(SC:ℚ)))
         ((r.value:ℚ)/(DS:ℚ)) ((r.slope:ℚ)/(DS:ℚ))
         ((p.fourth:ℚ)/(DS:ℚ)) ((r.error:ℚ)/(DS:ℚ)) = true ∧
       WindowCurvatureGrid.fourthCheck row index 331 p.first p.last a b
         ((p.fourth:ℚ)/(DS:ℚ)) = true := by
       simpa only [check,if_neg h0,if_neg h1,decide_eq_true_eq] using hc
     have ht := WindowCurvatureOracle.actual_w2 hh.2.1
       (fun y hy => WindowCurvatureGridAll.fourth hh.2.2 hy) (hx h0)
     push_cast at ht
     exact (sub_le_iff_le_add.mp (abs_le.mp ht).2).trans_eq (by ring)

def allCheck (cell : DifferenceCell.Cell 10) (r : Fin 41 → Row)
    (p : Fin 41 → Packet) : Bool := decide (∀ e : Fin 41,
 check ((WindowScalarLine.lower cell e:ℚ)/(SC:ℚ))
   ((WindowScalarLine.upper cell e:ℚ)/(SC:ℚ)) (r e) (p e) = true)

theorem scalarValid {cell : DifferenceCell.Cell 10} {r : Fin 41 → Row}
    {p : Fin 41 → Packet} (hc : allCheck cell r p = true)
    {g : Fin 9 → ℝ} (hg : WindowDifferenceCell.Contains cell g) :
    WindowCurvatureFlow.ScalarValid g r := by
 have hh : ∀ e : Fin 41,
   check ((WindowScalarLine.lower cell e:ℚ)/(SC:ℚ))
     ((WindowScalarLine.upper cell e:ℚ)/(SC:ℚ)) (r e) (p e) = true := of_decide_eq_true hc
 intro e
 apply actual (hh e)
 intro _
 have hs := WindowScalarLine.span_bounds hg e
 convert hs using 1 <;> norm_num [SC]

def supportCheck (cell : DifferenceCell.Cell 10) (d : Fin 9 → ℤ) : Bool :=
 decide (∀ r : Fin 9, d r ≠ 0 → cell r.succ r.castSucc < -31488)

theorem support {cell : DifferenceCell.Cell 10} {d : Fin 9 → ℤ}
 (hc : supportCheck cell d = true) {g : Fin 9 → ℝ}
 (hg : WindowDifferenceCell.Contains cell g) :
 ∀ r, d r ≠ 0 → (123:ℝ)/128 < g r := by
 have hh : ∀ r : Fin 9, d r ≠ 0 → cell r.succ r.castSucc < -31488 := of_decide_eq_true hc
 intro r hr
 have h := hg r.succ r.castSucc
 change 32768*Zeta23Ext.Bridge.ptsN 10 g r.castSucc-
   32768*Zeta23Ext.Bridge.ptsN 10 g r.succ ≤ (cell r.succ r.castSucc:ℝ) at h
 have ha := WindowDifferenceCell.adjacent_difference g r
 have ht : (cell r.succ r.castSucc:ℝ) < -31488 := by exact_mod_cast hh r hr
 nlinarith

theorem exclude {cell : DifferenceCell.Cell 10} {d : Fin 9 → ℤ}
 {r : Fin 41 → Row} {p : Fin 41 → Packet} {edges : List FlowBasisCodec.Edge}
 (hscalar : allCheck cell r p = true) (hsupport : supportCheck cell d = true)
 (hflow : WindowCurvatureFlow.check cell edges d r = true)
 {g : Fin 9 → ℝ} (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell g) : False :=
 WindowCurvatureFlow.exclude hg cell hcell edges d r (support hsupport hcell)
   (scalarValid hscalar hcell) hflow

set_option pp.fullNames true
#print axioms global_upper
#print axioms actual
#print axioms scalarValid
#print axioms support
#print axioms exclude
end StructuralGoal20261016.WindowCurvatureScalar
end
