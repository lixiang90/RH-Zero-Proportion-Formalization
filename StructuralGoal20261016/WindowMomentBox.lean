/- SPDX-License-Identifier: Apache-2.0
Tight rational boxes for the genuine 464 actual lifted coordinates.
Only coordinate geometry and queries into the proved derivative grid are used.
-/
import StructuralGoal20261016.WindowMomentLayout
import StructuralGoal20261016.WindowMomentRounding
import StructuralGoal20261016.WindowCellCuts
import StructuralGoal20261016.WindowFirstOrderCertificate
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowMomentBox
open WindowMomentLayout

structure Packet where
 center : Fin 9 → ℚ
 radius : Fin 9 → ℚ
 uLower : Fin 41 → ℚ
 uUpper : Fin 41 → ℚ
 firstCell : Fin 41 → ℕ
 lastCell : Fin 41 → ℕ

def lower (p : Packet) (i : Fin 464) : ℚ :=
 if h0 : (i:ℕ) < 9 then p.center ⟨i,by omega⟩-p.radius ⟨i,by omega⟩
 else if h1 : (i:ℕ) < 50 then p.uLower ⟨(i:ℕ)-9,by omega⟩
 else if h2 : (i:ℕ) < 95 then
   if hFirst ⟨(i:ℕ)-50,by omega⟩ = hSecond ⟨(i:ℕ)-50,by omega⟩ then 0 else -1
 else -max |p.uLower ⟨((i:ℕ)-95)%41,by omega⟩| |p.uUpper ⟨((i:ℕ)-95)%41,by omega⟩|

def upper (p : Packet) (i : Fin 464) : ℚ :=
 if h0 : (i:ℕ) < 9 then p.center ⟨i,by omega⟩+p.radius ⟨i,by omega⟩
 else if h1 : (i:ℕ) < 50 then p.uUpper ⟨(i:ℕ)-9,by omega⟩
 else if h2 : (i:ℕ) < 95 then 1
 else max |p.uLower ⟨((i:ℕ)-95)%41,by omega⟩| |p.uUpper ⟨((i:ℕ)-95)%41,by omega⟩|

def checkGeometry (cell : DifferenceCell.Cell 10) (p : Packet) : Bool := decide (
 ∀ r, 0 < p.radius r ∧ p.center r-p.radius r = -(cell r.succ r.castSucc:ℚ)/32768 ∧
   p.center r+p.radius r = (cell r.castSucc r.succ:ℚ)/32768)

def checkDerivatives (cell : DifferenceCell.Cell 10) (p : Packet) : Bool := decide (
 ∀ e, WindowGridRange.check (p.firstCell e) (p.lastCell e)
   (WindowFirstOrderCertificate.leftQ cell e) (WindowFirstOrderCertificate.rightQ cell e)
   (p.uLower e) (p.uUpper e) 1000000 = true)

def check (cell : DifferenceCell.Cell 10) (p : Packet) : Bool :=
 checkGeometry cell p && checkDerivatives cell p

def actual (p : Packet) (g : Fin 9 → ℝ) : Fin 464 → ℝ :=
 WindowMomentLayout.actual (fun r => (p.center r:ℝ)) (fun r => (p.radius r:ℝ)) g

theorem bounds (p : Packet) (g : Fin 9 → ℝ)
 (hr : ∀ r, (0:ℝ) < (p.radius r:ℝ))
 (hg : ∀ r, (p.center r:ℝ)-(p.radius r:ℝ) ≤ g r ∧ g r ≤ (p.center r:ℝ)+(p.radius r:ℝ))
 (hu : ∀ e, (p.uLower e:ℝ) ≤ u g e ∧ u g e ≤ (p.uUpper e:ℝ)) :
 ∀ i, (lower p i:ℝ) ≤ actual p g i ∧ actual p g i ≤ (upper p i:ℝ) := by
 let y := normalized (fun r => (p.center r:ℝ)) (fun r => (p.radius r:ℝ)) g
 have hy : ∀ r, -1 ≤ y r ∧ y r ≤ 1 := fun r => normalized_bounds r (hr r) (hg r)
 intro i
 by_cases h0 : (i:ℕ) < 9
 · simpa only [lower,upper,actual,WindowMomentLayout.actual,dif_pos h0,Rat.cast_sub,Rat.cast_add] using hg ⟨i,by omega⟩
 · by_cases h1 : (i:ℕ) < 50
   · simpa only [lower,upper,actual,WindowMomentLayout.actual,dif_neg h0,dif_pos h1] using hu ⟨(i:ℕ)-9,by omega⟩
   · by_cases h2 : (i:ℕ) < 95
     · let e : Fin 45 := ⟨(i:ℕ)-50,by omega⟩
       by_cases hd : hFirst e = hSecond e
       · have hb := diagonal_bounds (hy (hFirst e))
         simpa only [lower,upper,actual,WindowMomentLayout.actual,dif_neg h0,dif_neg h1,
           dif_pos h2,e,← hd,ite_true,Rat.cast_zero,Rat.cast_one] using hb
       · have hb := product_bounds (hy (hFirst e)) (hy (hSecond e))
         simpa only [lower,upper,actual,WindowMomentLayout.actual,dif_neg h0,dif_neg h1,
           dif_pos h2,e,hd,ite_false,Rat.cast_neg,Rat.cast_one] using hb
     · let s : Fin 9 := ⟨((i:ℕ)-95)/41,by omega⟩
       let e : Fin 41 := ⟨((i:ℕ)-95)%41,by omega⟩
       have hb := derivative_product_bounds (hy s)
         (abs_le.mp (WindowMomentRounding.abs_box (hu e)))
       simpa only [lower,upper,actual,WindowMomentLayout.actual,dif_neg h0,dif_neg h1,
         dif_neg h2,s,e,Rat.cast_neg,Rat.cast_max,Rat.cast_abs] using hb

theorem sound {cell : DifferenceCell.Cell 10} {p : Packet}
 (hc : check cell p = true) {g : Fin 9 → ℝ}
 (hcell : WindowDifferenceCell.Contains cell g) :
 ∀ i, (lower p i:ℝ) ≤ actual p g i ∧ actual p g i ≤ (upper p i:ℝ) := by
 have hh : checkGeometry cell p = true ∧ checkDerivatives cell p = true := by
   simpa only [check,Bool.and_eq_true] using hc
 have hgeom : ∀ r, 0 < p.radius r ∧
     p.center r-p.radius r = -(cell r.succ r.castSucc:ℚ)/32768 ∧
     p.center r+p.radius r = (cell r.castSucc r.succ:ℚ)/32768 := of_decide_eq_true hh.1
 have hd : ∀ e, WindowGridRange.check (p.firstCell e) (p.lastCell e)
     (WindowFirstOrderCertificate.leftQ cell e) (WindowFirstOrderCertificate.rightQ cell e)
     (p.uLower e) (p.uUpper e) 1000000 = true := of_decide_eq_true hh.2
 have hr : ∀ r, (0:ℝ) < (p.radius r:ℝ) := fun r => Rat.cast_pos.mpr (hgeom r).1
 have hg : ∀ r, (p.center r:ℝ)-(p.radius r:ℝ) ≤ g r ∧
     g r ≤ (p.center r:ℝ)+(p.radius r:ℝ) := by
   intro r
   have hl := hcell r.succ r.castSucc
   have hu := hcell r.castSucc r.succ
   have ha := WindowCellCuts.adjacent g r
   have hel : ((p.center r-p.radius r:ℚ):ℝ) = ((-(cell r.succ r.castSucc:ℚ)/32768:ℚ):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (hgeom r).2.1
   have heu : ((p.center r+p.radius r:ℚ):ℝ) = (((cell r.castSucc r.succ:ℚ)/32768:ℚ):ℝ) :=
     congrArg (fun x : ℚ => (x:ℝ)) (hgeom r).2.2
   push_cast at hel heu
   change WindowDifferenceCell.positions g r.castSucc-
     WindowDifferenceCell.positions g r.succ ≤ (cell r.succ r.castSucc:ℝ) at hl
   change WindowDifferenceCell.positions g r.succ-
     WindowDifferenceCell.positions g r.castSucc ≤ (cell r.castSucc r.succ:ℝ) at hu
   constructor <;> linarith
 have hu : ∀ e, (p.uLower e:ℝ) ≤ u g e ∧ u g e ≤ (p.uUpper e:ℝ) := by
   intro e
   have hb := WindowScalarLine.span_bounds hcell e
   have hx : WindowGramTransfer.span g e ∈ Icc
       (WindowFirstOrderCertificate.leftQ cell e:ℝ) (WindowFirstOrderCertificate.rightQ cell e:ℝ) := by
     simpa only [Set.mem_Icc,WindowFirstOrderCertificate.leftQ,WindowFirstOrderCertificate.rightQ,
       Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat] using hb
   have hdv := WindowGridAll.range_sound (hd e) hx
   exact ⟨hdv.1,hdv.2.1⟩
 exact bounds p g hr hg hu

set_option pp.fullNames true
#print axioms bounds
#print axioms sound
end StructuralGoal20261016.WindowMomentBox
end
