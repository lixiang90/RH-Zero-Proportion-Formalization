/- SPDX-License-Identifier: Apache-2.0
Unconditional scalar quadratic minorants at every frozen Gram anchor.
Every value/slope and curvature input is supplied by an actual checked
new-window theorem. Only membership of the evaluation point in its well
is an input to the resulting minorant.
-/
import StructuralGoal20261016.WindowAnchorAll
import StructuralGoal20261016.WindowConvexityAll
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowScalarBridge
open WindowAnchorCertificate WindowAnchorCertificateData WindowScalarMinorant

def radius (r : Row) : ℚ := 21/100+|r.anchor-(r.center:ℚ)|
def minorant (r : Row) (x : ℝ) : ℝ :=
 ((r.lower-r.error*radius r:ℚ):ℝ)+(r.slope:ℝ)*(x-r.anchor)+
   (WindowConvexityAll.lower r.center:ℝ)/2*(x-r.anchor)^2

theorem parameters : ∀ i : Fin 1567,
 1 ≤ (row i).center ∧ (row i).center ≤ 16 ∧
 |(row i).anchor-((row i).center:ℚ)| ≤ 21/100 ∧ 0 ≤ (row i).error := by decide +kernel

theorem actual (i : ℕ) (hi : i < 1567) {x : ℝ}
 (hx : x ∈ Icc (((row i).center:ℝ)-21/100) (((row i).center:ℝ)+21/100)) :
 minorant (row i) x ≤ f x := by
 let r := row i
 have hp := parameters ⟨i,hi⟩
 change 1 ≤ r.center ∧ r.center ≤ 16 ∧
   |r.anchor-(r.center:ℚ)| ≤ 21/100 ∧ 0 ≤ r.error at hp
 have hpa : |(r.anchor:ℝ)-(r.center:ℝ)| ≤ 21/100 := by
   have hh : ((|r.anchor-(r.center:ℚ)|:ℚ):ℝ) ≤ ((21/100:ℚ):ℝ) :=
     Rat.cast_le.mpr hp.2.2.1
   push_cast at hh
   exact hh
 have hpoint : (r.anchor:ℝ) ∈ Icc ((r.center:ℝ)-21/100) ((r.center:ℝ)+21/100) := by
   rw [abs_le] at hpa
   constructor <;> linarith [hpa.1,hpa.2]
 have hx0 : |x-(r.center:ℝ)| ≤ 21/100 := by
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 have hr : |x-(r.anchor:ℝ)| ≤ (radius r:ℝ) := by
   unfold radius
   push_cast
   calc
     _ = |(x-(r.center:ℝ))+((r.center:ℝ)-r.anchor)| := by congr 1; ring
     _ ≤ |x-(r.center:ℝ)|+|(r.center:ℝ)-r.anchor| := abs_add_le _ _
     _ ≤ 21/100+|(r.anchor:ℝ)-r.center| := by
       rw [abs_sub_comm (r.center:ℝ)]
       exact add_le_add hx0 le_rfl
 have hs : |iteratedDeriv 1 f r.anchor-(r.slope:ℝ)| ≤ (r.error:ℝ) := WindowAnchorAll.slope i hi
 have hv : (r.lower:ℝ) ≤ f r.anchor := WindowAnchorAll.value i hi
 unfold minorant
 apply quadratic_minorant (ε := (r.error:ℝ)) (radius := (radius r:ℝ))
   hpoint hx (by exact_mod_cast hp.2.2.2) hr
 · intro y hy
   have hh := WindowConvexityAll.lower_sound hp.1 hp.2.1 y hy
   change (WindowConvexityAll.lower r.center:ℝ) ≤ iteratedDeriv 2 f y at hh
   nlinarith only [hh]
 · push_cast
   nlinarith only [hv]
 · exact hs

set_option pp.fullNames true
#print axioms parameters
#print axioms actual
end StructuralGoal20261016.WindowScalarBridge
end
