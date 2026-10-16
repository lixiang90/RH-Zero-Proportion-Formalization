/- SPDX-License-Identifier: Apache-2.0
Factorial-normalized actual Fourier jets. This representation avoids large
intermediate derivatives in the rational interval certificates.
-/
import StructuralGoal20261016.WindowSincJet
import Mathlib.Data.Nat.Choose.Cast
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowNormalizedJets
open WindowKernel WindowDerivative WindowTaylorBridge WindowSincJet

def c (r : ℕ) (z : ℝ) : ℝ := sincMoment r z/(r.factorial:ℝ)
def b (r : ℕ) (z : ℝ) : ℝ := π^r*c r z
def e (r : ℕ) : ℝ := π^r/((r+1).factorial:ℝ)
def kc (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ := jet N d r x/(r.factorial:ℝ)
def wc (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
 iteratedDeriv r (w N d) x/(r.factorial:ℝ)

theorem c_succ {z : ℝ} (hz : z ≠ 0) (r : ℕ) :
 c (r+1) z = (Real.cos (z+(r:ℝ)*π/2)/((r+1).factorial:ℝ)-c r z)/z := by
 unfold c
 rw [sincMoment_succ hz, Nat.factorial_succ]
 have h0 : (r.factorial:ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
 have hr : ((r+1:ℕ):ℝ) ≠ 0 := by positivity
 push_cast
 field_simp [hz,h0,hr]
 <;> ring

theorem c_zero (r : ℕ) : c r 0 = Real.cos ((r:ℝ)*π/2)/((r+1).factorial:ℝ) := by
 unfold c
 rw [sincMoment_at_zero, Nat.factorial_succ]
 have h0 : (r.factorial:ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
 have hr : ((r+1:ℕ):ℝ) ≠ 0 := by positivity
 push_cast
 field_simp [h0,hr]
 <;> ring

theorem b_succ {z : ℝ} (hz : z ≠ 0) (r : ℕ) :
 b (r+1) z = (π/z)*(e r*Real.cos (z+(r:ℝ)*π/2)-b r z) := by
 unfold b e
 rw [c_succ hz, pow_succ]
 ring

theorem b_zero (r : ℕ) : b r 0 = e r*Real.cos ((r:ℝ)*π/2) := by
 rw [b, c_zero, e]
 ring

theorem e_succ (r : ℕ) : e (r+1) = e r*π/(r+2:ℕ) := by
 unfold e
 rw [pow_succ, Nat.factorial_succ]
 have h0 : ((r+1).factorial:ℝ) ≠ 0 := by exact_mod_cast (r+1).factorial_ne_zero
 have hr : ((r+2:ℕ):ℝ) ≠ 0 := by positivity
 push_cast
 field_simp [h0,hr]
 <;> ring

theorem kc_eq_finite (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 kc N d r x = π^r/(2*AMW.K0AM)*
   (c r (π*x-Real.sqrt 2/2)+c r (π*x+Real.sqrt 2/2)+
     ∑ j ∈ Finset.range N, d j*(c r (π*x-π*((j:ℝ)+1))+
       c r (π*x+π*((j:ℝ)+1)))) := by
 unfold kc
 rw [← finiteJet_eq_jet]
 unfold finiteJet rawJet c
 have hs : (∑ j ∈ Finset.range N, d j*
     (sincMoment r (π*x-π*((j:ℝ)+1))/(r.factorial:ℝ)+
       sincMoment r (π*x+π*((j:ℝ)+1))/(r.factorial:ℝ))) =
   (∑ j ∈ Finset.range N, d j*(sincMoment r (π*x-π*((j:ℝ)+1))+
       sincMoment r (π*x+π*((j:ℝ)+1))))/(r.factorial:ℝ) := by
   rw [Finset.sum_div]
   apply Finset.sum_congr rfl
   intro j _
   ring
 rw [hs]
 ring

theorem kc_eq_finite_b (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 kc N d r x =
   (b r (π*x-Real.sqrt 2/2)+b r (π*x+Real.sqrt 2/2)+
     ∑ j ∈ Finset.range N, d j*(b r (π*x-π*((j:ℝ)+1))+
       b r (π*x+π*((j:ℝ)+1))))/(2*AMW.K0AM) := by
 rw [kc_eq_finite]
 unfold b
 have hs : (∑ j ∈ Finset.range N, d j*
     (π^r*c r (π*x-π*((j:ℝ)+1))+π^r*c r (π*x+π*((j:ℝ)+1)))) =
   π^r*∑ j ∈ Finset.range N, d j*(c r (π*x-π*((j:ℝ)+1))+
     c r (π*x+π*((j:ℝ)+1))) := by
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro j _
   ring
 rw [hs]
 ring

theorem K0AM_eq_ratio : AMW.K0AM =
 Real.sin (Real.sqrt 2/2)/(Real.sqrt 2/2) := by
 unfold AMW.K0AM
 have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
 have hs2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
 apply (eq_div_iff (div_ne_zero hs (by norm_num))).2
 calc
   _ = (Real.sqrt 2)^2*Real.sin (Real.sqrt 2/2)/2 := by ring
   _ = _ := by rw [hs2]; ring

theorem wc_convolution (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 wc N d r x = ∑ i ∈ Finset.range (r+1), kc N d i x*kc N d (r-i) x := by
 rw [wc, iterated_w_eq, Finset.sum_div]
 apply Finset.sum_congr rfl
 intro i hi
 have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
 rw [Nat.cast_choose ℝ hir]
 unfold kc
 have hr0 : (r.factorial:ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
 have hi0 : (i.factorial:ℝ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
 have hri0 : ((r-i).factorial:ℝ) ≠ 0 := by exact_mod_cast (r-i).factorial_ne_zero
 field_simp [hr0,hi0,hri0]
 <;> ring

theorem wc_eq_iterated (N : ℕ) (d : ℕ → ℝ) (r : ℕ) (x : ℝ) :
 (r.factorial:ℝ)*wc N d r x = iteratedDeriv r (w N d) x := by
 unfold wc
 have h0 : (r.factorial:ℝ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
 field_simp

#print axioms c_succ
#print axioms kc_eq_finite
#print axioms wc_convolution
end StructuralGoal20261016.WindowNormalizedJets
end
