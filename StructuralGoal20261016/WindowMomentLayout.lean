/- SPDX-License-Identifier: Apache-2.0
Actual 464-variable position/derivative lift. Every moment is the product
of actual normalized gaps and actual first derivatives. Indices agree with
the frozen finite two-cell moment certificate; no abstract PSD witness is
assumed. This module does not assert a local or global exclusion.
-/
import StructuralGoal20261016.WindowBoundedMomentFarkas
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentLayout

def hFirst : Fin 45 → Fin 9 := ![0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,3,3,3,3,3,3,4,4,4,4,4,5,5,5,5,6,6,6,7,7,8]
def hSecond : Fin 45 → Fin 9 := ![0,1,2,3,4,5,6,7,8,1,2,3,4,5,6,7,8,2,3,4,5,6,7,8,3,4,5,6,7,8,4,5,6,7,8,5,6,7,8,6,7,8,7,8,8]

def normalized (center radius g : Fin 9 → ℝ) (r : Fin 9) : ℝ :=
  (g r-center r)/radius r

def u (g : Fin 9 → ℝ) (e : Fin 41) : ℝ :=
  WindowGapEnergy.w1 (WindowGramTransfer.span g e)

def gapIndex (r : Fin 9) : Fin 464 := ⟨r,by omega⟩
def uIndex (e : Fin 41) : Fin 464 := ⟨9+(e:ℕ),by omega⟩
def hIndex (e : Fin 45) : Fin 464 := ⟨50+(e:ℕ),by omega⟩
def qIndex (r : Fin 9) (e : Fin 41) : Fin 464 := ⟨95+41*(r:ℕ)+(e:ℕ),by omega⟩

def actual (center radius g : Fin 9 → ℝ) (i : Fin 464) : ℝ :=
  if h0 : (i:ℕ) < 9 then g ⟨i,by omega⟩
  else if h1 : (i:ℕ) < 50 then u g ⟨(i:ℕ)-9,by omega⟩
  else if h2 : (i:ℕ) < 95 then
    normalized center radius g (hFirst ⟨(i:ℕ)-50,by omega⟩)*
      normalized center radius g (hSecond ⟨(i:ℕ)-50,by omega⟩)
  else normalized center radius g ⟨((i:ℕ)-95)/41,by omega⟩*
    u g ⟨((i:ℕ)-95)%41,by omega⟩

theorem actual_gap (center radius g : Fin 9 → ℝ) (r : Fin 9) :
    actual center radius g (gapIndex r) = g r := by
  simp [actual,gapIndex]

theorem actual_u (center radius g : Fin 9 → ℝ) (e : Fin 41) :
    actual center radius g (uIndex e) = u g e := by
  have h0 : ¬ 9+(e:ℕ) < 9 := by omega
  have h1 : 9+(e:ℕ) < 50 := by omega
  simp [actual,uIndex,h0,h1]

theorem actual_h (center radius g : Fin 9 → ℝ) (e : Fin 45) :
    actual center radius g (hIndex e) =
      normalized center radius g (hFirst e)*normalized center radius g (hSecond e) := by
  have h0 : ¬ 50+(e:ℕ) < 9 := by omega
  have h1 : ¬ 50+(e:ℕ) < 50 := by omega
  have h2 : 50+(e:ℕ) < 95 := by omega
  simp [actual,hIndex,h0,h1,h2]

theorem actual_q (center radius g : Fin 9 → ℝ) (r : Fin 9) (e : Fin 41) :
    actual center radius g (qIndex r e) =
      normalized center radius g r*u g e := by
  have h0 : ¬ 95+41*(r:ℕ)+(e:ℕ) < 9 := by omega
  have h1 : ¬ 95+41*(r:ℕ)+(e:ℕ) < 50 := by omega
  have h2 : ¬ 95+41*(r:ℕ)+(e:ℕ) < 95 := by omega
  have hr : (95+41*(r:ℕ)+(e:ℕ)-95)/41 = (r:ℕ) := by omega
  have he : (95+41*(r:ℕ)+(e:ℕ)-95)%41 = (e:ℕ) := by omega
  simp [actual,qIndex,h0,h1,h2,hr,he]

theorem normalized_bounds {center radius g : Fin 9 → ℝ} (r : Fin 9)
    (hr : 0 < radius r)
    (hg : center r-radius r ≤ g r ∧ g r ≤ center r+radius r) :
    -1 ≤ normalized center radius g r ∧ normalized center radius g r ≤ 1 := by
  unfold normalized
  constructor
  · apply (le_div_iff₀ hr).mpr
    linarith [hg.1]
  · apply (div_le_iff₀ hr).mpr
    linarith [hg.2]

theorem factor_nonneg {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1) (positive : Bool) :
    0 ≤ 1+(if positive then (1:ℝ) else -1)*y := by
  cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true,neg_one_mul,one_mul] <;> linarith

theorem rlt_nonpos {value bound y : ℝ} (hrow : value ≤ bound)
    (hy : -1 ≤ y ∧ y ≤ 1) (positive : Bool) :
    (value-bound)*(1+(if positive then (1:ℝ) else -1)*y) ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrow) (factor_nonneg hy positive)

theorem diagonal_bounds {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1) :
    0 ≤ y*y ∧ y*y ≤ 1 := by
  constructor
  · nlinarith [sq_nonneg y]
  · nlinarith [mul_nonneg (by linarith [hy.2] : 0 ≤ 1-y)
      (by linarith [hy.1] : 0 ≤ 1+y)]

theorem product_bounds {y z : ℝ} (hy : -1 ≤ y ∧ y ≤ 1) (hz : -1 ≤ z ∧ z ≤ 1) :
    -1 ≤ y*z ∧ y*z ≤ 1 := by
  have h := WindowBoundedMomentFarkas.product_enclosure hy hz
  norm_num at h
  exact h

theorem derivative_product_bounds {y z B : ℝ}
    (hy : -1 ≤ y ∧ y ≤ 1) (hz : -B ≤ z ∧ z ≤ B) :
    -B ≤ y*z ∧ y*z ≤ B := by
  apply abs_le.mp
  rw [abs_mul]
  calc
    |y| * |z| ≤ 1*B := mul_le_mul (abs_le.mpr hy) (abs_le.mpr hz) (abs_nonneg _) (by norm_num)
    _ = B := one_mul _

set_option pp.fullNames true
#print axioms actual_gap
#print axioms actual_u
#print axioms actual_h
#print axioms actual_q
#print axioms normalized_bounds
#print axioms rlt_nonpos
#print axioms diagonal_bounds
#print axioms product_bounds
#print axioms derivative_product_bounds
end StructuralGoal20261016.WindowMomentLayout
end

