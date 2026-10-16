/- SPDX-License-Identifier: Apache-2.0
Actual local affine enclosures for the second derivative of the new
window. Point errors use the same frozen normalized coefficients and
the proved order-24 remainder. A whole-cell fourth-derivative bound
is the only analytic input and will be supplied by selected checked cells.
-/
import StructuralGoal20261016.WindowDerivativeAffineOracle
import StructuralGoal20261016.WindowSecondVariation
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCurvatureOracle
open WindowScalarMinorant WindowConvexityCertificate

theorem smooth (r : ℕ) : ContDiff ℝ r (iteratedDeriv 2 f) :=
 w_iterated_contDiff 24 WindowKernel.d24 2 r

theorem hasDerivAt (x : ℝ) :
 HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f x) x :=
 WindowFiniteMoveScalar.w_iterated_hasDerivAt 2 x

theorem taylor_two (p x : ℝ) :
 taylorPoly (iteratedDeriv 2 f) 1 p x =
 iteratedDeriv 2 f p+iteratedDeriv 3 f p*(x-p) := by
 simp only [taylorPoly,Finset.sum_range_succ,Finset.sum_range_zero,
   zero_add,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,
   pow_zero,pow_one,mul_one,iteratedDeriv_zero,iteratedDeriv_one]
 rw [(hasDerivAt p).deriv]

theorem local_remainder {a b p x M : ℝ}
 (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
 (hfourth : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ M) :
 |(iteratedDeriv 2 f) x-(iteratedDeriv 2 f) p-iteratedDeriv 3 f p*(x-p)| ≤
   M*(x-p)^2/2 := by
 by_cases hpx : p = x
 · subst x
   simp
 · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
   obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
     (f := (iteratedDeriv 2 f)) (n := 1) hpx (smooth 2).contDiffOn
   rw [taylorWithin_eq_poly (iteratedDeriv 2 f) smooth 1
     (uIcc p x) hu left_mem_uIcc,taylor_two] at he
   have hy' : y ∈ Icc a b := by
     have hh := uIoo_subset_uIcc_self hy
     rw [mem_uIcc] at hh
     rcases hh with hh | hh <;> constructor <;> linarith [hp.1,hp.2,hx.1,hx.2]
   have hid : iteratedDeriv 2 (iteratedDeriv 2 f) y = iteratedDeriv 4 f y := by
     rw [iterated_iterated]
   norm_num at he
   change (iteratedDeriv 2 f) x-((iteratedDeriv 2 f) p+iteratedDeriv 3 f p*(x-p)) =
     iteratedDeriv 2 (iteratedDeriv 2 f) y*(x-p)^2/2 at he
   rw [hid] at he
   have he' : (iteratedDeriv 2 f) x-(iteratedDeriv 2 f) p-iteratedDeriv 3 f p*(x-p) =
       iteratedDeriv 4 f y*(x-p)^2/2 := by linarith only [he]
   rw [he',abs_div,abs_mul,abs_of_nonneg (sq_nonneg (x-p))]
   norm_num
   exact div_le_div_of_nonneg_right
     (mul_le_mul_of_nonneg_right (hfourth y hy') (sq_nonneg (x-p))) (by norm_num)

theorem affine_enclosure {a b p x v s e0 e1 M radius : ℝ}
 (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : 0 ≤ M)
 (hfourth : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ M)
 (hvalue : |(iteratedDeriv 2 f) p-v| ≤ e0)
 (hslope : |iteratedDeriv 3 f p-s| ≤ e1) (hrad : |x-p| ≤ radius) :
 |(iteratedDeriv 2 f) x-(v+s*(x-p))| ≤ e0+e1*radius+M*radius^2/2 := by
 have ht := local_remainder hp hx hfourth
 have hmul : |(iteratedDeriv 3 f p-s)*(x-p)| ≤ e1*radius := by
   rw [abs_mul]
   exact mul_le_mul hslope hrad (abs_nonneg _) ((abs_nonneg _).trans hslope)
 have hsq : (x-p)^2 ≤ radius^2 := by
   have hh := abs_le.mp hrad
   nlinarith [abs_nonneg (x-p)]
 have hcurv : M*(x-p)^2/2 ≤ M*radius^2/2 := by
   exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hM) (by norm_num)
 calc
   _ = |(((iteratedDeriv 2 f) x-(iteratedDeriv 2 f) p-iteratedDeriv 3 f p*(x-p))+
       ((iteratedDeriv 2 f) p-v))+(iteratedDeriv 3 f p-s)*(x-p)| := by congr 1; ring
   _ ≤ |((iteratedDeriv 2 f) x-(iteratedDeriv 2 f) p-iteratedDeriv 3 f p*(x-p))+
       ((iteratedDeriv 2 f) p-v)|+|(iteratedDeriv 3 f p-s)*(x-p)| := abs_add_le _ _
   _ ≤ (|(iteratedDeriv 2 f) x-(iteratedDeriv 2 f) p-iteratedDeriv 3 f p*(x-p)|+
       |(iteratedDeriv 2 f) p-v|)+|(iteratedDeriv 3 f p-s)*(x-p)| :=
     add_le_add (abs_add_le _ _) le_rfl
   _ ≤ M*(x-p)^2/2+e0+e1*radius := add_le_add (add_le_add ht hvalue) hmul
   _ ≤ e0+e1*radius+M*radius^2/2 := by linarith

def radius (a b p : ℚ) : ℚ := max |a-p| |b-p|
def bound (n : ℕ) (a b p v s M : ℚ) : ℚ :=
 WindowDerivativeAffineOracle.pointError n 2 21 p v+WindowDerivativeAffineOracle.pointError n 3 20 p s*radius a b p+M*(radius a b p)^2/2
def check (n : ℕ) (a b p v s M E : ℚ) : Bool := decide (
 1 ≤ n ∧ n ≤ 32 ∧ a ≤ p ∧ p ≤ b ∧ 0 ≤ M ∧ bound n a b p v s M ≤ E)

theorem actual {n : ℕ} {a b p v s M E : ℚ}
 (hc : check n a b p v s M E = true)
 (hfourth : ∀ y ∈ Icc (a:ℝ) b, |iteratedDeriv 4 f y| ≤ (M:ℝ))
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 |(iteratedDeriv 2 f) x-((v:ℝ)+(s:ℝ)*(x-p))| ≤ (E:ℝ) := by
 have hh : 1 ≤ n ∧ n ≤ 32 ∧ a ≤ p ∧ p ≤ b ∧ 0 ≤ M ∧ bound n a b p v s M ≤ E :=
   of_decide_eq_true hc
 have hleft : -(radius a b p) ≤ a-p := (abs_le.mp (le_max_left |a-p| |b-p|)).1
 have hright : b-p ≤ radius a b p := (abs_le.mp (le_max_right |a-p| |b-p|)).2
 have hl : (-(radius a b p):ℝ) ≤ (a:ℝ)-(p:ℝ) := by
   have ht : ((-(radius a b p):ℚ):ℝ) ≤ ((a-p:ℚ):ℝ) := Rat.cast_le.mpr hleft
   push_cast at ht
   exact ht
 have hu : (b:ℝ)-(p:ℝ) ≤ (radius a b p:ℝ) := by
   have ht : ((b-p:ℚ):ℝ) ≤ (radius a b p:ℝ) := Rat.cast_le.mpr hright
   push_cast at ht
   exact ht
 have hr : |x-(p:ℝ)| ≤ (radius a b p:ℝ) := by
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 have hv := WindowDerivativeAffineOracle.point_error hh.1 hh.2.1 (by norm_num : 2+21+1 = 24) p v
 have hs := WindowDerivativeAffineOracle.point_error hh.1 hh.2.1 (by norm_num : 3+20+1 = 24) p s
 have ht := affine_enclosure
   (show (p:ℝ) ∈ Icc (a:ℝ) b from ⟨Rat.cast_le.mpr hh.2.2.1,Rat.cast_le.mpr hh.2.2.2.1⟩)
   hx (show (0:ℝ) ≤ (M:ℝ) from Rat.cast_nonneg.mpr hh.2.2.2.2.1) hfourth hv hs hr
 have hbound : (bound n a b p v s M:ℝ) ≤ (E:ℝ) := Rat.cast_le.mpr hh.2.2.2.2.2
 unfold bound at hbound
 push_cast at hbound
 exact ht.trans hbound

theorem actual_w2 {n : ℕ} {a b p v s M E : ℚ}
 (hc : check n a b p v s M E = true)
 (hfourth : ∀ y ∈ Icc (a:ℝ) b, |iteratedDeriv 4 f y| ≤ (M:ℝ))
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 |WindowSecondVariation.w2 x-((v:ℝ)+(s:ℝ)*(x-p))| ≤ (E:ℝ) := by
 rw [WindowSecondVariation.w2_eq_actual]
 exact actual hc hfourth hx

set_option pp.fullNames true
#print axioms local_remainder
#print axioms affine_enclosure
#print axioms actual
#print axioms actual_w2
end StructuralGoal20261016.WindowCurvatureOracle
end
