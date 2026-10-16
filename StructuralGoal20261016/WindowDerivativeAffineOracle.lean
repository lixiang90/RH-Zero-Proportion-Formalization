/- SPDX-License-Identifier: Apache-2.0
Actual local affine enclosures for w'. The finite check recomputes point
errors from the proved integer-centre coefficients and compares only the
final quantized error payment. It does not require the old narrow decimal
point intervals to be theorems. A cell-wide bound on w''' supplies the
local second-order remainder; the separated grid provides that input.
-/
import StructuralGoal20261016.WindowFixedDerivative
import StructuralGoal20261016.WindowFiniteMoveScalar
import StructuralGoal20261016.WindowGapEnergy
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowDerivativeAffineOracle
open WindowScalarMinorant WindowConvexityCertificate
open WindowFixedInterval WindowFixedRational
open WindowDerivativeTableArithmetic (derivative_remainder)

theorem iterated_one_eq : iteratedDeriv 1 f = WindowGapEnergy.w1 := by
 funext x
 rw [iteratedDeriv_one]
 exact (WindowGapEnergy.w_hasDerivAt x).deriv

theorem smooth (r : ℕ) : ContDiff ℝ r WindowGapEnergy.w1 := by
 rw [← iterated_one_eq]
 exact w_iterated_contDiff 24 WindowKernel.d24 1 r

theorem w1_hasDerivAt (x : ℝ) :
 HasDerivAt WindowGapEnergy.w1 (iteratedDeriv 2 f x) x := by
 rw [← iterated_one_eq]
 exact WindowFiniteMoveScalar.w_iterated_hasDerivAt 1 x

theorem taylor_one (p x : ℝ) :
 taylorPoly WindowGapEnergy.w1 1 p x =
 WindowGapEnergy.w1 p+iteratedDeriv 2 f p*(x-p) := by
 simp only [taylorPoly,Finset.sum_range_succ,Finset.sum_range_zero,
   zero_add,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,
   pow_zero,pow_one,mul_one,iteratedDeriv_zero,iteratedDeriv_one]
 rw [(w1_hasDerivAt p).deriv]

theorem local_remainder {a b p x M : ℝ}
 (hp : p ∈ Icc a b) (hx : x ∈ Icc a b)
 (hthird : ∀ y ∈ Icc a b, |iteratedDeriv 3 f y| ≤ M) :
 |WindowGapEnergy.w1 x-WindowGapEnergy.w1 p-iteratedDeriv 2 f p*(x-p)| ≤
   M*(x-p)^2/2 := by
 by_cases hpx : p = x
 · subst x
   simp
 · have hu : UniqueDiffOn ℝ (uIcc p x) := uniqueDiffOn_Icc (by grind)
   obtain ⟨y,hy,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
     (f := WindowGapEnergy.w1) (n := 1) hpx (smooth 2).contDiffOn
   rw [taylorWithin_eq_poly WindowGapEnergy.w1 smooth 1
     (uIcc p x) hu left_mem_uIcc,taylor_one] at he
   have hy' : y ∈ Icc a b := by
     have hh := uIoo_subset_uIcc_self hy
     rw [mem_uIcc] at hh
     rcases hh with hh | hh <;> constructor <;> linarith [hp.1,hp.2,hx.1,hx.2]
   have hid : iteratedDeriv 2 WindowGapEnergy.w1 y = iteratedDeriv 3 f y := by
     rw [← iterated_one_eq,iterated_iterated]
   norm_num at he
   change WindowGapEnergy.w1 x-(WindowGapEnergy.w1 p+iteratedDeriv 2 f p*(x-p)) =
     iteratedDeriv 2 WindowGapEnergy.w1 y*(x-p)^2/2 at he
   rw [hid] at he
   have he' : WindowGapEnergy.w1 x-WindowGapEnergy.w1 p-iteratedDeriv 2 f p*(x-p) =
       iteratedDeriv 3 f y*(x-p)^2/2 := by linarith only [he]
   rw [he',abs_div,abs_mul,abs_of_nonneg (sq_nonneg (x-p))]
   norm_num
   exact div_le_div_of_nonneg_right
     (mul_le_mul_of_nonneg_right (hthird y hy') (sq_nonneg (x-p))) (by norm_num)

theorem affine_enclosure {a b p x v s e0 e1 M radius : ℝ}
 (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : 0 ≤ M)
 (hthird : ∀ y ∈ Icc a b, |iteratedDeriv 3 f y| ≤ M)
 (hvalue : |WindowGapEnergy.w1 p-v| ≤ e0)
 (hslope : |iteratedDeriv 2 f p-s| ≤ e1) (hrad : |x-p| ≤ radius) :
 |WindowGapEnergy.w1 x-(v+s*(x-p))| ≤ e0+e1*radius+M*radius^2/2 := by
 have ht := local_remainder hp hx hthird
 have hmul : |(iteratedDeriv 2 f p-s)*(x-p)| ≤ e1*radius := by
   rw [abs_mul]
   exact mul_le_mul hslope hrad (abs_nonneg _) ((abs_nonneg _).trans hslope)
 have hsq : (x-p)^2 ≤ radius^2 := by
   have hh := abs_le.mp hrad
   nlinarith [abs_nonneg (x-p)]
 have hcurv : M*(x-p)^2/2 ≤ M*radius^2/2 := by
   exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hM) (by norm_num)
 calc
   _ = |((WindowGapEnergy.w1 x-WindowGapEnergy.w1 p-iteratedDeriv 2 f p*(x-p))+
       (WindowGapEnergy.w1 p-v))+(iteratedDeriv 2 f p-s)*(x-p)| := by congr 1; ring
   _ ≤ |(WindowGapEnergy.w1 x-WindowGapEnergy.w1 p-iteratedDeriv 2 f p*(x-p))+
       (WindowGapEnergy.w1 p-v)|+|(iteratedDeriv 2 f p-s)*(x-p)| := abs_add_le _ _
   _ ≤ (|WindowGapEnergy.w1 x-WindowGapEnergy.w1 p-iteratedDeriv 2 f p*(x-p)|+
       |WindowGapEnergy.w1 p-v|)+|(iteratedDeriv 2 f p-s)*(x-p)| :=
     add_le_add (abs_add_le _ _) le_rfl
   _ ≤ M*(x-p)^2/2+e0+e1*radius := add_le_add (add_le_add ht hvalue) hmul
   _ ≤ e0+e1*radius+M*radius^2/2 := by linarith

def pointBox (n q d : ℕ) (p : ℚ) : FI :=
 WindowFixedPolynomial.poly (WindowFixedDerivative.coeff n q) (p-n) d
def pointError (n q d : ℕ) (p v : ℚ) : ℚ :=
 max |(decode (pointBox n q d p)).1-v| |(decode (pointBox n q d p)).2-v|+
   WindowDerivativeTableArithmetic.error (p-n) d

theorem point_error {n q d : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32)
 (hqd : q+d+1 = 24) (p v : ℚ) :
 |iteratedDeriv q f p-(v:ℝ)| ≤ (pointError n q d p v:ℝ) := by
 have hp := WindowFixedPolynomial.poly_sound (iteratedDeriv q f) (n:ℝ)
   (WindowFixedDerivative.coeff n q) (p-n) d
   (WindowFixedDerivative.coeff_sound hn0 hn1 (by omega))
 have he : (n:ℝ)+((p-n:ℚ):ℝ) = p := by push_cast; ring
 rw [he] at hp
 change WindowRationalInterval.Holds (decode (pointBox n q d p))
   (taylorPoly (iteratedDeriv q f) d (n:ℝ) p) at hp
 let I := decode (pointBox n q d p)
 let A := max |I.1-v| |I.2-v|
 have hl : |(I.1:ℝ)-(v:ℝ)| ≤ (A:ℝ) := by
   have hh : ((|I.1-v|:ℚ):ℝ) ≤ (A:ℝ) := Rat.cast_le.mpr (le_max_left _ _)
   push_cast at hh
   exact hh
 have hu : |(I.2:ℝ)-(v:ℝ)| ≤ (A:ℝ) := by
   have hh : ((|I.2-v|:ℚ):ℝ) ≤ (A:ℝ) := Rat.cast_le.mpr (le_max_right _ _)
   push_cast at hh
   exact hh
 have hpoly : |taylorPoly (iteratedDeriv q f) d (n:ℝ) p-(v:ℝ)| ≤ (A:ℝ) := by
   rw [abs_le]
   exact ⟨by linarith [hp.1,(abs_le.mp hl).1],by linarith [hp.2,(abs_le.mp hu).2]⟩
 have hr := derivative_remainder q d hqd (n:ℝ) p
 have herr : (44/7:ℝ)^24*|((p:ℝ)-n)|^(d+1)/((d+1).factorial:ℝ) =
     (WindowDerivativeTableArithmetic.error (p-n) d:ℝ) := by
   unfold WindowDerivativeTableArithmetic.error
   push_cast
   rfl
 rw [herr] at hr
 calc
   _ = |(iteratedDeriv q f p-taylorPoly (iteratedDeriv q f) d (n:ℝ) p)+
       (taylorPoly (iteratedDeriv q f) d (n:ℝ) p-v)| := by congr 1; ring
   _ ≤ |iteratedDeriv q f p-taylorPoly (iteratedDeriv q f) d (n:ℝ) p|+
       |taylorPoly (iteratedDeriv q f) d (n:ℝ) p-v| := abs_add_le _ _
   _ ≤ (WindowDerivativeTableArithmetic.error (p-n) d:ℝ)+(A:ℝ) := add_le_add hr hpoly
   _ = (pointError n q d p v:ℝ) := by
     change (WindowDerivativeTableArithmetic.error (p-n) d:ℝ)+(A:ℝ) =
       ((A+WindowDerivativeTableArithmetic.error (p-n) d:ℚ):ℝ)
     push_cast
     ring

def radius (a b p : ℚ) : ℚ := max |a-p| |b-p|
def bound (n : ℕ) (a b p v s M : ℚ) : ℚ :=
 pointError n 1 22 p v+pointError n 2 21 p s*radius a b p+M*(radius a b p)^2/2
def check (n : ℕ) (a b p v s M E : ℚ) : Bool := decide (
 1 ≤ n ∧ n ≤ 32 ∧ a ≤ p ∧ p ≤ b ∧ 0 ≤ M ∧ bound n a b p v s M ≤ E)

theorem actual {n : ℕ} {a b p v s M E : ℚ}
 (hc : check n a b p v s M E = true)
 (hthird : ∀ y ∈ Icc (a:ℝ) b, |iteratedDeriv 3 f y| ≤ (M:ℝ))
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 |WindowGapEnergy.w1 x-((v:ℝ)+(s:ℝ)*(x-p))| ≤ (E:ℝ) := by
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
 have hv := point_error hh.1 hh.2.1 (by norm_num : 1+22+1 = 24) p v
 rw [iterated_one_eq] at hv
 have hs := point_error hh.1 hh.2.1 (by norm_num : 2+21+1 = 24) p s
 have ht := affine_enclosure
   (show (p:ℝ) ∈ Icc (a:ℝ) b from ⟨Rat.cast_le.mpr hh.2.2.1,Rat.cast_le.mpr hh.2.2.2.1⟩)
   hx (show (0:ℝ) ≤ (M:ℝ) from Rat.cast_nonneg.mpr hh.2.2.2.2.1) hthird hv hs hr
 have hbound : (bound n a b p v s M:ℝ) ≤ (E:ℝ) := Rat.cast_le.mpr hh.2.2.2.2.2
 unfold bound at hbound
 push_cast at hbound
 exact ht.trans hbound

set_option pp.fullNames true
#print axioms local_remainder
#print axioms affine_enclosure
#print axioms point_error
#print axioms actual
end StructuralGoal20261016.WindowDerivativeAffineOracle
end
