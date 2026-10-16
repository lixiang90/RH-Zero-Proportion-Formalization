/- SPDX-License-Identifier: Apache-2.0
Actual Fourier integral and sinc formula for arbitrary finite cosine profiles.
The generic integral identities adapt AMW.KfunAM_eq_sinc from the Core.
These identify the research kernel with the analytic Fourier kernel; they do
not assert the unproved global floor or a new zero-counting bound.
-/
import StructuralGoal20261016.WindowEnergy
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW
namespace StructuralGoal20261016.WindowKernel
open StructuralGoal20261016.WindowEnergy

def K (N : ℕ) (d : ℕ → ℝ) (x : ℝ) : ℝ :=
 ∫ t in (-(1:ℝ)/2)..(1/2), v N d t * Real.cos (2 * π * x * t)

def k (N : ℕ) (d : ℕ → ℝ) (x : ℝ) : ℝ := K N d x / K N d 0
def w (N : ℕ) (d : ℕ → ℝ) (x : ℝ) : ℝ := k N d x ^ 2

theorem integral_cos_cos_sinc (a b : ℝ) :
 (∫ t in (-(1:ℝ)/2)..(1/2), Real.cos (a*t) * Real.cos (b*t)) =
   (Real.sinc ((a-b)/2) + Real.sinc ((a+b)/2))/2 := by
 simp_rw [AMW.cos_mul_cos_eq]
 rw [intervalIntegral.integral_div,
   intervalIntegral.integral_add (AMW.cos_lin_intervalIntegrable _)
     (AMW.cos_lin_intervalIntegrable _),
   AMW.integral_cos_mul_sinc, AMW.integral_cos_mul_sinc]

theorem K_eq_sinc (N : ℕ) (d : ℕ → ℝ) (x : ℝ) :
 K N d x = AMW.KMT x + ∑ n ∈ Finset.range N, d n *
   ((Real.sinc (π * (x - ((n : ℝ)+1))) +
     Real.sinc (π * (x + ((n : ℝ)+1)))) / 2) := by
 unfold K v
 have hpt : ∀ t : ℝ,
   (Real.cos (Real.sqrt 2*t) + ∑ n ∈ Finset.range N, d n * ek n t) *
       Real.cos (2*π*x*t) =
     Real.cos (Real.sqrt 2*t) * Real.cos (2*π*x*t) +
       ∑ n ∈ Finset.range N, d n * (ek n t * Real.cos (2*π*x*t)) := by
   intro t
   rw [add_mul, Finset.sum_mul]
   congr 1
   apply Finset.sum_congr rfl
   intro n _
   ring
 simp_rw [hpt]
 have hI0 : IntervalIntegrable
     (fun t => Real.cos (Real.sqrt 2*t) * Real.cos (2*π*x*t))
     volume (-(1:ℝ)/2) (1/2) := (by fun_prop : Continuous _).intervalIntegrable _ _
 have hIn : ∀ n ∈ Finset.range N, IntervalIntegrable
     (fun t => d n * (ek n t * Real.cos (2*π*x*t)))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
       (continuous_const.mul ((ek_continuous n).mul (by fun_prop))).intervalIntegrable _ _
 have hS : IntervalIntegrable
     (fun t => ∑ n ∈ Finset.range N, d n * (ek n t * Real.cos (2*π*x*t)))
     volume (-(1:ℝ)/2) (1/2) :=
       (continuous_finsetSum _ fun n _ => continuous_const.mul
         ((ek_continuous n).mul (by fun_prop))).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hI0 hS,
   intervalIntegral.integral_finsetSum hIn, integral_cos_cos_sinc]
 change AMW.KMT x + _ = _
 congr 1
 apply Finset.sum_congr rfl
 intro n _
 rw [intervalIntegral.integral_const_mul]
 congr 1
 unfold ek
 rw [integral_cos_cos_sinc]
 have e1 : (2*π*((n : ℝ)+1)-2*π*x)/2 = -(π*(x-((n : ℝ)+1))) := by ring
 have e2 : (2*π*((n : ℝ)+1)+2*π*x)/2 = π*(x+((n : ℝ)+1)) := by ring
 rw [e1, e2, Real.sinc_neg]

theorem K_zero (N : ℕ) (d : ℕ → ℝ) :
 K N d 0 = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
 unfold K
 simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
 exact WindowEnergy.integral_v N d

theorem K_zero_pos (N : ℕ) (d : ℕ → ℝ) : 0 < K N d 0 := by
 rw [K_zero]
 exact mul_pos (by positivity) AMW.sin_theta0_pos

theorem K_neg (N : ℕ) (d : ℕ → ℝ) (x : ℝ) : K N d (-x) = K N d x := by
 unfold K
 congr 1
 funext t
 rw [show 2*π*(-x)*t = -(2*π*x*t) by ring, Real.cos_neg]

theorem k_zero (N : ℕ) (d : ℕ → ℝ) : k N d 0 = 1 := by
 unfold k
 exact div_self (K_zero_pos N d).ne'

theorem abs_K_le (N : ℕ) (d : ℕ → ℝ)
    (hpos : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v N d t) (x : ℝ) :
    |K N d x| ≤ K N d 0 := by
 have hab : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
 have hzero : K N d 0 = ∫ t in (-(1:ℝ)/2)..(1/2), v N d t := by
   unfold K
   simp
 rw [hzero]
 unfold K
 calc
   _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |v N d t * Real.cos (2*π*x*t)| :=
     intervalIntegral.abs_integral_le_integral_abs hab
   _ ≤ _ := by
     apply intervalIntegral.integral_mono_on hab
     · exact (((v_continuous N d).mul (by fun_prop)).abs).intervalIntegrable _ _
     · exact (v_continuous N d).intervalIntegrable _ _
     · intro t ht
       rw [abs_mul, abs_of_nonneg (hpos t ht)]
       exact mul_le_of_le_one_right (hpos t ht) (Real.abs_cos_le_one _)

theorem abs_k_le_one (N : ℕ) (d : ℕ → ℝ)
    (hpos : ∀ t ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v N d t) (x : ℝ) :
    |k N d x| ≤ 1 := by
 rw [k, abs_div, abs_of_pos (K_zero_pos N d), div_le_one (K_zero_pos N d)]
 exact abs_K_le N d hpos x

def d24 (n : ℕ) : ℝ :=
 (StructuralW10Followup20261016.NewWindows.nums24 n : ℝ) / 1000000000

theorem v24_eq (t : ℝ) :
 v 24 d24 t = StructuralW10Followup20261016.NewWindows.v24 t := by
 unfold v StructuralW10Followup20261016.NewWindows.v24
   StructuralW10Followup20261016.WindowProfileGeneral.profile
   StructuralW10Followup20261016.WindowProfileGeneral.perturb
   StructuralW10Followup20261016.NewWindows.c24
   d24 ek
 rw [Fin.sum_univ_eq_sum_range
   (fun n => (StructuralW10Followup20261016.NewWindows.nums24 n : ℝ) /
     1000000000 * Real.cos (2 * π * ((n : ℝ)+1) * t)) 24]

theorem v24_nonneg (t : ℝ) (ht : t ∈ Icc (-(1:ℝ)/2) (1/2)) :
 0 ≤ v 24 d24 t := by
 rw [v24_eq]
 exact (StructuralW10Followup20261016.NewWindows.v24_positive
   (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])).le

theorem k24_abs_le_one (x : ℝ) : |k 24 d24 x| ≤ 1 :=
 abs_k_le_one 24 d24 v24_nonneg x

#print axioms K_eq_sinc
#print axioms K_zero
#print axioms abs_k_le_one
#print axioms v24_eq
#print axioms k24_abs_le_one
end StructuralGoal20261016.WindowKernel
end
