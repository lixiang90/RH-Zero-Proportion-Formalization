/- SPDX-License-Identifier: Apache-2.0
Arbitrary finite cosine-window energy identity.
Adapted from AMW.kernel_vAM through AMW.energy_total in the attributed Core.
The profile and both integrals are actual analytic functions, not premises.
No zero-counting or global gap floor is asserted by this module.
-/
import StructuralW10Followup20261016.NewWindows
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW
namespace StructuralGoal20261016.WindowEnergy

def v (N : ℕ) (d : ℕ → ℝ) (t : ℝ) : ℝ :=
 Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range N, d n * AMW.ek n t

theorem v_continuous (N : ℕ) (d : ℕ → ℝ) : Continuous (v N d) := by
 unfold v
 exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).add
   (continuous_finsetSum _ fun n _ => continuous_const.mul (AMW.ek_continuous n))

variable (N : ℕ) (d : ℕ → ℝ)
local notation "V" => v N d

theorem v_eq (t : ℝ) :
 V t = Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range N, d n * ek n t := rfl

theorem kernel_v {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
   ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * V t
     = (Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2) - Real.cos (Real.sqrt 2 * s))
       + ∑ n ∈ Finset.range N,
           d n * (((-1) ^ (n + 1) - ek n s) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hpt : ∀ t, |s - t| * V t
     = |s - t| * Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range N, d n * (|s - t| * ek n t) := by
   intro t
   rw [v_eq, mul_add, Finset.mul_sum]
   congr 1
   refine Finset.sum_congr rfl fun n _ => ?_
   ring
 simp_rw [hpt]
 have hI0 : IntervalIntegrable (fun t => |s - t| * Real.cos (Real.sqrt 2 * t)) volume (-(1:ℝ)/2) (1/2) :=
   (by fun_prop : Continuous fun t => |s - t| * Real.cos (Real.sqrt 2 * t)).intervalIntegrable _ _
 have hIn : ∀ n ∈ Finset.range N, IntervalIntegrable (fun t => d n * (|s - t| * ek n t))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   ((continuous_const.mul ((continuous_const.sub continuous_id).abs.mul (ek_continuous n)))).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, d n * (|s - t| * ek n t))
     volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul
     ((continuous_const.sub continuous_id).abs.mul (ek_continuous n))).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hI0 hS,
   intervalIntegral.integral_finsetSum hIn, kernel_cos hs.ne' hs1 hs2, hsq]
 congr 1
 · field_simp
 · refine Finset.sum_congr rfl fun n _ => ?_
   rw [intervalIntegral.integral_const_mul]
   congr 1
   unfold ek
   rw [kernel_cos (two_pi_k_pos n).ne' hs1 hs2]
   have e1 : 2 * π * ((n : ℝ) + 1) / 2 = ((n + 1 : ℕ) : ℝ) * π := by push_cast; ring
   rw [e1, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
   have hk := two_pi_k_pos n
   have hπ := Real.pi_pos
   field_simp
   ring
def beta (N : ℕ) (d : ℕ → ℝ) : ℝ :=
 Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2)
   + ∑ n ∈ Finset.range N, d n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
def r (N : ℕ) (d : ℕ → ℝ) (s : ℝ) : ℝ :=
 ∑ n ∈ Finset.range N, d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * ek n s
local notation "B" => beta N d
local notation "R" => r N d

theorem r_continuous : Continuous R := by
 unfold r
 exact continuous_finsetSum _ fun n _ => continuous_const.mul (ek_continuous n)
theorem v_add_kernel {s : ℝ} (hs1 : -(1:ℝ)/2 ≤ s) (hs2 : s ≤ 1/2) :
   V s + ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * V t = B + R s := by
 rw [kernel_v N d hs1 hs2, v_eq]
 unfold beta r
 have e : ∀ n ∈ Finset.range N, d n * ek n s
     + d n * (((-1) ^ (n + 1) - ek n s) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
     = d n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2))
       + d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * ek n s := by
   intro n _
   have hk := two_pi_k_pos n
   have hπ := Real.pi_pos
   field_simp
   ring
 have hsum := Finset.sum_congr rfl e
 rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
 linarith
theorem integral_v :
   ∫ t in (-(1:ℝ)/2)..(1/2), V t = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
 simp_rw [v_eq]
 have hIn : ∀ n ∈ Finset.range N, IntervalIntegrable (fun t => d n * ek n t)
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   (continuous_const.mul (ek_continuous n)).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, d n * ek n t)
     volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul (ek_continuous n)).intervalIntegrable _ _
 rw [intervalIntegral.integral_add (cos_lin_intervalIntegrable _) hS,
   intervalIntegral.integral_finsetSum hIn, integral_cos_sqrt2]
 have h0 : ∀ n ∈ Finset.range N, ∫ t in (-(1:ℝ)/2)..(1/2), d n * ek n t = 0 := by
   intro n _
   rw [intervalIntegral.integral_const_mul]
   unfold ek
   rw [integral_cos_k, mul_zero]
 rw [Finset.sum_eq_zero h0, add_zero]
theorem integral_v_ek {m : ℕ} (hm : m ∈ Finset.range N) :
   ∫ t in (-(1:ℝ)/2)..(1/2), V t * ek m t = Xk m + d m / 2 := by
 have hpt : ∀ t, V t * ek m t
     = Real.cos (Real.sqrt 2 * t) * ek m t + ∑ n ∈ Finset.range N, d n * (ek n t * ek m t) := by
   intro t
   rw [v_eq, add_mul, Finset.sum_mul]
   congr 1
   refine Finset.sum_congr rfl fun n _ => ?_
   ring
 simp_rw [hpt]
 have hI0 : IntervalIntegrable (fun t => Real.cos (Real.sqrt 2 * t) * ek m t) volume (-(1:ℝ)/2) (1/2) :=
   ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul (ek_continuous m)).intervalIntegrable _ _
 have hIn : ∀ n ∈ Finset.range N, IntervalIntegrable (fun t => d n * (ek n t * ek m t))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   (continuous_const.mul ((ek_continuous n).mul (ek_continuous m))).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N, d n * (ek n t * ek m t))
     volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul
     ((ek_continuous n).mul (ek_continuous m))).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hI0 hS, intervalIntegral.integral_finsetSum hIn]
 unfold ek
 rw [integral_cos_sqrt2_cos_k]
 congr 1
 have h : ∀ n ∈ Finset.range N, ∫ t in (-(1:ℝ)/2)..(1/2),
     d n * (Real.cos (2 * π * ((n : ℝ) + 1) * t) * Real.cos (2 * π * ((m : ℝ) + 1) * t))
     = if n = m then d n / 2 else 0 := by
   intro n _
   rw [intervalIntegral.integral_const_mul, integral_cos_k_cos_k]
   split_ifs <;> ring
 rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' (Finset.range N) m (fun n => d n / 2), if_pos hm]
def penalty (N : ℕ) (d : ℕ → ℝ) : ℝ :=
 ∑ n ∈ Finset.range N, d n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2))

local notation "P" => penalty N d

theorem energy_total :
   (∫ t in (-(1:ℝ)/2)..(1/2), V t ^ 2)
     + (∫ s in (-(1:ℝ)/2)..(1/2), V s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * V t)
     = Real.sin (Real.sqrt 2 / 2) ^ 2
       + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) + P := by
 have hs : (0:ℝ) < Real.sqrt 2 := by positivity
 have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hK : ∫ s in (-(1:ℝ)/2)..(1/2), V s * ∫ t in (-(1:ℝ)/2)..(1/2), |s - t| * V t
     = ∫ s in (-(1:ℝ)/2)..(1/2), V s * (B + R s - V s) := by
   apply intervalIntegral.integral_congr
   intro s hs'
   rw [Set.uIcc_of_le (by norm_num)] at hs'
   have := v_add_kernel N d hs'.1 hs'.2
   show V s * _ = V s * (B + R s - V s)
   congr 1
   linarith
 have hA : IntervalIntegrable (fun t => V t ^ 2) volume (-(1:ℝ)/2) (1/2) :=
   ((v_continuous N d).pow 2).intervalIntegrable _ _
 have hB : IntervalIntegrable (fun s => V s * (B + R s - V s)) volume (-(1:ℝ)/2) (1/2) :=
   ((v_continuous N d).mul ((continuous_const.add (r_continuous N d)).sub (v_continuous N d))).intervalIntegrable _ _
 rw [hK, ← intervalIntegral.integral_add hA hB]
 have hpt : ∀ s, V s ^ 2 + V s * (B + R s - V s)
     = B * V s + ∑ n ∈ Finset.range N,
         d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (V s * ek n s) := by
   intro s
   have alg : ∀ a b S : ℝ, a ^ 2 + a * (b + S - a) = b * a + a * S := fun a b S => by ring
   rw [alg, r, Finset.mul_sum]
   congr 1
   refine Finset.sum_congr rfl fun n _ => ?_
   ring
 simp_rw [hpt]
 have hIn : ∀ n ∈ Finset.range N, IntervalIntegrable
     (fun s => d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (V s * ek n s))
     volume (-(1:ℝ)/2) (1/2) := fun n _ =>
   (continuous_const.mul ((v_continuous N d).mul (ek_continuous n))).intervalIntegrable _ _
 have hS : IntervalIntegrable (fun s => ∑ n ∈ Finset.range N,
     d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (V s * ek n s)) volume (-(1:ℝ)/2) (1/2) :=
   (continuous_finsetSum _ fun n _ => continuous_const.mul
     ((v_continuous N d).mul (ek_continuous n))).intervalIntegrable _ _
 have hC : IntervalIntegrable (fun s => B * V s) volume (-(1:ℝ)/2) (1/2) :=
   (continuous_const.mul (v_continuous N d)).intervalIntegrable _ _
 rw [intervalIntegral.integral_add hC hS,
   intervalIntegral.integral_finsetSum hIn, intervalIntegral.integral_const_mul, integral_v]
 have hterm : ∀ n ∈ Finset.range N,
     ∫ s in (-(1:ℝ)/2)..(1/2), d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (V s * ek n s)
       = d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + d n / 2) := by
   intro n hn
   rw [intervalIntegral.integral_const_mul, integral_v_ek N d hn]
 rw [Finset.sum_congr rfl hterm]
 unfold beta penalty
 have hEL : ∀ n ∈ Finset.range N,
     d n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
       + d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + d n / 2)
     = d n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
   intro n _
   have h := euler_lagrange n
   have hk2 : (0:ℝ) < 2 * π ^ 2 * ((n : ℝ) + 1) ^ 2 := by positivity
   have e : d n * ((-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
       + d n * (1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * (Xk n + d n / 2)
       = d n * ((1 - 1 / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) * Xk n
           + (-1) ^ (n + 1) / (2 * π ^ 2 * ((n : ℝ) + 1) ^ 2) * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)))
         + d n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2)) := by
     field_simp
     ring
   rw [e, h, mul_zero, zero_add]
 have hsum := Finset.sum_congr rfl hEL
 rw [Finset.sum_add_distrib] at hsum
 rw [add_mul, Finset.sum_mul]
 have e2 : (Real.sin (Real.sqrt 2 / 2) / Real.sqrt 2 + Real.cos (Real.sqrt 2 / 2))
       * (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
     = Real.sin (Real.sqrt 2 / 2) ^ 2 + Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * Real.cos (Real.sqrt 2 / 2) := by
   field_simp
 rw [e2]
 linarith

def H (N : ℕ) (d : ℕ → ℝ) : ℝ :=
  2 - ((∫ t in (-(1:ℝ)/2)..(1/2), v N d t ^ 2) +
    (∫ s in (-(1:ℝ)/2)..(1/2), v N d s *
      ∫ t in (-(1:ℝ)/2)..(1/2), |s-t| * v N d t)) /
    (∫ t in (-(1:ℝ)/2)..(1/2), v N d t) ^ 2

theorem H_eq : H N d =
  3 / 2 - Real.cos (Real.sqrt 2 / 2) /
    (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)) -
    penalty N d / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) := by
  unfold H
  rw [energy_total, integral_v]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsin := AMW.sin_theta0_pos
  rw [mul_pow, hsq]
  field_simp
  ring_nf
  rw [hsq]
  ring

#print axioms kernel_v
#print axioms integral_v
#print axioms integral_v_ek
#print axioms energy_total
#print axioms H_eq
end StructuralGoal20261016.WindowEnergy
end
