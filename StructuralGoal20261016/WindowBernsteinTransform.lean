/- SPDX-License-Identifier: Apache-2.0
Exact degree-13 affine power-to-Bernstein conversion for the convexity
certificates. The polynomial identity is proved for arbitrary real inputs.
-/
import StructuralGoal20261016.WindowConvexityCertificate
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowBernsteinTransform
open WindowConvexityCertificate

def powerCoeff (a : ℕ → ℝ) (l h : ℝ) (j : ℕ) : ℝ :=
 ∑ i ∈ Finset.range 14, if j ≤ i then a i*(i.choose j:ℝ)*l^(i-j)*h^j else 0
def beta (a : ℕ → ℝ) (l h : ℝ) (k : ℕ) : ℝ :=
 ∑ j ∈ Finset.range 14, powerCoeff a l h j*(k.choose j:ℝ)/((13:ℕ).choose j:ℝ)

theorem monomial_basis13 (j : Fin 14) (u : ℝ) :
 u^(j:ℕ) = bernsteinEval 13
   (fun k => (k.choose (j:ℕ):ℝ)/((13:ℕ).choose (j:ℕ):ℝ)) u := by
 fin_cases j <;>
   norm_num [bernsteinEval,Finset.sum_range_succ,Nat.choose] <;> ring

theorem linear_basis13 (c : ℕ → ℝ) (u : ℝ) :
 (∑ j ∈ Finset.range 14, c j*u^j) = bernsteinEval 13
   (fun k => ∑ j ∈ Finset.range 14, c j*(k.choose j:ℝ)/((13:ℕ).choose j:ℝ)) u := by
 have he : (∑ j ∈ Finset.range 14, c j*u^j) =
     ∑ j ∈ Finset.range 14, c j*bernsteinEval 13
       (fun k => (k.choose j:ℝ)/((13:ℕ).choose j:ℝ)) u := by
   apply Finset.sum_congr rfl
   intro j hj
   rw [← monomial_basis13 ⟨j,Finset.mem_range.mp hj⟩]
 rw [he]
 unfold bernsteinEval
 simp_rw [Finset.mul_sum]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro k _
 simp_rw [Finset.sum_mul]
 apply Finset.sum_congr rfl
 intro j _
 ring

theorem affine_power13 (a : ℕ → ℝ) (l h u : ℝ) :
 (∑ i ∈ Finset.range 14, a i*(l+h*u)^i) =
   ∑ j ∈ Finset.range 14, powerCoeff a l h j*u^j := by
 norm_num [powerCoeff,Finset.sum_range_succ,Nat.choose]
 <;> ring

theorem affine_identity13 (a : ℕ → ℝ) (l h u : ℝ) :
 (∑ i ∈ Finset.range 14, a i*(l+h*u)^i) = bernsteinEval 13 (beta a l h) u := by
 rw [affine_power13,linear_basis13]
 rfl

theorem taylor_identity13 (f : ℝ → ℝ) (p a b u : ℝ) :
 taylorPoly f 13 p (a+(b-a)*u) =
   bernsteinEval 13 (beta (fun j => iteratedDeriv j f p/(j.factorial:ℝ)) (a-p) (b-a)) u := by
 have he : a+(b-a)*u-p = (a-p)+(b-a)*u := by ring
 simpa only [taylorPoly,he] using
   affine_identity13 (fun j => iteratedDeriv j f p/(j.factorial:ℝ)) (a-p) (b-a) u

#print axioms affine_identity13
#print axioms taylor_identity13
end StructuralGoal20261016.WindowBernsteinTransform
end
