/- SPDX-License-Identifier: Apache-2.0
One diagonal reduction for all coherent Gram basins. Only the nine adjacent
positive quadratic terms are retained. The common graph identity is proved
once; later basin certificates need only rational coefficient comparisons.
-/
import StructuralGoal20261016.WindowDirectionalAffine
import StructuralGoal20261016.WindowDifferenceCell
import StructuralW10Unconditional20261016.DiagonalPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Finset
open scoped BigOperators
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowGramDiagonal
open WindowGramTransfer WindowDirectionalAffine
open StructuralW10Followup20261016.NewLedger (W)

def adjacent : Fin 9 → Fin 41 := ![0,7,15,22,28,33,36,39,40]

theorem adjacent_injective : Function.Injective adjacent := by decide +kernel

theorem pairI_adjacent : ∀ r : Fin 9, pairI (adjacent r) = r.castSucc := by decide +kernel
theorem pairJ_adjacent : ∀ r : Fin 9, pairJ (adjacent r) = r.succ := by decide +kernel

theorem span_adjacent (g : Fin 9 → ℝ) (r : Fin 9) : span g (adjacent r) = g r := by
 rw [span,pairJ_adjacent,pairI_adjacent]
 exact WindowDifferenceCell.adjacent_difference g r

theorem span_sub (g q : Fin 9 → ℝ) (e : Fin 41) :
 span g e-span q e = ∑ r, (g r-q r)*incidence e r := by
 rw [span_eq_sum,span_eq_sum,← Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro r _
 ring

def constant (q : Fin 9 → ℝ) (V : Fin 41 → ℝ) : ℝ := pressure q+∑ e, weight e*V e
def linear (S : Fin 41 → ℝ) (r : Fin 9) : ℝ :=
 W.b r+∑ e, weight e*S e*incidence e r
def diagonal (A : Fin 41 → ℝ) (r : Fin 9) : ℝ := weight (adjacent r)*A (adjacent r)

theorem linear_span_sum (g q : Fin 9 → ℝ) (S : Fin 41 → ℝ) :
 (∑ e : Fin 41, weight e*S e*(span g e-span q e)) =
   ∑ r : Fin 9, (∑ e : Fin 41, weight e*S e*incidence e r)*(g r-q r) := by
 simp_rw [span_sub,Finset.mul_sum,Finset.sum_mul]
 rw [Finset.sum_comm]
 apply Finset.sum_congr rfl
 intro r _
 apply Finset.sum_congr rfl
 intro e _
 ring

theorem pressure_sub (g q : Fin 9 → ℝ) :
 pressure g = pressure q+∑ r, W.b r*(g r-q r) := by
 unfold pressure
 simp_rw [mul_sub,Finset.sum_sub_distrib]
 ring

theorem linear_identity (g q : Fin 9 → ℝ) (V S : Fin 41 → ℝ) :
 pressure g+(∑ e : Fin 41, weight e*(V e+S e*(span g e-span q e))) =
 constant q V+∑ r, linear S r*(g r-q r) := by
 have hS : (∑ e : Fin 41, weight e*(S e*(span g e-span q e))) =
     ∑ r : Fin 9, (∑ e : Fin 41, weight e*S e*incidence e r)*(g r-q r) := by
   simpa only [mul_assoc] using linear_span_sum g q S
 simp only [constant,linear,mul_add,add_mul,Finset.sum_add_distrib]
 rw [pressure_sub g q,hS]
 ring

theorem quadratic_lower (g q : Fin 9 → ℝ) (A : Fin 41 → ℝ) (hA : ∀ e, 0 ≤ A e) :
 (∑ r : Fin 9, diagonal A r*(g r-q r)^2) ≤
   ∑ e : Fin 41, weight e*A e*(span g e-span q e)^2 := by
 let T : Fin 41 → ℝ := fun e => weight e*A e*(span g e-span q e)^2
 have hT : ∀ e, 0 ≤ T e := by
   intro e
   exact mul_nonneg (mul_nonneg (weight_nonneg e) (hA e)) (sq_nonneg _)
 have he : (∑ e ∈ Finset.univ.image adjacent, T e) = ∑ r : Fin 9, T (adjacent r) := by
   exact Finset.sum_image (by intro a _ b _ hab; exact adjacent_injective hab)
 have hsum : (∑ r : Fin 9, T (adjacent r)) ≤ ∑ e : Fin 41, T e := by
   rw [← he]
   exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => hT e)
 simpa only [T,diagonal,span_adjacent] using hsum

theorem actual_lower (g q : Fin 9 → ℝ) (V S A : Fin 41 → ℝ)
 (hA : ∀ e, 0 ≤ A e)
 (hscalar : ∀ e, V e+S e*(span g e-span q e)+A e*(span g e-span q e)^2 ≤
   WindowKernel.w 24 WindowKernel.d24 (span g e)) :
 constant q V+(∑ r, (linear S r*(g r-q r)+diagonal A r*(g r-q r)^2)) ≤
 WindowGapEnergy.Fw24 g := by
 have hlin := linear_identity g q V S
 have hquad := quadratic_lower g q A hA
 have hs := scalar_sum_le g
   (fun e => V e+S e*(span g e-span q e)+A e*(span g e-span q e)^2) hscalar
 have hexpand : pressure g+(∑ e : Fin 41,
     weight e*(V e+S e*(span g e-span q e)+A e*(span g e-span q e)^2)) =
     (pressure g+∑ e : Fin 41, weight e*(V e+S e*(span g e-span q e)))+
       ∑ e : Fin 41, weight e*A e*(span g e-span q e)^2 := by
   simp only [mul_add,Finset.sum_add_distrib]
   ring
 rw [hexpand,hlin] at hs
 rw [Finset.sum_add_distrib]
 have hlo : constant q V+((∑ r, linear S r*(g r-q r))+
     ∑ r, diagonal A r*(g r-q r)^2) ≤
     (constant q V+∑ r, linear S r*(g r-q r))+
       ∑ e, weight e*A e*(span g e-span q e)^2 := by linarith only [hquad]
 exact hlo.trans hs

theorem floor (g q : Fin 9 → ℝ) (V S A : Fin 41 → ℝ) (c : ℝ)
 (hA : ∀ e, 0 ≤ A e) (hd : ∀ r, 0 < diagonal A r)
 (hcertificate : c ≤ constant q V-∑ r, (linear S r)^2/(4*diagonal A r))
 (hscalar : ∀ e, V e+S e*(span g e-span q e)+A e*(span g e-span q e)^2 ≤
   WindowKernel.w 24 WindowKernel.d24 (span g e)) : c ≤ WindowGapEnergy.Fw24 g := by
 have hl := StructuralW10Unconditional20261016.DiagonalPolynomial.lower
   (constant q V) c (linear S) (diagonal A) hd hcertificate (fun r => g r-q r)
 exact hl.trans (actual_lower g q V S A hA hscalar)

set_option pp.fullNames true
#print axioms span_adjacent
#print axioms linear_identity
#print axioms quadratic_lower
#print axioms actual_lower
#print axioms floor
end StructuralGoal20261016.WindowGramDiagonal
end
