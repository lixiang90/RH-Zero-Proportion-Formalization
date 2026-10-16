/- SPDX-License-Identifier: Apache-2.0
Compact rational Gram certificates for actual coherent basins. Every
transcendental input is discharged by WindowScalarBridge. The checker
verifies anchor coherence, positive adjacent quadratics and the diagonal
completion-of-squares margin entirely over the rationals.
-/
import StructuralGoal20261016.WindowGramDiagonal
import StructuralGoal20261016.WindowScalarBridge
import StructuralGoal20261016.WindowValueFlow
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set Finset
open scoped BigOperators
namespace StructuralGoal20261016.WindowGramRational
open WindowGramTransfer WindowDirectionalAffine
open WindowAnchorCertificateData WindowAnchorCertificate
open StructuralW10Followup20261016.NewLedger (W)

structure Basin where
 q : Fin 9 → ℚ
 index : Fin 41 → ℕ

def weightQ (e : Fin 41) : ℚ :=
 (StructuralW10Followup20261016.NewLedger.aN (pairI e) (pairJ e):ℚ)/10000000000
def pressureQ (r : Fin 9) : ℚ :=
 (StructuralW10Followup20261016.NewLedger.bN r:ℚ)/10000000000
def incidenceQ (e : Fin 41) (r : Fin 9) : ℚ :=
 (if (r:ℕ) < (pairJ e:ℕ) then 1 else 0)-
   (if (r:ℕ) < (pairI e:ℕ) then 1 else 0)
def spanQ (q : Fin 9 → ℚ) (e : Fin 41) : ℚ := ∑ r, q r*incidenceQ e r
def VQ (B : Basin) (e : Fin 41) : ℚ :=
 (row (B.index e)).lower-(row (B.index e)).error*WindowScalarBridge.radius (row (B.index e))
def SQ (B : Basin) (e : Fin 41) : ℚ := (row (B.index e)).slope
def AQ (B : Basin) (e : Fin 41) : ℚ := WindowConvexityAll.lower (row (B.index e)).center/2
def constantQ (B : Basin) : ℚ := (∑ r, pressureQ r*B.q r)+∑ e, weightQ e*VQ B e
def linearQ (B : Basin) (r : Fin 9) : ℚ := pressureQ r+∑ e, weightQ e*SQ B e*incidenceQ e r
def diagonalQ (B : Basin) (r : Fin 9) : ℚ :=
 weightQ (WindowGramDiagonal.adjacent r)*AQ B (WindowGramDiagonal.adjacent r)
def check (B : Basin) (c : ℚ) : Bool := decide (
 (∀ e, B.index e < 1567 ∧ (row (B.index e)).anchor = spanQ B.q e ∧ 0 ≤ AQ B e) ∧
 (∀ r, 0 < diagonalQ B r) ∧ c ≤ constantQ B-∑ r, (linearQ B r)^2/(4*diagonalQ B r))

def Region (B : Basin) (g : Fin 9 → ℝ) : Prop := ∀ e,
 span g e ∈ Icc (((row (B.index e)).center:ℝ)-21/100)
   (((row (B.index e)).center:ℝ)+21/100)

theorem weight_cast (e : Fin 41) : (weightQ e:ℝ) = weight e := by
 simpa only [weightQ,WindowValueFlow.weight_ledger] using (WindowValueFlow.weight_cast e).symm

theorem pressure_cast (r : Fin 9) : (pressureQ r:ℝ) = W.b r := by
 norm_num [pressureQ,StructuralW10Followup20261016.NewLedger.W,
   StructuralW10Followup20261016.NewLedger.b]

theorem incidence_cast (e : Fin 41) (r : Fin 9) : (incidenceQ e r:ℝ) = incidence e r := by
 unfold incidenceQ incidence
 split_ifs <;> norm_num

theorem span_cast (q : Fin 9 → ℚ) (e : Fin 41) :
 (spanQ q e:ℝ) = span (fun r => (q r:ℝ)) e := by
 rw [span_eq_sum]
 simp only [spanQ,Rat.cast_sum,Rat.cast_mul,incidence_cast]

theorem constant_cast (B : Basin) : (constantQ B:ℝ) =
 WindowGramDiagonal.constant (fun r => (B.q r:ℝ)) (fun e => (VQ B e:ℝ)) := by
 simp only [constantQ,WindowGramDiagonal.constant,pressure,
   Rat.cast_add,Rat.cast_sum,Rat.cast_mul,pressure_cast,weight_cast]

theorem linear_cast (B : Basin) (r : Fin 9) : (linearQ B r:ℝ) =
 WindowGramDiagonal.linear (fun e => (SQ B e:ℝ)) r := by
 simp only [linearQ,WindowGramDiagonal.linear,Rat.cast_add,Rat.cast_sum,
   Rat.cast_mul,pressure_cast,weight_cast,incidence_cast]

theorem diagonal_cast (B : Basin) (r : Fin 9) : (diagonalQ B r:ℝ) =
 WindowGramDiagonal.diagonal (fun e => (AQ B e:ℝ)) r := by
 simp only [diagonalQ,WindowGramDiagonal.diagonal,Rat.cast_mul,weight_cast]

theorem minorant_eq (B : Basin) (e : Fin 41) (x : ℝ) :
 WindowScalarBridge.minorant (row (B.index e)) x =
 (VQ B e:ℝ)+(SQ B e:ℝ)*(x-(row (B.index e)).anchor)+
   (AQ B e:ℝ)*(x-(row (B.index e)).anchor)^2 := by
 unfold WindowScalarBridge.minorant VQ SQ AQ
 push_cast
 ring

theorem actual {B : Basin} {c : ℚ} (hc : check B c = true)
 (g : Fin 9 → ℝ) (hregion : Region B g) : (c:ℝ) ≤ WindowGapEnergy.Fw24 g := by
 have hh : (∀ e, B.index e < 1567 ∧ (row (B.index e)).anchor = spanQ B.q e ∧ 0 ≤ AQ B e) ∧
     (∀ r, 0 < diagonalQ B r) ∧ c ≤ constantQ B-∑ r, (linearQ B r)^2/(4*diagonalQ B r) :=
   of_decide_eq_true hc
 apply WindowGramDiagonal.floor g (fun r => (B.q r:ℝ))
   (fun e => (VQ B e:ℝ)) (fun e => (SQ B e:ℝ)) (fun e => (AQ B e:ℝ)) (c:ℝ)
 · intro e
   exact Rat.cast_nonneg.mpr (hh.1 e).2.2
 · intro r
   rw [← diagonal_cast]
   exact Rat.cast_pos.mpr (hh.2.1 r)
 · have ht : (c:ℝ) ≤ ((constantQ B-∑ r, (linearQ B r)^2/(4*diagonalQ B r):ℚ):ℝ) :=
     Rat.cast_le.mpr hh.2.2
   push_cast at ht
   simpa only [constant_cast,linear_cast,diagonal_cast] using ht
 · intro e
   have hs := WindowScalarBridge.actual (B.index e) (hh.1 e).1 (hregion e)
   rw [minorant_eq] at hs
   have ha : ((row (B.index e)).anchor:ℝ) = span (fun r => (B.q r:ℝ)) e := by
     rw [(hh.1 e).2.1,span_cast]
   rw [ha] at hs
   exact hs

set_option pp.fullNames true
#print axioms weight_cast
#print axioms minorant_eq
#print axioms actual
end StructuralGoal20261016.WindowGramRational
end
