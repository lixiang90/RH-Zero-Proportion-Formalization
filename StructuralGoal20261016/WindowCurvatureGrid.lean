/- SPDX-License-Identifier: Apache-2.0
Selected second/fourth derivative cells and sound consecutive-cell queries.
The lookup index is untrusted: each query checks its range, cell identity
and required derivative flag. No correctness of a search algorithm is assumed.
-/
import StructuralGoal20261016.WindowCellDerivative
import StructuralGoal20261016.WindowGridRange
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCurvatureGrid
open WindowScalarMinorant
open WindowGridCertificate (left right center)

structure Row where
 cell : ℕ
 has2 : Bool
 mask2 : ℕ
 lower : ℤ
 upper : ℤ
 has4 : Bool
 mask4 : ℕ
 fourth : ℤ
def defaultRow : Row := ⟨0,false,0,0,0,false,0,0⟩

def check (r : Row) : Bool := decide (
 (r.has2 = true → WindowCellDerivative.check (center r.cell) 2 21
   (left r.cell) (right r.cell) r.mask2 ((r.lower:ℚ)/10^15) ((r.upper:ℚ)/10^15) = true) ∧
 (r.has4 = true → WindowCellDerivative.check (center r.cell) 4 19
   (left r.cell) (right r.cell) r.mask4 (-(r.fourth:ℚ)/10^15) ((r.fourth:ℚ)/10^15) = true))

def Valid (r : Row) : Prop := ∀ x ∈ Icc (left r.cell:ℝ) (right r.cell:ℝ),
 (r.has2 = true → (r.lower:ℝ)/10^15 ≤ iteratedDeriv 2 f x ∧
   iteratedDeriv 2 f x ≤ (r.upper:ℝ)/10^15) ∧
 (r.has4 = true → |iteratedDeriv 4 f x| ≤ (r.fourth:ℝ)/10^15)

theorem sound {r : Row} (hc : check r = true) : Valid r := by
 have hh :
   (r.has2 = true → WindowCellDerivative.check (center r.cell) 2 21
     (left r.cell) (right r.cell) r.mask2 ((r.lower:ℚ)/10^15) ((r.upper:ℚ)/10^15) = true) ∧
   (r.has4 = true → WindowCellDerivative.check (center r.cell) 4 19
     (left r.cell) (right r.cell) r.mask4 (-(r.fourth:ℚ)/10^15) ((r.fourth:ℚ)/10^15) = true) :=
   of_decide_eq_true hc
 intro x hx
 constructor
 · intro h2
   have h := WindowCellDerivative.interval (hh.1 h2) hx
   push_cast at h
   exact h
 · intro h4
   have h := WindowCellDerivative.interval (hh.2 h4) hx
   push_cast at h
   exact abs_le.mpr (by simpa only [neg_div] using h)

def secondCheck (rows : ℕ → Row) (index : ℕ → ℕ) (count k0 k1 : ℕ)
    (a b L U : ℚ) : Bool := decide (
 k0 ≤ k1 ∧ left k0 ≤ a ∧ b ≤ right k1 ∧
 ∀ j : Fin (k1+1-k0),
   index (k0+(j:ℕ)) < count ∧ (rows (index (k0+(j:ℕ)))).cell = k0+(j:ℕ) ∧
   (rows (index (k0+(j:ℕ)))).has2 = true ∧
   L ≤ ((rows (index (k0+(j:ℕ)))).lower:ℚ)/10^15 ∧
   ((rows (index (k0+(j:ℕ)))).upper:ℚ)/10^15 ≤ U)

theorem second {rows : ℕ → Row} {index : ℕ → ℕ} {count k0 k1 : ℕ}
 (hvalid : ∀ i, i < count → Valid (rows i)) {a b L U : ℚ}
 (hc : secondCheck rows index count k0 k1 a b L U = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ iteratedDeriv 2 f x ∧ iteratedDeriv 2 f x ≤ (U:ℝ) := by
 have hh : k0 ≤ k1 ∧ left k0 ≤ a ∧ b ≤ right k1 ∧
   ∀ j : Fin (k1+1-k0),
     index (k0+(j:ℕ)) < count ∧ (rows (index (k0+(j:ℕ)))).cell = k0+(j:ℕ) ∧
     (rows (index (k0+(j:ℕ)))).has2 = true ∧
     L ≤ ((rows (index (k0+(j:ℕ)))).lower:ℚ)/10^15 ∧
     ((rows (index (k0+(j:ℕ)))).upper:ℚ)/10^15 ≤ U := of_decide_eq_true hc
 obtain ⟨k,hk0,hk1,hxk⟩ := WindowGridRange.covered k0 k1 hh.1 x
   ⟨(Rat.cast_le.mpr hh.2.1).trans hx.1,hx.2.trans (Rat.cast_le.mpr hh.2.2.1)⟩
 have he : k0+(k-k0) = k := by omega
 have ht := hh.2.2.2 ⟨k-k0,by omega⟩
 change index (k0+(k-k0)) < count ∧ (rows (index (k0+(k-k0)))).cell = k0+(k-k0) ∧
   (rows (index (k0+(k-k0)))).has2 = true ∧
   L ≤ ((rows (index (k0+(k-k0)))).lower:ℚ)/10^15 ∧
   ((rows (index (k0+(k-k0)))).upper:ℚ)/10^15 ≤ U at ht
 rw [he] at ht
 have hxr : x ∈ Icc (left (rows (index k)).cell:ℝ) (right (rows (index k)).cell:ℝ) := by
   simpa only [ht.2.1] using hxk
 have hv := (hvalid (index k) ht.1 x hxr).1 ht.2.2.1
 have hl : (L:ℝ) ≤ ((((rows (index k)).lower:ℚ)/10^15:ℚ):ℝ) := Rat.cast_le.mpr ht.2.2.2.1
 have hu : (((((rows (index k)).upper:ℚ)/10^15:ℚ):ℝ)) ≤ (U:ℝ) := Rat.cast_le.mpr ht.2.2.2.2
 push_cast at hl hu
 exact ⟨hl.trans hv.1,hv.2.trans hu⟩

def fourthCheck (rows : ℕ → Row) (index : ℕ → ℕ) (count k0 k1 : ℕ)
    (a b M : ℚ) : Bool := decide (
 k0 ≤ k1 ∧ left k0 ≤ a ∧ b ≤ right k1 ∧
 ∀ j : Fin (k1+1-k0),
   index (k0+(j:ℕ)) < count ∧ (rows (index (k0+(j:ℕ)))).cell = k0+(j:ℕ) ∧
   (rows (index (k0+(j:ℕ)))).has4 = true ∧
   ((rows (index (k0+(j:ℕ)))).fourth:ℚ)/10^15 ≤ M)

theorem fourth {rows : ℕ → Row} {index : ℕ → ℕ} {count k0 k1 : ℕ}
 (hvalid : ∀ i, i < count → Valid (rows i)) {a b M : ℚ}
 (hc : fourthCheck rows index count k0 k1 a b M = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) : |iteratedDeriv 4 f x| ≤ (M:ℝ) := by
 have hh : k0 ≤ k1 ∧ left k0 ≤ a ∧ b ≤ right k1 ∧
   ∀ j : Fin (k1+1-k0),
     index (k0+(j:ℕ)) < count ∧ (rows (index (k0+(j:ℕ)))).cell = k0+(j:ℕ) ∧
     (rows (index (k0+(j:ℕ)))).has4 = true ∧
     ((rows (index (k0+(j:ℕ)))).fourth:ℚ)/10^15 ≤ M := of_decide_eq_true hc
 obtain ⟨k,hk0,hk1,hxk⟩ := WindowGridRange.covered k0 k1 hh.1 x
   ⟨(Rat.cast_le.mpr hh.2.1).trans hx.1,hx.2.trans (Rat.cast_le.mpr hh.2.2.1)⟩
 have he : k0+(k-k0) = k := by omega
 have ht := hh.2.2.2 ⟨k-k0,by omega⟩
 change index (k0+(k-k0)) < count ∧ (rows (index (k0+(k-k0)))).cell = k0+(k-k0) ∧
   (rows (index (k0+(k-k0)))).has4 = true ∧
   ((rows (index (k0+(k-k0)))).fourth:ℚ)/10^15 ≤ M at ht
 rw [he] at ht
 have hxr : x ∈ Icc (left (rows (index k)).cell:ℝ) (right (rows (index k)).cell:ℝ) := by
   simpa only [ht.2.1] using hxk
 have hv := (hvalid (index k) ht.1 x hxr).2 ht.2.2.1
 have hu : (((((rows (index k)).fourth:ℚ)/10^15:ℚ):ℝ)) ≤ (M:ℝ) := Rat.cast_le.mpr ht.2.2.2
 push_cast at hu
 exact hv.trans hu

set_option pp.fullNames true
#print axioms sound
#print axioms second
#print axioms fourth
end StructuralGoal20261016.WindowCurvatureGrid
end
