/- SPDX-License-Identifier: Apache-2.0
Certified graph facets for the actual first derivative, using only the
already checked separated grid. Clipping is performed in integer span
coordinates, and each facet is checked on every selected grid cell.
-/
import StructuralGoal20261016.WindowGridAll
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowDerivativeGraph
open WindowGridCertificate WindowGridCertificateData

abbrev Bounds (l u : ℤ) (k0 k1 : ℕ) : Prop :=
  61 ≤ k0 ∧ k0 ≤ k1 ∧ k1 < 2048 ∧ (k0:ℤ)*512 ≤ l ∧
  l ≤ u ∧ u ≤ ((k1+1:ℕ):ℤ)*512

def loEnd (l : ℤ) (k : ℕ) : ℤ := max l ((k:ℤ)*512)
def hiEnd (u : ℤ) (k : ℕ) : ℤ := min u (((k+1:ℕ):ℤ)*512)
def upperCut (l u : ℤ) (k : ℕ) (S : ℤ) : ℤ :=
  32768*(row (k-61)).upper-S*(if 0 ≤ S then loEnd l k else hiEnd u k)
def lowerCut (l u : ℤ) (k : ℕ) (S : ℤ) : ℤ :=
  32768*(row (k-61)).lower-S*(if 0 ≤ S then hiEnd u k else loEnd l k)

def upperCheck (l u : ℤ) (k0 k1 : ℕ) (S C : ℤ) : Bool := decide (
  Bounds l u k0 k1 ∧ ∀ j : Fin (k1+1-k0), upperCut l u (k0+(j:ℕ)) S ≤ C)
def lowerCheck (l u : ℤ) (k0 k1 : ℕ) (S C : ℤ) : Bool := decide (
  Bounds l u k0 k1 ∧ ∀ j : Fin (k1+1-k0), C ≤ lowerCut l u (k0+(j:ℕ)) S)

theorem covered {l u : ℤ} {k0 k1 : ℕ} (hb : Bounds l u k0 k1) {x : ℝ}
    (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    ∃ k : ℕ, k0 ≤ k ∧ k ≤ k1 ∧ x ∈ Icc (left k:ℝ) (right k:ℝ) ∧
      (loEnd l k:ℝ) ≤ 32768*x ∧ 32768*x ≤ (hiEnd u k:ℝ) := by
  rcases hb with ⟨hk0,horder,hk1,hL,hlu,hU⟩
  have hLR : (k0:ℝ)*512 ≤ (l:ℝ) := by exact_mod_cast hL
  have hUR : (u:ℝ) ≤ ((k1+1:ℕ):ℝ)*512 := by exact_mod_cast hU
  push_cast at hUR
  have hxl : (l:ℝ) ≤ 32768*x := by linarith [hx.1]
  have hxu : 32768*x ≤ (u:ℝ) := by linarith [hx.2]
  have hbig : x ∈ Icc (left k0:ℝ) (right k1:ℝ) := by
    unfold left right
    push_cast
    constructor <;> linarith
  obtain ⟨k,hkL,hkU,hkx⟩ := WindowGridRange.covered k0 k1 horder x hbig
  have hkl : (k:ℝ)*512 ≤ 32768*x := by
    have h := hkx.1
    unfold left at h
    push_cast at h
    linarith
  have hku : 32768*x ≤ ((k+1:ℕ):ℝ)*512 := by
    have h := hkx.2
    unfold right at h
    push_cast at h
    push_cast
    linarith
  refine ⟨k,hkL,hkU,hkx,?_,?_⟩
  · have h := max_le hxl hkl
    simpa [loEnd] using h
  · have h := le_min hxu hku
    simpa [hiEnd] using h

theorem upper_sound {l u S C : ℤ} {k0 k1 : ℕ}
    (hc : upperCheck l u k0 k1 S C = true) {x : ℝ}
    (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    (32768:ℝ)*1000000000000000*WindowGapEnergy.w1 x-32768*(S:ℝ)*x ≤ (C:ℝ) := by
  have hh : Bounds l u k0 k1 ∧
      ∀ j : Fin (k1+1-k0), upperCut l u (k0+(j:ℕ)) S ≤ C := of_decide_eq_true hc
  obtain ⟨k,hkL,hkU,hkx,hlo,hhi⟩ := covered hh.1 hx
  have hindex : k-k0 < k1+1-k0 := by omega
  have he : k0+(k-k0) = k := by omega
  have hcutI := hh.2 ⟨k-k0,hindex⟩
  change upperCut l u (k0+(k-k0)) S ≤ C at hcutI
  rw [he] at hcutI
  have hcut : ((upperCut l u k S:ℤ):ℝ) ≤ (C:ℝ) := by exact_mod_cast hcutI
  have hw := (WindowGridAll.derivative k (by omega) (by omega) hkx).2
  have hscaled : (32768:ℝ)*1000000000000000*WindowGapEnergy.w1 x ≤
      32768*((row (k-61)).upper:ℝ) := by
    norm_num at hw
    linarith
  by_cases hS : (0:ℤ) ≤ S
  · have hs : (0:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hm := mul_le_mul_of_nonneg_left hlo hs
    simp only [upperCut,if_pos hS,Int.cast_sub,Int.cast_mul,Int.cast_ofNat] at hcut
    nlinarith
  · have hs : (S:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hS)
    have hm := mul_le_mul_of_nonpos_left hhi hs
    simp only [upperCut,if_neg hS,Int.cast_sub,Int.cast_mul,Int.cast_ofNat] at hcut
    nlinarith

theorem lower_sound {l u S C : ℤ} {k0 k1 : ℕ}
    (hc : lowerCheck l u k0 k1 S C = true) {x : ℝ}
    (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    (C:ℝ) ≤ (32768:ℝ)*1000000000000000*WindowGapEnergy.w1 x-32768*(S:ℝ)*x := by
  have hh : Bounds l u k0 k1 ∧
      ∀ j : Fin (k1+1-k0), C ≤ lowerCut l u (k0+(j:ℕ)) S := of_decide_eq_true hc
  obtain ⟨k,hkL,hkU,hkx,hlo,hhi⟩ := covered hh.1 hx
  have hindex : k-k0 < k1+1-k0 := by omega
  have he : k0+(k-k0) = k := by omega
  have hcutI := hh.2 ⟨k-k0,hindex⟩
  change C ≤ lowerCut l u (k0+(k-k0)) S at hcutI
  rw [he] at hcutI
  have hcut : (C:ℝ) ≤ ((lowerCut l u k S:ℤ):ℝ) := by exact_mod_cast hcutI
  have hw := (WindowGridAll.derivative k (by omega) (by omega) hkx).1
  have hscaled : 32768*((row (k-61)).lower:ℝ) ≤
      (32768:ℝ)*1000000000000000*WindowGapEnergy.w1 x := by
    norm_num at hw
    linarith
  by_cases hS : (0:ℤ) ≤ S
  · have hs : (0:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    have hm := mul_le_mul_of_nonneg_left hhi hs
    simp only [lowerCut,if_pos hS,Int.cast_sub,Int.cast_mul,Int.cast_ofNat] at hcut
    nlinarith
  · have hs : (S:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hS)
    have hm := mul_le_mul_of_nonpos_left hlo hs
    simp only [lowerCut,if_neg hS,Int.cast_sub,Int.cast_mul,Int.cast_ofNat] at hcut
    nlinarith

set_option pp.fullNames true
#print axioms covered
#print axioms upper_sound
#print axioms lower_sound
end StructuralGoal20261016.WindowDerivativeGraph
end
