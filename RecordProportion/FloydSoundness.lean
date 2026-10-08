import Mathlib

/-
Soundness of the simultaneous 9-by-9 Int Floyd update used by the finite certificate.
This file depends only on Mathlib and does not import the certificate data.
-/

namespace RHWeilRecord.FloydSoundness

def floydStep (d : Array Int) (k : Nat) : Array Int :=
  ((List.range 81).map fun slot =>
    let i := slot / 9
    let j := slot % 9
    min ((d[slot]?).getD 0)
      (((d[9*i+k]?).getD 0) + ((d[9*k+j]?).getD 0))).toArray

def closure (d : Array Int) : Array Int :=
  (List.range 9).foldl floydStep d

def PotentialBound (p : Nat → Int) (d : Array Int) : Prop :=
  ∀ i < 9, ∀ j < 9, p j - p i ≤ (d[9*i+j]?).getD 0

@[simp] theorem floydStep_size (d : Array Int) (k : Nat) :
    (floydStep d k).size = 81 := by
  simp [floydStep]

/-- Every updated entry is the actual minimum computed in the data file. -/
theorem floydStep_entry (d : Array Int) (k slot : Nat) (hs : slot < 81) :
    ((floydStep d k)[slot]?).getD 0 =
      min ((d[slot]?).getD 0)
        (((d[9*(slot/9)+k]?).getD 0) + ((d[9*k+slot%9]?).getD 0)) := by
  simp [floydStep, hs]

theorem floydStep_entry_ij (d : Array Int) (k i j : Nat)
    (hi : i < 9) (hj : j < 9) :
    ((floydStep d k)[9*i+j]?).getD 0 =
      min ((d[9*i+j]?).getD 0)
        (((d[9*i+k]?).getD 0) + ((d[9*k+j]?).getD 0)) := by
  have hs : 9*i+j < 81 := by omega
  have hd : (9*i+j)/9=i := by omega
  have hm : (9*i+j)%9=j := by omega
  simpa only [hd, hm] using floydStep_entry d k (9*i+j) hs

/-- Potential differences satisfy both branches of every true Floyd minimum. -/
theorem floydStep_preserves {p : Nat → Int} {d : Array Int} {k : Nat}
    (hk : k < 9) (h : PotentialBound p d) : PotentialBound p (floydStep d k) := by
  intro i hi j hj
  rw [floydStep_entry_ij d k i j hi hj]
  apply le_min
  · exact h i hi j hj
  · have hik := h i hi k hk
    have hkj := h k hk j hj
    omega

/-- Any list of genuine pivot indices preserves the same potential bounds. -/
theorem foldl_preserves {p : Nat → Int} : ∀ (ks : List Nat) (d : Array Int),
    (∀ k ∈ ks, k < 9) → PotentialBound p d →
      PotentialBound p (ks.foldl floydStep d) := by
  intro ks
  induction ks with
  | nil => intro d _ h; simpa using h
  | cons k ks ih =>
      intro d hks h
      have hk : k < 9 := hks k (by simp)
      have ht : ∀ a ∈ ks, a < 9 := fun a ha => hks a (by simp [ha])
      simpa only [List.foldl_cons] using ih (floydStep d k) ht (floydStep_preserves hk h)

theorem foldl_size : ∀ (ks : List Nat) (d : Array Int), d.size = 81 →
    (ks.foldl floydStep d).size = 81 := by
  intro ks
  induction ks with
  | nil => intro d h; simpa using h
  | cons k ks ih =>
      intro d _
      simpa only [List.foldl_cons] using ih (floydStep d k) (floydStep_size d k)

theorem closure_preserves {p : Nat → Int} {d : Array Int}
    (h : PotentialBound p d) : PotentialBound p (closure d) := by
  apply foldl_preserves (List.range 9) d _ h
  intro k hk
  exact List.mem_range.mp hk

@[simp] theorem closure_size (d : Array Int) (hd : d.size = 81) :
    (closure d).size = 81 := foldl_size (List.range 9) d hd

/-- The nonempty nine-pivot closure has 81 slots for every initial array. -/
@[simp] theorem closure_size_all (d : Array Int) : (closure d).size = 81 := by
  unfold closure
  rw [show List.range 9 = List.range 8 ++ [8] by decide, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, floydStep_size]

/-- The continuous certificate uses real potentials and integer edge bounds. -/
def RealPotentialBound (p : Nat → ℝ) (d : Array Int) : Prop :=
  ∀ i < 9, ∀ j < 9, p j - p i ≤ ((d[9*i+j]?).getD 0 : ℝ)

theorem floydStep_real_preserves {p : Nat → ℝ} {d : Array Int} {k : Nat}
    (hk : k < 9) (h : RealPotentialBound p d) :
    RealPotentialBound p (floydStep d k) := by
  intro i hi j hj
  rw [floydStep_entry_ij d k i j hi hj, Int.cast_min, Int.cast_add]
  apply le_min
  · exact h i hi j hj
  · have hik := h i hi k hk
    have hkj := h k hk j hj
    linarith

theorem foldl_real_preserves {p : Nat → ℝ} : ∀ (ks : List Nat) (d : Array Int),
    (∀ k ∈ ks, k < 9) → RealPotentialBound p d →
      RealPotentialBound p (ks.foldl floydStep d) := by
  intro ks
  induction ks with
  | nil => intro d _ h; simpa using h
  | cons k ks ih =>
      intro d hks h
      have hk : k < 9 := hks k (by simp)
      have ht : ∀ a ∈ ks, a < 9 := fun a ha => hks a (by simp [ha])
      simpa only [List.foldl_cons] using
        ih (floydStep d k) ht (floydStep_real_preserves hk h)

theorem closure_real_preserves {p : Nat → ℝ} {d : Array Int}
    (h : RealPotentialBound p d) : RealPotentialBound p (closure d) := by
  apply foldl_real_preserves (List.range 9) d _ h
  intro k hk
  exact List.mem_range.mp hk

end RHWeilRecord.FloydSoundness

#print axioms RHWeilRecord.FloydSoundness.floydStep_preserves
#print axioms RHWeilRecord.FloydSoundness.closure_preserves

#print axioms RHWeilRecord.FloydSoundness.closure_real_preserves
