import Lean

/- Ordinary lookup compatibility for a bounded table represented by a getter.
No certificate values, computations, or continuous assertions are assumed. -/
namespace RHWeilRecord.GetterSoundness
universe u

def fromGetter {α : Type u} (n : Nat) (get : Nat → α) : Array α :=
  (Array.range n).map get

@[simp] theorem size_fromGetter {α : Type u} (n : Nat) (get : Nat → α) :
    (fromGetter n get).size = n := by
  simp [fromGetter]

@[simp] theorem getElem?_fromGetter {α : Type u}
    (n i : Nat) (get : Nat → α) :
    (fromGetter n get)[i]? = if i < n then some (get i) else none := by
  simp only [fromGetter, Array.getElem?_map, Array.getElem?_range]
  split <;> rfl

theorem getD_fromGetter {α : Type u} (n i : Nat)
    (get : Nat → α) (fallback : α) :
    ((fromGetter n get)[i]?).getD fallback =
      if i < n then get i else fallback := by
  rw [getElem?_fromGetter]
  split <;> rfl

theorem getD_fromGetter_of_lt {α : Type u} (n i : Nat)
    (get : Nat → α) (fallback : α) (hi : i < n) :
    ((fromGetter n get)[i]?).getD fallback = get i := by
  rw [getD_fromGetter, if_pos hi]

theorem getD_fromGetter_eq_get {α : Type u} (n i : Nat)
    (get : Nat → α) (fallback : α)
    (houtside : ∀ j, n ≤ j → get j = fallback) :
    ((fromGetter n get)[i]?).getD fallback = get i := by
  rw [getD_fromGetter]
  by_cases hi : i < n
  · rw [if_pos hi]
  · rw [if_neg hi, houtside i (Nat.le_of_not_gt hi)]

end RHWeilRecord.GetterSoundness
#print axioms RHWeilRecord.GetterSoundness.size_fromGetter
#print axioms RHWeilRecord.GetterSoundness.getElem?_fromGetter
#print axioms RHWeilRecord.GetterSoundness.getD_fromGetter
#print axioms RHWeilRecord.GetterSoundness.getD_fromGetter_of_lt
#print axioms RHWeilRecord.GetterSoundness.getD_fromGetter_eq_get
