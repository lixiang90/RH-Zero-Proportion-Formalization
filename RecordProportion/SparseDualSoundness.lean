import Mathlib

/- Soundness of the actual sparse integer list-fold and signed box correction.
Rows may repeat. No optimality or zero-residual premise is required. -/
namespace RHWeilRecord.SparseDualSoundness
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

 def boxTerm (r lo hi : ℝ) : ℝ := if 0 ≤ r then r*lo else r*hi

theorem boxTerm_le_mul {r lo hi x : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    boxTerm r lo hi ≤ r*x := by
  by_cases hr : 0 ≤ r
  · simp only [boxTerm,if_pos hr]
    exact mul_le_mul_of_nonneg_left hlo hr
  · simp only [boxTerm,if_neg hr]
    exact mul_le_mul_of_nonpos_left hhi (le_of_lt (lt_of_not_ge hr))

def dot (n : Nat) (a x : Nat → ℝ) : ℝ := ∑ i ∈ Finset.range n, a i*x i

def residual {α : Type*} (rows : List α) (c : Nat → ℝ)
    (A : α → Nat → ℝ) (lam : α → ℝ) (i : Nat) : ℝ :=
  c i + (rows.map fun r => lam r*A r i).sum

def lowerReal {α : Type*} (n : Nat) (rows : List α) (c : Nat → ℝ)
    (A : α → Nat → ℝ) (b lam : α → ℝ) (lo hi : Nat → ℝ) : ℝ :=
  -(rows.map fun r => lam r*b r).sum +
    ∑ i ∈ Finset.range n, boxTerm (residual rows c A lam i) (lo i) (hi i)

theorem residual_dot {α : Type*} (n : Nat) (rows : List α)
    (c x : Nat → ℝ) (A : α → Nat → ℝ) (lam : α → ℝ) :
    dot n (residual rows c A lam) x = dot n c x +
      (rows.map fun r => lam r*dot n (A r) x).sum := by
  induction rows with
  | nil => simp [residual,dot]
  | cons r rows ih =>
    have he : residual (r::rows) c A lam =
        fun i => lam r*A r i + residual rows c A lam i := by
      funext i
      simp only [residual,List.map_cons,List.sum_cons]
      ring
    rw [he]
    simp only [dot,add_mul,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum]
    change lam r*dot n (A r) x + dot n (residual rows c A lam) x = _
    rw [ih]
    simp only [List.map_cons,List.sum_cons,dot]
    ring

theorem lowerReal_sound {α : Type*} (n : Nat) (rows : List α)
    (c x : Nat → ℝ) (A : α → Nat → ℝ) (b lam : α → ℝ) (lo hi : Nat → ℝ)
    (hlam : ∀ r ∈ rows, 0 ≤ lam r)
    (hrows : ∀ r ∈ rows, dot n (A r) x ≤ b r)
    (hlo : ∀ i < n, lo i ≤ x i) (hhi : ∀ i < n, x i ≤ hi i) :
    lowerReal n rows c A b lam lo hi ≤ dot n c x := by
  have hr : (rows.map fun r => lam r*dot n (A r) x).sum ≤
      (rows.map fun r => lam r*b r).sum := by
    induction rows with
    | nil => simp
    | cons r rows ih =>
      simp only [List.map_cons,List.sum_cons]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hrows r (by simp)) (hlam r (by simp))
      · apply ih
        · intro s hs; exact hlam s (by simp [hs])
        · intro s hs; exact hrows s (by simp [hs])
  have hb : (∑ i ∈ Finset.range n,
      boxTerm (residual rows c A lam i) (lo i) (hi i)) ≤
      dot n (residual rows c A lam) x :=
    Finset.sum_le_sum fun i hi =>
      boxTerm_le_mul (hlo i (Finset.mem_range.mp hi)) (hhi i (Finset.mem_range.mp hi))
  rw [residual_dot] at hb
  unfold lowerReal
  linarith

/-- The residual is exactly the source's sequential integer accumulator. -/
def residualFold {α : Type*} (rows : List α) (c : Nat → Int)
    (A : α → Nat → Int) (lam : α → Int) (i : Nat) : Int :=
  rows.foldl (fun total r => total+lam r*A r i) (c i)

/-- This is literally the list-fold/map/sum expression consumed by Data. -/
def checkerL {α : Type*} (n : Nat) (rows : List α) (c : Nat → Int)
    (A : α → Nat → Int) (b lam : α → Int) (lo hi : Nat → Int) : Int :=
  rows.foldl (fun total r => total-lam r*b r) 0 +
    ((List.range n).map fun i =>
      let r := residualFold rows c A lam i
      r*(if 0 ≤ r then lo i else hi i)).sum

theorem foldl_add_value {α β : Type*} [AddCommGroup β] (rows : List α)
    (f : α → β) (initial : β) :
    rows.foldl (fun total r => total+f r) initial = initial+(rows.map f).sum := by
  induction rows generalizing initial with
  | nil => simp
  | cons r rows ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    rw [ih]
    exact add_assoc _ _ _

theorem intList_sum_cast (xs : List Int) :
    ((xs.sum : Int) : ℝ) = (xs.map fun (a : Int) => (a : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem range_sum (n : Nat) (f : Nat → ℝ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,ih,Finset.sum_range_succ]

theorem residualFold_cast {α : Type*} (rows : List α) (c : Nat → Int)
    (A : α → Nat → Int) (lam : α → Int) (i : Nat) :
    (residualFold rows c A lam i : ℝ) =
      residual rows (fun i => (c i : ℝ))
        (fun r i => (A r i : ℝ)) (fun r => (lam r : ℝ)) i := by
  simp only [residualFold,foldl_add_value,Int.cast_add,intList_sum_cast,
    List.map_map,Function.comp_def,Int.cast_mul,residual]

theorem boxTerm_cast (r lo hi : Int) :
    ((r*(if 0 ≤ r then lo else hi) : Int) : ℝ) = boxTerm (r:ℝ) (lo:ℝ) (hi:ℝ) := by
  by_cases hr : 0 ≤ r
  · have hrR : 0 ≤ (r:ℝ) := by exact_mod_cast hr
    simp [boxTerm,hr,hrR,Int.cast_mul]
  · have hrR : ¬0 ≤ (r:ℝ) := by exact_mod_cast hr
    simp [boxTerm,hr,hrR,Int.cast_mul]

theorem list_sum_neg {α : Type*} (rows : List α) (f : α → ℝ) :
    (rows.map fun r => -(f r)).sum = -(rows.map f).sum := by
  induction rows with
  | nil => simp
  | cons r rows ih => simp only [List.map_cons,List.sum_cons,ih,neg_add]

theorem checkerL_cast {α : Type*} (n : Nat) (rows : List α) (c : Nat → Int)
    (A : α → Nat → Int) (b lam : α → Int) (lo hi : Nat → Int) :
    (checkerL n rows c A b lam lo hi : ℝ) =
      lowerReal n rows (fun i => (c i : ℝ)) (fun r i => (A r i : ℝ))
        (fun r => (b r : ℝ)) (fun r => (lam r : ℝ))
        (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ)) := by
  have hbase : ((rows.foldl (fun total r => total-lam r*b r) 0 : Int) : ℝ) =
      -(rows.map fun r => (lam r:ℝ)*(b r:ℝ)).sum := by
    simp only [sub_eq_add_neg,foldl_add_value,zero_add,intList_sum_cast,
      List.map_map,Function.comp_def,Int.cast_neg,Int.cast_mul,list_sum_neg]
  simp only [checkerL,Int.cast_add,hbase,intList_sum_cast,List.map_map,Function.comp_def]
  simp_rw [boxTerm_cast,residualFold_cast]
  rw [range_sum]
  rfl

/-- The actual integer computation is a lower bound for the real objective. -/
theorem checkerL_sound {α : Type*} (n : Nat) (rows : List α)
    (c : Nat → Int) (x : Nat → ℝ) (A : α → Nat → Int) (b lam : α → Int)
    (lo hi : Nat → Int)
    (hlam : ∀ r ∈ rows, 0 ≤ lam r)
    (hrows : ∀ r ∈ rows, (∑ i ∈ Finset.range n, (A r i:ℝ)*x i) ≤ (b r:ℝ))
    (hlo : ∀ i < n, (lo i:ℝ) ≤ x i) (hhi : ∀ i < n, x i ≤ (hi i:ℝ)) :
    (checkerL n rows c A b lam lo hi : ℝ) ≤ ∑ i ∈ Finset.range n, (c i:ℝ)*x i := by
  rw [checkerL_cast]
  apply lowerReal_sound
  · intro r hr; exact_mod_cast hlam r hr
  · exact hrows
  · exact hlo
  · exact hhi

theorem threshold_sound {α : Type*} (n : Nat) (rows : List α)
    (c : Nat → Int) (x : Nat → ℝ) (A : α → Nat → Int) (b lam : α → Int)
    (lo hi : Nat → Int) (target : Int)
    (hc : target ≤ checkerL n rows c A b lam lo hi)
    (hlam : ∀ r ∈ rows, 0 ≤ lam r)
    (hrows : ∀ r ∈ rows, (∑ i ∈ Finset.range n, (A r i:ℝ)*x i) ≤ (b r:ℝ))
    (hlo : ∀ i < n, (lo i:ℝ) ≤ x i) (hhi : ∀ i < n, x i ≤ (hi i:ℝ)) :
    (target:ℝ) ≤ ∑ i ∈ Finset.range n, (c i:ℝ)*x i := by
  have ht : (target:ℝ) ≤ (checkerL n rows c A b lam lo hi : ℝ) := by exact_mod_cast hc
  exact ht.trans (checkerL_sound n rows c x A b lam lo hi hlam hrows hlo hhi)

end
end RHWeilRecord.SparseDualSoundness
#print axioms RHWeilRecord.SparseDualSoundness.checkerL_sound
#print axioms RHWeilRecord.SparseDualSoundness.threshold_sound
