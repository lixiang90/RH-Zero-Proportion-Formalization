import Mathlib.Tactic

/-! Integer path witnesses give real potential bounds.  This module is independent
of every certificate dataset: its boolean check is evaluated by the Lean kernel. -/

namespace RHWeil.RecordSubmission.NinthSpanPaths

/-- Low nibble is the vertex count; subsequent nibbles are vertex labels. -/
def vertices (word : Nat) : List Nat :=
  (List.range (word % 16)).map (fun k => (word / 2 ^ (4 + 4 * k)) % 16)

/-- Sum the directed edge weights along the adjacent vertices of a path. -/
def cost (e : Nat → Nat → Int) : List Nat → Int
  | [] => 0
  | [_] => 0
  | a :: b :: rest => e a b + cost e (b :: rest)

/-- Check a nonempty path, its endpoints, vertex range, and integer cost. -/
def check (e : Nat → Nat → Int) (first last : Nat) (bound : Int) (word : Nat) : Bool :=
  decide (0 < (vertices word).length ∧ (vertices word).length ≤ 9 ∧
    (vertices word).headD 0 = first ∧ (vertices word).getLastD 0 = last ∧
    (∀ v ∈ vertices word, v < 9) ∧ cost e (vertices word) ≤ bound)

/-- The real potential difference along any admissible path is at most its cost. -/
theorem cost_real_bound {p : Nat → ℝ} {e : Nat → Nat → Int}
    (he : ∀ i < 9, ∀ j < 9, p j - p i ≤ (e i j : ℝ)) :
    ∀ xs : List Nat, (∀ v ∈ xs, v < 9) →
      p (xs.getLastD 0) - p (xs.headD 0) ≤ (cost e xs : ℝ) := by
  intro xs
  induction xs with
  | nil =>
    intro _
    simp [cost]
  | cons a tail ih =>
    intro hall
    cases tail with
    | nil => simp [cost]
    | cons b rest =>
      have ha : a < 9 := hall a (by simp)
      have hb : b < 9 := hall b (by simp)
      have htail : ∀ v ∈ b :: rest, v < 9 := by
        intro v hv
        exact hall v (List.mem_cons_of_mem a hv)
      have hsum := ih htail
      have hedge := he a ha b hb
      have hlast : (a :: b :: rest).getLastD 0 = (b :: rest).getLastD 0 := by
        simp only [List.getLastD_eq_getLast?, List.getLast?_cons_cons]
      simp only [List.headD_cons] at hsum
      simp only [cost, Int.cast_add, List.headD_cons, hlast]
      linarith only [hedge, hsum]

/-- Soundness of the compact integer path certificate for a real potential. -/
theorem check_real_bound {p : Nat → ℝ} {e : Nat → Nat → Int}
    {first last : Nat} {bound : Int} {word : Nat}
    (hc : check e first last bound word = true)
    (he : ∀ i < 9, ∀ j < 9, p j - p i ≤ (e i j : ℝ)) :
    p last - p first ≤ (bound : ℝ) := by
  obtain ⟨_, _, hfirst, hlast, hvertices, hcost⟩ := of_decide_eq_true hc
  have hpath := cost_real_bound he (vertices word) hvertices
  rw [hfirst, hlast] at hpath
  exact hpath.trans (by exact_mod_cast hcost)

end RHWeil.RecordSubmission.NinthSpanPaths
