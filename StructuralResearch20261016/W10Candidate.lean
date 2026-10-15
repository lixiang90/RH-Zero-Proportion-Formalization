/- Exact research parameters only; the analytic Fw floor is not claimed. -/
import GramDefect20261015.Core

noncomputable section
open Finset Zeta23Ext.BridgeW
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace StructuralResearch20261016.W10Candidate
def aN : Fin 10 → Fin 10 → ℕ
  | 0, 1 => 864532781
  | 0, 5 => 1830661123
  | 0, 6 => 6755974882
  | 0, 7 => 7196066641
  | 0, 8 => 10000000000
  | 0, 9 => 20000000000
  | 1, 2 => 1722216192
  | 1, 3 => 1472756067
  | 1, 4 => 2870423789
  | 1, 5 => 2426972296
  | 1, 6 => 6286682997
  | 1, 7 => 3244025117
  | 1, 8 => 5607866717
  | 1, 9 => 10000000000
  | 2, 3 => 2468896527
  | 2, 4 => 3292868711
  | 2, 5 => 5038257708
  | 2, 6 => 7573027703
  | 2, 7 => 3765311758
  | 2, 8 => 3244025117
  | 2, 9 => 7196066641
  | 3, 4 => 3252458899
  | 3, 5 => 5234375221
  | 3, 6 => 4182637003
  | 3, 7 => 7573027703
  | 3, 8 => 6286682997
  | 3, 9 => 6755974882
  | 4, 5 => 3383791198
  | 4, 6 => 5234375221
  | 4, 7 => 5038257708
  | 4, 8 => 2426972296
  | 4, 9 => 1830661123
  | 5, 6 => 3252458899
  | 5, 7 => 3292868711
  | 5, 8 => 2870423789
  | 6, 7 => 2468896527
  | 6, 8 => 1472756067
  | 7, 8 => 1722216192
  | 8, 9 => 864532781
  | _, _ => 0
def bN : Fin 9 → ℕ
  | 0 => 2000745
  | 1 => 3802596
  | 2 => 5399599
  | 3 => 7035033
  | 4 => 7535770
  | 5 => 7035033
  | 6 => 5399599
  | 7 => 3802596
  | 8 => 2000745
def a (i j : Fin 10) : ℝ := (aN i j : ℝ) / 10000000000
def b (i : Fin 9) : ℝ := (bN i : ℝ) / 10000000000
def W : WCert 10 := ⟨a, b⟩
theorem a_nonneg : ∀ i j, 0 ≤ W.a i j := by
  intro i j
  dsimp [W, a]
  positivity
theorem b_nonneg : ∀ i, 0 ≤ W.b i := by
  intro i
  dsimp [W, b]
  positivity
def spanN (s : ℕ) : ℕ := ∑ i : Fin 10, ∑ j : Fin 10,
  if (i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s then aN i j else 0
theorem nat_capacity : ∀ s : ℕ, spanN s ≤ 20000000000 := by
  intro s
  rcases lt_or_ge s 10 with hs | hs
  · interval_cases s <;> decide
  · have h0 : ∀ i j : Fin 10, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [spanN, h0, if_false, Finset.sum_const_zero]
    norm_num
theorem span_eq (s : ℕ) : W.spanMass s = (spanN s : ℝ) / 10000000000 := by
  simp only [WCert.spanMass, W, a, spanN, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_zero, Finset.sum_div, ite_div, zero_div]
theorem capacity (s : ℕ) : W.spanMass s ≤ 2 := by
  rw [span_eq]
  have hn : (spanN s : ℝ) ≤ 20000000000 := by exact_mod_cast nat_capacity s
  nlinarith
theorem adm : W.Adm := ⟨a_nonneg, b_nonneg, capacity⟩
theorem bN_sum : (∑ i : Fin 9, bN i) = 44011716 := by decide
theorem pressure_eq : W.B = (11002929 : ℝ) / 2500000000 := by
  change (∑ i : Fin 9, (bN i : ℝ) / 10000000000) = _
  rw [← Finset.sum_div, ← Nat.cast_sum, bN_sum]
  norm_num
-- No analytic floor or zeta proportion theorem is asserted in this module.
#print axioms adm
#print axioms pressure_eq
end StructuralResearch20261016.W10Candidate
end
