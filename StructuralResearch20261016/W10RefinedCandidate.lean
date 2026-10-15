/- Revised exact parameters only; the analytic Fw floor remains unproved.
   Parameter JSON SHA256: ad117819d63588c55d89bd59ae7f0ad11072faaf33ffc53bf08d7eef54010e03 -/
import GramDefect20261015.Core

noncomputable section
open Finset Zeta23Ext.BridgeW
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace StructuralResearch20261016.W10RefinedCandidate
def aN : Fin 10 → Fin 10 → ℕ
  | 0, 1 => 856023725
  | 0, 5 => 2431155644
  | 0, 6 => 6271589178
  | 0, 7 => 6414869991
  | 0, 8 => 10000000000
  | 0, 9 => 20000000000
  | 1, 2 => 1769970138
  | 1, 3 => 1139482463
  | 1, 4 => 3005622676
  | 1, 5 => 3187144078
  | 1, 6 => 5479076134
  | 1, 7 => 3728410821
  | 1, 8 => 7170260017
  | 1, 9 => 10000000000
  | 2, 3 => 2492616294
  | 2, 4 => 3741136898
  | 2, 5 => 4658843169
  | 2, 6 => 6812855921
  | 2, 7 => 4179536443
  | 2, 8 => 3728410821
  | 2, 9 => 6414869991
  | 3, 4 => 3184724710
  | 3, 5 => 5119380638
  | 3, 6 => 4671068306
  | 3, 7 => 6812855921
  | 3, 8 => 5479076134
  | 3, 9 => 6271589178
  | 4, 5 => 3393330261
  | 4, 6 => 5119380638
  | 4, 7 => 4658843169
  | 4, 8 => 3187144078
  | 4, 9 => 2431155644
  | 5, 6 => 3184724710
  | 5, 7 => 3741136898
  | 5, 8 => 3005622676
  | 6, 7 => 2492616294
  | 6, 8 => 1139482463
  | 7, 8 => 1769970138
  | 8, 9 => 856023725
  | _, _ => 0
def bN : Fin 9 → ℕ
  | 0 => 1960353
  | 1 => 3889123
  | 2 => 5428938
  | 3 => 6964154
  | 4 => 7513588
  | 5 => 6964154
  | 6 => 5428938
  | 7 => 3889123
  | 8 => 1960353
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
theorem bN_sum : (∑ i : Fin 9, bN i) = 43998724 := by decide
theorem pressure_eq : W.B = (10999681 : ℝ) / 2500000000 := by
  change (∑ i : Fin 9, (bN i : ℝ) / 10000000000) = _
  rw [← Finset.sum_div, ← Nat.cast_sum, bN_sum]
  norm_num
-- No analytic floor or zeta proportion theorem is asserted in this module.
#print axioms adm
#print axioms pressure_eq
end StructuralResearch20261016.W10RefinedCandidate
end
