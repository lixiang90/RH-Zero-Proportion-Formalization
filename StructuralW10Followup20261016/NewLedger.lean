/- Redesigned-window ledger: exact admissibility and reflection only.
   Parameter JSON SHA256: 61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11
   IMPORTANT: Core.Fw still denotes the OLD AM kernel. W is only a numerical
   pair/pressure ledger; no Fw lower bound or redesigned analytic bridge is
   asserted here. All new-window local floors remain unproved. -/
import GramDefect20261015.Core

noncomputable section
open Finset Zeta23Ext.BridgeW
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace StructuralW10Followup20261016.NewLedger
def aN : Fin 10 → Fin 10 → ℕ
  | 0, 1 => 975978555
  | 0, 2 => 0
  | 0, 3 => 1008375533
  | 0, 4 => 0
  | 0, 5 => 3759835382
  | 0, 6 => 2851965903
  | 0, 7 => 6554559405
  | 0, 8 => 10000000000
  | 0, 9 => 20000000000
  | 1, 2 => 1940903748
  | 1, 3 => 1568887398
  | 1, 4 => 3243044065
  | 1, 5 => 4055278472
  | 1, 6 => 4454867458
  | 1, 7 => 7148034096
  | 1, 8 => 6890881189
  | 1, 9 => 10000000000
  | 2, 3 => 2565879585
  | 2, 4 => 4121909221
  | 2, 5 => 3824161541
  | 2, 6 => 5944721527
  | 2, 7 => 3570594318
  | 2, 8 => 7148034096
  | 2, 9 => 6554559405
  | 3, 4 => 2928557891
  | 3, 5 => 4309203380
  | 3, 6 => 3848837718
  | 3, 7 => 5944721527
  | 3, 8 => 4454867458
  | 3, 9 => 2851965903
  | 4, 5 => 3177360440
  | 4, 6 => 4309203380
  | 4, 7 => 3824161541
  | 4, 8 => 4055278472
  | 4, 9 => 3759835382
  | 5, 6 => 2928557891
  | 5, 7 => 4121909221
  | 5, 8 => 3243044065
  | 5, 9 => 0
  | 6, 7 => 2565879585
  | 6, 8 => 1568887398
  | 6, 9 => 1008375533
  | 7, 8 => 1940903748
  | 7, 9 => 0
  | 8, 9 => 975978555
  | _, _ => 0
def bN : Fin 9 → ℕ
  | 0 => 2050531
  | 1 => 4047384
  | 2 => 5655513
  | 3 => 6706494
  | 4 => 7302840
  | 5 => 6706494
  | 6 => 5655513
  | 7 => 4047384
  | 8 => 2050531
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
theorem bN_sum : (∑ i : Fin 9, bN i) = 44222684 := by decide
theorem pressure_eq : W.B = (11055671 : ℝ) / 2500000000 := by
  change (∑ i : Fin 9, (bN i : ℝ) / 10000000000) = _
  rw [← Finset.sum_div, ← Nat.cast_sum, bN_sum]
  norm_num

theorem aN_reflection (i j : Fin 10) : aN i j = aN j.rev i.rev := by
  fin_cases i <;> fin_cases j <;> decide

theorem bN_reflection (i : Fin 9) : bN i = bN i.rev := by
  fin_cases i <;> decide

theorem pair_reflection (i j : Fin 10) : W.a i j = W.a j.rev i.rev := by
  change (aN i j : ℝ) / 10000000000 = (aN j.rev i.rev : ℝ) / 10000000000
  rw [aN_reflection]

theorem pressure_reflection (i : Fin 9) : W.b i = W.b i.rev := by
  change (bN i : ℝ) / 10000000000 = (bN i.rev : ℝ) / 10000000000
  rw [bN_reflection]

-- No analytic floor or zeta proportion theorem is asserted in this module.
#print axioms adm
#print axioms pressure_eq
#print axioms pair_reflection
#print axioms pressure_reflection
end StructuralW10Followup20261016.NewLedger
end
