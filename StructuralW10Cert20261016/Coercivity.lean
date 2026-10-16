/-
SPDX-License-Identifier: Apache-2.0
Positive pressure confines any counterexample to a bounded domain.
No local analytic energy floor is assumed or asserted here.
-/
import GramDefect20261015.Core

noncomputable section
open Finset
open scoped BigOperators
open Zeta23Ext.Bridge Zeta23Ext.BridgeW

namespace StructuralW10Cert20261016.Coercivity

theorem pressure_le_energy {n : ℕ} (W : WCert n) (hW : W.Adm)
    (g : Fin (n - 1) → ℝ) : (∑ r, W.b r * g r) ≤ Fw W g := by
  have hq : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      if (i : ℕ) < (j : ℕ) then
        W.a i j * wfun (ptsN n g j - ptsN n g i) else 0 := by
    refine sum_nonneg fun i _ => sum_nonneg fun j _ => ?_
    split_ifs
    · exact mul_nonneg (hW.a_nonneg i j) (wfun_nonneg _)
    · exact le_rfl
  exact le_add_of_nonneg_right hq

theorem pressure_shift {n : ℕ} (W : WCert n) (g : Fin (n - 1) → ℝ)
    (sep : ℝ) :
    (∑ r, W.b r * g r) = W.B * sep + ∑ r, W.b r * (g r - sep) := by
  unfold WCert.B
  rw [sum_mul, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

theorem coordinate_payment {n : ℕ} (W : WCert n) (hW : W.Adm)
    {sep : ℝ} {g : Fin (n - 1) → ℝ} (hg : ∀ r, sep ≤ g r)
    (r : Fin (n - 1)) :
    W.B * sep + W.b r * (g r - sep) ≤ Fw W g := by
  have ht : W.b r * (g r - sep) ≤ ∑ s, W.b s * (g s - sep) :=
    single_le_sum (fun s _ => mul_nonneg (hW.b_nonneg s) (sub_nonneg.mpr (hg s)))
      (mem_univ r)
  have hp := pressure_le_energy W hW g
  rw [pressure_shift W g sep] at hp
  linarith

theorem coordinate_bound {n : ℕ} (W : WCert n) (hW : W.Adm)
    {sep c : ℝ} {g : Fin (n - 1) → ℝ} (hg : ∀ r, sep ≤ g r)
    (hcounter : Fw W g < c) (r : Fin (n - 1)) (hb : 0 < W.b r) :
    g r < sep + (c - W.B * sep) / W.b r := by
  have h := lt_of_le_of_lt (coordinate_payment W hW hg r) hcounter
  have hm : W.b r * (g r - sep) < c - W.B * sep := by linarith
  have hdiv : g r - sep < (c - W.B * sep) / W.b r :=
    (lt_div_iff₀ hb).2 (by nlinarith only [hm])
  linarith only [hdiv]

theorem span_payment {n : ℕ} (W : WCert n) (hW : W.Adm)
    {sep bmin : ℝ} {g : Fin (n - 1) → ℝ}
    (hg : ∀ r, sep ≤ g r) (hmin : ∀ r, bmin ≤ W.b r) :
    W.B * sep + bmin * ((∑ r, g r) - ((n - 1 : ℕ) : ℝ) * sep) ≤ Fw W g := by
  have hs : bmin * ∑ r, (g r - sep) ≤ ∑ r, W.b r * (g r - sep) := by
    rw [mul_sum]
    exact sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hmin r) (sub_nonneg.mpr (hg r))
  have heq : (∑ r : Fin (n - 1), (g r - sep)) =
      (∑ r, g r) - ((n - 1 : ℕ) : ℝ) * sep := by simp [sum_sub_distrib]
  rw [heq] at hs
  have hp := pressure_le_energy W hW g
  rw [pressure_shift W g sep] at hp
  linarith

theorem span_bound {n : ℕ} (W : WCert n) (hW : W.Adm)
    {sep c bmin : ℝ} {g : Fin (n - 1) → ℝ} (hg : ∀ r, sep ≤ g r)
    (hmin : ∀ r, bmin ≤ W.b r) (hb : 0 < bmin) (hcounter : Fw W g < c) :
    (∑ r, g r) < ((n - 1 : ℕ) : ℝ) * sep + (c - W.B * sep) / bmin := by
  have h := lt_of_le_of_lt (span_payment W hW hg hmin) hcounter
  have hm : bmin * ((∑ r, g r) - ((n - 1 : ℕ) : ℝ) * sep) < c - W.B * sep := by
    linarith
  have hdiv : (∑ r, g r) - ((n - 1 : ℕ) : ℝ) * sep < (c - W.B * sep) / bmin :=
    (lt_div_iff₀ hb).2 (by nlinarith only [hm])
  linarith only [hdiv]

end StructuralW10Cert20261016.Coercivity
end
