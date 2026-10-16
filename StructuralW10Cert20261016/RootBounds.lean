/- SPDX-License-Identifier: Apache-2.0
Exact pressure bounds on every possible counterexample to the W10 floor.
This is the initial-domain lemma, not the remaining finite coverage proof. -/
import StructuralW10Cert20261016.LocalChecker

noncomputable section
open Finset AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralResearch20261016.W10RefinedCandidate
open Zeta23Ext.BridgeW
open scoped BigOperators
set_option maxHeartbeats 4000000
namespace StructuralW10Cert20261016.RootBounds

def initialCell : Cl :=
  ⟨[27852, 27852, 27852, 27852, 27852, 27852, 27852, 27852, 27852], [850284, 442408, 324827, 259360, 242431, 259360, 324827, 442408, 850284], [55704, 83556, 111408, 139260, 167112, 194964, 222816, 250668, 55704, 83556, 111408, 139260, 167112, 194964, 222816, 55704, 83556, 111408, 139260, 167112, 194964, 55704, 83556, 111408, 139260, 167112, 55704, 83556, 111408, 139260, 55704, 83556, 111408, 55704, 83556, 55704], [878136, 905988, 933840, 961692, 989544, 1017396, 1045248, 1073100, 470260, 498112, 525964, 553816, 581668, 609520, 1045248, 352679, 380531, 408383, 436235, 581668, 1017396, 287212, 315064, 408383, 553816, 989544, 287212, 380531, 525964, 961692, 352679, 498112, 933840, 470260, 905988, 878136]⟩

theorem counterexample_in_root {g : ℕ → ℝ}
    (hg : ∀ r < 9, (17 / 20 : ℝ) ≤ g r)
    (hcounter : Fw W (fun r : Fin 9 => g r) < (433 : ℝ) / 50000) :
    InCell 9 PR initialCell g := by
  have hscale : Fg 9 BS TS g < 86600000 := by
    rw [fg_eq_scaled_Fw]
    nlinarith only [hcounter]
  have hkernel : 0 ≤ ∑ t ∈ range TS.length,
      ((tA TS t : ℕ) : ℝ) * AMW.Cert.wfun (gsum g (tI TS t) (tJ TS t)) :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (AMW.Cert.wfun_nonneg _)
  have hp : (∑ r ∈ range 9, ((BS.getD r 0 : ℕ) : ℝ) * g r) < 86600000 := by
    unfold Fg at hscale
    linarith only [hscale, hkernel]
  norm_num [BS, Finset.sum_range_succ] at hp
  have hg0 := hg 0 (by decide)
  have h0 : (27852 : ℝ) / 32768 ≤ g 0 := by linarith only [hg0]
  have hg1 := hg 1 (by decide)
  have h1 : (27852 : ℝ) / 32768 ≤ g 1 := by linarith only [hg1]
  have hg2 := hg 2 (by decide)
  have h2 : (27852 : ℝ) / 32768 ≤ g 2 := by linarith only [hg2]
  have hg3 := hg 3 (by decide)
  have h3 : (27852 : ℝ) / 32768 ≤ g 3 := by linarith only [hg3]
  have hg4 := hg 4 (by decide)
  have h4 : (27852 : ℝ) / 32768 ≤ g 4 := by linarith only [hg4]
  have hg5 := hg 5 (by decide)
  have h5 : (27852 : ℝ) / 32768 ≤ g 5 := by linarith only [hg5]
  have hg6 := hg 6 (by decide)
  have h6 : (27852 : ℝ) / 32768 ≤ g 6 := by linarith only [hg6]
  have hg7 := hg 7 (by decide)
  have h7 : (27852 : ℝ) / 32768 ≤ g 7 := by linarith only [hg7]
  have hg8 := hg 8 (by decide)
  have h8 : (27852 : ℝ) / 32768 ≤ g 8 := by linarith only [hg8]
  constructor
  · intro r hr
    interval_cases r <;> constructor <;>
      norm_num [initialCell, SC] <;> linarith only [hp, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · intro k hk
    norm_num [PR] at hk
    interval_cases k <;> constructor <;>
      norm_num [initialCell, PR, pI, pJ, gsum_range, Finset.sum_range_succ, SC] <;>
      linarith only [hp, h0, h1, h2, h3, h4, h5, h6, h7, h8]

#print axioms counterexample_in_root
end StructuralW10Cert20261016.RootBounds
end
