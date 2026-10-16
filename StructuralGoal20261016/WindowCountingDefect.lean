/- SPDX-License-Identifier: Apache-2.0
Actual new-window defect payment from its separated energy and short pairs.
All finite-height Gram, spectral, and kernel-limit inputs are discharged.
Only the explicitly named actual scalar energy/pair certificates remain.
-/
import StructuralGoal20261016.WindowMatching
import StructuralGoal20261016.WindowUniformKernel
import StructuralGoal20261016.WindowSeparated
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg Filter
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowCountingDefect

def ActualDefectEstimate (Z : ZeroConfig) (n : ℕ) (c B : ℝ) : Prop :=
 ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
   (c-4*((n-1:ℕ):ℝ)*δ)*((retained Z (WindowCountingBase.mtParams T) T).card:ℝ)-
     B*spanOf (xret Z (WindowCountingBase.mtParams T) T) univ-((n-1:ℕ):ℝ)*c ≤
       Dcirc Z (WindowCountingBase.mtParams T) T

theorem actual_defect_estimate (Z : ZeroConfig) {n : ℕ} (hn : 2 ≤ n)
 (W : WCert n) (hW : W.Adm) {c C B sep : ℝ}
 (hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hc64 : c ≤ 1/64)
 (hsep : 17/20 ≤ sep) (hB : W.B = B)
 (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
 (hCert : WindowDiscreteEnergy.SeparatedSummedCertificate W c C sep) :
 ActualDefectEstimate Z (n+1) c B := by
 classical
 intro δ hδ
 have hLpos : ∀ᶠ T in atTop, 0 < (WindowCountingBase.mtParams T).L T :=
   (tendsto_L WindowCountingBase.P₀_valid).eventually_gt_atTop 0
 filter_upwards [WindowUniformKernel.kernel_limit_uniform Z δ hδ,
   WindowSeparatedSpectrum.eventually_principal_eigenvalues_le_two Z,hLpos]
   with T hclose hcap hL
 have hx := xret_injective Z (WindowCountingBase.mtParams T) T hL
 have hspan : ∀ i j : retained Z (WindowCountingBase.mtParams T) T,
   xret Z (WindowCountingBase.mtParams T) T i-xret Z (WindowCountingBase.mtParams T) T j ≤
     spanOf (xret Z (WindowCountingBase.mtParams T) T) univ := by
   intro i j
   exact (le_abs_self _).trans
     (abs_sub_le_spanOf (xret Z (WindowCountingBase.mtParams T) T) (mem_univ i) (mem_univ j))
 have hcap' : ∀ S : Finset (retained Z (WindowCountingBase.mtParams T) T),
     (∀ i j : S, i ≠ j → sep ≤ |xret Z (WindowCountingBase.mtParams T) T i.1-
       xret Z (WindowCountingBase.mtParams T) T j.1|) →
     ∀ k : S, ((gram_isHermitian Z (WindowCountingBase.mtParams T) T).submatrix
       (Subtype.val : S → retained Z (WindowCountingBase.mtParams T) T)).eigenvalues k ≤ 2 := by
   intro S hS k
   exact hcap S (fun i j hij => hsep.trans (hS i j hij)) k
 have h := WindowMatching.matching_defect_bound_effective hn hx
   (gram_isHermitian Z (WindowCountingBase.mtParams T) T) hc hC hCc hc64 hPair W hW hCert
   hδ.le (fun i j _ => hclose i j) hcap'
   (spanOf_nonneg (xret Z (WindowCountingBase.mtParams T) T) univ) hspan
 simpa only [Fintype.card_coe,hB,Dcirc] using h

set_option pp.fullNames true
#print axioms actual_defect_estimate
end StructuralGoal20261016.WindowCountingDefect
end
