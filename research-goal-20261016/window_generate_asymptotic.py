"""Adapt the attributed Core taper-limit proof to actual v24.

All generic integration lemmas are reused; new inputs are the already
defined actual profile, its bounds and admissible realization. This source
must be checked by ordinary Lean before it is research evidence.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
start=core.index('theorem abs_hW_le (L u : ℝ)')
stop=core.index('\nend AMW',start)
body=core[start:stop]
body=body.replace('vAM_pos_core','V_pos_core').replace('vAM_ge_core','V_ge_core')
body=body.replace('vAM_continuous','V_continuous').replace('abs_vAM_le','abs_V_le')
body=re.sub(r'\bvAM\b','V',body).replace('vConvAM','vConv')
start2=core.index('theorem aInf_eq :')
stop2=core.index('\nend AMW',start2)
last=core[start2:stop2].replace('integral_vAM','integral_V')
last=last.replace('vAM_continuous','V_continuous')
last=re.sub(r'\bvAM\b','V',last)
head='''/- SPDX-License-Identifier: Apache-2.0
Actual v24 taper limits and limiting cRatio.
Adapted from AMW.abs_hW_le through AMW.cRatio_W_pos, and the subsequent
AMW.bInf_gt_half argument, in the attributed Core. This replaces the fixed
profile only, without asserting any unproved local floor or proportion.
-/
import StructuralGoal20261016.WindowRealization
import StructuralGoal20261016.WindowEnergyBound
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter Topology
open scoped BigOperators
open Zeta23 AMW
namespace StructuralGoal20261016.WindowAsymptotic
open WindowProfile

def hW (L u : ℝ) : ℝ := V (u/L) / MAM
def phiW (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ := WindowProfile.phi ϱ L w
def localFunW (P : Params) (T : ℝ) : PrimeSide.LocalFun :=
 AdmWindow.localFun (phiW P.ϱ (P.L T) P.w) (P.L T)
def vConv (r : ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2-r), V s * V (s+r)
def aInf : ℝ := (∫ s in (-(1:ℝ)/2)..(1/2), V s) / MAM
def bInf : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), (V s / MAM)^2
def JInf : ℝ := 2 * (∫ r in (0:ℝ)..1, vConv r * r) / MAM^2

theorem abs_V_le (s : ℝ) : |V s| ≤ 5/4 := by
 rw [V_eq_v24]
 have hp := StructuralW10Followup20261016.WindowProfileGeneral.abs_perturb_le _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 s
 have hc := Real.abs_cos_le_one (Real.sqrt 2*s)
 unfold StructuralW10Followup20261016.NewWindows.v24
   StructuralW10Followup20261016.WindowProfileGeneral.profile
 exact (abs_add_le _ _).trans (by linarith)

theorem hW_core_ge {L : ℝ} (hL : 0 < L) {u : ℝ} (hu : |u| ≤ L/2) :
 (67/125 : ℝ) ≤ hW L u := by
 have h := V_ge_core (AMW.abs_div_le_half hL hu)
 unfold hW MAM
 rw [le_div_iff₀ (by norm_num)]
 linarith

theorem phiW_nonneg {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (u : ℝ) :
 0 ≤ phiW ϱ L w u := by
 unfold phiW WindowProfile.phi AMW.phiM AMW.fP
 exact mul_nonneg (Real.sqrt_nonneg _) (Taper.phi_nonneg hϱ u)

theorem phiW_le_one {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (u : ℝ) :
 phiW ϱ L w u ≤ 1 := by
 have hf : Real.sqrt (V (u/L)/MAM) ≤ 1 := by
   rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
   apply Real.sqrt_le_sqrt
   rw [div_le_one MAM_pos]
   exact V_le _
 unfold phiW WindowProfile.phi AMW.phiM AMW.fP
 exact (mul_le_mul hf (Taper.phi_le_one hϱ u)
   (Taper.phi_nonneg hϱ u) zero_le_one).trans (by norm_num)

theorem phiW_eq_zero {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L/2 ≤ |u|) :
 phiW ϱ L w u = 0 := AMW.phiM_eq_zero hϱ hw hu

theorem phiW_sq_eq {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 0 < w) (hL : 0 < L) (u : ℝ) :
 phiW ϱ L w u ^ 2 = hW L u * Taper.phi ϱ L w u ^ 2 := by
 rcases le_or_gt (L/2) |u| with hu | hu
 · rw [phiW_eq_zero hϱ hw hu, Taper.phi_eq_zero hϱ hw hu]
   simp
 · have hv : 0 ≤ V (u/L)/MAM :=
     (by norm_num : (0:ℝ) ≤ 67/125).trans (hW_core_ge hL hu.le)
   unfold phiW WindowProfile.phi AMW.phiM AMW.fP hW
   rw [mul_pow, Real.sq_sqrt hv]

theorem phiW_continuous {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2*w ≤ L) :
 Continuous (phiW ϱ L w) :=
 (AMW.phiM_contDiff (AMW.pvFactor_fP actual_profile (by linarith)) hϱ hw hwL).continuous

'''
middle='''
theorem integral_V : (∫ t in (-(1:ℝ)/2)..(1/2), V t) =
 Real.sqrt 2 * Real.sin (Real.sqrt 2/2) := by
 simp_rw [V_eq]
 exact WindowEnergy.integral_v 24 WindowKernel.d24

'''
tail='''
theorem JInf_eq_energy : MAM^2 * JInf =
 ∫ s in (-(1:ℝ)/2)..(1/2), V s *
   ∫ t in (-(1:ℝ)/2)..(1/2), |s-t| * V t := by
 rw [← AMW.swap_identity V_continuous abs_V_le]
 unfold JInf vConv
 field_simp [MAM_pos.ne']

theorem H24_eq_cRatio : WindowEnergy.H 24 WindowKernel.d24 =
 2 - (ThmD.cRatio 1 aInf bInf JInf)⁻¹ := by
 have ha : aInf = (∫ t in (-(1:ℝ)/2)..(1/2), V t) / MAM := rfl
 have hb : bInf = (∫ t in (-(1:ℝ)/2)..(1/2), V t^2) / MAM^2 := by
   unfold bInf
   rw [← intervalIntegral.integral_div]
   congr 1
   funext t
   ring
 have hJ := JInf_eq_energy
 have he : ∀ t : ℝ, V t = WindowEnergy.v 24 WindowKernel.d24 t := V_eq
 have hZ : (∫ t in (-(1:ℝ)/2)..(1/2), V t) ≠ 0 := by
   rw [integral_V]
   exact mul_ne_zero (by positivity) AMW.sin_theta0_pos.ne'
 unfold WindowEnergy.H ThmD.cRatio
 simp_rw [← he]
 rw [ha, hb, inv_div]
 have hJ' : JInf =
   (∫ s in (-(1:ℝ)/2)..(1/2), V s *
     ∫ t in (-(1:ℝ)/2)..(1/2), |s-t| * V t) / MAM^2 := by
   rw [← hJ]
   field_simp [MAM_pos.ne']
 rw [hJ']
 field_simp [MAM_pos.ne', hZ]
 <;> ring

theorem actual_localHypsCore {P : Params} (hP : P.Valid) :
 AMW.LocalHypsCoreWEventually P (WindowRealization.W P) (WindowRealization.c P) := by
 apply AMW.localHypsCoreW_eventually hP (WindowRealization.admWindow hP)
 exact eventually_bW_ge_half hP

theorem actual_concreteFacts (Z : ZeroConfig) (H : PaperInputs Z)
 {P : Params} (hP : P.Valid) : Zeta23.ThmD.FactsD (AMW.concreteDataW P (WindowRealization.W P) Z) := by
 apply AMW.concreteFactsW hP H (WindowRealization.admWindow hP)
 exact actual_localHypsCore hP

#print axioms tendsto_cRatio_W
#print axioms H24_eq_cRatio
#print axioms actual_concreteFacts
end StructuralGoal20261016.WindowAsymptotic
end
'''
out=ROOT/'StructuralGoal20261016/WindowAsymptotic.lean'
out.write_text(head+body+middle+last+tail,encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
