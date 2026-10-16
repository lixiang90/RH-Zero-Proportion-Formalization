"""Emit actual v24 Profile and variation certificate source.

The displayed decimal sine table is untrusted data until tabOk is proved by
Lean against Core's rational Taylor enclosure. A high precision generator is
used only to choose enclosing integers. The finite check uses +kernel.
"""
from pathlib import Path
import re
import mpmath as mp

ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
mp.mp.dps=60
table=[]
for q in range(257):
    a=int(mp.floor(mp.sin(mp.pi*q/512)*10**10))
    table.append((a-100000,a+100001))

start=core.index('def vAMd (s : ℝ)')
stop=core.index('def hW (L : ℝ)',start)
deriv=core[start:stop]
deriv=deriv.replace('Finset.range 13','Finset.range 25')
deriv=deriv.replace('7 / 2','5').replace('≤ 78','≤ 160')
for old,new in [('hasDerivAt_vAMd','hasDerivAt_Vd'),('hasDerivAt_vAM','hasDerivAt_V'),
                ('abs_vAMdd_le','abs_Vdd_le'),('abs_vAMd_le','abs_Vd_le'),
                ('vAMdd','Vdd'),('vAMd','Vd'),('vAM','V'),
                ('ωAM_sq_le','freq_sq_le'),('ωAM_nonneg','freq_nonneg'),
                ('ωAM_zero','freq_zero'),('ωAM_le','freq_le'),('ωAM','freq')]:
    deriv=deriv.replace(old,new)
deriv=deriv.replace('cAM, cAMn','coeffQ, StructuralW10Followup20261016.NewWindows.nums24')
deriv=re.sub(r'\bcAM\b','coeffQ',deriv)

start=core.index('def sinTabZ : List')
stop=core.index('theorem deriv2_vAM_div',start)
pv=core[start:stop]
pv=re.sub(r'def sinTabZ : List \(ℤ × ℤ\) := \[[^\n]*\]',
    'def sinTabZ : List (ℤ × ℤ) := ['+', '.join(f'({a}, {b})'for a,b in table)+']',pv)
# First enlarge grid constants, before substituting the new table.
line_end=pv.index('\n')
tabline=pv[:line_end]
pv=pv[line_end:]
changes={64:256,65:257,78:160,128:512,160:640,192:768,256:1024,13:25}
pv=re.sub(r'\b(?:'+ '|'.join(str(x)for x in changes)+r')\b',lambda x:str(changes[int(x[0])]),pv)
pv=tabline+pv
for old,new in [('hasDerivAt_vAMd','hasDerivAt_Vd'),('hasDerivAt_vAM','hasDerivAt_V'),
                ('abs_vAMdd_le','abs_Vdd_le'),('vAMd_mid_le','Vd_mid_le'),
                ('vAMd_lipschitz','Vd_lipschitz'),('deriv_vAM_div','deriv_V_div'),
                ('pvCheck_AM','pvCheck_v24'),('vAMd','Vd'),('vAM','V'),
                ('cAM_zero','coeffQ_zero'),('ωAM_zero','freq_zero'),('ωAM','freq')]:
    pv=pv.replace(old,new)
pv=re.sub(r'\bcAM\b','coeffQ',pv)

head='''/- SPDX-License-Identifier: Apache-2.0
Actual 24-mode admissible window, including positive-variation budget.
Derivative and rational variation proofs adapt the attributed AMW proofs.
The 257 sine table entries are checked with Core's rational Taylor theorem;
the data generator is not trusted. No new zero-proportion is asserted here.
-/
import StructuralGoal20261016.WindowKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW Zeta23
namespace StructuralGoal20261016.WindowProfile

def coeffQ (j : ℕ) : ℚ := if j = 0 then 1 else
 (StructuralW10Followup20261016.NewWindows.nums24 (j-1) : ℚ) / 1000000000
def freq (j : ℕ) : ℝ := if j = 0 then Real.sqrt 2 else 2 * π * j
def V (s : ℝ) : ℝ := ∑ j ∈ Finset.range 25, (coeffQ j : ℝ) * Real.cos (freq j*s)

theorem coeffQ_zero : (coeffQ 0 : ℝ) = 1 := by norm_num [coeffQ]
theorem freq_zero : freq 0 = Real.sqrt 2 := by simp [freq]

theorem V_eq (s : ℝ) : V s = WindowEnergy.v 24 WindowKernel.d24 s := by
 rw [V, Finset.sum_range_succ', coeffQ_zero, freq_zero, one_mul, add_comm]
 unfold WindowEnergy.v
 congr 1
 apply Finset.sum_congr rfl
 intro j _
 simp [coeffQ, freq, WindowKernel.d24, AMW.ek]
 <;> ring

theorem V_eq_v24 (s : ℝ) : V s = StructuralW10Followup20261016.NewWindows.v24 s := by
 rw [V_eq, WindowKernel.v24_eq]

theorem V_continuous : Continuous V := by
 unfold V
 fun_prop
theorem V_contDiff : ContDiff ℝ ⊤ V := by
 unfold V
 exact ContDiff.sum fun j _ => contDiff_const.mul
   (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
theorem V_even (s : ℝ) : V (-s) = V s := by
 simp only [V, mul_neg, Real.cos_neg]
theorem V_zero : V 0 = 1011052017 / 1000000000 := by
 norm_num [V, coeffQ, freq, StructuralW10Followup20261016.NewWindows.nums24,
   Finset.sum_range_succ]
theorem V_ge_core {s : ℝ} (hs : |s| ≤ 1/2) : 67/100 ≤ V s := by
 rw [V_eq_v24]
 exact StructuralW10Followup20261016.WindowProfileGeneral.profile_ge_core _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 hs
theorem V_pos_wide {s : ℝ} (hs : |s| ≤ 3/5) : 0 < V s := by
 rw [V_eq_v24]
 exact StructuralW10Followup20261016.NewWindows.v24_positive hs
theorem V_le (s : ℝ) : V s ≤ 5/4 := by
 rw [V_eq_v24]
 have hp := StructuralW10Followup20261016.WindowProfileGeneral.abs_perturb_le _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 s
 have hc := Real.cos_le_one (Real.sqrt 2*s)
 unfold StructuralW10Followup20261016.NewWindows.v24
   StructuralW10Followup20261016.WindowProfileGeneral.profile
 linarith only [(abs_le.mp hp).2, hc]

'''
tail='''
theorem deriv2_V_div : deriv (deriv (fun s => V s / MAM)) = fun s => Vdd s / MAM := by
 rw [deriv_V_div]
 exact funext fun s => ((hasDerivAt_Vd s).div_const MAM).deriv

theorem V_zero_div_le : V 0 / MAM ≤ 81/100 := by
 rw [V_zero, MAM]
 norm_num

theorem actual_profile : AMW.Profile (fun s => V s / MAM) (1/10) 4 128 (9/200) where
 δ_pos := by norm_num
 A₁_nonneg := by norm_num
 A₂_nonneg := by norm_num
 even := fun s => by simp only [V_even]
 contDiff := (V_contDiff.of_le le_top).div_const MAM
 pos := fun s hs => div_pos (V_pos_wide (by linarith)) MAM_pos
 ge_quarter := fun s hs => by
   have := V_ge_core hs
   rw [MAM, le_div_iff₀ (by norm_num)]
   linarith
 le_one := fun s _ => by rw [div_le_one MAM_pos]; exact V_le s
 deriv_le := fun s _ => by
   rw [deriv_V_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
   linarith [abs_Vd_le s]
 deriv2_le := fun s _ => by
   rw [deriv2_V_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
   linarith [abs_Vdd_le s]
 posVar := by
   have h := posVar_of_check pvCheck_v24
   push_cast at h
   exact h
 budget := by
   have h0 : Real.sqrt (V 0 / MAM) ≤ 9/10 := by
     rw [show (9/10 : ℝ) = Real.sqrt (81/100) by
       rw [show (81/100 : ℝ) = (9/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
     exact Real.sqrt_le_sqrt V_zero_div_le
   linarith
 budget_sq := by linarith [V_zero_div_le]

def phi (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ :=
 AMW.phiM (AMW.fP (fun s => V s / MAM) L) ϱ L w

theorem actual_admWindow {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8*w ≤ L) :
 AdmWindow (phi ϱ L w) L w (AMW.cMod ϱ 4 (128+2*4^2)) :=
 AMW.admWindow_fP actual_profile hϱ hw hwL

#print axioms V_eq_v24
#print axioms abs_Vdd_le
#print axioms pvCheck_v24
#print axioms actual_profile
#print axioms actual_admWindow
end StructuralGoal20261016.WindowProfile
end
'''
out=ROOT/'StructuralGoal20261016/WindowProfile.lean'
out.write_text(head+deriv+pv+tail,encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
