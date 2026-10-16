"""Adapt Core's Gram-entry uniform limit to actual new Fourier kernel.

The constants are allowed to grow with the actual new taper profile; their
limit is zero. No local gap-floor assumption enters this uniform convergence.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
start=core.index('lemma integral_sW_mul_cos')
stop=core.index('\nend Limit',start)
limit=core[start:stop]
start=core.index('lemma Kfun_eq_sum')
stop=core.index('\nend Assembly',start)
assembly=core[start:stop]
start=core.index('theorem kernel_limit_uniform (Z : ZeroConfig)')
stop=core.index('\nend Opeth.AMUniformKernel',start)
uniform=core[start:stop]
def adapt(s):
 s=s.replace('Zeta23Ext.Bridge.kfun','kfun')
 s=re.sub(r'\bmtParams\b','WindowCountingBase.mtParams',s)
 for old,new in [
  ('AMW.localHypsCoreAM_eventually','WindowAsymptotic.actual_localHypsCore'),
  ('AMW.admWindow_WAM','WindowRealization.admWindow'),
  ('AMW.aAM_range_of','WindowRealization.a_range_of'),
  ('AMW.atAM_a','WindowRealization.at_a'),
  ('AMW.atAM','WindowRealization.at24'),
  ('AMW.WAM','WindowRealization.W'),
  ('AMW.integral_abs_phiWsq_sub_sharp','WindowAsymptotic.integral_abs_phiWsq_sub_sharp'),
  ('AMW.sW_integrable','WindowAsymptotic.sW_integrable'),
  ('AMW.sW','WindowAsymptotic.sW'),
  ('AMW.hW','WindowAsymptotic.hW'),
  ('AMW.vAM','WindowProfile.V'),
  ('phiHatReal_atAM','WindowSeparated.phiHatReal_at24'),
  ('atAM_phiHatR_eq','WindowSeparated.at24_phiHatR_eq'),
  ('atAM_L','WindowSeparated.at24_L')]:
   s=s.replace(old,new)
 s=s.replace('AMW.cAMW P.ϱ','WindowRealization.c P')
 s=s.replace('AMW.cAMW (paramsOf stdProfile 1).ϱ','WindowRealization.c (paramsOf stdProfile 1)')
 s=s.replace('unfold Kfun AMW.KfunAM\n ring',
   'unfold Kfun WindowKernel.K\n simp_rw [WindowProfile.V_eq]\n ring')
 return s
head='''/- SPDX-License-Identifier: Apache-2.0
Actual new-window uniform retained Gram-entry limit.
Adapted from Zeta23Ext.Bridge's Limit/Assembly kernel estimates and
Opeth.AMUniformKernel.kernel_limit_uniform in the attributed Core.
Every analytic window input is discharged for the actual new v24 profile;
no local floor or zero-proportion conclusion is supplied as a premise.
-/
import StructuralGoal20261016.WindowSeparated
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset Filter MeasureTheory Real Set
open scoped BigOperators
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowUniformKernel

def Kfun (x : ℝ) : ℝ := WindowKernel.K 24 WindowKernel.d24 x
def kfun (x : ℝ) : ℝ := Kfun x / Kfun 0
theorem Kfun_zero_pos : 0 < Kfun 0 := WindowKernel.K_zero_pos 24 WindowKernel.d24
theorem abs_Kfun_le (x : ℝ) : |Kfun x| ≤ Kfun 0 :=
 WindowKernel.abs_K_le 24 WindowKernel.d24 WindowKernel.v24_nonneg x

section Limit
'''
middle='''
end Limit
section Assembly
'''
tail='''
end Assembly

'''
end='''
#print axioms gram_close_of
#print axioms kernel_limit_uniform
end StructuralGoal20261016.WindowUniformKernel
end
'''
out=ROOT/'StructuralGoal20261016/WindowUniformKernel.lean'
out.write_text(head+adapt(limit)+middle+adapt(assembly)+tail+adapt(uniform)+end,
 encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
