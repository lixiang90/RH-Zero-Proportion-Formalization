"""Emit actual new-window separated Gram/spectral bridge.

All finite-height Gram realizations, Poisson and normalization arguments are
adapted from the attributed Core. New profile domination is discharged by
the previously proved 24-mode profile majorant, not supplied as a premise.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
start=core.index('private lemma re_paperFT_ofReal')
stop=core.index('\nend Opeth.AMSeparatedGram',start)
part=core[start:stop]
start2=core.index('theorem gram_entry_eq_re (Z : ZeroConfig)')
stop2=core.index('\nend Opeth.AMSeparatedSpectrum',start2)
part2=core[start2:stop2]

def adapt(s):
    s=s.replace('Zeta23Ext.Bridge.mtParams','WINDOW_PARAMS')
    s=re.sub(r'\bmtParams\b','WindowCountingBase.mtParams',s)
    s=s.replace('WINDOW_PARAMS','WindowCountingBase.mtParams')
    for old,new in [
      ('AMW.admWindow_WAM','WindowRealization.admWindow'),
      ('AMW.atAM_a','WindowRealization.at_a'),
      ('AMW.atAM','WindowRealization.at24'),
      ('AMW.WAM','WindowRealization.W'),
      ('AMW.phiW_sq_eq','WindowAsymptotic.phiW_sq_eq'),
      ('AMW.hW','WindowAsymptotic.hW'),
      ('AMW.vAM_ge_core','WindowProfile.V_ge_core'),
      ('AMW.vAM','WindowProfile.V'),
      ('AMW.aInf_eq','WindowAsymptotic.aInf_eq'),
      ('AMW.aInf_pos','WindowAsymptotic.aInf_pos'),
      ('AMW.aInf','WindowAsymptotic.aInf'),
      ('AMW.tendsto_aW','WindowAsymptotic.tendsto_aW'),
      ('Zeta23Ext.Bridge.phiHatReal_atAM','phiHatReal_at24'),
      ('Zeta23Ext.Bridge.atAM_phiHatR_eq','at24_phiHatR_eq'),
      ('Zeta23Ext.Bridge.atAM_L','at24_L'),
      ('phiHatReal_atAM','phiHatReal_at24'),
      ('AMSeparatedGram.','WindowSeparated.')]:
        s=s.replace(old,new)
    s=s.replace('137 / 200','67 / 100')
    s=s.replace('AMMajorant.normalized_profile_le_scaled_majorant hs',
                'normalized_profile_le_scaled_majorant hs')
    return s
part=adapt(part)
part=part.replace('rw [WindowRealization.W, WindowAsymptotic.phiW_sq_eq hP.taper hw hL, WindowAsymptotic.hW,',
 'change WindowAsymptotic.phiW P.ϱ (P.L T) P.w (P.L T * s) ^ 2 = _\n      rw [WindowAsymptotic.phiW_sq_eq hP.taper hw hL, WindowAsymptotic.hW,')
part2=adapt(part2)

head='''/- SPDX-License-Identifier: Apache-2.0
Actual new-window separated Gram and spectral bounds.
Adapted from Opeth.AMSeparatedGram and Opeth.AMSeparatedSpectrum in the
attributed Core. Actual new-profile domination and normalization replace the
old fixed cosine coefficients. No local floor or new proportion is assumed.
-/
import StructuralGoal20261016.WindowCountingBase
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg Filter MeasureTheory Real Set
open scoped ComplexOrder BigOperators Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD
open Zeta23Ext.Bridge Opeth
namespace StructuralGoal20261016.WindowSeparated

@[simp] theorem at24_L (P : Params) (T : ℝ) : (WindowRealization.at24 P T).L = P.L := rfl
theorem at24_phiHatR_eq {P : Params} (hP : P.Valid) (T : ℝ) :
 (WindowRealization.at24 P T).phiHatR T = AdmWindow.vHatR (WindowRealization.W P T) :=
 AMW.atW_phiHatR T hP (WindowRealization.W_even P T)
theorem phiHatReal_at24 {P : Params} (hP : P.Valid) (T : ℝ) :
 PhiHatReal T (WindowRealization.at24 P T) := fun r => GzGp.phiHat_ofReal _ T r
theorem normalized_profile_le_scaled_majorant {s : ℝ} (hs : |s| ≤ 1/2) :
 AMW.rhoAM * WindowProfile.V s ≤ Opeth.AMMajorant.scaledMajorant s := by
 rw [WindowProfile.V_eq_v24]
 exact StructuralW10Followup20261016.NewWindows.v24_dominated hs

'''
middle='''
#print axioms eventually_gram_form_le
end StructuralGoal20261016.WindowSeparated
namespace StructuralGoal20261016.WindowSeparatedSpectrum
open WindowSeparated
open Classical
'''
tail='''
#print axioms eventually_principal_eigenvalues_le_two
end StructuralGoal20261016.WindowSeparatedSpectrum
end
'''
out=ROOT/'StructuralGoal20261016/WindowSeparated.lean'
out.write_text(head+part+middle+part2+tail,encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
