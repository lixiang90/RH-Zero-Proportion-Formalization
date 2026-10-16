"""Specialize the proven generic energy to the actual 24-mode coefficients.

Uses Core's already-proven conservative sine/cosine rational bounds. The
floor is slightly below the older research decimal to avoid strengthening
any inherited analytic enclosure; the difference is below 1e-22.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
start=core.index('def PAMhi : ℝ :=')
stop=core.index('theorem aInf_eq :',start)
proof=core[start:stop]
proof=proof.replace('6721684105641188747759454444013516755656 / 10 ^ 40',
                    '6720963398090236473924 / 10 ^ 22')
proof=proof.replace('Finset.range 12','Finset.range 24')
proof=proof.replace('PAMhi_nonneg','penaltyHi_nonneg').replace('PAM_le','penalty_le')
proof=proof.replace('PAMhi','penaltyHi').replace('HW_ge','H24_ge')
proof=proof.replace('HW_eq','WindowEnergy.H_eq')
proof=re.sub(r'\bHW\b','WindowEnergy.H 24 WindowKernel.d24',proof)
proof=re.sub(r'\bPAM\b','WindowEnergy.penalty 24 WindowKernel.d24',proof)
proof=re.sub(r'\bdAM\b','WindowKernel.d24',proof)
proof=proof.replace('unfold WindowEnergy.penalty 24 WindowKernel.d24 penaltyHi',
                    'unfold WindowEnergy.penalty penaltyHi')
proof=proof.replace('unfold penaltyHi WindowKernel.d24',
                    'unfold penaltyHi WindowKernel.d24')
proof=proof.replace('cAM, cAMn','StructuralW10Followup20261016.NewWindows.nums24')
head='''/- SPDX-License-Identifier: Apache-2.0
Conservative rational lower bound on the actual 24-mode analytic energy.
Adapted from the attributed AMW.PAM_le/HW_ge proof, using the same proven
sine/cosine enclosures. No global gap floor or zero-counting bound is assumed.
-/
import StructuralGoal20261016.WindowKernel
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW
namespace StructuralGoal20261016.WindowEnergyBound

'''
tail='''
#print axioms penalty_le
#print axioms floor_numeric
#print axioms H24_ge
end StructuralGoal20261016.WindowEnergyBound
end
'''
out=ROOT/'StructuralGoal20261016/WindowEnergyBound.lean'
out.write_text(head+proof+tail,encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
