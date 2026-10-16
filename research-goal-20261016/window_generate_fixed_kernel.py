"""Emit compact ordinary-kernel checks for the fixed-integer K/W evaluator."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
mods=[]
for n in range(1,33):
    name=f'WindowFixedKernelCenter{n:02}'
    src=f'''/- SPDX-License-Identifier: Apache-2.0
Actual Fourier kernel and squared-kernel coefficients at integer centre {n}.
-/
import StructuralGoal20261016.WindowFixedKernel
'''
    if n==1:src+='import StructuralGoal20261016.WindowFixedKernelPilot\n'
    src+='''set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelCenters
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational
'''
    for kind,target,op in [('k','K','kernel'),('w','W','square')]:
        src+=f'\ntheorem {kind}_{n} : ∀ r ≤ 23, Holds ({target} {n} r) ({kind}c 24 WindowKernel.d24 r ({n}:ℝ)) := by\n'
        if n==1:
            src+=f' simpa only [Nat.cast_one] using WindowFixedKernelPilot.{kind}_one\n'
        else:
            src+=f''' have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.{op} {n} r) ({target} {n} r) = true := by decide +kernel
 intro r hr
'''
            if kind=='k':src+=f''' have h := WindowFixedKernel.FI.kernel_of_check (n := {n}) (by decide) (by decide) hr (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
'''
            else:src+=f''' have h := WindowFixedKernel.FI.square_of_check (n := {n})
   (fun j hj => by simpa only [Nat.cast_ofNat] using k_{n} j (by omega)) (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
'''
        src+=f'set_option pp.fullNames true\n#print axioms {kind}_{n}\n'
    src+='end StructuralGoal20261016.WindowFixedKernelCenters\nend\n'
    (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(src,encoding='utf8',newline='\n')
    mods.append('StructuralGoal20261016.'+name)
(HERE/'window_fixed_kernel_modules.json').write_text(json.dumps(mods,indent=2)+'\n',encoding='utf8')
print(json.dumps({'centres':len(mods),'source_bytes':sum((ROOT/(m.replace('.','/')+'.lean')).stat().st_size for m in mods)}))
