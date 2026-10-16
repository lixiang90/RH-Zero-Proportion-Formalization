"""Generate untrusted fixed-grid jet tables and small ordinary-Lean checks.

The data are chosen by the exact Fraction oracle. Their analytic meaning
comes exclusively from WindowJetTableConsumer and the finite checks below.
"""
from pathlib import Path
from fractions import Fraction as F
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(Path(__file__).resolve().parent))
import window_normalized_interval as oracle
I=oracle.I
Q=10**30

def qi(v):
    lo=v.l*Q;hi=v.u*Q
    assert lo.denominator==hi.denominator==1
    return f'qi30 ({lo.numerator}) ({hi.numerator})'
def vec(vs):return '['+', '.join(map(qi,vs))+']'
def mat(vss):return '['+',\n '.join(map(vec,vss))+']'

es=[I(1)]
for r in range(23):es.append(es[-1]*oracle.PI/(r+2))
base=[]
for n in range(33):
    for s in [-1,1]:
        base.append(oracle.normalized_sinc(oracle.PI*n+s*oracle.THETA,
          s*((-1)**n)*oracle.SIN,((-1)**n)*oracle.COS,23))
cos=[]
for m in range(-24,57):
    cos.append(oracle.normalized_sinc(oracle.PI*m,I(0),I((-1)**m),23))
ks=[];ws=[]
for n in range(33):
    total=[base[2*n][r]+base[2*n+1][r] for r in range(24)]
    for j,c in enumerate(oracle.ik.COEFF[1:],1):
        for s in [-1,1]:
            for r,v in enumerate(cos[n+s*j+24]):total[r]+=c*v
    k=[v/(2*oracle.Z) for v in total]
    ks.append(k)
    ws.append([sum((k[j]*k[r-j] for j in range(r+1)),I(0)) for r in range(24)])

head='''/- SPDX-License-Identifier: Apache-2.0
Untrusted 10^-30 rational interval data for the redesigned Fourier window.
No theorem about these table entries is asserted by this data module.
-/
import StructuralGoal20261016.WindowJetTableConsumer
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowJetTableData
open WindowRationalInterval
def qi30 (l u : ℤ) : QI := ((l:ℚ)/10^30,(u:ℚ)/10^30)
'''
data=head
data+='def eValues : List QI := '+vec(es)+'\n'
for name,values in [('baseValues',base),('cosValues',cos),('kValues',ks),('wValues',ws)]:
    data+=f'def {name} : List (List QI) := '+mat(values)+'\n'
data+='''def E (r : ℕ) : QI := eValues.getD r (0,0)
def Base (n : ℕ) (s : Bool) (r : ℕ) : QI :=
 ((baseValues.getD (2*n+(if s then 1 else 0)) []).getD r (0,0))
def Cos (m : ℤ) (r : ℕ) : QI :=
 ((cosValues.getD (m+24).toNat []).getD r (0,0))
def K (n r : ℕ) : QI := ((kValues.getD n []).getD r (0,0))
def W (n r : ℕ) : QI := ((wValues.getD n []).getD r (0,0))
end StructuralGoal20261016.WindowJetTableData
'''
out=ROOT/'StructuralGoal20261016/WindowJetTableData.lean'
out.write_text(data,encoding='utf8',newline='\n')

pilot='''/- SPDX-License-Identifier: Apache-2.0
Small ordinary-kernel pilot for the fixed-grid stepwise jet tables.
-/
import StructuralGoal20261016.WindowJetTableData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowJetTablePilot
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableConsumer WindowJetTableData
theorem e_sound : ∀ r ≤ 23, Holds (E r) (WindowNormalizedJets.e r) := by
 apply e_table_sound
 · decide +kernel
 · have h : ∀ r : Fin 23, covers (rdiv (rmul (E r) piI) (point ((r:ℕ)+2))) (E ((r:ℕ)+1)) = true := by
     decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
theorem base_one_false : ∀ r ≤ 23, Holds (Base 1 false r) (b r (baseZ 1 false)) := by
 apply b_table_sound E (Base 1 false) e_sound (baseZI_sound 1 false)
   (base_trig_sound 1 false).1 (base_trig_sound 1 false).2 (base_guard ⟨1,by decide⟩ false)
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI 1 false) (baseSI 1 false) (baseCI 1) (Base 1 false r) r)
       (Base 1 false ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
set_option pp.fullNames true
#print axioms e_sound
#print axioms base_one_false
end StructuralGoal20261016.WindowJetTablePilot
end
'''
(ROOT/'StructuralGoal20261016/WindowJetTablePilot.lean').write_text(pilot,encoding='utf8',newline='\n')
proofhead='''/- SPDX-License-Identifier: Apache-2.0
Stepwise fixed-grid interval checks for actual normalized sinc moments.
-/
import StructuralGoal20261016.WindowJetTablePilot
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowJetTableBounds
set_option pp.fullNames true
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableConsumer WindowJetTableData WindowJetTablePilot
'''
prooftail='\nend StructuralGoal20261016.WindowJetTableBounds\nend\n'
modules=[]
baseproofs=[]
for n in range(1,33):
    for s in ['false','true']:
        name=f'base_{n}_{s}'
        src=f'''theorem {name} : ∀ r ≤ 23, Holds (Base {n} {s} r) (b r (baseZ {n} {s})) := by
 apply b_table_sound E (Base {n} {s}) e_sound (baseZI_sound {n} {s})
   (base_trig_sound {n} {s}).1 (base_trig_sound {n} {s}).2
   (base_guard ⟨{n},by decide⟩ {s})
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (baseZI {n} {s}) (baseSI {n} {s}) (baseCI {n}) (Base {n} {s} r) r)
       (Base {n} {s} ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms {name}
'''
        baseproofs.append(src)
for g in range((len(baseproofs)+7)//8):
    mod=f'WindowJetTableBase{g:02}'
    (ROOT/f'StructuralGoal20261016/{mod}.lean').write_text(
      proofhead+'\n'.join(baseproofs[g*8:g*8+8])+prooftail,encoding='utf8',newline='\n')
    modules.append('StructuralGoal20261016.'+mod)
cosproofs=[]
for m in range(-24,57):
    name='cos_'+('neg'+str(-m) if m<0 else str(m))
    mz=f'({m}:ℤ)'
    if m==0:
        src=f'''theorem {name} : ∀ r ≤ 23, Holds (Cos {mz} r) (b r (Real.pi*({mz}:ℝ))) := by
 simpa only [Int.cast_zero,mul_zero] using pole_table_sound E (Cos 0) e_sound
   (by
     have h : ∀ r : Fin 24, covers
       (rmul (E r) (phaseI (point 0) (point 1) r).2) (Cos 0 r) = true := by decide +kernel
     intro r hr
     exact h ⟨r,by omega⟩)
#print axioms {name}
'''
    else:
        src=f'''theorem {name} : ∀ r ≤ 23, Holds (Cos {mz} r) (b r (Real.pi*({mz}:ℝ))) := by
 apply b_table_sound E (Cos {mz}) (Z := cosZI {mz}) (S := point 0) (C := signI {mz}) e_sound
 · exact rmul_sound piI_sound (by norm_num [Holds,point])
 · rw [mul_comm,Real.sin_int_mul_pi]
   norm_num [Holds,point]
 · rw [mul_comm,Real.cos_int_mul_pi]
   exact signI_sound {mz}
 · decide +kernel
 · decide +kernel
 · have h : ∀ r : Fin 23, covers
       (bStep E (cosZI {mz}) (point 0) (signI {mz}) (Cos {mz} r) r)
       (Cos {mz} ((r:ℕ)+1)) = true := by decide +kernel
   intro r hr
   exact h ⟨r,hr⟩
#print axioms {name}
'''
    cosproofs.append(src)
for g in range((len(cosproofs)+7)//8):
    mod=f'WindowJetTableCos{g:02}'
    (ROOT/f'StructuralGoal20261016/{mod}.lean').write_text(
      proofhead+'\n'.join(cosproofs[g*8:g*8+8])+prooftail,encoding='utf8',newline='\n')
    modules.append('StructuralGoal20261016.'+mod)
import json
(Path(__file__).parent/'window_jet_table_modules.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
allhead='''/- SPDX-License-Identifier: Apache-2.0
Assemble the checked elementary moment tables over the required finite range.
-/
'''+''.join(f'import {m}\n'for m in modules)+'''
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowJetTablesAll
set_option pp.fullNames true
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableData WindowJetTableBounds
'''
alltext=allhead+'''theorem base_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32)
 (s : Bool) : ∀ r ≤ 23, Holds (Base n s r) (b r (baseZ n s)) := by
 intro r hr
 interval_cases n <;> cases s <;> first
'''+''.join(f' | exact base_{n}_{s} r hr\n'for n in range(1,33) for s in ['false','true'])+'''
theorem cos_sound {m : ℤ} (hm0 : -24 ≤ m) (hm1 : m ≤ 56) :
 ∀ r ≤ 23, Holds (Cos m r) (b r (Real.pi*(m:ℝ))) := by
 intro r hr
 interval_cases m <;> first
'''+''.join(' | exact cos_'+('neg'+str(-m)if m<0 else str(m))+' r hr\n'for m in range(-24,57))+'''
#print axioms base_sound
#print axioms cos_sound
end StructuralGoal20261016.WindowJetTablesAll
end
'''
(ROOT/'StructuralGoal20261016/WindowJetTablesAll.lean').write_text(alltext,encoding='utf8',newline='\n')
finalmodules=[]
for g in range(8):
    text='''/- SPDX-License-Identifier: Apache-2.0
Checked actual normalized k and w coefficients at four integer centres.
-/
import StructuralGoal20261016.WindowJetTablesAll
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowKernelJetTables
set_option pp.fullNames true
open WindowRationalInterval WindowNormalizedJets WindowJetTableConsumer
open WindowIntegerKernelRecipe WindowJetTableData WindowJetTablesAll
'''
    for n in range(4*g+1,4*g+5):
        text+=f'''theorem k_{n} : ∀ r ≤ 23, Holds (K {n} r) (kc 24 WindowKernel.d24 r ({n}:ℝ)) := by
 have h : ∀ r : Fin 24, covers (kOp Base Cos {n} r) (K {n} r) = true := by decide +kernel
 intro r hr
 apply covers_sound (h ⟨r,by omega⟩)
 exact kOp_sound Base Cos (by decide : {n}<33)
   (fun s => base_sound (by decide) (by decide) s r hr)
   (fun m hm0 hm1 => cos_sound hm0 hm1 r hr)
theorem w_{n} : ∀ r ≤ 23, Holds (W {n} r) (wc 24 WindowKernel.d24 r ({n}:ℝ)) := by
 have h : ∀ r : Fin 24, covers (wOp (K {n}) r) (W {n} r) = true := by decide +kernel
 intro r hr
 apply covers_sound (h ⟨r,by omega⟩)
 exact wOp_sound (K {n}) (fun j hj => k_{n} j (by omega))
#print axioms w_{n}
'''
    text+='end StructuralGoal20261016.WindowKernelJetTables\nend\n'
    mod=f'StructuralGoal20261016.WindowKernelJetTables{g:02}'
    (ROOT/(mod.replace('.','/')+'.lean')).write_text(text,encoding='utf8',newline='\n')
    finalmodules.append(mod)
(Path(__file__).parent/'window_jet_table_final_modules.json').write_text(
 json.dumps(modules+['StructuralGoal20261016.WindowJetTablesAll']+finalmodules,indent=2)+'\n',encoding='utf8')
print(out.relative_to(ROOT),out.stat().st_size)
