"""Thin actual-basin wrappers using the common checked scalar row theorem."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
gram=json.loads((HERE/'cover-newwindow-gram.json').read_bytes());mapping=json.loads((HERE/'window_anchor_map.json').read_bytes())
mods=[]
for b,g in enumerate(gram['results']):
 ids=[mapping[s['anchor']]for s in g['scalar_minorants']];chunks=sorted({i//64 for i in ids})
 imp='WindowGramTransferPart00'if b<8 else f'WindowGramTransferItem{b:02}'
 name=f'WindowActualBasin{b:02}'
 defs=', '.join(f'WindowAnchorCertificateData.rows{j:02}'for j in chunks)
 src=f'''/- SPDX-License-Identifier: Apache-2.0
Actual new-window energy floor in coherent integer basin {b}.
All 41 scalar inequalities come from the common checked row minorants.
-/
import StructuralGoal20261016.WindowScalarBridge
import StructuralGoal20261016.{imp}
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowActualBasins
open WindowGramTransfer WindowGramBasins WindowScalarBridge WindowAnchorCertificateData

def index{b} : Fin 41 → ℕ := ![{', '.join(map(str,ids))}]
def Region{b} (g : Fin 9 → ℝ) : Prop := ∀ t : Fin 41,
 span g t ∈ Icc (((row (index{b} t)).center:ℝ)-21/100) (((row (index{b} t)).center:ℝ)+21/100)

theorem index{b}_lt (t : Fin 41) : index{b} t < 1567 := by fin_cases t <;> decide

theorem scalar{b}_eq (g : Fin 9 → ℝ) (t : Fin 41) :
 WindowGramTransfer.scalar{b} g t = minorant (row (index{b} t)) (span g t) := by
 unfold WindowGramTransfer.scalar{b}
 suffices ∀ x : ℝ, V{b} t+S{b} t*(x-span q{b} t)+A{b} t*(x-span q{b} t)^2 =
     minorant (row (index{b} t)) x from this (span g t)
 intro x
 fin_cases t <;>
   norm_num [V{b},S{b},A{b},q{b},span,pairI,pairJ,ptsN,index{b},minorant,radius,
     WindowConvexityAll.lower,WindowAnchorCertificateData.row,{defs},
     Fin.sum_univ_succ,Fin.succ] <;> ring

theorem actual{b} (g : Fin 9 → ℝ) (hregion : Region{b} g) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
 apply WindowGramTransfer.actual{b} g
 intro t
 rw [scalar{b}_eq]
 exact WindowScalarBridge.actual (index{b} t) (index{b}_lt t) (hregion t)

set_option pp.fullNames true
#print axioms actual{b}
end StructuralGoal20261016.WindowActualBasins
end
'''
 (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(src,encoding='utf8',newline='\n')
 mods.append('StructuralGoal20261016.'+name)
(HERE/'window_actual_basin_modules.json').write_text(json.dumps(mods,indent=2)+'\n',encoding='utf8')
print(json.dumps({'basins':len(mods),'source_bytes':sum((ROOT/(m.replace('.','/')+'.lean')).stat().st_size for m in mods)}))
