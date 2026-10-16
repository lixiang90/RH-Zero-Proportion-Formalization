"""Generate actual Fw24 transfers from the 41 explicit scalar minorants.

The generated theorems keep every scalar actual-kernel inequality as a
premise. Finite rational algebra discharges all remaining energy assembly.
It asserts neither those analytic premises nor a global chamber cover.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def lit(x):
    x=F(x);return f'({x.numerator} : ℝ) / {x.denominator}'
def vector(v):return '!['+', '.join(lit(x) for x in v)+']'
def main():
    source=HERE/'cover-newwindow-gram.json';doc=json.loads(source.read_bytes());rows=doc['results']
    param=ROOT/'research-20261016-followup/window_reweight_rational.json';P=json.loads(param.read_bytes());terms=[(i,j,F(a,P['denominator'])) for i,j,a in P['a_upper'] if a]
    assert len(rows)==69 and len(terms)==41
    pairs=lambda v:'!['+', '.join(str(x) for x in v)+']'
    out=['''/- SPDX-License-Identifier: Apache-2.0
Actual Fw24 transfer from 41 explicit scalar minorants per coherent basin.
The actual-kernel scalar inequalities remain hypotheses. No global floor is
asserted without those analytic hypotheses and a complete chamber cover.
-/
import StructuralGoal20261016.WindowGapEnergy
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
open Finset
open scoped BigOperators
open Zeta23Ext.Bridge
open Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowGramTransfer
''',f'def pairI : Fin 41 → Fin 10 := {pairs([i for i,j,a in terms])}\n',
      f'def pairJ : Fin 41 → Fin 10 := {pairs([j for i,j,a in terms])}\n',
      f'def weight : Fin 41 → ℝ := {vector([a for i,j,a in terms])}\n',
      '''def span (g : Fin 9 → ℝ) (t : Fin 41) : ℝ :=
  ptsN 10 g (pairJ t)-ptsN 10 g (pairI t)
def pressure (g : Fin 9 → ℝ) : ℝ :=
  ∑ r, StructuralW10Followup20261016.NewLedger.W.b r*g r

theorem weight_nonneg (t : Fin 41) : 0 ≤ weight t := by
  fin_cases t <;> norm_num [weight]

theorem actual_energy_expansion (g : Fin 9 → ℝ) :
    WindowGapEnergy.Fw24 g = pressure g+∑ t : Fin 41,
      weight t*WindowKernel.w 24 WindowKernel.d24 (span g t) := by
  simp [WindowGapEnergy.Fw24, WindowGapEnergy.Fw, pressure, span,
    pairI, pairJ, weight, StructuralW10Followup20261016.NewLedger.W,
    StructuralW10Followup20261016.NewLedger.a,
    StructuralW10Followup20261016.NewLedger.aN,
    StructuralW10Followup20261016.NewLedger.b,
    StructuralW10Followup20261016.NewLedger.bN,
    Fin.sum_univ_succ, Fin.succ] <;> ring

theorem scalar_sum_le (g : Fin 9 → ℝ) (Q : Fin 41 → ℝ)
    (hQ : ∀ t, Q t ≤ WindowKernel.w 24 WindowKernel.d24 (span g t)) :
    pressure g+∑ t, weight t*Q t ≤ WindowGapEnergy.Fw24 g := by
  rw [actual_energy_expansion]
  exact add_le_add le_rfl (Finset.sum_le_sum fun t _ =>
    mul_le_mul_of_nonneg_left (hQ t) (weight_nonneg t))
''']
    expansion=ROOT/'StructuralGoal20261016/WindowGramExpansion.lean'
    expansion.write_bytes((''.join(out)+'end StructuralGoal20261016.WindowGramTransfer\nend\n').encode('utf8'))
    out=['''/- SPDX-License-Identifier: Apache-2.0
Actual energy transfers for the 69 coherent Gram basins. The 41 scalar
actual-kernel inequalities per basin remain explicit analytic hypotheses.
-/
import StructuralGoal20261016.WindowGramBasins
import StructuralGoal20261016.WindowGramExpansion
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
open Finset
open scoped BigOperators
open Zeta23Ext.Bridge
open Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowGramTransfer
open WindowGramBasins
''']
    for k,row in enumerate(rows):
        scalar=row['scalar_minorants'];V=[F(s['value_lower'])-F(s['slope_error_loss']) for s in scalar];S=[F(s['slope']) for s in scalar];A=[F(s['quadratic_coefficient']) for s in scalar]
        out.extend([f'def V{k} : Fin 41 → ℝ := {vector(V)}\n',f'def S{k} : Fin 41 → ℝ := {vector(S)}\n',f'def A{k} : Fin 41 → ℝ := {vector(A)}\n',f'''def scalar{k} (g : Fin 9 → ℝ) (t : Fin 41) : ℝ :=
  V{k} t+S{k} t*(span g t-span q{k} t)+A{k} t*(span g t-span q{k} t)^2
def remainder{k} (g : Fin 9 → ℝ) : ℝ := ∑ t : Fin 41,
  if (pairJ t : ℕ) = (pairI t : ℕ)+1 then 0
  else weight t*A{k} t*(span g t-span q{k} t)^2

theorem remainder{k}_nonneg (g : Fin 9 → ℝ) : 0 ≤ remainder{k} g := by
  have hA (t : Fin 41) : 0 ≤ A{k} t := by
    fin_cases t <;> norm_num [A{k}]
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mul_nonneg (weight_nonneg t) (hA t)) (sq_nonneg _)

theorem expansion{k} (g : Fin 9 → ℝ) :
    pressure g+∑ t, weight t*scalar{k} g t =
      (C{k}+∑ r, (b{k} r*(g r-q{k} r)+d{k} r*(g r-q{k} r)^2))+remainder{k} g := by
  simp [pressure, scalar{k}, remainder{k}, span, ptsN,
    C{k}, b{k}, d{k}, q{k}, V{k}, S{k}, A{k}, pairI, pairJ, weight,
    StructuralW10Followup20261016.NewLedger.W,
    StructuralW10Followup20261016.NewLedger.b,
    StructuralW10Followup20261016.NewLedger.bN,
    Fin.sum_univ_succ, Fin.succ] <;> ring

/-- The 41 pointwise analytic inputs are all explicit in scalar{k}. -/
theorem actual{k} (g : Fin 9 → ℝ)
    (hs : ∀ t : Fin 41, scalar{k} g t ≤
      WindowKernel.w 24 WindowKernel.d24 (span g t)) :
    (221 : ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
  have h := scalar_sum_le g (scalar{k} g) hs
  rw [expansion{k}] at h
  exact (lower{k} (fun r => g r-q{k} r)).trans
    ((le_add_of_nonneg_right (remainder{k}_nonneg g)).trans h)
#print axioms actual{k}
'''])
    tail='end StructuralGoal20261016.WindowGramTransfer\nend\n'
    assert len(out)==1+4*69
    parts=[]
    specs=[(0,8,'WindowGramTransferPart00')]+[(k,k+1,f'WindowGramTransferItem{k:02}') for k in range(8,69)]
    for start,end,name in specs:
        part=ROOT/f'StructuralGoal20261016/{name}.lean'
        encoded=(out[0]+''.join(out[1+4*start:1+4*end])+tail).encode('utf8')
        if name=='WindowGramTransferPart00' and part.exists():
            assert part.read_bytes()==encoded,'Preserve the ordinary-kernel verified Part00 source'
        else:part.write_bytes(encoded)
        parts.append({'path':str(part.relative_to(ROOT)).replace('\\','/'),'first_basin':start,'last_basin':end-1,
          'basins':end-start,'sha256':hashlib.sha256(part.read_bytes()).hexdigest(),'bytes':part.stat().st_size,
          'ordinary_Lean_compiled':False})
    target=ROOT/'StructuralGoal20261016/WindowGramTransfer.lean'
    target.write_text('/- SPDX-License-Identifier: Apache-2.0\nAll 69 actual energy transfers. The scalar actual-kernel hypotheses remain explicit.\n-/\n'+
      ''.join(f'import StructuralGoal20261016.{Path(p["path"]).stem}\n' for p in parts)+
      'set_option pp.fullNames true\n'+
      '#print axioms StructuralGoal20261016.WindowGramTransfer.actual_energy_expansion\n'+
      '#print axioms StructuralGoal20261016.WindowGramTransfer.scalar_sum_le\n'+
      ''.join(f'#print axioms StructuralGoal20261016.WindowGramTransfer.actual{k}\n' for k in range(69)),encoding='utf8')
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'parameter_sha256':hashlib.sha256(param.read_bytes()).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
      'expansion_output_sha256':hashlib.sha256(expansion.read_bytes()).hexdigest(),'expansion_source_bytes':expansion.stat().st_size,
      'source_bytes':target.stat().st_size,'parts':parts,'total_partitioned_basins':sum(p['basins'] for p in parts),
      'retired_unverified_partitions':[f'StructuralGoal20261016/WindowGramTransferPart{k:02}.lean' for k in range(1,9)],
      'basins':69,'explicit_scalar_minorants_per_basin':41,'ordinary_Lean_compiled':False,'actual_scalar_minorants_proven':False,'global_cover':False}
    (HERE/'cover-window-transfer-generated.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt))
if __name__=='__main__':main()
