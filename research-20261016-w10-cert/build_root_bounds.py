"""Generate the exact initial polytope and its coercive coverage proof."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
raw=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_text())
bs=raw['b_numerators'] if 'b_numerators' in raw else raw['b']
if isinstance(bs[0],list):bs=[v[-1] for v in bs]
SC=32768;SEP=27852;CN=86600000
extra=CN*SC-sum(bs)*SEP
adj=[(i,i+1) for i in range(9)]
pr=[(i,j) for i in range(10) for j in range(i+2,10)]
def hi(i,j):
    b=min(bs[i:j]);return (j-i)*SEP+(extra+b-1)//b
def lean(xs):return str(xs)
source='''/- SPDX-License-Identifier: Apache-2.0
Exact pressure bounds on every possible counterexample to the W10 floor.
This is the initial-domain lemma, not the remaining finite coverage proof. -/
import StructuralW10Cert20261016.LocalChecker

noncomputable section
open Finset AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralResearch20261016.W10RefinedCandidate
open Zeta23Ext.BridgeW
open scoped BigOperators
set_option maxHeartbeats 4000000
namespace StructuralW10Cert20261016.RootBounds

def initialCell : Cl :=
  ⟨L_LIST, U_LIST, A_LIST, B_LIST⟩

theorem counterexample_in_root {g : ℕ → ℝ}
    (hg : ∀ r < 9, (17 / 20 : ℝ) ≤ g r)
    (hcounter : Fw W (fun r : Fin 9 => g r) < (433 : ℝ) / 50000) :
    InCell 9 PR initialCell g := by
  have hscale : Fg 9 BS TS g < 86600000 := by
    rw [fg_eq_scaled_Fw]
    nlinarith only [hcounter]
  have hkernel : 0 ≤ ∑ t ∈ range TS.length,
      ((tA TS t : ℕ) : ℝ) * AMW.Cert.wfun (gsum g (tI TS t) (tJ TS t)) :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (AMW.Cert.wfun_nonneg _)
  have hp : (∑ r ∈ range 9, ((BS.getD r 0 : ℕ) : ℝ) * g r) < 86600000 := by
    unfold Fg at hscale
    linarith only [hscale, hkernel]
  norm_num [BS, Finset.sum_range_succ] at hp
GRID_HYPOTHESES
  constructor
  · intro r hr
    interval_cases r <;> constructor <;>
      norm_num [initialCell, SC] <;> linarith only [HYPOTHESES]
  · intro k hk
    norm_num [PR] at hk
    interval_cases k <;> constructor <;>
      norm_num [initialCell, PR, pI, pJ, gsum_range, Finset.sum_range_succ, SC] <;>
      linarith only [HYPOTHESES]

#print axioms counterexample_in_root
end StructuralW10Cert20261016.RootBounds
end
'''
source=source.replace('L_LIST',lean([SEP]*9)).replace('U_LIST',lean([hi(*p) for p in adj]))
source=source.replace('A_LIST',lean([(j-i)*SEP for i,j in pr])).replace('B_LIST',lean([hi(*p) for p in pr]))
lines=[]
for r in range(9):
    lines += [f'  have hg{r} := hg {r} (by decide)',
              f'  have h{r} : (27852 : ℝ) / 32768 ≤ g {r} := by linarith only [hg{r}]']
source=source.replace('GRID_HYPOTHESES','\n'.join(lines))
source=source.replace('HYPOTHESES',', '.join(['hp']+[f'h{r}' for r in range(9)]))
out=ROOT/'StructuralW10Cert20261016/RootBounds.lean'
out.write_text(source,encoding='utf8')
(Path(__file__).with_name('initial-domain.json')).write_text(json.dumps({
    'SC':SC,'SEP':SEP,'cN':CN,'BS':bs,'extra':extra,
    'all_pairs':adj+pr,'lo':[(j-i)*SEP for i,j in adj+pr],
    'hi':[hi(i,j) for i,j in adj+pr]},indent=2)+'\n',encoding='utf8')
print(out)
