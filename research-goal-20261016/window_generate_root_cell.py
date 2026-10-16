"""Instantiate the exact coupled-pressure difference cell used by discovery."""
from pathlib import Path
import argparse,hashlib,json
import window_global_cover as w
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def vec(xs):return '!['+', '.join(map(str,xs))+']'
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--lower',action='store_true');args=ap.parse_args()
    if args.lower:
        import window_lower_global_cover as cov
    else:cov=w
    lo,hi=cov.root();b=cov.g.BS
    matrix=[[0]*10 for _ in range(10)]
    minimum=[[1]*10 for _ in range(10)]
    for (i,j),l,u in zip(cov.g.ALL,lo,hi):
        matrix[i][j]=u;matrix[j][i]=-l
        minimum[i][j]=min(b[i:j])
    body='''/- SPDX-License-Identifier: Apache-2.0
Actual root cell of the new-window cover: every coupled pressure bound.
The numeric comparisons are kernel-checked over rationals. No global floor
or complete coverage is claimed by this root-containment theorem.
-/
import StructuralGoal20261016.WindowPressureRoot
import StructuralGoal20261016.WindowDifferenceCell
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Finset Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowRootCell
open StructuralW10Followup20261016.NewLedger

def indices (i j : Fin 10) : Finset (Fin 9) :=
  Finset.univ.filter (fun r => (i:ℕ) ≤ (r:ℕ) ∧ (r:ℕ) < (j:ℕ))

def root : DifferenceCell.Cell 10 := MATRIX
def minimum : Fin 10 → Fin 10 → ℕ := MINIMUM

theorem span_indices (g : Fin 9 → ℝ) (i j : Fin 10) (hij : (i:ℕ) ≤ (j:ℕ)) :
    ptsN 10 g j-ptsN 10 g i = ∑ r ∈ indices i j, g r := by
  simp only [ptsN,indices,← Finset.sum_sub_distrib,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp_all <;> omega

def Numeric : Prop :=
  (∀ i : Fin 10, root i i = 0) ∧ ∀ i j : Fin 10, (i:ℕ) < (j:ℕ) →
    0 < minimum i j ∧
    (∀ r ∈ indices i j, minimum i j ≤ bN r) ∧
    ((indices i j).card:ℚ)*(123/128)+
      ((221/25000)-(123/128)*(11055671/2500000000))/((minimum i j:ℚ)/10000000000)
        ≤ (root i j:ℚ)/32768 ∧
    -(root j i:ℚ)/32768 ≤ ((indices i j).card:ℚ)*(123/128)

theorem numeric : Numeric := by
  unfold Numeric
  decide +kernel

theorem positive_span_upper (g : Fin 9 → ℝ)
    (hg : WindowPressureRoot.Region (123/128) (221/25000) g)
    (i j : Fin 10) (hij : (i:ℕ) < (j:ℕ)) :
    ptsN 10 g j-ptsN 10 g i ≤ (root i j:ℝ)/32768 := by
  have data := numeric.2 i j hij
  have hmN : (0:ℝ) < (minimum i j:ℝ) := by exact_mod_cast data.1
  have hm : (0:ℝ) < (minimum i j:ℝ)/10000000000 := by positivity
  have hmb : ∀ r ∈ indices i j, (minimum i j:ℝ)/10000000000 ≤ W.b r := by
    intro r hr
    change (minimum i j:ℝ)/10000000000 ≤ (bN r:ℝ)/10000000000
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact_mod_cast data.2.1 r hr
  have h := WindowPressureRoot.selected_span_upper (indices i j) W.b g
    (123/128) (221/25000) ((minimum i j:ℝ)/10000000000)
    b_nonneg hg.1 hm hmb hg.2
  have hB : (∑ r, W.b r) = (11055671:ℝ)/2500000000 := pressure_eq
  rw [hB] at h
  have hu : ((indices i j).card:ℝ)*(123/128)+
      ((221/25000)-(123/128)*(11055671/2500000000))/((minimum i j:ℝ)/10000000000)
        ≤ (root i j:ℝ)/32768 := by
    have hQ := data.2.2.1
    have hR : ((((indices i j).card:ℚ)*(123/128)+
      ((221/25000)-(123/128)*(11055671/2500000000))/((minimum i j:ℚ)/10000000000):ℚ):ℝ)
        ≤ (((root i j:ℚ)/32768:ℚ):ℝ) := Rat.cast_le.mpr hQ
    push_cast at hR
    exact hR
  rw [span_indices g i j hij.le]
  exact h.le.trans hu

theorem positive_span_lower (g : Fin 9 → ℝ)
    (hg : CoverCoerciveKKT.Orthant (123/128) g)
    (i j : Fin 10) (hij : (i:ℕ) < (j:ℕ)) :
    -(root j i:ℝ)/32768 ≤ ptsN 10 g j-ptsN 10 g i := by
  have hl : -(root j i:ℝ)/32768 ≤ ((indices i j).card:ℝ)*(123/128) := by
    have hQ := (numeric.2 i j hij).2.2.2
    have hR : ((-(root j i:ℚ)/32768:ℚ):ℝ) ≤
      ((((indices i j).card:ℚ)*(123/128):ℚ):ℝ) := Rat.cast_le.mpr hQ
    push_cast at hR
    exact hR
  rw [span_indices g i j hij.le]
  apply hl.trans
  calc
    ((indices i j).card:ℝ)*(123/128) = ∑ r ∈ indices i j, (123/128:ℝ) := by simp
    _ ≤ ∑ r ∈ indices i j, g r := Finset.sum_le_sum (fun r _ => hg r)

theorem contains (g : Fin 9 → ℝ)
    (hg : WindowPressureRoot.Region (123/128) (221/25000) g) :
    WindowDifferenceCell.Contains root g := by
  intro i j
  change 32768*ptsN 10 g j-32768*ptsN 10 g i ≤ (root i j:ℝ)
  rcases lt_trichotomy (i:ℕ) (j:ℕ) with hij | hij | hij
  · have h := positive_span_upper g hg i j hij
    linarith
  · have heq : i = j := Fin.ext hij
    subst j
    rw [numeric.1 i]
    simp
  · have h := positive_span_lower g hg.1 j i hij
    linarith

set_option pp.fullNames true
#print axioms numeric
#print axioms span_indices
#print axioms positive_span_upper
#print axioms positive_span_lower
#print axioms contains
end StructuralGoal20261016.WindowRootCell
end
'''.replace('MATRIX',vec([vec(row) for row in matrix])).replace('MINIMUM',vec([vec(row) for row in minimum]))
    module='WindowLowerRootCell' if args.lower else 'WindowRootCell'
    if args.lower:body=body.replace('WindowRootCell',module).replace('221/25000','11/1250')
    dest=ROOT/f'StructuralGoal20261016/{module}.lean';dest.write_text(body,encoding='utf8')
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'parameter_sha256':hashlib.sha256(cov.PARAM.read_bytes()).hexdigest(),
      'target':'11/1250' if args.lower else '221/25000',
      'source_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'root':matrix,
      'ordinary_passed':False,'complete_global_cover_proven':False,'submission_ready':False}
    receipt=HERE/('window_generate_lower_root_cell.json' if args.lower else 'window_generate_root_cell.json')
    receipt.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k!='root'}))
if __name__=='__main__':main()
