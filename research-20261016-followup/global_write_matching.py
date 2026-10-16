"""Generate a source-only generic matching-threshold adaptation.

The adaptation copies the already verified matching proof with explicit
threshold / close-pair payment hypotheses. It does not run Lean.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
source=(ROOT/'StructuralResearch20261016/CoboundaryCounting.lean').read_text(encoding='utf8')
source=source.replace('import StructuralResearch20261016.Coboundary\n','import StructuralResearch20261016.CoboundaryCounting\n')
source=source.replace('namespace StructuralResearch20261016.CoboundaryCounting','namespace StructuralW10Followup20261016.MatchingThreshold')
source=source.replace('end StructuralResearch20261016.CoboundaryCounting','end StructuralW10Followup20261016.MatchingThreshold')
source=source.replace('noncomputable section\n','set_option Elab.async false\nset_option maxHeartbeats 0\nnoncomputable section\n',1)
source=source.replace('open Matrix Finset RHLinalg Filter Topology','open Matrix Finset RHLinalg Filter Topology Meshuggah.Gram')
source=source.replace('have hpair : S (some s(i, σ i)) = {i, σ i}',
                      'have hpairSet : S (some s(i, σ i)) = {i, σ i}')
source=source.replace('rw [hpair]','rw [hpairSet]')
marker='section Matching\n'
close='''/-- A chosen matching distance is admissible when every close kernel
entry pays the desired floor. The cap c≤1/2 is exactly the min-1 branch. -/
theorem close_pair_block_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    {x : ι → ℝ} {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c sep δ : ℝ}
    (hc : c ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hpair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    {i j : ι} (hij : i ≠ j) (hnear : |x i - x j| ≤ sep) :
    2 * c - 4 * δ ≤ blockDefect hG {i, j} := by
  classical
  have hkij : c ≤ wfun (x i - x j) := hpair _ hnear
  have hkji : c ≤ wfun (x j - x i) :=
    hpair _ (by simpa only [abs_sub_comm] using hnear)
  have heij := wfun_sub_le_norm_sq (hclose i j hij)
  have heji := wfun_sub_le_norm_sq (hclose j i hij.symm)
  have hoff : offDiagSqOn G {i, j} = ‖G i j‖ ^ 2 + ‖G j i‖ ^ 2 := by
    simp [offDiagSqOn, hij, hij.symm]
  have hmin : 2 * c - 4 * δ ≤ min 1 (offDiagSqOn G {i, j}) := by
    apply le_min
    · linarith
    · rw [hoff]
      linarith
  have hd := block_defect_of_isHermitian
    (hG.submatrix (Subtype.val : ({i, j} : Finset ι) → ι))
  rw [offDiagSqOn_submatrix] at hd
  exact hmin.trans hd

'''
source=source.replace(marker,close+marker,1)
# The first matching theorem and its effective version carry the pair bound.
source=source.replace('{c C : ℝ}\n    (hc : 0 ≤ c) (hC : 0 ≤ C) (hcPair : c ≤ 1 / 64)',
    '{c C sep : ℝ}\n    (hc : 0 ≤ c) (hC : 0 ≤ C) (hcPair : c ≤ 1 / 2)\n    (hpair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t)')
source=source.replace('{c C : ℝ}\n    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hcPair : c ≤ 1 / 64)',
    '{c C sep : ℝ}\n    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hcPair : c ≤ 1 / 2)\n    (hpair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t)')
source=source.replace('SeparatedSummedCertificate W c C (17 / 20)','SeparatedSummedCertificate W c C sep')
source=source.replace('(∀ i j : S, i ≠ j → 17 / 20 ≤ |x i - x j|)',
                      '(∀ i j : S, i ≠ j → sep ≤ |x i - x j|)')
source=source.replace('exists_maximal_matching x (17 / 20)','exists_maximal_matching x sep')
source=source.replace('have hsep : ∀ i j : S none, i ≠ j → 17 / 20 ≤ |x i - x j|',
                      'have hsep : ∀ i j : S none, i ≠ j → sep ≤ |x i - x j|')
source=source.replace('Opeth.AMMatching.close_pair_block_bound hG hcPair hδ hclose hij',
                      'close_pair_block_bound hG hcPair hδ hpair hclose hij')
source=source.replace('matching_defect_bound_summed hn hx hG hc hC hcPair W hW hCert',
                      'matching_defect_bound_summed hn hx hG hc hC hcPair hpair W hW hCert')
# The actual retained Gram cap remains the old proven .85 cap, by monotonicity.
source=source.replace('(W : WCert n) (hW : W.Adm) {c C B : ℝ}',
                      '(W : WCert n) (hW : W.Adm) {c C B sep : ℝ}')
source=source.replace('(hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hc64 : c ≤ 1 / 64)',
                      '(hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hcHalf : c ≤ 1 / 2)\n    (hsep0 : (17 / 20 : ℝ) ≤ sep)\n    (hpair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t)')
source=source.replace('(gram_isHermitian Z (mtParams T) T) hc hC hCc hc64 W hW hCert',
                      '(gram_isHermitian Z (mtParams T) T) hc hC hCc hcHalf hpair W hW hCert')
source=source.replace('hδ.le (fun i j _ => hclose i j) hcap\n',
                      'hδ.le (fun i j _ => hclose i j)\n    (fun S hS => hcap S (fun i j hij => hsep0.trans (hS i j hij)))\n')
# Counting wrappers, retaining the original actual-defect consumer.
source=source.replace('{c C B hw : ℝ}', '{c C B hw sep : ℝ}')
source=source.replace('(hc64 : c ≤ 1 / 64) (hB : W.B = B)',
                      '(hcHalf : c ≤ 1 / 2) (hsep0 : (17 / 20 : ℝ) ≤ sep)\n    (hpair : ∀ t : ℝ, |t| ≤ sep → c ≤ wfun t) (hB : W.B = B)')
source=source.replace('hc.le hC hCc hc64 hB hCert', 'hc.le hC hCc hcHalf hsep0 hpair hB hCert')
source=source.replace('hc hC hCc hc64 hB hfloor hCert', 'hc hC hCc hcHalf hsep0 hpair hB hfloor hCert')
source=source.replace('All numerical local certificate premises remain explicit.',
    'The matching distance is now a parameter, with an explicit kernel pair-payment\nhypothesis. SOURCE ONLY: verification has not yet been run for this adaptation.')
source=source.replace('end StructuralW10Followup20261016.MatchingThreshold',
    '#print axioms close_pair_block_bound\n#print axioms matching_defect_bound_summed\n#print axioms actual_defect_estimate_effective\n#print axioms simple_dyadic\nend StructuralW10Followup20261016.MatchingThreshold')
assert 'hc64' not in source
out=ROOT/'StructuralW10Followup20261016/MatchingThreshold.lean';out.write_text(source,encoding='utf8')
print(out)
