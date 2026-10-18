import StructuralS1RM20261018.PhaseB2.LocalComponents
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.PCell AMW.Cert.Pyr AMW.Cert.PyrD
open StructuralS1RM20261018
open StructuralS1RM20261018.LocalGeometry
open StructuralS1RM20261018.LocalComponents
namespace StructuralS1RM20261018.LocalPair
def pairEnergy (P : ℕ → ℝ) : ℝ :=
  AMW.Cert.PC9QB6M.G (P 1-P 0) (P 2-P 1) (P 3-P 2) (P 4-P 3)
    (P 5-P 4) (P 6-P 5) (P 7-P 6) (P 8-P 7) +
  AMW.Cert.PC9QB6M.G (P 2-P 1) (P 3-P 2) (P 4-P 3) (P 5-P 4)
    (P 6-P 5) (P 7-P 6) (P 8-P 7) (P 9-P 8)

theorem objective_eq (P : ℕ → ℝ) :
    (∑ j : Fin 78, (LocalData.objective j : ℝ) * actualZ P j) =
      2 * (QuantizedComponent.kappa : ℝ) *
        (Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P false) +
         Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P true)) := by
  have hs0 : gsum (canonicalGap P false) 0 1 = P 1-P 0 :=
    canonical_span P false 0 1 (by decide) (by decide)
  have hs1 : gsum (canonicalGap P false) 0 3 = P 3-P 0 :=
    canonical_span P false 0 3 (by decide) (by decide)
  have hs2 : gsum (canonicalGap P false) 0 4 = P 4-P 0 :=
    canonical_span P false 0 4 (by decide) (by decide)
  have hs3 : gsum (canonicalGap P false) 0 5 = P 5-P 0 :=
    canonical_span P false 0 5 (by decide) (by decide)
  have hs4 : gsum (canonicalGap P false) 0 6 = P 6-P 0 :=
    canonical_span P false 0 6 (by decide) (by decide)
  have hs5 : gsum (canonicalGap P false) 0 7 = P 7-P 0 :=
    canonical_span P false 0 7 (by decide) (by decide)
  have hs6 : gsum (canonicalGap P false) 0 8 = P 8-P 0 :=
    canonical_span P false 0 8 (by decide) (by decide)
  have hs7 : gsum (canonicalGap P false) 1 2 = P 2-P 1 :=
    canonical_span P false 1 2 (by decide) (by decide)
  have hs8 : gsum (canonicalGap P false) 1 3 = P 3-P 1 :=
    canonical_span P false 1 3 (by decide) (by decide)
  have hs9 : gsum (canonicalGap P false) 1 4 = P 4-P 1 :=
    canonical_span P false 1 4 (by decide) (by decide)
  have hs10 : gsum (canonicalGap P false) 1 5 = P 5-P 1 :=
    canonical_span P false 1 5 (by decide) (by decide)
  have hs11 : gsum (canonicalGap P false) 1 6 = P 6-P 1 :=
    canonical_span P false 1 6 (by decide) (by decide)
  have hs12 : gsum (canonicalGap P false) 1 7 = P 7-P 1 :=
    canonical_span P false 1 7 (by decide) (by decide)
  have hs13 : gsum (canonicalGap P false) 1 8 = P 8-P 1 :=
    canonical_span P false 1 8 (by decide) (by decide)
  have hs14 : gsum (canonicalGap P false) 2 3 = P 3-P 2 :=
    canonical_span P false 2 3 (by decide) (by decide)
  have hs15 : gsum (canonicalGap P false) 2 4 = P 4-P 2 :=
    canonical_span P false 2 4 (by decide) (by decide)
  have hs16 : gsum (canonicalGap P false) 2 5 = P 5-P 2 :=
    canonical_span P false 2 5 (by decide) (by decide)
  have hs17 : gsum (canonicalGap P false) 2 6 = P 6-P 2 :=
    canonical_span P false 2 6 (by decide) (by decide)
  have hs18 : gsum (canonicalGap P false) 2 7 = P 7-P 2 :=
    canonical_span P false 2 7 (by decide) (by decide)
  have hs19 : gsum (canonicalGap P false) 2 8 = P 8-P 2 :=
    canonical_span P false 2 8 (by decide) (by decide)
  have hs20 : gsum (canonicalGap P false) 3 4 = P 4-P 3 :=
    canonical_span P false 3 4 (by decide) (by decide)
  have hs21 : gsum (canonicalGap P false) 3 5 = P 5-P 3 :=
    canonical_span P false 3 5 (by decide) (by decide)
  have hs22 : gsum (canonicalGap P false) 3 6 = P 6-P 3 :=
    canonical_span P false 3 6 (by decide) (by decide)
  have hs23 : gsum (canonicalGap P false) 3 7 = P 7-P 3 :=
    canonical_span P false 3 7 (by decide) (by decide)
  have hs24 : gsum (canonicalGap P false) 3 8 = P 8-P 3 :=
    canonical_span P false 3 8 (by decide) (by decide)
  have hs25 : gsum (canonicalGap P false) 4 5 = P 5-P 4 :=
    canonical_span P false 4 5 (by decide) (by decide)
  have hs26 : gsum (canonicalGap P false) 4 6 = P 6-P 4 :=
    canonical_span P false 4 6 (by decide) (by decide)
  have hs27 : gsum (canonicalGap P false) 4 7 = P 7-P 4 :=
    canonical_span P false 4 7 (by decide) (by decide)
  have hs28 : gsum (canonicalGap P false) 4 8 = P 8-P 4 :=
    canonical_span P false 4 8 (by decide) (by decide)
  have hs29 : gsum (canonicalGap P false) 5 6 = P 6-P 5 :=
    canonical_span P false 5 6 (by decide) (by decide)
  have hs30 : gsum (canonicalGap P false) 5 7 = P 7-P 5 :=
    canonical_span P false 5 7 (by decide) (by decide)
  have hs31 : gsum (canonicalGap P false) 5 8 = P 8-P 5 :=
    canonical_span P false 5 8 (by decide) (by decide)
  have hs32 : gsum (canonicalGap P false) 6 7 = P 7-P 6 :=
    canonical_span P false 6 7 (by decide) (by decide)
  have hs33 : gsum (canonicalGap P false) 7 8 = P 8-P 7 :=
    canonical_span P false 7 8 (by decide) (by decide)
  have hs34 : gsum (canonicalGap P true) 0 1 = P 9-P 8 :=
    canonical_span P true 0 1 (by decide) (by decide)
  have hs35 : gsum (canonicalGap P true) 0 3 = P 9-P 6 :=
    canonical_span P true 0 3 (by decide) (by decide)
  have hs36 : gsum (canonicalGap P true) 0 4 = P 9-P 5 :=
    canonical_span P true 0 4 (by decide) (by decide)
  have hs37 : gsum (canonicalGap P true) 0 5 = P 9-P 4 :=
    canonical_span P true 0 5 (by decide) (by decide)
  have hs38 : gsum (canonicalGap P true) 0 6 = P 9-P 3 :=
    canonical_span P true 0 6 (by decide) (by decide)
  have hs39 : gsum (canonicalGap P true) 0 7 = P 9-P 2 :=
    canonical_span P true 0 7 (by decide) (by decide)
  have hs40 : gsum (canonicalGap P true) 0 8 = P 9-P 1 :=
    canonical_span P true 0 8 (by decide) (by decide)
  have hs41 : gsum (canonicalGap P true) 1 2 = P 8-P 7 :=
    canonical_span P true 1 2 (by decide) (by decide)
  have hs42 : gsum (canonicalGap P true) 1 3 = P 8-P 6 :=
    canonical_span P true 1 3 (by decide) (by decide)
  have hs43 : gsum (canonicalGap P true) 1 4 = P 8-P 5 :=
    canonical_span P true 1 4 (by decide) (by decide)
  have hs44 : gsum (canonicalGap P true) 1 5 = P 8-P 4 :=
    canonical_span P true 1 5 (by decide) (by decide)
  have hs45 : gsum (canonicalGap P true) 1 6 = P 8-P 3 :=
    canonical_span P true 1 6 (by decide) (by decide)
  have hs46 : gsum (canonicalGap P true) 1 7 = P 8-P 2 :=
    canonical_span P true 1 7 (by decide) (by decide)
  have hs47 : gsum (canonicalGap P true) 1 8 = P 8-P 1 :=
    canonical_span P true 1 8 (by decide) (by decide)
  have hs48 : gsum (canonicalGap P true) 2 3 = P 7-P 6 :=
    canonical_span P true 2 3 (by decide) (by decide)
  have hs49 : gsum (canonicalGap P true) 2 4 = P 7-P 5 :=
    canonical_span P true 2 4 (by decide) (by decide)
  have hs50 : gsum (canonicalGap P true) 2 5 = P 7-P 4 :=
    canonical_span P true 2 5 (by decide) (by decide)
  have hs51 : gsum (canonicalGap P true) 2 6 = P 7-P 3 :=
    canonical_span P true 2 6 (by decide) (by decide)
  have hs52 : gsum (canonicalGap P true) 2 7 = P 7-P 2 :=
    canonical_span P true 2 7 (by decide) (by decide)
  have hs53 : gsum (canonicalGap P true) 2 8 = P 7-P 1 :=
    canonical_span P true 2 8 (by decide) (by decide)
  have hs54 : gsum (canonicalGap P true) 3 4 = P 6-P 5 :=
    canonical_span P true 3 4 (by decide) (by decide)
  have hs55 : gsum (canonicalGap P true) 3 5 = P 6-P 4 :=
    canonical_span P true 3 5 (by decide) (by decide)
  have hs56 : gsum (canonicalGap P true) 3 6 = P 6-P 3 :=
    canonical_span P true 3 6 (by decide) (by decide)
  have hs57 : gsum (canonicalGap P true) 3 7 = P 6-P 2 :=
    canonical_span P true 3 7 (by decide) (by decide)
  have hs58 : gsum (canonicalGap P true) 3 8 = P 6-P 1 :=
    canonical_span P true 3 8 (by decide) (by decide)
  have hs59 : gsum (canonicalGap P true) 4 5 = P 5-P 4 :=
    canonical_span P true 4 5 (by decide) (by decide)
  have hs60 : gsum (canonicalGap P true) 4 6 = P 5-P 3 :=
    canonical_span P true 4 6 (by decide) (by decide)
  have hs61 : gsum (canonicalGap P true) 4 7 = P 5-P 2 :=
    canonical_span P true 4 7 (by decide) (by decide)
  have hs62 : gsum (canonicalGap P true) 4 8 = P 5-P 1 :=
    canonical_span P true 4 8 (by decide) (by decide)
  have hs63 : gsum (canonicalGap P true) 5 6 = P 4-P 3 :=
    canonical_span P true 5 6 (by decide) (by decide)
  have hs64 : gsum (canonicalGap P true) 5 7 = P 4-P 2 :=
    canonical_span P true 5 7 (by decide) (by decide)
  have hs65 : gsum (canonicalGap P true) 5 8 = P 4-P 1 :=
    canonical_span P true 5 8 (by decide) (by decide)
  have hs66 : gsum (canonicalGap P true) 6 7 = P 3-P 2 :=
    canonical_span P true 6 7 (by decide) (by decide)
  have hs67 : gsum (canonicalGap P true) 7 8 = P 2-P 1 :=
    canonical_span P true 7 8 (by decide) (by decide)
  norm_num [Fin.sum_univ_succ, LocalData.objective, actualZ, Fg, AMW.Cert.PC9QB6M.BS,
    AMW.Cert.PC9QB6M.TS, tI, tJ, tA, Finset.sum_range_succ, canonicalGap] 
  simp only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31, hs32, hs33, hs34, hs35, hs36, hs37, hs38, hs39, hs40, hs41, hs42, hs43, hs44, hs45, hs46, hs47, hs48, hs49, hs50, hs51, hs52, hs53, hs54, hs55, hs56, hs57, hs58, hs59, hs60, hs61, hs62, hs63, hs64, hs65, hs66, hs67]
  ring

theorem fg_eq (P : ℕ → ℝ) :
    Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P false) +
      Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P true) =
        (AMW.Cert.PC9QB6M.SA : ℝ) * pairEnergy P := by
  have hl := AMW.Cert.PC9QB6M.Fg_G (P 1-P 0) (P 2-P 1) (P 3-P 2) (P 4-P 3)
    (P 5-P 4) (P 6-P 5) (P 7-P 6) (P 8-P 7)
  have hr := AMW.Cert.PC9QB6M.Fg_G (P 9-P 8) (P 8-P 7) (P 7-P 6) (P 6-P 5)
    (P 5-P 4) (P 4-P 3) (P 3-P 2) (P 2-P 1)
  change Fg 8 _ _ (canonicalGap P false) = _ at hl
  change Fg 8 _ _ (canonicalGap P true) = _ at hr
  rw [hl, hr, AMW.Cert.PC9QB6M_G_rev]
  unfold pairEnergy
  ring

-- This theorem covers only the two literal original cells in the id/rev chart.
-- Reaching them from a global product cover remains a separate obligation.
theorem actual_pair_lower (P : ℕ → ℝ) (h : Domain P) :
    (2 * 893766123055294719 : ℝ) / AMW.Cert.PC9QB6M.SA ≤ pairEnergy P := by
  have hv := Sparse78.sound LocalData.rows LocalData.weights LocalData.den
    LocalData.objective LocalData.target LocalData.checked (actualZ P) (rowsSound P h)
  rw [objective_eq, fg_eq] at hv
  norm_num [LocalData.target, QuantizedComponent.kappa, AMW.Cert.PC9QB6M.SA] at hv ⊢
  nlinarith

set_option pp.fullNames true
#print axioms objective_eq
#print axioms fg_eq
#print axioms actual_pair_lower
end StructuralS1RM20261018.LocalPair
end
