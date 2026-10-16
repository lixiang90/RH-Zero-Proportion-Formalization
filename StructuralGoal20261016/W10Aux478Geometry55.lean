/- Frozen 478-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux478Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
open StructuralGoal20261016.LeanCoverBase
open StructuralW10Unconditional20261016
open StructuralW10Cert20261016
namespace StructuralGoal20261016.W10Aux478
theorem normalized440 : AdaptiveCoverage.normalize SL cell879 = normal873 := by
  calc
    AdaptiveCoverage.normalize SL cell879 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell879)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell879)).symm
    _ = normal873 := by rfl
theorem left440 : leftChild 9 PR SL normal873 1 2 81036 = cell881 := by
  calc
    leftChild 9 PR SL normal873 1 2 81036 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal873) 1 2 81036).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal873) 1 2 81036).symm
    _ = cell881 := by rfl
theorem right440 : rightChild 9 PR SL normal873 1 2 81036 = cell882 := by
  calc
    rightChild 9 PR SL normal873 1 2 81036 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal873) 1 2 81036).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal873) 1 2 81036).symm
    _ = cell882 := by rfl
theorem normalized441 : AdaptiveCoverage.normalize SL cell881 = normal874 := by
  calc
    AdaptiveCoverage.normalize SL cell881 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell881)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell881)).symm
    _ = normal874 := by rfl
theorem left441 : leftChild 9 PR SL normal874 6 7 48247 = cell883 := by
  calc
    leftChild 9 PR SL normal874 6 7 48247 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal874) 6 7 48247).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal874) 6 7 48247).symm
    _ = cell883 := by rfl
theorem right441 : rightChild 9 PR SL normal874 6 7 48247 = cell884 := by
  calc
    rightChild 9 PR SL normal874 6 7 48247 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal874) 6 7 48247).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal874) 6 7 48247).symm
    _ = cell884 := by rfl
theorem normalized442 : AdaptiveCoverage.normalize SL cell883 = normal875 := by
  calc
    AdaptiveCoverage.normalize SL cell883 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell883)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell883)).symm
    _ = normal875 := by rfl
theorem left442 : leftChild 9 PR SL normal875 2 3 48230 = cell885 := by
  calc
    leftChild 9 PR SL normal875 2 3 48230 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal875) 2 3 48230).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal875) 2 3 48230).symm
    _ = cell885 := by rfl
theorem right442 : rightChild 9 PR SL normal875 2 3 48230 = cell886 := by
  calc
    rightChild 9 PR SL normal875 2 3 48230 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal875) 2 3 48230).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal875) 2 3 48230).symm
    _ = cell886 := by rfl
theorem normalized443 : AdaptiveCoverage.normalize SL cell885 = normal876 := by
  calc
    AdaptiveCoverage.normalize SL cell885 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell885)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell885)).symm
    _ = normal876 := by rfl
theorem left443 : leftChild 9 PR SL normal876 5 6 47724 = cell887 := by
  calc
    leftChild 9 PR SL normal876 5 6 47724 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal876) 5 6 47724).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal876) 5 6 47724).symm
    _ = cell887 := by rfl
theorem right443 : rightChild 9 PR SL normal876 5 6 47724 = cell888 := by
  calc
    rightChild 9 PR SL normal876 5 6 47724 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal876) 5 6 47724).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal876) 5 6 47724).symm
    _ = cell888 := by rfl
theorem normalized444 : AdaptiveCoverage.normalize SL cell887 = normal877 := by
  calc
    AdaptiveCoverage.normalize SL cell887 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell887)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell887)).symm
    _ = normal877 := by rfl
theorem left444 : leftChild 9 PR SL normal877 3 4 47724 = cell889 := by
  calc
    leftChild 9 PR SL normal877 3 4 47724 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal877) 3 4 47724).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal877) 3 4 47724).symm
    _ = cell889 := by rfl
theorem right444 : rightChild 9 PR SL normal877 3 4 47724 = cell890 := by
  calc
    rightChild 9 PR SL normal877 3 4 47724 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal877) 3 4 47724).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal877) 3 4 47724).symm
    _ = cell890 := by rfl
theorem normalized445 : AdaptiveCoverage.normalize SL cell889 = normal878 := by
  calc
    AdaptiveCoverage.normalize SL cell889 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell889)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell889)).symm
    _ = normal878 := by rfl
theorem left445 : leftChild 9 PR SL normal878 4 5 47532 = cell891 := by
  calc
    leftChild 9 PR SL normal878 4 5 47532 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal878) 4 5 47532).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal878) 4 5 47532).symm
    _ = cell891 := by rfl
theorem right445 : rightChild 9 PR SL normal878 4 5 47532 = cell892 := by
  calc
    rightChild 9 PR SL normal878 4 5 47532 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal878) 4 5 47532).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal878) 4 5 47532).symm
    _ = cell892 := by rfl
theorem normalized446 : AdaptiveCoverage.normalize SL cell891 = normal879 := by
  calc
    AdaptiveCoverage.normalize SL cell891 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell891)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell891)).symm
    _ = normal879 := by rfl
theorem left446 : leftChild 9 PR SL normal879 2 6 140288 = cell893 := by
  calc
    leftChild 9 PR SL normal879 2 6 140288 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal879) 2 6 140288).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal879) 2 6 140288).symm
    _ = cell893 := by rfl
theorem right446 : rightChild 9 PR SL normal879 2 6 140288 = cell894 := by
  calc
    rightChild 9 PR SL normal879 2 6 140288 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal879) 2 6 140288).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal879) 2 6 140288).symm
    _ = cell894 := by rfl
theorem normalized447 : AdaptiveCoverage.normalize SL cell893 = normal880 := by
  calc
    AdaptiveCoverage.normalize SL cell893 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell893)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell893)).symm
    _ = normal880 := by rfl
theorem left447 : leftChild 9 PR SL normal880 0 8 310639 = cell895 := by
  calc
    leftChild 9 PR SL normal880 0 8 310639 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal880) 0 8 310639).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal880) 0 8 310639).symm
    _ = cell895 := by rfl
theorem right447 : rightChild 9 PR SL normal880 0 8 310639 = cell896 := by
  calc
    rightChild 9 PR SL normal880 0 8 310639 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal880) 0 8 310639).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal880) 0 8 310639).symm
    _ = cell896 := by rfl

set_option pp.fullNames true
#print axioms normalized440
#print axioms left440
#print axioms right440
#print axioms normalized441
#print axioms left441
#print axioms right441
#print axioms normalized442
#print axioms left442
#print axioms right442
#print axioms normalized443
#print axioms left443
#print axioms right443
#print axioms normalized444
#print axioms left444
#print axioms right444
#print axioms normalized445
#print axioms left445
#print axioms right445
#print axioms normalized446
#print axioms left446
#print axioms right446
#print axioms normalized447
#print axioms left447
#print axioms right447
end StructuralGoal20261016.W10Aux478
end
