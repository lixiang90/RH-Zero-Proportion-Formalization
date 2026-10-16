/- Eight-leaf pilot only; complete W10 coverage is not asserted. -/
import StructuralGoal20261016.W10LeafPilotData
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
namespace StructuralGoal20261016.W10LeafPilot
theorem root_eq : cell000 = RootBounds.initialCell := by rfl
theorem normalized00 : AdaptiveCoverage.normalize SL cell000 = normal000 := by
  calc
    AdaptiveCoverage.normalize SL cell000 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell000)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell000)).symm
    _ = normal000 := by rfl
theorem left00 : leftChild 9 PR SL normal000 0 9 458752 = cell001 := by
  calc
    leftChild 9 PR SL normal000 0 9 458752 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).symm
    _ = cell001 := by rfl
theorem right00 : rightChild 9 PR SL normal000 0 9 458752 = cell002 := by
  calc
    rightChild 9 PR SL normal000 0 9 458752 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal000) 0 9 458752).symm
    _ = cell002 := by rfl
theorem normalized01 : AdaptiveCoverage.normalize SL cell001 = normal001 := by
  calc
    AdaptiveCoverage.normalize SL cell001 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell001)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell001)).symm
    _ = normal001 := by rfl
theorem left01 : leftChild 9 PR SL normal001 0 9 360448 = cell003 := by
  calc
    leftChild 9 PR SL normal001 0 9 360448 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).symm
    _ = cell003 := by rfl
theorem right01 : rightChild 9 PR SL normal001 0 9 360448 = cell004 := by
  calc
    rightChild 9 PR SL normal001 0 9 360448 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal001) 0 9 360448).symm
    _ = cell004 := by rfl
theorem normalized02 : AdaptiveCoverage.normalize SL cell003 = normal002 := by
  calc
    AdaptiveCoverage.normalize SL cell003 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell003)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell003)).symm
    _ = normal002 := by rfl
theorem left02 : leftChild 9 PR SL normal002 0 9 311296 = cell005 := by
  calc
    leftChild 9 PR SL normal002 0 9 311296 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).symm
    _ = cell005 := by rfl
theorem right02 : rightChild 9 PR SL normal002 0 9 311296 = cell006 := by
  calc
    rightChild 9 PR SL normal002 0 9 311296 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal002) 0 9 311296).symm
    _ = cell006 := by rfl
theorem normalized03 : AdaptiveCoverage.normalize SL cell006 = normal003 := by
  calc
    AdaptiveCoverage.normalize SL cell006 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell006)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell006)).symm
    _ = normal003 := by rfl
theorem left03 : leftChild 9 PR SL normal003 0 9 327680 = cell007 := by
  calc
    leftChild 9 PR SL normal003 0 9 327680 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).symm
    _ = cell007 := by rfl
theorem right03 : rightChild 9 PR SL normal003 0 9 327680 = cell008 := by
  calc
    rightChild 9 PR SL normal003 0 9 327680 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal003) 0 9 327680).symm
    _ = cell008 := by rfl
theorem normalized04 : AdaptiveCoverage.normalize SL cell007 = normal004 := by
  calc
    AdaptiveCoverage.normalize SL cell007 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell007)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell007)).symm
    _ = normal004 := by rfl
theorem left04 : leftChild 9 PR SL normal004 0 8 262144 = cell009 := by
  calc
    leftChild 9 PR SL normal004 0 8 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal004) 0 8 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal004) 0 8 262144).symm
    _ = cell009 := by rfl
theorem right04 : rightChild 9 PR SL normal004 0 8 262144 = cell010 := by
  calc
    rightChild 9 PR SL normal004 0 8 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal004) 0 8 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal004) 0 8 262144).symm
    _ = cell010 := by rfl
theorem normalized05 : AdaptiveCoverage.normalize SL cell010 = normal005 := by
  calc
    AdaptiveCoverage.normalize SL cell010 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell010)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell010)).symm
    _ = normal005 := by rfl
theorem left05 : leftChild 9 PR SL normal005 1 9 262144 = cell011 := by
  calc
    leftChild 9 PR SL normal005 1 9 262144 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal005) 1 9 262144).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal005) 1 9 262144).symm
    _ = cell011 := by rfl
theorem right05 : rightChild 9 PR SL normal005 1 9 262144 = cell012 := by
  calc
    rightChild 9 PR SL normal005 1 9 262144 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal005) 1 9 262144).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal005) 1 9 262144).symm
    _ = cell012 := by rfl
theorem normalized06 : AdaptiveCoverage.normalize SL cell012 = normal006 := by
  calc
    AdaptiveCoverage.normalize SL cell012 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell012)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell012)).symm
    _ = normal006 := by rfl
theorem left06 : leftChild 9 PR SL normal006 2 6 147456 = cell013 := by
  calc
    leftChild 9 PR SL normal006 2 6 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal006) 2 6 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal006) 2 6 147456).symm
    _ = cell013 := by rfl
theorem right06 : rightChild 9 PR SL normal006 2 6 147456 = cell014 := by
  calc
    rightChild 9 PR SL normal006 2 6 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal006) 2 6 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal006) 2 6 147456).symm
    _ = cell014 := by rfl
theorem normalized07 : AdaptiveCoverage.normalize SL cell013 = normal007 := by
  calc
    AdaptiveCoverage.normalize SL cell013 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell013)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell013)).symm
    _ = normal007 := by rfl
theorem left07 : leftChild 9 PR SL normal007 3 7 147456 = cell015 := by
  calc
    leftChild 9 PR SL normal007 3 7 147456 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal007) 3 7 147456).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal007) 3 7 147456).symm
    _ = cell015 := by rfl
theorem right07 : rightChild 9 PR SL normal007 3 7 147456 = cell016 := by
  calc
    rightChild 9 PR SL normal007 3 7 147456 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal007) 3 7 147456).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal007) 3 7 147456).symm
    _ = cell016 := by rfl
theorem normalized08 : AdaptiveCoverage.normalize SL cell015 = normal008 := by
  calc
    AdaptiveCoverage.normalize SL cell015 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell015)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell015)).symm
    _ = normal008 := by rfl
theorem left08 : leftChild 9 PR SL normal008 1 8 229376 = cell017 := by
  calc
    leftChild 9 PR SL normal008 1 8 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal008) 1 8 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal008) 1 8 229376).symm
    _ = cell017 := by rfl
theorem right08 : rightChild 9 PR SL normal008 1 8 229376 = cell018 := by
  calc
    rightChild 9 PR SL normal008 1 8 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal008) 1 8 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal008) 1 8 229376).symm
    _ = cell018 := by rfl
theorem normalized09 : AdaptiveCoverage.normalize SL cell018 = normal009 := by
  calc
    AdaptiveCoverage.normalize SL cell018 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell018)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell018)).symm
    _ = normal009 := by rfl
theorem left09 : leftChild 9 PR SL normal009 0 6 212992 = cell019 := by
  calc
    leftChild 9 PR SL normal009 0 6 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal009) 0 6 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal009) 0 6 212992).symm
    _ = cell019 := by rfl
theorem right09 : rightChild 9 PR SL normal009 0 6 212992 = cell020 := by
  calc
    rightChild 9 PR SL normal009 0 6 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal009) 0 6 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal009) 0 6 212992).symm
    _ = cell020 := by rfl
theorem normalized10 : AdaptiveCoverage.normalize SL cell019 = normal010 := by
  calc
    AdaptiveCoverage.normalize SL cell019 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell019)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell019)).symm
    _ = normal010 := by rfl
theorem left10 : leftChild 9 PR SL normal010 0 7 229376 = cell021 := by
  calc
    leftChild 9 PR SL normal010 0 7 229376 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal010) 0 7 229376).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal010) 0 7 229376).symm
    _ = cell021 := by rfl
theorem right10 : rightChild 9 PR SL normal010 0 7 229376 = cell022 := by
  calc
    rightChild 9 PR SL normal010 0 7 229376 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal010) 0 7 229376).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal010) 0 7 229376).symm
    _ = cell022 := by rfl
theorem normalized11 : AdaptiveCoverage.normalize SL cell022 = normal011 := by
  calc
    AdaptiveCoverage.normalize SL cell022 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell022)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell022)).symm
    _ = normal011 := by rfl
theorem left11 : leftChild 9 PR SL normal011 3 9 212992 = cell023 := by
  calc
    leftChild 9 PR SL normal011 3 9 212992 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal011) 3 9 212992).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal011) 3 9 212992).symm
    _ = cell023 := by rfl
theorem right11 : rightChild 9 PR SL normal011 3 9 212992 = cell024 := by
  calc
    rightChild 9 PR SL normal011 3 9 212992 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal011) 3 9 212992).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal011) 3 9 212992).symm
    _ = cell024 := by rfl
theorem normalized12 : AdaptiveCoverage.normalize SL cell024 = normal012 := by
  calc
    AdaptiveCoverage.normalize SL cell024 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell024)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell024)).symm
    _ = normal012 := by rfl
theorem left12 : leftChild 9 PR SL normal012 3 8 180224 = cell025 := by
  calc
    leftChild 9 PR SL normal012 3 8 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal012) 3 8 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal012) 3 8 180224).symm
    _ = cell025 := by rfl
theorem right12 : rightChild 9 PR SL normal012 3 8 180224 = cell026 := by
  calc
    rightChild 9 PR SL normal012 3 8 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal012) 3 8 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal012) 3 8 180224).symm
    _ = cell026 := by rfl
theorem normalized13 : AdaptiveCoverage.normalize SL cell026 = normal013 := by
  calc
    AdaptiveCoverage.normalize SL cell026 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell026)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell026)).symm
    _ = normal013 := by rfl
theorem left13 : leftChild 9 PR SL normal013 0 8 278528 = cell027 := by
  calc
    leftChild 9 PR SL normal013 0 8 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal013) 0 8 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal013) 0 8 278528).symm
    _ = cell027 := by rfl
theorem right13 : rightChild 9 PR SL normal013 0 8 278528 = cell028 := by
  calc
    rightChild 9 PR SL normal013 0 8 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal013) 0 8 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal013) 0 8 278528).symm
    _ = cell028 := by rfl
theorem normalized14 : AdaptiveCoverage.normalize SL cell028 = normal014 := by
  calc
    AdaptiveCoverage.normalize SL cell028 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell028)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell028)).symm
    _ = normal014 := by rfl
theorem left14 : leftChild 9 PR SL normal014 0 6 196608 = cell029 := by
  calc
    leftChild 9 PR SL normal014 0 6 196608 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal014) 0 6 196608).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal014) 0 6 196608).symm
    _ = cell029 := by rfl
theorem right14 : rightChild 9 PR SL normal014 0 6 196608 = cell030 := by
  calc
    rightChild 9 PR SL normal014 0 6 196608 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal014) 0 6 196608).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal014) 0 6 196608).symm
    _ = cell030 := by rfl
theorem normalized15 : AdaptiveCoverage.normalize SL cell030 = normal015 := by
  calc
    AdaptiveCoverage.normalize SL cell030 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell030)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell030)).symm
    _ = normal015 := by rfl
theorem left15 : leftChild 9 PR SL normal015 0 9 319488 = cell031 := by
  calc
    leftChild 9 PR SL normal015 0 9 319488 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal015) 0 9 319488).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal015) 0 9 319488).symm
    _ = cell031 := by rfl
theorem right15 : rightChild 9 PR SL normal015 0 9 319488 = cell032 := by
  calc
    rightChild 9 PR SL normal015 0 9 319488 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal015) 0 9 319488).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal015) 0 9 319488).symm
    _ = cell032 := by rfl
theorem normalized16 : AdaptiveCoverage.normalize SL cell032 = normal016 := by
  calc
    AdaptiveCoverage.normalize SL cell032 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell032)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell032)).symm
    _ = normal016 := by rfl
theorem left16 : leftChild 9 PR SL normal016 2 7 180224 = cell033 := by
  calc
    leftChild 9 PR SL normal016 2 7 180224 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal016) 2 7 180224).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal016) 2 7 180224).symm
    _ = cell033 := by rfl
theorem right16 : rightChild 9 PR SL normal016 2 7 180224 = cell034 := by
  calc
    rightChild 9 PR SL normal016 2 7 180224 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal016) 2 7 180224).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal016) 2 7 180224).symm
    _ = cell034 := by rfl
theorem normalized17 : AdaptiveCoverage.normalize SL cell033 = normal017 := by
  calc
    AdaptiveCoverage.normalize SL cell033 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell033)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell033)).symm
    _ = normal017 := by rfl
theorem left17 : leftChild 9 PR SL normal017 1 9 278528 = cell035 := by
  calc
    leftChild 9 PR SL normal017 1 9 278528 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal017) 1 9 278528).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal017) 1 9 278528).symm
    _ = cell035 := by rfl
theorem right17 : rightChild 9 PR SL normal017 1 9 278528 = cell036 := by
  calc
    rightChild 9 PR SL normal017 1 9 278528 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal017) 1 9 278528).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal017) 1 9 278528).symm
    _ = cell036 := by rfl
theorem normalized18 : AdaptiveCoverage.normalize SL cell036 = normal019 := by
  calc
    AdaptiveCoverage.normalize SL cell036 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell036)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell036)).symm
    _ = normal019 := by rfl
theorem left18 : leftChild 9 PR SL normal019 2 6 131072 = cell037 := by
  calc
    leftChild 9 PR SL normal019 2 6 131072 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal019) 2 6 131072).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal019) 2 6 131072).symm
    _ = cell037 := by rfl
theorem right18 : rightChild 9 PR SL normal019 2 6 131072 = cell038 := by
  calc
    rightChild 9 PR SL normal019 2 6 131072 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal019) 2 6 131072).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal019) 2 6 131072).symm
    _ = cell038 := by rfl
theorem normalized19 : AdaptiveCoverage.normalize SL cell038 = normal021 := by
  calc
    AdaptiveCoverage.normalize SL cell038 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell038)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell038)).symm
    _ = normal021 := by rfl
theorem left19 : leftChild 9 PR SL normal021 3 5 65536 = cell039 := by
  calc
    leftChild 9 PR SL normal021 3 5 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal021) 3 5 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal021) 3 5 65536).symm
    _ = cell039 := by rfl
theorem right19 : rightChild 9 PR SL normal021 3 5 65536 = cell040 := by
  calc
    rightChild 9 PR SL normal021 3 5 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal021) 3 5 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal021) 3 5 65536).symm
    _ = cell040 := by rfl
theorem normalized20 : AdaptiveCoverage.normalize SL cell040 = normal023 := by
  calc
    AdaptiveCoverage.normalize SL cell040 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell040)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell040)).symm
    _ = normal023 := by rfl
theorem left20 : leftChild 9 PR SL normal023 4 6 65536 = cell041 := by
  calc
    leftChild 9 PR SL normal023 4 6 65536 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal023) 4 6 65536).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal023) 4 6 65536).symm
    _ = cell041 := by rfl
theorem right20 : rightChild 9 PR SL normal023 4 6 65536 = cell042 := by
  calc
    rightChild 9 PR SL normal023 4 6 65536 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal023) 4 6 65536).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal023) 4 6 65536).symm
    _ = cell042 := by rfl
theorem normalized21 : AdaptiveCoverage.normalize SL cell042 = normal025 := by
  calc
    AdaptiveCoverage.normalize SL cell042 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell042)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell042)).symm
    _ = normal025 := by rfl
theorem left21 : leftChild 9 PR SL normal025 1 8 245760 = cell043 := by
  calc
    leftChild 9 PR SL normal025 1 8 245760 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal025) 1 8 245760).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal025) 1 8 245760).symm
    _ = cell043 := by rfl
theorem right21 : rightChild 9 PR SL normal025 1 8 245760 = cell044 := by
  calc
    rightChild 9 PR SL normal025 1 8 245760 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal025) 1 8 245760).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal025) 1 8 245760).symm
    _ = cell044 := by rfl
theorem normalized22 : AdaptiveCoverage.normalize SL cell044 = normal027 := by
  calc
    AdaptiveCoverage.normalize SL cell044 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell044)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell044)).symm
    _ = normal027 := by rfl
theorem left22 : leftChild 9 PR SL normal027 5 8 114688 = cell045 := by
  calc
    leftChild 9 PR SL normal027 5 8 114688 =
        (FixedGeometry.left SL (FixedGeometry.Cell.ofCl normal027) 5 8 114688).toCl :=
      (FixedGeometry.left_eq SL (FixedGeometry.Cell.ofCl normal027) 5 8 114688).symm
    _ = cell045 := by rfl
theorem right22 : rightChild 9 PR SL normal027 5 8 114688 = cell046 := by
  calc
    rightChild 9 PR SL normal027 5 8 114688 =
        (FixedGeometry.right SL (FixedGeometry.Cell.ofCl normal027) 5 8 114688).toCl :=
      (FixedGeometry.right_eq SL (FixedGeometry.Cell.ofCl normal027) 5 8 114688).symm
    _ = cell046 := by rfl

set_option pp.fullNames true
#print axioms root_eq
#print axioms normalized00
#print axioms left00
#print axioms right00
#print axioms normalized01
#print axioms left01
#print axioms right01
#print axioms normalized02
#print axioms left02
#print axioms right02
#print axioms normalized03
#print axioms left03
#print axioms right03
#print axioms normalized04
#print axioms left04
#print axioms right04
#print axioms normalized05
#print axioms left05
#print axioms right05
#print axioms normalized06
#print axioms left06
#print axioms right06
#print axioms normalized07
#print axioms left07
#print axioms right07
#print axioms normalized08
#print axioms left08
#print axioms right08
#print axioms normalized09
#print axioms left09
#print axioms right09
#print axioms normalized10
#print axioms left10
#print axioms right10
#print axioms normalized11
#print axioms left11
#print axioms right11
#print axioms normalized12
#print axioms left12
#print axioms right12
#print axioms normalized13
#print axioms left13
#print axioms right13
#print axioms normalized14
#print axioms left14
#print axioms right14
#print axioms normalized15
#print axioms left15
#print axioms right15
#print axioms normalized16
#print axioms left16
#print axioms right16
#print axioms normalized17
#print axioms left17
#print axioms right17
#print axioms normalized18
#print axioms left18
#print axioms right18
#print axioms normalized19
#print axioms left19
#print axioms right19
#print axioms normalized20
#print axioms left20
#print axioms right20
#print axioms normalized21
#print axioms left21
#print axioms right21
#print axioms normalized22
#print axioms left22
#print axioms right22
end StructuralGoal20261016.W10LeafPilot
end
