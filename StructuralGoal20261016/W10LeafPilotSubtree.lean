/- Eight-leaf pilot only; complete W10 coverage is not asserted. -/
import StructuralGoal20261016.W10LeafPilotGeometry
import StructuralGoal20261016.W10LeafPilotLeaf00
import StructuralGoal20261016.W10LeafPilotLeaf01
import StructuralGoal20261016.W10LeafPilotLeaf02
import StructuralGoal20261016.W10LeafPilotLeaf03
import StructuralGoal20261016.W10LeafPilotLeaf04
import StructuralGoal20261016.W10LeafPilotLeaf05
import StructuralGoal20261016.W10LeafPilotLeaf06
import StructuralGoal20261016.W10LeafPilotLeaf07
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
theorem coveredNode22 : CovBy 9 PR (Pg cN 9 BS TS) cell044 :=
  branch 5 8 114688 (by decide) (by decide) normalized22 left22 right22 coveredLeaf05 coveredLeaf06
theorem coveredNode21 : CovBy 9 PR (Pg cN 9 BS TS) cell042 :=
  branch 1 8 245760 (by decide) (by decide) normalized21 left21 right21 coveredLeaf04 coveredNode22
theorem coveredNode20 : CovBy 9 PR (Pg cN 9 BS TS) cell040 :=
  branch 4 6 65536 (by decide) (by decide) normalized20 left20 right20 coveredLeaf03 coveredNode21
theorem coveredNode19 : CovBy 9 PR (Pg cN 9 BS TS) cell038 :=
  branch 3 5 65536 (by decide) (by decide) normalized19 left19 right19 coveredLeaf02 coveredNode20
theorem coveredNode18 : CovBy 9 PR (Pg cN 9 BS TS) cell036 :=
  branch 2 6 131072 (by decide) (by decide) normalized18 left18 right18 coveredLeaf01 coveredNode19
theorem coveredNode17 : CovBy 9 PR (Pg cN 9 BS TS) cell033 :=
  branch 1 9 278528 (by decide) (by decide) normalized17 left17 right17 coveredLeaf00 coveredNode18
theorem coveredNode16 : CovBy 9 PR (Pg cN 9 BS TS) cell032 :=
  branch 2 7 180224 (by decide) (by decide) normalized16 left16 right16 coveredNode17 coveredLeaf07
theorem selected_covered : CovBy 9 PR (Pg cN 9 BS TS) cell032 := coveredNode16
theorem root_covered_of_siblings
    (sibling00 : CovBy 9 PR (Pg cN 9 BS TS) cell002)
    (sibling01 : CovBy 9 PR (Pg cN 9 BS TS) cell004)
    (sibling02 : CovBy 9 PR (Pg cN 9 BS TS) cell005)
    (sibling03 : CovBy 9 PR (Pg cN 9 BS TS) cell008)
    (sibling04 : CovBy 9 PR (Pg cN 9 BS TS) cell009)
    (sibling05 : CovBy 9 PR (Pg cN 9 BS TS) cell011)
    (sibling06 : CovBy 9 PR (Pg cN 9 BS TS) cell014)
    (sibling07 : CovBy 9 PR (Pg cN 9 BS TS) cell016)
    (sibling08 : CovBy 9 PR (Pg cN 9 BS TS) cell017)
    (sibling09 : CovBy 9 PR (Pg cN 9 BS TS) cell020)
    (sibling10 : CovBy 9 PR (Pg cN 9 BS TS) cell021)
    (sibling11 : CovBy 9 PR (Pg cN 9 BS TS) cell023)
    (sibling12 : CovBy 9 PR (Pg cN 9 BS TS) cell025)
    (sibling13 : CovBy 9 PR (Pg cN 9 BS TS) cell027)
    (sibling14 : CovBy 9 PR (Pg cN 9 BS TS) cell029)
    (sibling15 : CovBy 9 PR (Pg cN 9 BS TS) cell031)
    : CovBy 9 PR (Pg cN 9 BS TS) RootBounds.initialCell := by
  have route15 : CovBy 9 PR (Pg cN 9 BS TS) cell030 :=
    branch 0 9 319488 (by decide) (by decide) normalized15 left15 right15 sibling15 coveredNode16
  have route14 : CovBy 9 PR (Pg cN 9 BS TS) cell028 :=
    branch 0 6 196608 (by decide) (by decide) normalized14 left14 right14 sibling14 route15
  have route13 : CovBy 9 PR (Pg cN 9 BS TS) cell026 :=
    branch 0 8 278528 (by decide) (by decide) normalized13 left13 right13 sibling13 route14
  have route12 : CovBy 9 PR (Pg cN 9 BS TS) cell024 :=
    branch 3 8 180224 (by decide) (by decide) normalized12 left12 right12 sibling12 route13
  have route11 : CovBy 9 PR (Pg cN 9 BS TS) cell022 :=
    branch 3 9 212992 (by decide) (by decide) normalized11 left11 right11 sibling11 route12
  have route10 : CovBy 9 PR (Pg cN 9 BS TS) cell019 :=
    branch 0 7 229376 (by decide) (by decide) normalized10 left10 right10 sibling10 route11
  have route09 : CovBy 9 PR (Pg cN 9 BS TS) cell018 :=
    branch 0 6 212992 (by decide) (by decide) normalized09 left09 right09 route10 sibling09
  have route08 : CovBy 9 PR (Pg cN 9 BS TS) cell015 :=
    branch 1 8 229376 (by decide) (by decide) normalized08 left08 right08 sibling08 route09
  have route07 : CovBy 9 PR (Pg cN 9 BS TS) cell013 :=
    branch 3 7 147456 (by decide) (by decide) normalized07 left07 right07 route08 sibling07
  have route06 : CovBy 9 PR (Pg cN 9 BS TS) cell012 :=
    branch 2 6 147456 (by decide) (by decide) normalized06 left06 right06 route07 sibling06
  have route05 : CovBy 9 PR (Pg cN 9 BS TS) cell010 :=
    branch 1 9 262144 (by decide) (by decide) normalized05 left05 right05 sibling05 route06
  have route04 : CovBy 9 PR (Pg cN 9 BS TS) cell007 :=
    branch 0 8 262144 (by decide) (by decide) normalized04 left04 right04 sibling04 route05
  have route03 : CovBy 9 PR (Pg cN 9 BS TS) cell006 :=
    branch 0 9 327680 (by decide) (by decide) normalized03 left03 right03 route04 sibling03
  have route02 : CovBy 9 PR (Pg cN 9 BS TS) cell003 :=
    branch 0 9 311296 (by decide) (by decide) normalized02 left02 right02 sibling02 route03
  have route01 : CovBy 9 PR (Pg cN 9 BS TS) cell001 :=
    branch 0 9 360448 (by decide) (by decide) normalized01 left01 right01 route02 sibling01
  have route00 : CovBy 9 PR (Pg cN 9 BS TS) cell000 :=
    branch 0 9 458752 (by decide) (by decide) normalized00 left00 right00 route01 sibling00
  simpa only [root_eq] using route00

set_option pp.fullNames true
#print axioms selected_covered
#print axioms root_covered_of_siblings
end StructuralGoal20261016.W10LeafPilot
end
