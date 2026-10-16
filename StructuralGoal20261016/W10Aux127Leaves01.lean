/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux127Data
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
namespace StructuralGoal20261016.W10Aux127
theorem normalizedLeaf032 : AdaptiveCoverage.normalize SL cell056 = normal070 := by
  calc
    AdaptiveCoverage.normalize SL cell056 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell056)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell056)).symm
    _ = normal070 := by rfl

theorem numeric032 : ForcedCoverage2.dispatch (fun _ => payload032) normal070 46 = true := by
  decide +kernel

theorem coveredLeaf032 : CovBy 9 PR (Pg cN 9 BS TS) cell056 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf032]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload032) normal070 46 numeric032
theorem normalizedLeaf033 : AdaptiveCoverage.normalize SL cell079 = normal073 := by
  calc
    AdaptiveCoverage.normalize SL cell079 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell079)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell079)).symm
    _ = normal073 := by rfl

theorem numeric033 : ForcedCoverage2.dispatch (fun _ => payload033) normal073 46 = true := by
  decide +kernel

theorem coveredLeaf033 : CovBy 9 PR (Pg cN 9 BS TS) cell079 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf033]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload033) normal073 46 numeric033
theorem normalizedLeaf034 : AdaptiveCoverage.normalize SL cell083 = normal076 := by
  calc
    AdaptiveCoverage.normalize SL cell083 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell083)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell083)).symm
    _ = normal076 := by rfl

theorem numeric034 : ForcedCoverage2.dispatch (fun _ => payload034) normal076 46 = true := by
  decide +kernel

theorem coveredLeaf034 : CovBy 9 PR (Pg cN 9 BS TS) cell083 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf034]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload034) normal076 46 numeric034
theorem normalizedLeaf035 : AdaptiveCoverage.normalize SL cell085 = normal078 := by
  calc
    AdaptiveCoverage.normalize SL cell085 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell085)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell085)).symm
    _ = normal078 := by rfl

theorem numeric035 : ForcedCoverage2.dispatch (fun _ => payload035) normal078 46 = true := by
  decide +kernel

theorem coveredLeaf035 : CovBy 9 PR (Pg cN 9 BS TS) cell085 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf035]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload035) normal078 46 numeric035
theorem normalizedLeaf036 : AdaptiveCoverage.normalize SL cell089 = normal081 := by
  calc
    AdaptiveCoverage.normalize SL cell089 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell089)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell089)).symm
    _ = normal081 := by rfl

theorem numeric036 : ForcedCoverage2.dispatch (fun _ => payload036) normal081 46 = true := by
  decide +kernel

theorem coveredLeaf036 : CovBy 9 PR (Pg cN 9 BS TS) cell089 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf036]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload036) normal081 46 numeric036
theorem normalizedLeaf037 : AdaptiveCoverage.normalize SL cell091 = normal083 := by
  calc
    AdaptiveCoverage.normalize SL cell091 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell091)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell091)).symm
    _ = normal083 := by rfl

theorem numeric037 : ForcedCoverage2.dispatch (fun _ => payload037) normal083 46 = true := by
  decide +kernel

theorem coveredLeaf037 : CovBy 9 PR (Pg cN 9 BS TS) cell091 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf037]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload037) normal083 46 numeric037
theorem normalizedLeaf038 : AdaptiveCoverage.normalize SL cell093 = normal085 := by
  calc
    AdaptiveCoverage.normalize SL cell093 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell093)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell093)).symm
    _ = normal085 := by rfl

theorem numeric038 : ForcedCoverage2.dispatch (fun _ => payload038) normal085 46 = true := by
  decide +kernel

theorem coveredLeaf038 : CovBy 9 PR (Pg cN 9 BS TS) cell093 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf038]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload038) normal085 46 numeric038
theorem normalizedLeaf039 : AdaptiveCoverage.normalize SL cell095 = normal087 := by
  calc
    AdaptiveCoverage.normalize SL cell095 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell095)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell095)).symm
    _ = normal087 := by rfl

theorem numeric039 : ForcedCoverage2.dispatch (fun _ => payload039) normal087 46 = true := by
  decide +kernel

theorem coveredLeaf039 : CovBy 9 PR (Pg cN 9 BS TS) cell095 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf039]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload039) normal087 46 numeric039
theorem normalizedLeaf040 : AdaptiveCoverage.normalize SL cell097 = normal089 := by
  calc
    AdaptiveCoverage.normalize SL cell097 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell097)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell097)).symm
    _ = normal089 := by rfl

theorem numeric040 : ForcedCoverage2.dispatch (fun _ => payload040) normal089 46 = true := by
  decide +kernel

theorem coveredLeaf040 : CovBy 9 PR (Pg cN 9 BS TS) cell097 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf040]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload040) normal089 46 numeric040
theorem normalizedLeaf041 : AdaptiveCoverage.normalize SL cell099 = normal091 := by
  calc
    AdaptiveCoverage.normalize SL cell099 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell099)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell099)).symm
    _ = normal091 := by rfl

theorem numeric041 : ForcedCoverage2.dispatch (fun _ => payload041) normal091 46 = true := by
  decide +kernel

theorem coveredLeaf041 : CovBy 9 PR (Pg cN 9 BS TS) cell099 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf041]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload041) normal091 46 numeric041
theorem normalizedLeaf042 : AdaptiveCoverage.normalize SL cell103 = normal094 := by
  calc
    AdaptiveCoverage.normalize SL cell103 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell103)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell103)).symm
    _ = normal094 := by rfl

theorem numeric042 : ForcedCoverage2.dispatch (fun _ => payload042) normal094 46 = true := by
  decide +kernel

theorem coveredLeaf042 : CovBy 9 PR (Pg cN 9 BS TS) cell103 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf042]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload042) normal094 46 numeric042
theorem normalizedLeaf043 : AdaptiveCoverage.normalize SL cell104 = normal095 := by
  calc
    AdaptiveCoverage.normalize SL cell104 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell104)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell104)).symm
    _ = normal095 := by rfl

theorem numeric043 : ForcedCoverage2.dispatch (fun _ => payload043) normal095 46 = true := by
  decide +kernel

theorem coveredLeaf043 : CovBy 9 PR (Pg cN 9 BS TS) cell104 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf043]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload043) normal095 46 numeric043
theorem normalizedLeaf044 : AdaptiveCoverage.normalize SL cell102 = normal096 := by
  calc
    AdaptiveCoverage.normalize SL cell102 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell102)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell102)).symm
    _ = normal096 := by rfl

theorem numeric044 : ForcedCoverage2.dispatch (fun _ => payload044) normal096 46 = true := by
  decide +kernel

theorem coveredLeaf044 : CovBy 9 PR (Pg cN 9 BS TS) cell102 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf044]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload044) normal096 46 numeric044
theorem normalizedLeaf045 : AdaptiveCoverage.normalize SL cell088 = normal097 := by
  calc
    AdaptiveCoverage.normalize SL cell088 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell088)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell088)).symm
    _ = normal097 := by rfl

theorem numeric045 : ForcedCoverage2.dispatch (fun _ => payload045) normal097 46 = true := by
  decide +kernel

theorem coveredLeaf045 : CovBy 9 PR (Pg cN 9 BS TS) cell088 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf045]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload045) normal097 46 numeric045
theorem normalizedLeaf046 : AdaptiveCoverage.normalize SL cell082 = normal098 := by
  calc
    AdaptiveCoverage.normalize SL cell082 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell082)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell082)).symm
    _ = normal098 := by rfl

theorem numeric046 : ForcedCoverage2.dispatch (fun _ => payload046) normal098 46 = true := by
  decide +kernel

theorem coveredLeaf046 : CovBy 9 PR (Pg cN 9 BS TS) cell082 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf046]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload046) normal098 46 numeric046
theorem normalizedLeaf047 : AdaptiveCoverage.normalize SL cell078 = normal099 := by
  calc
    AdaptiveCoverage.normalize SL cell078 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell078)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell078)).symm
    _ = normal099 := by rfl

theorem numeric047 : ForcedCoverage2.dispatch (fun _ => payload047) normal099 46 = true := by
  decide +kernel

theorem coveredLeaf047 : CovBy 9 PR (Pg cN 9 BS TS) cell078 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf047]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload047) normal099 46 numeric047
theorem normalizedLeaf048 : AdaptiveCoverage.normalize SL cell109 = normal103 := by
  calc
    AdaptiveCoverage.normalize SL cell109 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell109)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell109)).symm
    _ = normal103 := by rfl

theorem numeric048 : ForcedCoverage2.dispatch (fun _ => payload048) normal103 46 = true := by
  decide +kernel

theorem coveredLeaf048 : CovBy 9 PR (Pg cN 9 BS TS) cell109 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf048]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload048) normal103 46 numeric048
theorem normalizedLeaf049 : AdaptiveCoverage.normalize SL cell113 = normal106 := by
  calc
    AdaptiveCoverage.normalize SL cell113 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell113)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell113)).symm
    _ = normal106 := by rfl

theorem numeric049 : ForcedCoverage2.dispatch (fun _ => payload049) normal106 46 = true := by
  decide +kernel

theorem coveredLeaf049 : CovBy 9 PR (Pg cN 9 BS TS) cell113 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf049]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload049) normal106 46 numeric049
theorem normalizedLeaf050 : AdaptiveCoverage.normalize SL cell115 = normal108 := by
  calc
    AdaptiveCoverage.normalize SL cell115 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell115)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell115)).symm
    _ = normal108 := by rfl

theorem numeric050 : ForcedCoverage2.dispatch (fun _ => payload050) normal108 46 = true := by
  decide +kernel

theorem coveredLeaf050 : CovBy 9 PR (Pg cN 9 BS TS) cell115 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf050]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload050) normal108 46 numeric050
theorem normalizedLeaf051 : AdaptiveCoverage.normalize SL cell119 = normal111 := by
  calc
    AdaptiveCoverage.normalize SL cell119 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell119)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell119)).symm
    _ = normal111 := by rfl

theorem numeric051 : ForcedCoverage2.dispatch (fun _ => payload051) normal111 46 = true := by
  decide +kernel

theorem coveredLeaf051 : CovBy 9 PR (Pg cN 9 BS TS) cell119 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf051]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload051) normal111 46 numeric051
theorem normalizedLeaf052 : AdaptiveCoverage.normalize SL cell121 = normal113 := by
  calc
    AdaptiveCoverage.normalize SL cell121 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell121)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell121)).symm
    _ = normal113 := by rfl

theorem numeric052 : ForcedCoverage2.dispatch (fun _ => payload052) normal113 46 = true := by
  decide +kernel

theorem coveredLeaf052 : CovBy 9 PR (Pg cN 9 BS TS) cell121 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf052]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload052) normal113 46 numeric052
theorem normalizedLeaf053 : AdaptiveCoverage.normalize SL cell123 = normal115 := by
  calc
    AdaptiveCoverage.normalize SL cell123 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell123)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell123)).symm
    _ = normal115 := by rfl

theorem numeric053 : ForcedCoverage2.dispatch (fun _ => payload053) normal115 46 = true := by
  decide +kernel

theorem coveredLeaf053 : CovBy 9 PR (Pg cN 9 BS TS) cell123 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf053]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload053) normal115 46 numeric053
theorem normalizedLeaf054 : AdaptiveCoverage.normalize SL cell125 = normal117 := by
  calc
    AdaptiveCoverage.normalize SL cell125 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell125)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell125)).symm
    _ = normal117 := by rfl

theorem numeric054 : ForcedCoverage2.dispatch (fun _ => payload054) normal117 46 = true := by
  decide +kernel

theorem coveredLeaf054 : CovBy 9 PR (Pg cN 9 BS TS) cell125 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf054]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload054) normal117 46 numeric054
theorem normalizedLeaf055 : AdaptiveCoverage.normalize SL cell127 = normal119 := by
  calc
    AdaptiveCoverage.normalize SL cell127 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell127)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell127)).symm
    _ = normal119 := by rfl

theorem numeric055 : ForcedCoverage2.dispatch (fun _ => payload055) normal119 46 = true := by
  decide +kernel

theorem coveredLeaf055 : CovBy 9 PR (Pg cN 9 BS TS) cell127 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf055]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload055) normal119 46 numeric055
theorem normalizedLeaf056 : AdaptiveCoverage.normalize SL cell129 = normal121 := by
  calc
    AdaptiveCoverage.normalize SL cell129 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell129)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell129)).symm
    _ = normal121 := by rfl

theorem numeric056 : ForcedCoverage2.dispatch (fun _ => payload056) normal121 46 = true := by
  decide +kernel

theorem coveredLeaf056 : CovBy 9 PR (Pg cN 9 BS TS) cell129 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf056]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload056) normal121 46 numeric056
theorem normalizedLeaf057 : AdaptiveCoverage.normalize SL cell133 = normal124 := by
  calc
    AdaptiveCoverage.normalize SL cell133 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell133)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell133)).symm
    _ = normal124 := by rfl

theorem numeric057 : ForcedCoverage2.dispatch (fun _ => payload057) normal124 46 = true := by
  decide +kernel

theorem coveredLeaf057 : CovBy 9 PR (Pg cN 9 BS TS) cell133 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf057]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload057) normal124 46 numeric057
theorem normalizedLeaf058 : AdaptiveCoverage.normalize SL cell134 = normal125 := by
  calc
    AdaptiveCoverage.normalize SL cell134 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell134)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell134)).symm
    _ = normal125 := by rfl

theorem numeric058 : ForcedCoverage2.dispatch (fun _ => payload058) normal125 46 = true := by
  decide +kernel

theorem coveredLeaf058 : CovBy 9 PR (Pg cN 9 BS TS) cell134 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf058]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload058) normal125 46 numeric058
theorem normalizedLeaf059 : AdaptiveCoverage.normalize SL cell132 = normal126 := by
  calc
    AdaptiveCoverage.normalize SL cell132 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell132)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell132)).symm
    _ = normal126 := by rfl

theorem numeric059 : ForcedCoverage2.dispatch (fun _ => payload059) normal126 46 = true := by
  decide +kernel

theorem coveredLeaf059 : CovBy 9 PR (Pg cN 9 BS TS) cell132 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf059]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload059) normal126 46 numeric059
theorem normalizedLeaf060 : AdaptiveCoverage.normalize SL cell118 = normal127 := by
  calc
    AdaptiveCoverage.normalize SL cell118 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell118)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell118)).symm
    _ = normal127 := by rfl

theorem numeric060 : ForcedCoverage2.dispatch (fun _ => payload060) normal127 46 = true := by
  decide +kernel

theorem coveredLeaf060 : CovBy 9 PR (Pg cN 9 BS TS) cell118 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf060]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload060) normal127 46 numeric060
theorem normalizedLeaf061 : AdaptiveCoverage.normalize SL cell112 = normal128 := by
  calc
    AdaptiveCoverage.normalize SL cell112 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell112)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell112)).symm
    _ = normal128 := by rfl

theorem numeric061 : ForcedCoverage2.dispatch (fun _ => payload061) normal128 46 = true := by
  decide +kernel

theorem coveredLeaf061 : CovBy 9 PR (Pg cN 9 BS TS) cell112 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf061]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload061) normal128 46 numeric061
theorem normalizedLeaf062 : AdaptiveCoverage.normalize SL cell108 = normal129 := by
  calc
    AdaptiveCoverage.normalize SL cell108 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell108)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell108)).symm
    _ = normal129 := by rfl

theorem numeric062 : ForcedCoverage2.dispatch (fun _ => payload062) normal129 46 = true := by
  decide +kernel

theorem coveredLeaf062 : CovBy 9 PR (Pg cN 9 BS TS) cell108 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf062]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload062) normal129 46 numeric062
theorem normalizedLeaf063 : AdaptiveCoverage.normalize SL cell139 = normal133 := by
  calc
    AdaptiveCoverage.normalize SL cell139 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell139)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell139)).symm
    _ = normal133 := by rfl

theorem numeric063 : ForcedCoverage2.dispatch (fun _ => payload063) normal133 46 = true := by
  decide +kernel

theorem coveredLeaf063 : CovBy 9 PR (Pg cN 9 BS TS) cell139 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf063]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload063) normal133 46 numeric063

set_option pp.fullNames true
#print axioms normalizedLeaf032
#print axioms numeric032
#print axioms coveredLeaf032
#print axioms normalizedLeaf033
#print axioms numeric033
#print axioms coveredLeaf033
#print axioms normalizedLeaf034
#print axioms numeric034
#print axioms coveredLeaf034
#print axioms normalizedLeaf035
#print axioms numeric035
#print axioms coveredLeaf035
#print axioms normalizedLeaf036
#print axioms numeric036
#print axioms coveredLeaf036
#print axioms normalizedLeaf037
#print axioms numeric037
#print axioms coveredLeaf037
#print axioms normalizedLeaf038
#print axioms numeric038
#print axioms coveredLeaf038
#print axioms normalizedLeaf039
#print axioms numeric039
#print axioms coveredLeaf039
#print axioms normalizedLeaf040
#print axioms numeric040
#print axioms coveredLeaf040
#print axioms normalizedLeaf041
#print axioms numeric041
#print axioms coveredLeaf041
#print axioms normalizedLeaf042
#print axioms numeric042
#print axioms coveredLeaf042
#print axioms normalizedLeaf043
#print axioms numeric043
#print axioms coveredLeaf043
#print axioms normalizedLeaf044
#print axioms numeric044
#print axioms coveredLeaf044
#print axioms normalizedLeaf045
#print axioms numeric045
#print axioms coveredLeaf045
#print axioms normalizedLeaf046
#print axioms numeric046
#print axioms coveredLeaf046
#print axioms normalizedLeaf047
#print axioms numeric047
#print axioms coveredLeaf047
#print axioms normalizedLeaf048
#print axioms numeric048
#print axioms coveredLeaf048
#print axioms normalizedLeaf049
#print axioms numeric049
#print axioms coveredLeaf049
#print axioms normalizedLeaf050
#print axioms numeric050
#print axioms coveredLeaf050
#print axioms normalizedLeaf051
#print axioms numeric051
#print axioms coveredLeaf051
#print axioms normalizedLeaf052
#print axioms numeric052
#print axioms coveredLeaf052
#print axioms normalizedLeaf053
#print axioms numeric053
#print axioms coveredLeaf053
#print axioms normalizedLeaf054
#print axioms numeric054
#print axioms coveredLeaf054
#print axioms normalizedLeaf055
#print axioms numeric055
#print axioms coveredLeaf055
#print axioms normalizedLeaf056
#print axioms numeric056
#print axioms coveredLeaf056
#print axioms normalizedLeaf057
#print axioms numeric057
#print axioms coveredLeaf057
#print axioms normalizedLeaf058
#print axioms numeric058
#print axioms coveredLeaf058
#print axioms normalizedLeaf059
#print axioms numeric059
#print axioms coveredLeaf059
#print axioms normalizedLeaf060
#print axioms numeric060
#print axioms coveredLeaf060
#print axioms normalizedLeaf061
#print axioms numeric061
#print axioms coveredLeaf061
#print axioms normalizedLeaf062
#print axioms numeric062
#print axioms coveredLeaf062
#print axioms normalizedLeaf063
#print axioms numeric063
#print axioms coveredLeaf063
end StructuralGoal20261016.W10Aux127
end
