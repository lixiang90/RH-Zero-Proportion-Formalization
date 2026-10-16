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
theorem normalizedLeaf064 : AdaptiveCoverage.normalize SL cell145 = normal137 := by
  calc
    AdaptiveCoverage.normalize SL cell145 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell145)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell145)).symm
    _ = normal137 := by rfl

theorem numeric064 : ForcedCoverage2.dispatch (fun _ => payload064) normal137 46 = true := by
  decide +kernel

theorem coveredLeaf064 : CovBy 9 PR (Pg cN 9 BS TS) cell145 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf064]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload064) normal137 46 numeric064
theorem normalizedLeaf065 : AdaptiveCoverage.normalize SL cell147 = normal139 := by
  calc
    AdaptiveCoverage.normalize SL cell147 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell147)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell147)).symm
    _ = normal139 := by rfl

theorem numeric065 : ForcedCoverage2.dispatch (fun _ => payload065) normal139 46 = true := by
  decide +kernel

theorem coveredLeaf065 : CovBy 9 PR (Pg cN 9 BS TS) cell147 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf065]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload065) normal139 46 numeric065
theorem normalizedLeaf066 : AdaptiveCoverage.normalize SL cell153 = normal143 := by
  calc
    AdaptiveCoverage.normalize SL cell153 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell153)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell153)).symm
    _ = normal143 := by rfl

theorem numeric066 : ForcedCoverage2.dispatch (fun _ => payload066) normal143 46 = true := by
  decide +kernel

theorem coveredLeaf066 : CovBy 9 PR (Pg cN 9 BS TS) cell153 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf066]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload066) normal143 46 numeric066
theorem normalizedLeaf067 : AdaptiveCoverage.normalize SL cell155 = normal145 := by
  calc
    AdaptiveCoverage.normalize SL cell155 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell155)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell155)).symm
    _ = normal145 := by rfl

theorem numeric067 : ForcedCoverage2.dispatch (fun _ => payload067) normal145 46 = true := by
  decide +kernel

theorem coveredLeaf067 : CovBy 9 PR (Pg cN 9 BS TS) cell155 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf067]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload067) normal145 46 numeric067
theorem normalizedLeaf068 : AdaptiveCoverage.normalize SL cell157 = normal147 := by
  calc
    AdaptiveCoverage.normalize SL cell157 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell157)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell157)).symm
    _ = normal147 := by rfl

theorem numeric068 : ForcedCoverage2.dispatch (fun _ => payload068) normal147 46 = true := by
  decide +kernel

theorem coveredLeaf068 : CovBy 9 PR (Pg cN 9 BS TS) cell157 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf068]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload068) normal147 46 numeric068
theorem normalizedLeaf069 : AdaptiveCoverage.normalize SL cell159 = normal149 := by
  calc
    AdaptiveCoverage.normalize SL cell159 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell159)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell159)).symm
    _ = normal149 := by rfl

theorem numeric069 : ForcedCoverage2.dispatch (fun _ => payload069) normal149 46 = true := by
  decide +kernel

theorem coveredLeaf069 : CovBy 9 PR (Pg cN 9 BS TS) cell159 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf069]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload069) normal149 46 numeric069
theorem normalizedLeaf070 : AdaptiveCoverage.normalize SL cell160 = normal150 := by
  calc
    AdaptiveCoverage.normalize SL cell160 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell160)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell160)).symm
    _ = normal150 := by rfl

theorem numeric070 : ForcedCoverage2.dispatch (fun _ => payload070) normal150 46 = true := by
  decide +kernel

theorem coveredLeaf070 : CovBy 9 PR (Pg cN 9 BS TS) cell160 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf070]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload070) normal150 46 numeric070
theorem normalizedLeaf071 : AdaptiveCoverage.normalize SL cell152 = normal151 := by
  calc
    AdaptiveCoverage.normalize SL cell152 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell152)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell152)).symm
    _ = normal151 := by rfl

theorem numeric071 : ForcedCoverage2.dispatch (fun _ => payload071) normal151 46 = true := by
  decide +kernel

theorem coveredLeaf071 : CovBy 9 PR (Pg cN 9 BS TS) cell152 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf071]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload071) normal151 46 numeric071
theorem normalizedLeaf072 : AdaptiveCoverage.normalize SL cell163 = normal154 := by
  calc
    AdaptiveCoverage.normalize SL cell163 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell163)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell163)).symm
    _ = normal154 := by rfl

theorem numeric072 : ForcedCoverage2.dispatch (fun _ => payload072) normal154 46 = true := by
  decide +kernel

theorem coveredLeaf072 : CovBy 9 PR (Pg cN 9 BS TS) cell163 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf072]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload072) normal154 46 numeric072
theorem normalizedLeaf073 : AdaptiveCoverage.normalize SL cell165 = normal156 := by
  calc
    AdaptiveCoverage.normalize SL cell165 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell165)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell165)).symm
    _ = normal156 := by rfl

theorem numeric073 : ForcedCoverage2.dispatch (fun _ => payload073) normal156 46 = true := by
  decide +kernel

theorem coveredLeaf073 : CovBy 9 PR (Pg cN 9 BS TS) cell165 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf073]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload073) normal156 46 numeric073
theorem normalizedLeaf074 : AdaptiveCoverage.normalize SL cell166 = normal157 := by
  calc
    AdaptiveCoverage.normalize SL cell166 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell166)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell166)).symm
    _ = normal157 := by rfl

theorem numeric074 : ForcedCoverage2.dispatch (fun _ => payload074) normal157 46 = true := by
  decide +kernel

theorem coveredLeaf074 : CovBy 9 PR (Pg cN 9 BS TS) cell166 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf074]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload074) normal157 46 numeric074
theorem normalizedLeaf075 : AdaptiveCoverage.normalize SL cell162 = normal158 := by
  calc
    AdaptiveCoverage.normalize SL cell162 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell162)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell162)).symm
    _ = normal158 := by rfl

theorem numeric075 : ForcedCoverage2.dispatch (fun _ => payload075) normal158 46 = true := by
  decide +kernel

theorem coveredLeaf075 : CovBy 9 PR (Pg cN 9 BS TS) cell162 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf075]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload075) normal158 46 numeric075
theorem normalizedLeaf076 : AdaptiveCoverage.normalize SL cell144 = normal159 := by
  calc
    AdaptiveCoverage.normalize SL cell144 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell144)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell144)).symm
    _ = normal159 := by rfl

theorem numeric076 : ForcedCoverage2.dispatch (fun _ => payload076) normal159 46 = true := by
  decide +kernel

theorem coveredLeaf076 : CovBy 9 PR (Pg cN 9 BS TS) cell144 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf076]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload076) normal159 46 numeric076
theorem normalizedLeaf077 : AdaptiveCoverage.normalize SL cell171 = normal163 := by
  calc
    AdaptiveCoverage.normalize SL cell171 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell171)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell171)).symm
    _ = normal163 := by rfl

theorem numeric077 : ForcedCoverage2.dispatch (fun _ => payload077) normal163 46 = true := by
  decide +kernel

theorem coveredLeaf077 : CovBy 9 PR (Pg cN 9 BS TS) cell171 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf077]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload077) normal163 46 numeric077
theorem normalizedLeaf078 : AdaptiveCoverage.normalize SL cell173 = normal165 := by
  calc
    AdaptiveCoverage.normalize SL cell173 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell173)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell173)).symm
    _ = normal165 := by rfl

theorem numeric078 : ForcedCoverage2.dispatch (fun _ => payload078) normal165 46 = true := by
  decide +kernel

theorem coveredLeaf078 : CovBy 9 PR (Pg cN 9 BS TS) cell173 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf078]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload078) normal165 46 numeric078
theorem normalizedLeaf079 : AdaptiveCoverage.normalize SL cell179 = normal169 := by
  calc
    AdaptiveCoverage.normalize SL cell179 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell179)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell179)).symm
    _ = normal169 := by rfl

theorem numeric079 : ForcedCoverage2.dispatch (fun _ => payload079) normal169 46 = true := by
  decide +kernel

theorem coveredLeaf079 : CovBy 9 PR (Pg cN 9 BS TS) cell179 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf079]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload079) normal169 46 numeric079
theorem normalizedLeaf080 : AdaptiveCoverage.normalize SL cell181 = normal171 := by
  calc
    AdaptiveCoverage.normalize SL cell181 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell181)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell181)).symm
    _ = normal171 := by rfl

theorem numeric080 : ForcedCoverage2.dispatch (fun _ => payload080) normal171 46 = true := by
  decide +kernel

theorem coveredLeaf080 : CovBy 9 PR (Pg cN 9 BS TS) cell181 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf080]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload080) normal171 46 numeric080
theorem normalizedLeaf081 : AdaptiveCoverage.normalize SL cell185 = normal174 := by
  calc
    AdaptiveCoverage.normalize SL cell185 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell185)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell185)).symm
    _ = normal174 := by rfl

theorem numeric081 : ForcedCoverage2.dispatch (fun _ => payload081) normal174 46 = true := by
  decide +kernel

theorem coveredLeaf081 : CovBy 9 PR (Pg cN 9 BS TS) cell185 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf081]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload081) normal174 46 numeric081
theorem normalizedLeaf082 : AdaptiveCoverage.normalize SL cell189 = normal177 := by
  calc
    AdaptiveCoverage.normalize SL cell189 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell189)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell189)).symm
    _ = normal177 := by rfl

theorem numeric082 : ForcedCoverage2.dispatch (fun _ => payload082) normal177 46 = true := by
  decide +kernel

theorem coveredLeaf082 : CovBy 9 PR (Pg cN 9 BS TS) cell189 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf082]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload082) normal177 46 numeric082
theorem normalizedLeaf083 : AdaptiveCoverage.normalize SL cell190 = normal178 := by
  calc
    AdaptiveCoverage.normalize SL cell190 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell190)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell190)).symm
    _ = normal178 := by rfl

theorem numeric083 : ForcedCoverage2.dispatch (fun _ => payload083) normal178 46 = true := by
  decide +kernel

theorem coveredLeaf083 : CovBy 9 PR (Pg cN 9 BS TS) cell190 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf083]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload083) normal178 46 numeric083
theorem normalizedLeaf084 : AdaptiveCoverage.normalize SL cell191 = normal180 := by
  calc
    AdaptiveCoverage.normalize SL cell191 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell191)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell191)).symm
    _ = normal180 := by rfl

theorem numeric084 : ForcedCoverage2.dispatch (fun _ => payload084) normal180 46 = true := by
  decide +kernel

theorem coveredLeaf084 : CovBy 9 PR (Pg cN 9 BS TS) cell191 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf084]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload084) normal180 46 numeric084
theorem normalizedLeaf085 : AdaptiveCoverage.normalize SL cell195 = normal183 := by
  calc
    AdaptiveCoverage.normalize SL cell195 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell195)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell195)).symm
    _ = normal183 := by rfl

theorem numeric085 : ForcedCoverage2.dispatch (fun _ => payload085) normal183 46 = true := by
  decide +kernel

theorem coveredLeaf085 : CovBy 9 PR (Pg cN 9 BS TS) cell195 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf085]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload085) normal183 46 numeric085
theorem normalizedLeaf086 : AdaptiveCoverage.normalize SL cell196 = normal184 := by
  calc
    AdaptiveCoverage.normalize SL cell196 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell196)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell196)).symm
    _ = normal184 := by rfl

theorem numeric086 : ForcedCoverage2.dispatch (fun _ => payload086) normal184 46 = true := by
  decide +kernel

theorem coveredLeaf086 : CovBy 9 PR (Pg cN 9 BS TS) cell196 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf086]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload086) normal184 46 numeric086
theorem normalizedLeaf087 : AdaptiveCoverage.normalize SL cell197 = normal186 := by
  calc
    AdaptiveCoverage.normalize SL cell197 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell197)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell197)).symm
    _ = normal186 := by rfl

theorem numeric087 : ForcedCoverage2.dispatch (fun _ => payload087) normal186 46 = true := by
  decide +kernel

theorem coveredLeaf087 : CovBy 9 PR (Pg cN 9 BS TS) cell197 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf087]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload087) normal186 46 numeric087
theorem normalizedLeaf088 : AdaptiveCoverage.normalize SL cell198 = normal187 := by
  calc
    AdaptiveCoverage.normalize SL cell198 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell198)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell198)).symm
    _ = normal187 := by rfl

theorem numeric088 : ForcedCoverage2.dispatch (fun _ => payload088) normal187 46 = true := by
  decide +kernel

theorem coveredLeaf088 : CovBy 9 PR (Pg cN 9 BS TS) cell198 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf088]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload088) normal187 46 numeric088
theorem normalizedLeaf089 : AdaptiveCoverage.normalize SL cell201 = normal190 := by
  calc
    AdaptiveCoverage.normalize SL cell201 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell201)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell201)).symm
    _ = normal190 := by rfl

theorem numeric089 : ForcedCoverage2.dispatch (fun _ => payload089) normal190 46 = true := by
  decide +kernel

theorem coveredLeaf089 : CovBy 9 PR (Pg cN 9 BS TS) cell201 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf089]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload089) normal190 46 numeric089
theorem normalizedLeaf090 : AdaptiveCoverage.normalize SL cell202 = normal191 := by
  calc
    AdaptiveCoverage.normalize SL cell202 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell202)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell202)).symm
    _ = normal191 := by rfl

theorem numeric090 : ForcedCoverage2.dispatch (fun _ => payload090) normal191 46 = true := by
  decide +kernel

theorem coveredLeaf090 : CovBy 9 PR (Pg cN 9 BS TS) cell202 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf090]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload090) normal191 46 numeric090
theorem normalizedLeaf091 : AdaptiveCoverage.normalize SL cell200 = normal192 := by
  calc
    AdaptiveCoverage.normalize SL cell200 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell200)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell200)).symm
    _ = normal192 := by rfl

theorem numeric091 : ForcedCoverage2.dispatch (fun _ => payload091) normal192 46 = true := by
  decide +kernel

theorem coveredLeaf091 : CovBy 9 PR (Pg cN 9 BS TS) cell200 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf091]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload091) normal192 46 numeric091
theorem normalizedLeaf092 : AdaptiveCoverage.normalize SL cell178 = normal193 := by
  calc
    AdaptiveCoverage.normalize SL cell178 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell178)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell178)).symm
    _ = normal193 := by rfl

theorem numeric092 : ForcedCoverage2.dispatch (fun _ => payload092) normal193 46 = true := by
  decide +kernel

theorem coveredLeaf092 : CovBy 9 PR (Pg cN 9 BS TS) cell178 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf092]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload092) normal193 46 numeric092
theorem normalizedLeaf093 : AdaptiveCoverage.normalize SL cell205 = normal196 := by
  calc
    AdaptiveCoverage.normalize SL cell205 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell205)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell205)).symm
    _ = normal196 := by rfl

theorem numeric093 : ForcedCoverage2.dispatch (fun _ => payload093) normal196 46 = true := by
  decide +kernel

theorem coveredLeaf093 : CovBy 9 PR (Pg cN 9 BS TS) cell205 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf093]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload093) normal196 46 numeric093
theorem normalizedLeaf094 : AdaptiveCoverage.normalize SL cell207 = normal198 := by
  calc
    AdaptiveCoverage.normalize SL cell207 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell207)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell207)).symm
    _ = normal198 := by rfl

theorem numeric094 : ForcedCoverage2.dispatch (fun _ => payload094) normal198 46 = true := by
  decide +kernel

theorem coveredLeaf094 : CovBy 9 PR (Pg cN 9 BS TS) cell207 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf094]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload094) normal198 46 numeric094
theorem normalizedLeaf095 : AdaptiveCoverage.normalize SL cell208 = normal199 := by
  calc
    AdaptiveCoverage.normalize SL cell208 =
        (FixedGeometry.normalize SL (FixedGeometry.Cell.ofCl cell208)).toCl :=
      (FixedGeometry.normalize_eq SL (FixedGeometry.Cell.ofCl cell208)).symm
    _ = normal199 := by rfl

theorem numeric095 : ForcedCoverage2.dispatch (fun _ => payload095) normal199 46 = true := by
  decide +kernel

theorem coveredLeaf095 : CovBy 9 PR (Pg cN 9 BS TS) cell208 := by
  apply AdaptiveCoverage.normalize_sound hSL
  rw [normalizedLeaf095]
  exact ForcedCoverage2.dispatch_sound (fun _ => payload095) normal199 46 numeric095

set_option pp.fullNames true
#print axioms normalizedLeaf064
#print axioms numeric064
#print axioms coveredLeaf064
#print axioms normalizedLeaf065
#print axioms numeric065
#print axioms coveredLeaf065
#print axioms normalizedLeaf066
#print axioms numeric066
#print axioms coveredLeaf066
#print axioms normalizedLeaf067
#print axioms numeric067
#print axioms coveredLeaf067
#print axioms normalizedLeaf068
#print axioms numeric068
#print axioms coveredLeaf068
#print axioms normalizedLeaf069
#print axioms numeric069
#print axioms coveredLeaf069
#print axioms normalizedLeaf070
#print axioms numeric070
#print axioms coveredLeaf070
#print axioms normalizedLeaf071
#print axioms numeric071
#print axioms coveredLeaf071
#print axioms normalizedLeaf072
#print axioms numeric072
#print axioms coveredLeaf072
#print axioms normalizedLeaf073
#print axioms numeric073
#print axioms coveredLeaf073
#print axioms normalizedLeaf074
#print axioms numeric074
#print axioms coveredLeaf074
#print axioms normalizedLeaf075
#print axioms numeric075
#print axioms coveredLeaf075
#print axioms normalizedLeaf076
#print axioms numeric076
#print axioms coveredLeaf076
#print axioms normalizedLeaf077
#print axioms numeric077
#print axioms coveredLeaf077
#print axioms normalizedLeaf078
#print axioms numeric078
#print axioms coveredLeaf078
#print axioms normalizedLeaf079
#print axioms numeric079
#print axioms coveredLeaf079
#print axioms normalizedLeaf080
#print axioms numeric080
#print axioms coveredLeaf080
#print axioms normalizedLeaf081
#print axioms numeric081
#print axioms coveredLeaf081
#print axioms normalizedLeaf082
#print axioms numeric082
#print axioms coveredLeaf082
#print axioms normalizedLeaf083
#print axioms numeric083
#print axioms coveredLeaf083
#print axioms normalizedLeaf084
#print axioms numeric084
#print axioms coveredLeaf084
#print axioms normalizedLeaf085
#print axioms numeric085
#print axioms coveredLeaf085
#print axioms normalizedLeaf086
#print axioms numeric086
#print axioms coveredLeaf086
#print axioms normalizedLeaf087
#print axioms numeric087
#print axioms coveredLeaf087
#print axioms normalizedLeaf088
#print axioms numeric088
#print axioms coveredLeaf088
#print axioms normalizedLeaf089
#print axioms numeric089
#print axioms coveredLeaf089
#print axioms normalizedLeaf090
#print axioms numeric090
#print axioms coveredLeaf090
#print axioms normalizedLeaf091
#print axioms numeric091
#print axioms coveredLeaf091
#print axioms normalizedLeaf092
#print axioms numeric092
#print axioms coveredLeaf092
#print axioms normalizedLeaf093
#print axioms numeric093
#print axioms coveredLeaf093
#print axioms normalizedLeaf094
#print axioms numeric094
#print axioms coveredLeaf094
#print axioms normalizedLeaf095
#print axioms numeric095
#print axioms coveredLeaf095
end StructuralGoal20261016.W10Aux127
end
