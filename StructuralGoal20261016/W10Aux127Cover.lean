/- Frozen 127-leaf W10 subtree; complete global coverage is not asserted. -/
import StructuralGoal20261016.W10Aux127Leaves00
import StructuralGoal20261016.W10Aux127Leaves01
import StructuralGoal20261016.W10Aux127Leaves02
import StructuralGoal20261016.W10Aux127Leaves03
import StructuralGoal20261016.W10Aux127Geometry00
import StructuralGoal20261016.W10Aux127Geometry01
import StructuralGoal20261016.W10Aux127Geometry02
import StructuralGoal20261016.W10Aux127Geometry03
import StructuralGoal20261016.W10Aux127Geometry04
import StructuralGoal20261016.W10Aux127Geometry05
import StructuralGoal20261016.W10Aux127Geometry06
import StructuralGoal20261016.W10Aux127Geometry07
import StructuralGoal20261016.W10Aux127Geometry08
import StructuralGoal20261016.W10Aux127Geometry09
import StructuralGoal20261016.W10Aux127Geometry10
import StructuralGoal20261016.W10Aux127Geometry11
import StructuralGoal20261016.W10Aux127Geometry12
import StructuralGoal20261016.W10Aux127Geometry13
import StructuralGoal20261016.W10Aux127Geometry14
import StructuralGoal20261016.W10Aux127Geometry15
import StructuralGoal20261016.W10Aux127Geometry16
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
theorem coveredNode129 : CovBy 9 PR (Pg cN 9 BS TS) cell254 :=
  branch 3 5 81920 (by decide) (by decide) normalized129 left129 right129 coveredLeaf123 coveredLeaf124
theorem coveredNode128 : CovBy 9 PR (Pg cN 9 BS TS) cell256 :=
  branch 4 6 81920 (by decide) (by decide) normalized128 left128 right128 coveredLeaf121 coveredLeaf122
theorem coveredNode127 : CovBy 9 PR (Pg cN 9 BS TS) cell253 :=
  branch 3 5 81920 (by decide) (by decide) normalized127 left127 right127 coveredLeaf120 coveredNode128
theorem coveredNode126 : CovBy 9 PR (Pg cN 9 BS TS) cell252 :=
  branch 3 6 131072 (by decide) (by decide) normalized126 left126 right126 coveredNode127 coveredNode129
theorem coveredNode125 : CovBy 9 PR (Pg cN 9 BS TS) cell240 :=
  branch 0 9 319488 (by decide) (by decide) normalized125 left125 right125 coveredLeaf119 coveredNode126
theorem coveredNode124 : CovBy 9 PR (Pg cN 9 BS TS) cell247 :=
  branch 4 6 81920 (by decide) (by decide) normalized124 left124 right124 coveredLeaf115 coveredLeaf116
theorem coveredNode123 : CovBy 9 PR (Pg cN 9 BS TS) cell245 :=
  branch 3 9 229376 (by decide) (by decide) normalized123 left123 right123 coveredNode124 coveredLeaf117
theorem coveredNode122 : CovBy 9 PR (Pg cN 9 BS TS) cell244 :=
  branch 2 5 131072 (by decide) (by decide) normalized122 left122 right122 coveredNode123 coveredLeaf118
theorem coveredNode121 : CovBy 9 PR (Pg cN 9 BS TS) cell242 :=
  branch 0 9 319488 (by decide) (by decide) normalized121 left121 right121 coveredLeaf114 coveredNode122
theorem coveredNode120 : CovBy 9 PR (Pg cN 9 BS TS) cell239 :=
  branch 3 5 81920 (by decide) (by decide) normalized120 left120 right120 coveredLeaf113 coveredNode121
theorem coveredNode119 : CovBy 9 PR (Pg cN 9 BS TS) cell214 :=
  branch 3 7 163840 (by decide) (by decide) normalized119 left119 right119 coveredNode120 coveredNode125
theorem coveredNode118 : CovBy 9 PR (Pg cN 9 BS TS) cell235 :=
  branch 3 5 81920 (by decide) (by decide) normalized118 left118 right118 coveredLeaf109 coveredLeaf110
theorem coveredNode117 : CovBy 9 PR (Pg cN 9 BS TS) cell233 :=
  branch 0 6 229376 (by decide) (by decide) normalized117 left117 right117 coveredNode118 coveredLeaf111
theorem coveredNode116 : CovBy 9 PR (Pg cN 9 BS TS) cell232 :=
  branch 4 7 131072 (by decide) (by decide) normalized116 left116 right116 coveredNode117 coveredLeaf112
theorem coveredNode115 : CovBy 9 PR (Pg cN 9 BS TS) cell230 :=
  branch 0 9 319488 (by decide) (by decide) normalized115 left115 right115 coveredLeaf108 coveredNode116
theorem coveredNode114 : CovBy 9 PR (Pg cN 9 BS TS) cell216 :=
  branch 4 6 81920 (by decide) (by decide) normalized114 left114 right114 coveredLeaf107 coveredNode115
theorem coveredNode113 : CovBy 9 PR (Pg cN 9 BS TS) cell222 :=
  branch 4 5 49152 (by decide) (by decide) normalized113 left113 right113 coveredLeaf105 coveredLeaf106
theorem coveredNode112 : CovBy 9 PR (Pg cN 9 BS TS) cell224 :=
  branch 4 5 49152 (by decide) (by decide) normalized112 left112 right112 coveredLeaf103 coveredLeaf104
theorem coveredNode111 : CovBy 9 PR (Pg cN 9 BS TS) cell221 :=
  branch 0 7 245760 (by decide) (by decide) normalized111 left111 right111 coveredLeaf102 coveredNode112
theorem coveredNode110 : CovBy 9 PR (Pg cN 9 BS TS) cell220 :=
  branch 0 6 229376 (by decide) (by decide) normalized110 left110 right110 coveredNode111 coveredNode113
theorem coveredNode109 : CovBy 9 PR (Pg cN 9 BS TS) cell218 :=
  branch 1 8 245760 (by decide) (by decide) normalized109 left109 right109 coveredLeaf101 coveredNode110
theorem coveredNode108 : CovBy 9 PR (Pg cN 9 BS TS) cell215 :=
  branch 0 9 319488 (by decide) (by decide) normalized108 left108 right108 coveredLeaf100 coveredNode109
theorem coveredNode107 : CovBy 9 PR (Pg cN 9 BS TS) cell213 :=
  branch 3 7 163840 (by decide) (by decide) normalized107 left107 right107 coveredNode108 coveredNode114
theorem coveredNode106 : CovBy 9 PR (Pg cN 9 BS TS) cell212 :=
  branch 2 6 163840 (by decide) (by decide) normalized106 left106 right106 coveredNode107 coveredNode119
theorem coveredNode105 : CovBy 9 PR (Pg cN 9 BS TS) cell210 :=
  branch 1 9 278528 (by decide) (by decide) normalized105 left105 right105 coveredLeaf099 coveredNode106
theorem coveredNode104 : CovBy 9 PR (Pg cN 9 BS TS) cell168 :=
  branch 0 8 278528 (by decide) (by decide) normalized104 left104 right104 coveredLeaf098 coveredNode105
theorem coveredNode103 : CovBy 9 PR (Pg cN 9 BS TS) cell206 :=
  branch 3 5 81920 (by decide) (by decide) normalized103 left103 right103 coveredLeaf094 coveredLeaf095
theorem coveredNode102 : CovBy 9 PR (Pg cN 9 BS TS) cell203 :=
  branch 0 9 319488 (by decide) (by decide) normalized102 left102 right102 coveredLeaf093 coveredNode103
theorem coveredNode101 : CovBy 9 PR (Pg cN 9 BS TS) cell176 :=
  branch 3 7 163840 (by decide) (by decide) normalized101 left101 right101 coveredNode102 coveredLeaf096
theorem coveredNode100 : CovBy 9 PR (Pg cN 9 BS TS) cell199 :=
  branch 3 5 81920 (by decide) (by decide) normalized100 left100 right100 coveredLeaf089 coveredLeaf090
theorem coveredNode099 : CovBy 9 PR (Pg cN 9 BS TS) cell184 :=
  branch 1 4 131072 (by decide) (by decide) normalized099 left099 right099 coveredNode100 coveredLeaf091
theorem coveredNode098 : CovBy 9 PR (Pg cN 9 BS TS) cell194 :=
  branch 3 4 49152 (by decide) (by decide) normalized098 left098 right098 coveredLeaf087 coveredLeaf088
theorem coveredNode097 : CovBy 9 PR (Pg cN 9 BS TS) cell193 :=
  branch 3 4 49152 (by decide) (by decide) normalized097 left097 right097 coveredLeaf085 coveredLeaf086
theorem coveredNode096 : CovBy 9 PR (Pg cN 9 BS TS) cell192 :=
  branch 3 8 196608 (by decide) (by decide) normalized096 left096 right096 coveredNode097 coveredNode098
theorem coveredNode095 : CovBy 9 PR (Pg cN 9 BS TS) cell188 :=
  branch 4 6 65536 (by decide) (by decide) normalized095 left095 right095 coveredLeaf084 coveredNode096
theorem coveredNode094 : CovBy 9 PR (Pg cN 9 BS TS) cell187 :=
  branch 3 5 81920 (by decide) (by decide) normalized094 left094 right094 coveredLeaf082 coveredLeaf083
theorem coveredNode093 : CovBy 9 PR (Pg cN 9 BS TS) cell186 :=
  branch 3 9 229376 (by decide) (by decide) normalized093 left093 right093 coveredNode094 coveredNode095
theorem coveredNode092 : CovBy 9 PR (Pg cN 9 BS TS) cell183 :=
  branch 0 7 245760 (by decide) (by decide) normalized092 left092 right092 coveredLeaf081 coveredNode093
theorem coveredNode091 : CovBy 9 PR (Pg cN 9 BS TS) cell182 :=
  branch 0 6 229376 (by decide) (by decide) normalized091 left091 right091 coveredNode092 coveredNode099
theorem coveredNode090 : CovBy 9 PR (Pg cN 9 BS TS) cell180 :=
  branch 1 8 245760 (by decide) (by decide) normalized090 left090 right090 coveredLeaf080 coveredNode091
theorem coveredNode089 : CovBy 9 PR (Pg cN 9 BS TS) cell177 :=
  branch 0 9 319488 (by decide) (by decide) normalized089 left089 right089 coveredLeaf079 coveredNode090
theorem coveredNode088 : CovBy 9 PR (Pg cN 9 BS TS) cell175 :=
  branch 3 7 163840 (by decide) (by decide) normalized088 left088 right088 coveredNode089 coveredLeaf092
theorem coveredNode087 : CovBy 9 PR (Pg cN 9 BS TS) cell174 :=
  branch 2 6 163840 (by decide) (by decide) normalized087 left087 right087 coveredNode088 coveredNode101
theorem coveredNode086 : CovBy 9 PR (Pg cN 9 BS TS) cell172 :=
  branch 1 9 278528 (by decide) (by decide) normalized086 left086 right086 coveredLeaf078 coveredNode087
theorem coveredNode085 : CovBy 9 PR (Pg cN 9 BS TS) cell169 :=
  branch 0 8 278528 (by decide) (by decide) normalized085 left085 right085 coveredLeaf077 coveredNode086
theorem coveredNode084 : CovBy 9 PR (Pg cN 9 BS TS) cell167 :=
  branch 2 4 98304 (by decide) (by decide) normalized084 left084 right084 coveredNode085 coveredLeaf097
theorem coveredNode083 : CovBy 9 PR (Pg cN 9 BS TS) cell142 :=
  branch 4 7 114688 (by decide) (by decide) normalized083 left083 right083 coveredNode084 coveredNode104
theorem coveredNode082 : CovBy 9 PR (Pg cN 9 BS TS) cell164 :=
  branch 4 6 81920 (by decide) (by decide) normalized082 left082 right082 coveredLeaf073 coveredLeaf074
theorem coveredNode081 : CovBy 9 PR (Pg cN 9 BS TS) cell161 :=
  branch 0 9 319488 (by decide) (by decide) normalized081 left081 right081 coveredLeaf072 coveredNode082
theorem coveredNode080 : CovBy 9 PR (Pg cN 9 BS TS) cell150 :=
  branch 2 6 163840 (by decide) (by decide) normalized080 left080 right080 coveredNode081 coveredLeaf075
theorem coveredNode079 : CovBy 9 PR (Pg cN 9 BS TS) cell158 :=
  branch 0 6 229376 (by decide) (by decide) normalized079 left079 right079 coveredLeaf069 coveredLeaf070
theorem coveredNode078 : CovBy 9 PR (Pg cN 9 BS TS) cell156 :=
  branch 4 6 81920 (by decide) (by decide) normalized078 left078 right078 coveredLeaf068 coveredNode079
theorem coveredNode077 : CovBy 9 PR (Pg cN 9 BS TS) cell154 :=
  branch 1 8 245760 (by decide) (by decide) normalized077 left077 right077 coveredLeaf067 coveredNode078
theorem coveredNode076 : CovBy 9 PR (Pg cN 9 BS TS) cell151 :=
  branch 0 9 319488 (by decide) (by decide) normalized076 left076 right076 coveredLeaf066 coveredNode077
theorem coveredNode075 : CovBy 9 PR (Pg cN 9 BS TS) cell149 :=
  branch 2 6 163840 (by decide) (by decide) normalized075 left075 right075 coveredNode076 coveredLeaf071
theorem coveredNode074 : CovBy 9 PR (Pg cN 9 BS TS) cell148 :=
  branch 3 7 163840 (by decide) (by decide) normalized074 left074 right074 coveredNode075 coveredNode080
theorem coveredNode073 : CovBy 9 PR (Pg cN 9 BS TS) cell146 :=
  branch 1 9 278528 (by decide) (by decide) normalized073 left073 right073 coveredLeaf065 coveredNode074
theorem coveredNode072 : CovBy 9 PR (Pg cN 9 BS TS) cell143 :=
  branch 0 8 278528 (by decide) (by decide) normalized072 left072 right072 coveredLeaf064 coveredNode073
theorem coveredNode071 : CovBy 9 PR (Pg cN 9 BS TS) cell141 :=
  branch 4 7 131072 (by decide) (by decide) normalized071 left071 right071 coveredNode072 coveredLeaf076
theorem coveredNode070 : CovBy 9 PR (Pg cN 9 BS TS) cell140 :=
  branch 2 5 114688 (by decide) (by decide) normalized070 left070 right070 coveredNode071 coveredNode083
theorem coveredNode069 : CovBy 9 PR (Pg cN 9 BS TS) cell137 :=
  branch 3 6 114688 (by decide) (by decide) normalized069 left069 right069 coveredLeaf063 coveredNode070
theorem coveredNode068 : CovBy 9 PR (Pg cN 9 BS TS) cell135 :=
  branch 4 6 98304 (by decide) (by decide) normalized068 left068 right068 coveredNode069 coveredLeaf125
theorem coveredNode067 : CovBy 9 PR (Pg cN 9 BS TS) cell106 :=
  branch 3 5 98304 (by decide) (by decide) normalized067 left067 right067 coveredNode068 coveredLeaf126
theorem coveredNode066 : CovBy 9 PR (Pg cN 9 BS TS) cell131 :=
  branch 2 4 81920 (by decide) (by decide) normalized066 left066 right066 coveredLeaf057 coveredLeaf058
theorem coveredNode065 : CovBy 9 PR (Pg cN 9 BS TS) cell130 :=
  branch 0 6 229376 (by decide) (by decide) normalized065 left065 right065 coveredNode066 coveredLeaf059
theorem coveredNode064 : CovBy 9 PR (Pg cN 9 BS TS) cell128 :=
  branch 4 6 65536 (by decide) (by decide) normalized064 left064 right064 coveredLeaf056 coveredNode065
theorem coveredNode063 : CovBy 9 PR (Pg cN 9 BS TS) cell126 :=
  branch 3 5 65536 (by decide) (by decide) normalized063 left063 right063 coveredLeaf055 coveredNode064
theorem coveredNode062 : CovBy 9 PR (Pg cN 9 BS TS) cell124 :=
  branch 3 7 131072 (by decide) (by decide) normalized062 left062 right062 coveredLeaf054 coveredNode063
theorem coveredNode061 : CovBy 9 PR (Pg cN 9 BS TS) cell122 :=
  branch 1 8 245760 (by decide) (by decide) normalized061 left061 right061 coveredLeaf053 coveredNode062
theorem coveredNode060 : CovBy 9 PR (Pg cN 9 BS TS) cell120 :=
  branch 0 9 319488 (by decide) (by decide) normalized060 left060 right060 coveredLeaf052 coveredNode061
theorem coveredNode059 : CovBy 9 PR (Pg cN 9 BS TS) cell117 :=
  branch 3 9 196608 (by decide) (by decide) normalized059 left059 right059 coveredLeaf051 coveredNode060
theorem coveredNode058 : CovBy 9 PR (Pg cN 9 BS TS) cell116 :=
  branch 2 6 163840 (by decide) (by decide) normalized058 left058 right058 coveredNode059 coveredLeaf060
theorem coveredNode057 : CovBy 9 PR (Pg cN 9 BS TS) cell114 :=
  branch 1 9 278528 (by decide) (by decide) normalized057 left057 right057 coveredLeaf050 coveredNode058
theorem coveredNode056 : CovBy 9 PR (Pg cN 9 BS TS) cell111 :=
  branch 0 8 278528 (by decide) (by decide) normalized056 left056 right056 coveredLeaf049 coveredNode057
theorem coveredNode055 : CovBy 9 PR (Pg cN 9 BS TS) cell110 :=
  branch 2 4 98304 (by decide) (by decide) normalized055 left055 right055 coveredNode056 coveredLeaf061
theorem coveredNode054 : CovBy 9 PR (Pg cN 9 BS TS) cell107 :=
  branch 2 5 114688 (by decide) (by decide) normalized054 left054 right054 coveredLeaf048 coveredNode055
theorem coveredNode053 : CovBy 9 PR (Pg cN 9 BS TS) cell105 :=
  branch 3 9 212992 (by decide) (by decide) normalized053 left053 right053 coveredNode054 coveredLeaf062
theorem coveredNode052 : CovBy 9 PR (Pg cN 9 BS TS) cell014 :=
  branch 3 7 147456 (by decide) (by decide) normalized052 left052 right052 coveredNode053 coveredNode067
theorem coveredNode051 : CovBy 9 PR (Pg cN 9 BS TS) cell101 :=
  branch 5 7 81920 (by decide) (by decide) normalized051 left051 right051 coveredLeaf042 coveredLeaf043
theorem coveredNode050 : CovBy 9 PR (Pg cN 9 BS TS) cell100 :=
  branch 3 9 229376 (by decide) (by decide) normalized050 left050 right050 coveredNode051 coveredLeaf044
theorem coveredNode049 : CovBy 9 PR (Pg cN 9 BS TS) cell098 :=
  branch 4 6 65536 (by decide) (by decide) normalized049 left049 right049 coveredLeaf041 coveredNode050
theorem coveredNode048 : CovBy 9 PR (Pg cN 9 BS TS) cell096 :=
  branch 3 5 65536 (by decide) (by decide) normalized048 left048 right048 coveredLeaf040 coveredNode049
theorem coveredNode047 : CovBy 9 PR (Pg cN 9 BS TS) cell094 :=
  branch 2 6 131072 (by decide) (by decide) normalized047 left047 right047 coveredLeaf039 coveredNode048
theorem coveredNode046 : CovBy 9 PR (Pg cN 9 BS TS) cell092 :=
  branch 1 8 245760 (by decide) (by decide) normalized046 left046 right046 coveredLeaf038 coveredNode047
theorem coveredNode045 : CovBy 9 PR (Pg cN 9 BS TS) cell090 :=
  branch 0 9 319488 (by decide) (by decide) normalized045 left045 right045 coveredLeaf037 coveredNode046
theorem coveredNode044 : CovBy 9 PR (Pg cN 9 BS TS) cell087 :=
  branch 0 6 196608 (by decide) (by decide) normalized044 left044 right044 coveredLeaf036 coveredNode045
theorem coveredNode043 : CovBy 9 PR (Pg cN 9 BS TS) cell086 :=
  branch 3 7 163840 (by decide) (by decide) normalized043 left043 right043 coveredNode044 coveredLeaf045
theorem coveredNode042 : CovBy 9 PR (Pg cN 9 BS TS) cell084 :=
  branch 1 9 278528 (by decide) (by decide) normalized042 left042 right042 coveredLeaf035 coveredNode043
theorem coveredNode041 : CovBy 9 PR (Pg cN 9 BS TS) cell081 :=
  branch 0 8 278528 (by decide) (by decide) normalized041 left041 right041 coveredLeaf034 coveredNode042
theorem coveredNode040 : CovBy 9 PR (Pg cN 9 BS TS) cell080 :=
  branch 5 7 98304 (by decide) (by decide) normalized040 left040 right040 coveredNode041 coveredLeaf046
theorem coveredNode039 : CovBy 9 PR (Pg cN 9 BS TS) cell077 :=
  branch 4 7 114688 (by decide) (by decide) normalized039 left039 right039 coveredLeaf033 coveredNode040
theorem coveredNode038 : CovBy 9 PR (Pg cN 9 BS TS) cell016 :=
  branch 0 6 212992 (by decide) (by decide) normalized038 left038 right038 coveredNode039 coveredLeaf047
theorem coveredNode037 : CovBy 9 PR (Pg cN 9 BS TS) cell074 :=
  branch 2 9 245760 (by decide) (by decide) normalized037 left037 right037 coveredLeaf029 coveredLeaf030
theorem coveredNode036 : CovBy 9 PR (Pg cN 9 BS TS) cell072 :=
  branch 1 8 245760 (by decide) (by decide) normalized036 left036 right036 coveredLeaf028 coveredNode037
theorem coveredNode035 : CovBy 9 PR (Pg cN 9 BS TS) cell070 :=
  branch 4 6 65536 (by decide) (by decide) normalized035 left035 right035 coveredLeaf027 coveredNode036
theorem coveredNode034 : CovBy 9 PR (Pg cN 9 BS TS) cell068 :=
  branch 3 5 65536 (by decide) (by decide) normalized034 left034 right034 coveredLeaf026 coveredNode035
theorem coveredNode033 : CovBy 9 PR (Pg cN 9 BS TS) cell066 :=
  branch 3 7 131072 (by decide) (by decide) normalized033 left033 right033 coveredLeaf025 coveredNode034
theorem coveredNode032 : CovBy 9 PR (Pg cN 9 BS TS) cell064 :=
  branch 2 6 131072 (by decide) (by decide) normalized032 left032 right032 coveredLeaf024 coveredNode033
theorem coveredNode031 : CovBy 9 PR (Pg cN 9 BS TS) cell062 :=
  branch 0 8 278528 (by decide) (by decide) normalized031 left031 right031 coveredLeaf023 coveredNode032
theorem coveredNode030 : CovBy 9 PR (Pg cN 9 BS TS) cell059 :=
  branch 0 9 319488 (by decide) (by decide) normalized030 left030 right030 coveredLeaf022 coveredNode031
theorem coveredNode029 : CovBy 9 PR (Pg cN 9 BS TS) cell058 :=
  branch 2 7 180224 (by decide) (by decide) normalized029 left029 right029 coveredNode030 coveredLeaf031
theorem coveredNode028 : CovBy 9 PR (Pg cN 9 BS TS) cell055 :=
  branch 1 9 278528 (by decide) (by decide) normalized028 left028 right028 coveredLeaf021 coveredNode029
theorem coveredNode027 : CovBy 9 PR (Pg cN 9 BS TS) cell052 :=
  branch 3 8 180224 (by decide) (by decide) normalized027 left027 right027 coveredNode028 coveredLeaf032
theorem coveredNode026 : CovBy 9 PR (Pg cN 9 BS TS) cell051 :=
  branch 3 8 180224 (by decide) (by decide) normalized026 left026 right026 coveredLeaf019 coveredLeaf020
theorem coveredNode025 : CovBy 9 PR (Pg cN 9 BS TS) cell050 :=
  branch 1 6 180224 (by decide) (by decide) normalized025 left025 right025 coveredNode026 coveredNode027
theorem coveredNode024 : CovBy 9 PR (Pg cN 9 BS TS) cell020 :=
  branch 3 9 196608 (by decide) (by decide) normalized024 left024 right024 coveredLeaf018 coveredNode025
theorem coveredNode023 : CovBy 9 PR (Pg cN 9 BS TS) cell046 :=
  branch 5 8 114688 (by decide) (by decide) normalized023 left023 right023 coveredLeaf015 coveredLeaf016
theorem coveredNode022 : CovBy 9 PR (Pg cN 9 BS TS) cell044 :=
  branch 1 8 245760 (by decide) (by decide) normalized022 left022 right022 coveredLeaf014 coveredNode023
theorem coveredNode021 : CovBy 9 PR (Pg cN 9 BS TS) cell042 :=
  branch 4 6 65536 (by decide) (by decide) normalized021 left021 right021 coveredLeaf013 coveredNode022
theorem coveredNode020 : CovBy 9 PR (Pg cN 9 BS TS) cell040 :=
  branch 3 5 65536 (by decide) (by decide) normalized020 left020 right020 coveredLeaf012 coveredNode021
theorem coveredNode019 : CovBy 9 PR (Pg cN 9 BS TS) cell038 :=
  branch 2 6 131072 (by decide) (by decide) normalized019 left019 right019 coveredLeaf011 coveredNode020
theorem coveredNode018 : CovBy 9 PR (Pg cN 9 BS TS) cell035 :=
  branch 1 9 278528 (by decide) (by decide) normalized018 left018 right018 coveredLeaf010 coveredNode019
theorem coveredNode017 : CovBy 9 PR (Pg cN 9 BS TS) cell034 :=
  branch 2 7 180224 (by decide) (by decide) normalized017 left017 right017 coveredNode018 coveredLeaf017
theorem coveredNode016 : CovBy 9 PR (Pg cN 9 BS TS) cell032 :=
  branch 0 9 319488 (by decide) (by decide) normalized016 left016 right016 coveredLeaf009 coveredNode017
theorem coveredNode015 : CovBy 9 PR (Pg cN 9 BS TS) cell030 :=
  branch 0 6 196608 (by decide) (by decide) normalized015 left015 right015 coveredLeaf008 coveredNode016
theorem coveredNode014 : CovBy 9 PR (Pg cN 9 BS TS) cell026 :=
  branch 0 8 278528 (by decide) (by decide) normalized014 left014 right014 coveredLeaf007 coveredNode015
theorem coveredNode013 : CovBy 9 PR (Pg cN 9 BS TS) cell025 :=
  branch 0 8 278528 (by decide) (by decide) normalized013 left013 right013 coveredLeaf005 coveredLeaf006
theorem coveredNode012 : CovBy 9 PR (Pg cN 9 BS TS) cell024 :=
  branch 3 8 180224 (by decide) (by decide) normalized012 left012 right012 coveredNode013 coveredNode014
theorem coveredNode011 : CovBy 9 PR (Pg cN 9 BS TS) cell022 :=
  branch 3 9 212992 (by decide) (by decide) normalized011 left011 right011 coveredLeaf004 coveredNode012
theorem coveredNode010 : CovBy 9 PR (Pg cN 9 BS TS) cell019 :=
  branch 0 7 229376 (by decide) (by decide) normalized010 left010 right010 coveredLeaf003 coveredNode011
theorem coveredNode009 : CovBy 9 PR (Pg cN 9 BS TS) cell018 :=
  branch 0 6 212992 (by decide) (by decide) normalized009 left009 right009 coveredNode010 coveredNode024
theorem coveredNode008 : CovBy 9 PR (Pg cN 9 BS TS) cell015 :=
  branch 1 8 229376 (by decide) (by decide) normalized008 left008 right008 coveredLeaf002 coveredNode009
theorem coveredNode007 : CovBy 9 PR (Pg cN 9 BS TS) cell013 :=
  branch 3 7 147456 (by decide) (by decide) normalized007 left007 right007 coveredNode008 coveredNode038
theorem coveredNode006 : CovBy 9 PR (Pg cN 9 BS TS) cell012 :=
  branch 2 6 147456 (by decide) (by decide) normalized006 left006 right006 coveredNode007 coveredNode052
theorem coveredNode005 : CovBy 9 PR (Pg cN 9 BS TS) cell010 :=
  branch 1 9 262144 (by decide) (by decide) normalized005 left005 right005 coveredLeaf001 coveredNode006
theorem coveredNode004 : CovBy 9 PR (Pg cN 9 BS TS) cell007 :=
  branch 0 8 262144 (by decide) (by decide) normalized004 left004 right004 coveredLeaf000 coveredNode005
theorem selected_covered : CovBy 9 PR (Pg cN 9 BS TS) selectedCell := coveredNode004
theorem root_covered_of_siblings
    (sibling000 : CovBy 9 PR (Pg cN 9 BS TS) cell002)
    (sibling001 : CovBy 9 PR (Pg cN 9 BS TS) cell004)
    (sibling002 : CovBy 9 PR (Pg cN 9 BS TS) cell005)
    (sibling003 : CovBy 9 PR (Pg cN 9 BS TS) cell008)
    : CovBy 9 PR (Pg cN 9 BS TS) RootBounds.initialCell := by
  have route003 : CovBy 9 PR (Pg cN 9 BS TS) cell006 :=
    branch 0 9 327680 (by decide) (by decide) normalized003 left003 right003 coveredNode004 sibling003
  have route002 : CovBy 9 PR (Pg cN 9 BS TS) cell003 :=
    branch 0 9 311296 (by decide) (by decide) normalized002 left002 right002 sibling002 route003
  have route001 : CovBy 9 PR (Pg cN 9 BS TS) cell001 :=
    branch 0 9 360448 (by decide) (by decide) normalized001 left001 right001 route002 sibling001
  have route000 : CovBy 9 PR (Pg cN 9 BS TS) cell000 :=
    branch 0 9 458752 (by decide) (by decide) normalized000 left000 right000 route001 sibling000
  simpa only [root_eq] using route000

set_option pp.fullNames true
#print axioms selected_covered
#print axioms root_covered_of_siblings
end StructuralGoal20261016.W10Aux127
end
