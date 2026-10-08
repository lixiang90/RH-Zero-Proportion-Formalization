import RecordProportion.FiniteCertificateData
import RecordProportion.FloydSoundness

/- Complete physical-pair coverage of the fixed captured cells.
All finite checks use kernel reduction; continuous exclusion uses real potentials. -/
noncomputable section

namespace RHWeilRecord.GeometryCoverage
open RHWeil.RecordSubmission.FiniteCertificateData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

 def initialBounds (left right : Nat) : Array Int :=
  ((List.range 81).map fun slot => primitiveBound left right (slot/9) (slot%9)).toArray

@[simp] theorem initialBounds_entry (left right i j : Nat) (hi : i < 9) (hj : j < 9) :
    ((initialBounds left right)[9*i+j]?).getD 0 = primitiveBound left right i j := by
  have hs : 9*i+j < 81 := by omega
  have hd : (9*i+j)/9=i := by omega
  have hm : (9*i+j)%9=j := by omega
  simp [initialBounds, hs, hd, hm]

theorem pairClosure_eq (left right : Nat) :
    pairClosure left right = FloydSoundness.closure (initialBounds left right) := rfl

-- Closed leaves share their actual data expressions instead of repeatedly traversing cells.
def fastOriginalCellWord (l : Nat) : Nat :=
  let c := fun i => (cellPacket i).1
  (if l<120 then (if l<60 then (if l<30 then (if l<15 then (if l<7 then (if l<3 then (if l<1 then c 0 else (if l<2 then c 1 else c 2)) else (if l<5 then (if l<4 then c 3 else c 4) else (if l<6 then c 5 else c 6))) else (if l<11 then (if l<9 then (if l<8 then c 7 else c 8) else (if l<10 then c 9 else c 10)) else (if l<13 then (if l<12 then c 11 else c 12) else (if l<14 then c 13 else c 14)))) else (if l<22 then (if l<18 then (if l<16 then c 15 else (if l<17 then c 16 else c 17)) else (if l<20 then (if l<19 then c 18 else c 19) else (if l<21 then c 20 else c 21))) else (if l<26 then (if l<24 then (if l<23 then c 22 else c 23) else (if l<25 then c 24 else c 25)) else (if l<28 then (if l<27 then c 26 else c 27) else (if l<29 then c 28 else c 29))))) else (if l<45 then (if l<37 then (if l<33 then (if l<31 then c 30 else (if l<32 then c 31 else c 32)) else (if l<35 then (if l<34 then c 33 else c 34) else (if l<36 then c 35 else c 36))) else (if l<41 then (if l<39 then (if l<38 then c 37 else c 38) else (if l<40 then c 39 else c 40)) else (if l<43 then (if l<42 then c 41 else c 42) else (if l<44 then c 43 else c 44)))) else (if l<52 then (if l<48 then (if l<46 then c 45 else (if l<47 then c 46 else c 47)) else (if l<50 then (if l<49 then c 48 else c 49) else (if l<51 then c 50 else c 51))) else (if l<56 then (if l<54 then (if l<53 then c 52 else c 53) else (if l<55 then c 54 else c 55)) else (if l<58 then (if l<57 then c 56 else c 57) else (if l<59 then c 58 else c 59)))))) else (if l<90 then (if l<75 then (if l<67 then (if l<63 then (if l<61 then c 60 else (if l<62 then c 61 else c 62)) else (if l<65 then (if l<64 then c 63 else c 64) else (if l<66 then c 65 else c 66))) else (if l<71 then (if l<69 then (if l<68 then c 67 else c 68) else (if l<70 then c 69 else c 70)) else (if l<73 then (if l<72 then c 71 else c 72) else (if l<74 then c 73 else c 74)))) else (if l<82 then (if l<78 then (if l<76 then c 75 else (if l<77 then c 76 else c 77)) else (if l<80 then (if l<79 then c 78 else c 79) else (if l<81 then c 80 else c 81))) else (if l<86 then (if l<84 then (if l<83 then c 82 else c 83) else (if l<85 then c 84 else c 85)) else (if l<88 then (if l<87 then c 86 else c 87) else (if l<89 then c 88 else c 89))))) else (if l<105 then (if l<97 then (if l<93 then (if l<91 then c 90 else (if l<92 then c 91 else c 92)) else (if l<95 then (if l<94 then c 93 else c 94) else (if l<96 then c 95 else c 96))) else (if l<101 then (if l<99 then (if l<98 then c 97 else c 98) else (if l<100 then c 99 else c 100)) else (if l<103 then (if l<102 then c 101 else c 102) else (if l<104 then c 103 else c 104)))) else (if l<112 then (if l<108 then (if l<106 then c 105 else (if l<107 then c 106 else c 107)) else (if l<110 then (if l<109 then c 108 else c 109) else (if l<111 then c 110 else c 111))) else (if l<116 then (if l<114 then (if l<113 then c 112 else c 113) else (if l<115 then c 114 else c 115)) else (if l<118 then (if l<117 then c 116 else c 117) else (if l<119 then c 118 else c 119))))))) else (if l<180 then (if l<150 then (if l<135 then (if l<127 then (if l<123 then (if l<121 then c 120 else (if l<122 then c 121 else c 122)) else (if l<125 then (if l<124 then c 123 else c 124) else (if l<126 then c 125 else c 126))) else (if l<131 then (if l<129 then (if l<128 then c 127 else c 128) else (if l<130 then c 129 else c 130)) else (if l<133 then (if l<132 then c 131 else c 132) else (if l<134 then c 133 else c 134)))) else (if l<142 then (if l<138 then (if l<136 then c 135 else (if l<137 then c 136 else c 137)) else (if l<140 then (if l<139 then c 138 else c 139) else (if l<141 then c 140 else c 141))) else (if l<146 then (if l<144 then (if l<143 then c 142 else c 143) else (if l<145 then c 144 else c 145)) else (if l<148 then (if l<147 then c 146 else c 147) else (if l<149 then c 148 else c 149))))) else (if l<165 then (if l<157 then (if l<153 then (if l<151 then c 150 else (if l<152 then c 151 else c 152)) else (if l<155 then (if l<154 then c 153 else c 154) else (if l<156 then c 155 else c 156))) else (if l<161 then (if l<159 then (if l<158 then c 157 else c 158) else (if l<160 then c 159 else c 160)) else (if l<163 then (if l<162 then c 161 else c 162) else (if l<164 then c 163 else c 164)))) else (if l<172 then (if l<168 then (if l<166 then c 165 else (if l<167 then c 166 else c 167)) else (if l<170 then (if l<169 then c 168 else c 169) else (if l<171 then c 170 else c 171))) else (if l<176 then (if l<174 then (if l<173 then c 172 else c 173) else (if l<175 then c 174 else c 175)) else (if l<178 then (if l<177 then c 176 else c 177) else (if l<179 then c 178 else c 179)))))) else (if l<210 then (if l<195 then (if l<187 then (if l<183 then (if l<181 then c 180 else (if l<182 then c 181 else c 182)) else (if l<185 then (if l<184 then c 183 else c 184) else (if l<186 then c 185 else c 186))) else (if l<191 then (if l<189 then (if l<188 then c 187 else c 188) else (if l<190 then c 189 else c 190)) else (if l<193 then (if l<192 then c 191 else c 192) else (if l<194 then c 193 else c 194)))) else (if l<202 then (if l<198 then (if l<196 then c 195 else (if l<197 then c 196 else c 197)) else (if l<200 then (if l<199 then c 198 else c 199) else (if l<201 then c 200 else c 201))) else (if l<206 then (if l<204 then (if l<203 then c 202 else c 203) else (if l<205 then c 204 else c 205)) else (if l<208 then (if l<207 then c 206 else c 207) else (if l<209 then c 208 else c 209))))) else (if l<225 then (if l<217 then (if l<213 then (if l<211 then c 210 else (if l<212 then c 211 else c 212)) else (if l<215 then (if l<214 then c 213 else c 214) else (if l<216 then c 215 else c 216))) else (if l<221 then (if l<219 then (if l<218 then c 217 else c 218) else (if l<220 then c 219 else c 220)) else (if l<223 then (if l<222 then c 221 else c 222) else (if l<224 then c 223 else c 224)))) else (if l<233 then (if l<229 then (if l<227 then (if l<226 then c 225 else c 226) else (if l<228 then c 227 else c 228)) else (if l<231 then (if l<230 then c 229 else c 230) else (if l<232 then c 231 else c 232))) else (if l<237 then (if l<235 then (if l<234 then c 233 else c 234) else (if l<236 then c 235 else c 236)) else (if l<239 then (if l<238 then c 237 else c 238) else (if l<240 then c 239 else c 240))))))))

def fastCellWord (label : Nat) : Nat :=
  fastOriginalCellWord (if label < 241 then label else label-241)

def fastCellBound (label i j side : Nat) : Nat :=
  let pos := if label < 241 then geometrySlot i j else geometrySlot (7-j) (7-i)
  bits (fastCellWord label) (22*(pos+side)) 22

def sharedSpans : List (Nat × Nat) :=
  (List.range 6).flatMap fun i => (List.range (6-i)).map fun k => (i,i+k+1)

def sharedSpanCheck (left right i j : Nat) : Bool :=
  decide (fastCellBound left (i+1) (j+1) 0 ≤ fastCellBound right i j 1) &&
  decide (fastCellBound right i j 0 ≤ fastCellBound left (i+1) (j+1) 1)

def sharedOverlapCheck (left right : Nat) : Bool :=
  sharedSpans.all fun ij => sharedSpanCheck left right ij.1 ij.2

/-- Twelve bounded comparisons are only a search hint. The equality guard below
checks the actual packed label, so no sorting premise is needed for soundness. -/
def candidateIndex (left right : Nat) : Nat :=
  ((List.range 12).foldl (fun state _ =>
    let mid := (state.1+state.2)/2
    let label := pairLabelAt mid
    if label%512 < left ∨ (label%512=left ∧ label/512 < right)
      then (mid+1,state.2) else (state.1,mid)) (0,2399)).1

def negativeDiagCheck (left right : Nat) : Bool :=
  (List.range 9).any fun i => decide (((pairClosure left right)[9*i+i]?).getD 0 < 0)

def geometryCheck (left right : Nat) : Bool :=
  if sharedOverlapCheck left right then
    let k := candidateIndex left right
    if k < 2399 ∧ pairLabelAt k = pairLabel left right then true
    else negativeDiagCheck left right
  else true

def geometryBlockCheck (block : Nat) : Bool :=
  (List.range 8).all fun offset =>
    let left := 8*block+offset
    if left < 482 then (List.range 482).all fun right => geometryCheck left right
    else true

theorem geometry_block_0 : geometryBlockCheck 0 = true := by decide +kernel
theorem geometry_block_1 : geometryBlockCheck 1 = true := by decide +kernel
theorem geometry_block_2 : geometryBlockCheck 2 = true := by decide +kernel
theorem geometry_block_3 : geometryBlockCheck 3 = true := by decide +kernel
theorem geometry_block_4 : geometryBlockCheck 4 = true := by decide +kernel
theorem geometry_block_5 : geometryBlockCheck 5 = true := by decide +kernel
theorem geometry_block_6 : geometryBlockCheck 6 = true := by decide +kernel
theorem geometry_block_7 : geometryBlockCheck 7 = true := by decide +kernel
theorem geometry_block_8 : geometryBlockCheck 8 = true := by decide +kernel
theorem geometry_block_9 : geometryBlockCheck 9 = true := by decide +kernel
theorem geometry_block_10 : geometryBlockCheck 10 = true := by decide +kernel
theorem geometry_block_11 : geometryBlockCheck 11 = true := by decide +kernel
theorem geometry_block_12 : geometryBlockCheck 12 = true := by decide +kernel
theorem geometry_block_13 : geometryBlockCheck 13 = true := by decide +kernel
theorem geometry_block_14 : geometryBlockCheck 14 = true := by decide +kernel
theorem geometry_block_15 : geometryBlockCheck 15 = true := by decide +kernel
theorem geometry_block_16 : geometryBlockCheck 16 = true := by decide +kernel
theorem geometry_block_17 : geometryBlockCheck 17 = true := by decide +kernel
theorem geometry_block_18 : geometryBlockCheck 18 = true := by decide +kernel
theorem geometry_block_19 : geometryBlockCheck 19 = true := by decide +kernel
theorem geometry_block_20 : geometryBlockCheck 20 = true := by decide +kernel
theorem geometry_block_21 : geometryBlockCheck 21 = true := by decide +kernel
theorem geometry_block_22 : geometryBlockCheck 22 = true := by decide +kernel
theorem geometry_block_23 : geometryBlockCheck 23 = true := by decide +kernel
theorem geometry_block_24 : geometryBlockCheck 24 = true := by decide +kernel
theorem geometry_block_25 : geometryBlockCheck 25 = true := by decide +kernel
theorem geometry_block_26 : geometryBlockCheck 26 = true := by decide +kernel
theorem geometry_block_27 : geometryBlockCheck 27 = true := by decide +kernel
theorem geometry_block_28 : geometryBlockCheck 28 = true := by decide +kernel
theorem geometry_block_29 : geometryBlockCheck 29 = true := by decide +kernel
theorem geometry_block_30 : geometryBlockCheck 30 = true := by decide +kernel
theorem geometry_block_31 : geometryBlockCheck 31 = true := by decide +kernel
theorem geometry_block_32 : geometryBlockCheck 32 = true := by decide +kernel
theorem geometry_block_33 : geometryBlockCheck 33 = true := by decide +kernel
theorem geometry_block_34 : geometryBlockCheck 34 = true := by decide +kernel
theorem geometry_block_35 : geometryBlockCheck 35 = true := by decide +kernel
theorem geometry_block_36 : geometryBlockCheck 36 = true := by decide +kernel
theorem geometry_block_37 : geometryBlockCheck 37 = true := by decide +kernel
theorem geometry_block_38 : geometryBlockCheck 38 = true := by decide +kernel
theorem geometry_block_39 : geometryBlockCheck 39 = true := by decide +kernel
theorem geometry_block_40 : geometryBlockCheck 40 = true := by decide +kernel
theorem geometry_block_41 : geometryBlockCheck 41 = true := by decide +kernel
theorem geometry_block_42 : geometryBlockCheck 42 = true := by decide +kernel
theorem geometry_block_43 : geometryBlockCheck 43 = true := by decide +kernel
theorem geometry_block_44 : geometryBlockCheck 44 = true := by decide +kernel
theorem geometry_block_45 : geometryBlockCheck 45 = true := by decide +kernel
theorem geometry_block_46 : geometryBlockCheck 46 = true := by decide +kernel
theorem geometry_block_47 : geometryBlockCheck 47 = true := by decide +kernel
theorem geometry_block_48 : geometryBlockCheck 48 = true := by decide +kernel
theorem geometry_block_49 : geometryBlockCheck 49 = true := by decide +kernel
theorem geometry_block_50 : geometryBlockCheck 50 = true := by decide +kernel
theorem geometry_block_51 : geometryBlockCheck 51 = true := by decide +kernel
theorem geometry_block_52 : geometryBlockCheck 52 = true := by decide +kernel
theorem geometry_block_53 : geometryBlockCheck 53 = true := by decide +kernel
theorem geometry_block_54 : geometryBlockCheck 54 = true := by decide +kernel
theorem geometry_block_55 : geometryBlockCheck 55 = true := by decide +kernel
theorem geometry_block_56 : geometryBlockCheck 56 = true := by decide +kernel
theorem geometry_block_57 : geometryBlockCheck 57 = true := by decide +kernel
theorem geometry_block_58 : geometryBlockCheck 58 = true := by decide +kernel
theorem geometry_block_59 : geometryBlockCheck 59 = true := by decide +kernel
theorem geometry_block_60 : geometryBlockCheck 60 = true := by decide +kernel

theorem geometry_block_checked (block : Nat) (hb : block < 61) :
    geometryBlockCheck block = true := by
  match block with
  | 0 => exact geometry_block_0
  | 1 => exact geometry_block_1
  | 2 => exact geometry_block_2
  | 3 => exact geometry_block_3
  | 4 => exact geometry_block_4
  | 5 => exact geometry_block_5
  | 6 => exact geometry_block_6
  | 7 => exact geometry_block_7
  | 8 => exact geometry_block_8
  | 9 => exact geometry_block_9
  | 10 => exact geometry_block_10
  | 11 => exact geometry_block_11
  | 12 => exact geometry_block_12
  | 13 => exact geometry_block_13
  | 14 => exact geometry_block_14
  | 15 => exact geometry_block_15
  | 16 => exact geometry_block_16
  | 17 => exact geometry_block_17
  | 18 => exact geometry_block_18
  | 19 => exact geometry_block_19
  | 20 => exact geometry_block_20
  | 21 => exact geometry_block_21
  | 22 => exact geometry_block_22
  | 23 => exact geometry_block_23
  | 24 => exact geometry_block_24
  | 25 => exact geometry_block_25
  | 26 => exact geometry_block_26
  | 27 => exact geometry_block_27
  | 28 => exact geometry_block_28
  | 29 => exact geometry_block_29
  | 30 => exact geometry_block_30
  | 31 => exact geometry_block_31
  | 32 => exact geometry_block_32
  | 33 => exact geometry_block_33
  | 34 => exact geometry_block_34
  | 35 => exact geometry_block_35
  | 36 => exact geometry_block_36
  | 37 => exact geometry_block_37
  | 38 => exact geometry_block_38
  | 39 => exact geometry_block_39
  | 40 => exact geometry_block_40
  | 41 => exact geometry_block_41
  | 42 => exact geometry_block_42
  | 43 => exact geometry_block_43
  | 44 => exact geometry_block_44
  | 45 => exact geometry_block_45
  | 46 => exact geometry_block_46
  | 47 => exact geometry_block_47
  | 48 => exact geometry_block_48
  | 49 => exact geometry_block_49
  | 50 => exact geometry_block_50
  | 51 => exact geometry_block_51
  | 52 => exact geometry_block_52
  | 53 => exact geometry_block_53
  | 54 => exact geometry_block_54
  | 55 => exact geometry_block_55
  | 56 => exact geometry_block_56
  | 57 => exact geometry_block_57
  | 58 => exact geometry_block_58
  | 59 => exact geometry_block_59
  | 60 => exact geometry_block_60
  | n + 61 => omega

-- PROOFS

theorem fastOriginalCellWord_eq (label : Nat) (hl : label < 241) :
    fastOriginalCellWord label = (cellPacket label).1 := by
  match label with |0=>rfl |1=>rfl |2=>rfl |3=>rfl |4=>rfl |5=>rfl |6=>rfl |7=>rfl |8=>rfl |9=>rfl |10=>rfl |11=>rfl |12=>rfl |13=>rfl |14=>rfl |15=>rfl |16=>rfl |17=>rfl |18=>rfl |19=>rfl |20=>rfl |21=>rfl |22=>rfl |23=>rfl |24=>rfl |25=>rfl |26=>rfl |27=>rfl |28=>rfl |29=>rfl |30=>rfl |31=>rfl |32=>rfl |33=>rfl |34=>rfl |35=>rfl |36=>rfl |37=>rfl |38=>rfl |39=>rfl |40=>rfl |41=>rfl |42=>rfl |43=>rfl |44=>rfl |45=>rfl |46=>rfl |47=>rfl |48=>rfl |49=>rfl |50=>rfl |51=>rfl |52=>rfl |53=>rfl |54=>rfl |55=>rfl |56=>rfl |57=>rfl |58=>rfl |59=>rfl |60=>rfl |61=>rfl |62=>rfl |63=>rfl |64=>rfl |65=>rfl |66=>rfl |67=>rfl |68=>rfl |69=>rfl |70=>rfl |71=>rfl |72=>rfl |73=>rfl |74=>rfl |75=>rfl |76=>rfl |77=>rfl |78=>rfl |79=>rfl |80=>rfl |81=>rfl |82=>rfl |83=>rfl |84=>rfl |85=>rfl |86=>rfl |87=>rfl |88=>rfl |89=>rfl |90=>rfl |91=>rfl |92=>rfl |93=>rfl |94=>rfl |95=>rfl |96=>rfl |97=>rfl |98=>rfl |99=>rfl |100=>rfl |101=>rfl |102=>rfl |103=>rfl |104=>rfl |105=>rfl |106=>rfl |107=>rfl |108=>rfl |109=>rfl |110=>rfl |111=>rfl |112=>rfl |113=>rfl |114=>rfl |115=>rfl |116=>rfl |117=>rfl |118=>rfl |119=>rfl |120=>rfl |121=>rfl |122=>rfl |123=>rfl |124=>rfl |125=>rfl |126=>rfl |127=>rfl |128=>rfl |129=>rfl |130=>rfl |131=>rfl |132=>rfl |133=>rfl |134=>rfl |135=>rfl |136=>rfl |137=>rfl |138=>rfl |139=>rfl |140=>rfl |141=>rfl |142=>rfl |143=>rfl |144=>rfl |145=>rfl |146=>rfl |147=>rfl |148=>rfl |149=>rfl |150=>rfl |151=>rfl |152=>rfl |153=>rfl |154=>rfl |155=>rfl |156=>rfl |157=>rfl |158=>rfl |159=>rfl |160=>rfl |161=>rfl |162=>rfl |163=>rfl |164=>rfl |165=>rfl |166=>rfl |167=>rfl |168=>rfl |169=>rfl |170=>rfl |171=>rfl |172=>rfl |173=>rfl |174=>rfl |175=>rfl |176=>rfl |177=>rfl |178=>rfl |179=>rfl |180=>rfl |181=>rfl |182=>rfl |183=>rfl |184=>rfl |185=>rfl |186=>rfl |187=>rfl |188=>rfl |189=>rfl |190=>rfl |191=>rfl |192=>rfl |193=>rfl |194=>rfl |195=>rfl |196=>rfl |197=>rfl |198=>rfl |199=>rfl |200=>rfl |201=>rfl |202=>rfl |203=>rfl |204=>rfl |205=>rfl |206=>rfl |207=>rfl |208=>rfl |209=>rfl |210=>rfl |211=>rfl |212=>rfl |213=>rfl |214=>rfl |215=>rfl |216=>rfl |217=>rfl |218=>rfl |219=>rfl |220=>rfl |221=>rfl |222=>rfl |223=>rfl |224=>rfl |225=>rfl |226=>rfl |227=>rfl |228=>rfl |229=>rfl |230=>rfl |231=>rfl |232=>rfl |233=>rfl |234=>rfl |235=>rfl |236=>rfl |237=>rfl |238=>rfl |239=>rfl |240=>rfl |n+241 => omega

theorem fastCellWord_eq (label : Nat) (hl : label < 482) :
    fastCellWord label = (cellPacket label).1 := by
  by_cases h : label < 241
  · simp only [fastCellWord,if_pos h]
    exact fastOriginalCellWord_eq label h
  · have hs : label-241 < 241 := by omega
    simp only [fastCellWord,if_neg h]
    rw [fastOriginalCellWord_eq (label-241) hs]
    simp only [cellPacket,if_pos hs,if_neg h]

theorem fastCellBound_eq (label i j side : Nat) (hl : label < 482) :
    fastCellBound label i j side = cellBound label i j side := by
  simp only [fastCellBound,cellBound,fastCellWord_eq label hl]



theorem primitive_le_first (left right i j : Nat) (hne : i ≠ j) :
    primitiveBound left right i j ≤
      (if i ≤ 7 ∧ j ≤ 7 then
        if i < j then 5*(cellUpper left i j : Int) else -5*(cellLower left j i : Int)
       else 1000000000000000000000000000000) := by
  unfold primitiveBound
  simp only [if_neg hne]
  by_cases h : i = j+1
  · simp only [if_pos h]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  · simp only [if_neg h]
    exact min_le_left _ _

theorem primitive_le_second (left right i j : Nat) (hne : i ≠ j) :
    primitiveBound left right i j ≤
      (if 1 ≤ i ∧ 1 ≤ j then
        if i < j then 5*(cellUpper right (i-1) (j-1) : Int)
        else -5*(cellLower right (j-1) (i-1) : Int)
       else 1000000000000000000000000000000) := by
  unfold primitiveBound
  simp only [if_neg hne]
  by_cases h : i = j+1
  · simp only [if_pos h]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  · simp only [if_neg h]
    exact min_le_right _ _

theorem sharedSpanCheck_of_potential {p : Nat → ℝ} {left right : Nat}
    (hl : left < 482) (hr : right < 482)
    (hp : FloydSoundness.RealPotentialBound p (initialBounds left right))
    {i j : Nat} (hij : i < j) (hj : j ≤ 6) : sharedSpanCheck left right i j = true := by
  have hip : i+1 < 9 := by omega
  have hjp : j+1 < 9 := by omega
  have hrev := hp (j+1) hjp (i+1) hip
  have hfwd := hp (i+1) hip (j+1) hjp
  rw [initialBounds_entry left right (j+1) (i+1) hjp hip] at hrev
  rw [initialBounds_entry left right (i+1) (j+1) hip hjp] at hfwd
  have hlf := primitive_le_first left right (j+1) (i+1) (by omega)
  have huf := primitive_le_first left right (i+1) (j+1) (by omega)
  have hlr := primitive_le_second left right (j+1) (i+1) (by omega)
  have hur := primitive_le_second left right (i+1) (j+1) (by omega)
  simp only [show j+1 ≤ 7 ∧ i+1 ≤ 7 by omega,
    show 1 ≤ j+1 ∧ 1 ≤ i+1 by omega,
    if_pos, show ¬j+1 < i+1 by omega, show i+1 < j+1 by omega,
    Nat.add_sub_cancel] at hlf huf hlr hur
  have hlfR : (primitiveBound left right (j+1) (i+1) : ℝ) ≤
      -5*(cellLower left (i+1) (j+1) : ℝ) := by exact_mod_cast hlf
  have hurR : (primitiveBound left right (i+1) (j+1) : ℝ) ≤
      5*(cellUpper right i j : ℝ) := by exact_mod_cast hur
  have hlrR : (primitiveBound left right (j+1) (i+1) : ℝ) ≤
      -5*(cellLower right i j : ℝ) := by exact_mod_cast hlr
  have hufR : (primitiveBound left right (i+1) (j+1) : ℝ) ≤
      5*(cellUpper left (i+1) (j+1) : ℝ) := by exact_mod_cast huf
  have h1 : (cellLower left (i+1) (j+1) : ℝ) ≤ (cellUpper right i j : ℝ) := by linarith
  have h2 : (cellLower right i j : ℝ) ≤ (cellUpper left (i+1) (j+1) : ℝ) := by linarith
  have h1N : cellLower left (i+1) (j+1) ≤ cellUpper right i j := by exact_mod_cast h1
  have h2N : cellLower right i j ≤ cellUpper left (i+1) (j+1) := by exact_mod_cast h2
  simp only [sharedSpanCheck,fastCellBound_eq left _ _ _ hl,fastCellBound_eq right _ _ _ hr]
  change (decide (cellLower left (i+1) (j+1) ≤ cellUpper right i j) &&
    decide (cellLower right i j ≤ cellUpper left (i+1) (j+1))) = true
  simp only [h1N,h2N,decide_true,Bool.and_self]

theorem sharedOverlapCheck_of_potential {p : Nat → ℝ} {left right : Nat}
    (hl : left < 482) (hr : right < 482)
    (hp : FloydSoundness.RealPotentialBound p (initialBounds left right)) :
    sharedOverlapCheck left right = true := by
  apply List.all_eq_true.mpr
  intro ij hij
  simp only [sharedSpans, List.mem_flatMap, List.mem_range, List.mem_map] at hij
  obtain ⟨i,hi,k,hk,heq⟩ := hij
  subst ij
  exact sharedSpanCheck_of_potential hl hr hp (by omega) (by omega)

theorem negativeDiagCheck_false {p : Nat → ℝ} {left right : Nat}
    (hp : FloydSoundness.RealPotentialBound p (initialBounds left right)) :
    negativeDiagCheck left right = false := by
  have hclosed := FloydSoundness.closure_real_preserves hp
  rw [← pairClosure_eq] at hclosed
  apply Bool.eq_false_iff.mpr
  intro hneg
  obtain ⟨i,hi,hbad⟩ := List.any_eq_true.mp hneg
  have hi9 := List.mem_range.mp hi
  have h0 := hclosed i hi9 i hi9
  have hb : ((pairClosure left right)[9*i+i]?).getD 0 < 0 := by simpa using hbad
  have hbR : (((pairClosure left right)[9*i+i]?).getD 0 : ℝ) < 0 := by exact_mod_cast hb
  linarith


/-- All 482² label pairs are checked, including every pair absent from the table. -/
theorem geometry_checked (left right : Nat) (hl : left < 482) (hr : right < 482) :
    geometryCheck left right = true := by
  have hb := geometry_block_checked (left/8) (by omega)
  have ho : left%8 ∈ List.range 8 := List.mem_range.mpr (by omega)
  have he : 8*(left/8)+left%8=left := by omega
  have row := List.all_eq_true.mp hb (left%8) ho
  simp only [he, if_pos hl] at row
  exact List.all_eq_true.mp row right (List.mem_range.mpr hr)

/-- A genuine continuous potential rules out both finite rejection mechanisms.
The returned equality is with the actual packed table, not a search abstraction. -/
theorem physical_pair_covered {p : Nat → ℝ} {left right : Nat}
    (hl : left < 482) (hr : right < 482)
    (hp : FloydSoundness.RealPotentialBound p (initialBounds left right)) :
    ∃ index < 2399, pairLabelAt index = pairLabel left right := by
  have hc := geometry_checked left right hl hr
  have hs := sharedOverlapCheck_of_potential hl hr hp
  have hn := negativeDiagCheck_false hp
  by_cases h : candidateIndex left right < 2399 ∧
      pairLabelAt (candidateIndex left right) = pairLabel left right
  · exact ⟨candidateIndex left right,h.1,h.2⟩
  · simp [geometryCheck,hs,h,hn] at hc

theorem bits_nine_eq (word offset : Nat) :
    bits word offset 9 = (word / 2^offset) % 512 := by
  simp only [bits, Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem pairLabel_lower {left right : Nat} (hl : left < 482) :
    bits (pairLabel left right) 0 9 = left := by
  rw [bits_nine_eq]
  simp only [pairLabel, Nat.shiftLeft_eq]
  norm_num
  omega

theorem pairLabel_upper {left right : Nat} (hl : left < 482) (hr : right < 482) :
    bits (pairLabel left right) 9 9 = right := by
  rw [bits_nine_eq]
  simp only [pairLabel, Nat.shiftLeft_eq]
  norm_num
  omega

theorem pairLabel_injective {left right left' right' : Nat}
    (hl : left < 482) (hr : right < 482)
    (hl' : left' < 482) (hr' : right' < 482)
    (h : pairLabel left right = pairLabel left' right') :
    left = left' ∧ right = right' := by
  constructor
  · have he := congrArg (fun x => bits x 0 9) h
    simpa only [pairLabel_lower hl, pairLabel_lower hl'] using he
  · have he := congrArg (fun x => bits x 9 9) h
    simpa only [pairLabel_upper hl hr, pairLabel_upper hl' hr'] using he

theorem reflectedPair_pairLabel {left right : Nat}
    (hl : left < 482) (hr : right < 482) :
    reflectedPair (pairLabel left right) =
      pairLabel (reflectionLabel right) (reflectionLabel left) := by
  simp only [reflectedPair, pairLabel_lower hl, pairLabel_upper hl hr]


end RHWeilRecord.GeometryCoverage

#print axioms RHWeilRecord.GeometryCoverage.physical_pair_covered

#print axioms RHWeilRecord.GeometryCoverage.pairLabel_lower

#print axioms RHWeilRecord.GeometryCoverage.pairLabel_upper

#print axioms RHWeilRecord.GeometryCoverage.pairLabel_injective

#print axioms RHWeilRecord.GeometryCoverage.reflectedPair_pairLabel
