import RecordProportion.NinthSpanPoints

namespace RHWeil.RecordSubmission.JointFramePairPoints
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option stderrAsMessages false
set_option Elab.async false

/-- The original 541-entry proved catalog is preserved; only 180 new entries are added. -/
def extraCatalog : Array (Nat × Nat) := #[
  (30720,41894994329259158241186375848),
  (30976,41507254357351159527025985095),
  (32384,39554776384858047300823491724),
  (32480,39433226803687955611184668704),
  (32512,39393048448492453579269719460),
  (33440,38302505623795691298215086906),
  (33888,37828448429552979279753679797),
  (34048,37667506933227296910176425035),
  (34064,37651655553814728606502157357),
  (34368,37358877059192835283076653975),
  (34400,37328986932780191573912223776),
  (34592,37153361920408975542290328761),
  (35296,36563818147049930737824375834),
  (35552,36370547182216097474110341167),
  (35584,36347175286607357681679274444),
  (64256,37487900929018460525712365426),
  (64288,37481115128191829746138681663),
  (64320,37474330139021938025101678868),
  (64352,37467546182869714182691466992),
  (64864,37359337803519457068335922519),
  (64937,37343992141595551765490437093),
  (65184,37292298166607044776923730439),
  (65216,37285630424942458254984765492),
  (65248,37278970135762475772242902057),
  (66368,37052220654732407788513829269),
  (66624,37002642023226572778576018190),
  (67840,36782935213934302172512054082),
  (67904,36772199504033807995071285946),
  (67936,36766865812453577462161066768),
  (68128,36735350324974233560263340683),
  (68224,36719911562333009922011608988),
  (68320,36704690213017388412640631752),
  (68352,36699665319932879879871965032),
  (68368,36697162115209404385899409692),
  (68640,36655565777244030528599645261),
  (68704,36646045947585383674655295500),
  (68960,36609013795271384712291121737),
  (69021,36600440929219541260327840927),
  (94976,37222577350784375296816884878),
  (95392,37192965216804857656846297339),
  (95648,37174207294609736117902174514),
  (96896,37078703704408918767080792120),
  (96928,37076197529759648105949946827),
  (97568,37025878851775236317422317281),
  (98272,36970728547243931261316223201),
  (98592,36945987423609895101948793829),
  (99616,36869459537864682798657372230),
  (127744,37031975187095528661789043468),
  (128768,36990200745816164598084760639),
  (129152,36973884065731189389525179955),
  (129632,36953199362671273427834921103),
  (129760,36947650102439847711797184918),
  (129952,36939313207138140211196075333),
  (129984,36937922876037628433975853041),
  (130144,36930970796259955951339313264),
  (130208,36928190742801486687580160810),
  (131328,36880081800289150076404664608),
  (131744,36862737802580205095935466384),
  (131872,36857487453389680178117210027),
  (132192,36844569014050428450572295745),
  (132224,36843294731416857360502080700),
  (132256,36842023824537450969005829592),
  (132555,36830320232422378682035503575),
  (132800,36820978247823305054098601018),
  (132832,36819775667683931778517650283),
  (133088,36810309868538664239890849171),
  (133302,36802618646172874384275607886),
  (133312,36802264394899765346598341668),
  (133504,36795555184954510772084400595),
  (133632,36791182568740296743312367117),
  (134262,36770912290232644249675171608),
  (136192,36723826459486629579594740652),
  (161248,36974352760604505075284297338),
  (161280,36973496518085035058523873315),
  (161536,36966585076484547496216374665),
  (161888,36956927265180261416885689422),
  (162848,36930020899620845516734463063),
  (163123,36922254193178323616639727646),
  (163296,36917373627419414179283636686),
  (163520,36911070725459032538993485234),
  (163744,36904796932460792430622446752),
  (163968,36898563574725552479020260889),
  (164160,36893261408630936575634571279),
  (164256,36890626733962478368214485413),
  (164480,36884527650077319685371617099),
  (164512,36883662350206511586050339512),
  (164544,36882798655202437525797898223),
  (164672,36879360440362315619084856984),
  (166592,36832190141975207099619317548),
  (166912,36825365787453471243565060596),
  (194912,36918211423194814785754759902),
  (195168,36913297800870532961758515832),
  (195360,36909601110252510417889899418),
  (195488,36907134024253922841968326789),
  (196128,36894823589599199019122295554),
  (196448,36888723749397533490281457296),
  (197184,36874988063955774484112363977),
  (197248,36873819554952697421563601080),
  (197344,36872076097830464840955797544),
  (197888,36862433837131429282415295395),
  (197932,36861673462340888013249647877),
  (198208,36856978378593596543834093193),
  (198240,36856442685145820740010492567),
  (198656,36849655832854778008101061242),
  (198720,36848642387182348440253151709),
  (200704,36822149339370551838985961222),
  (226592,36923714806373739859131482697),
  (227040,36917154756801030579535787465),
  (227328,36912868987857895346036483360),
  (227872,36904680736419899188155845492),
  (228896,36889214026961410391103514441),
  (229280,36883493267350371331970488444),
  (229536,36879728139311851259994152203),
  (230208,36870102185534573063946159393),
  (230592,36864814444793819442765581167),
  (230769,36862439334261161963666579722),
  (231200,36856840636755630225133162607),
  (231360,36854834442657616972600956357),
  (231456,36853650715090682634430236992),
  (231648,36851330114686750284017878529),
  (231840,36849074373034965990989029159),
  (232704,36839801379258711973597911249),
  (235008,36823415892818357844346812627),
  (260928,36903281606222466300178923756),
  (262144,36888692574400056179633962644),
  (262624,36883082753507850579811052206),
  (263520,36873060895709354607954406051),
  (263536,36872888621566490345151447001),
  (263616,36872031235348888024686865552),
  (263700,36871138339148952081147470712),
  (264160,36866391733645474736797942534),
  (265088,36857663250860661699106564057),
  (265120,36857384889492654233029194296),
  (265248,36856287603368429175895581034),
  (292128,36912280702742777649822996672),
  (293280,36901118633246607093094465025),
  (293376,36900170027879581517510381980),
  (294336,36890663609003873127968545305),
  (295360,36880736419895941387463565234),
  (295744,36877145871843294259408242913),
  (295808,36876556867305157851730922928),
  (296096,36873943738433772720545407288),
  (296224,36872803379162145580357371805),
  (296256,36872520443001608899463082670),
  (296288,36872238373838043481054256725),
  (296293,36872194378353437927270655285),
  (296352,36871676928735546778765916002),
  (296800,36867853195391118176655320745),
  (296864,36867323109753539479160328648),
  (296928,36866797303760584885848899350),
  (297536,36862029613628636200629597914),
  (297632,36861316831437794021091523644),
  (297792,36860154723454909041108618986),
  (298048,36858364780537621535748441419),
  (299264,36851141994790730394087896985),
  (299520,36849912962020361577993174648),
  (299776,36848791971830007323118819529),
  (326400,36900242708051215010972609337),
  (328544,36882043058118610235009661740),
  (328672,36881004174386108944449953317),
  (328704,36880745883075649001440311355),
  (329216,36876699239275885593492742463),
  (329792,36872372555454404402740667270),
  (329952,36871219615503321921806140374),
  (330400,36868118016848978692427920871),
  (331424,36861824080006214783331343235),
  (333568,36853008233441488998169439090),
  (360192,36895822019621956083498621103),
  (360448,36893997341485585870476017965),
  (360960,36890377407769636160692825179),
  (361600,36885951166870412339429050629),
  (362304,36881280395931804358435588889),
  (362592,36879447693461763950068875119),
  (362656,36879047472902433931247483477),
  (362688,36878848377193692739638925415),
  (362816,36878058801207289582891340998),
  (363264,36875387325284412897670625920),
  (363456,36874289411970889480441127407),
  (395008,36884688782386766021765744097),
  (395136,36884010348033381092183642490),
]

def catalogPoint (t : Nat) : Nat := if t < 541 then NinthSpanPoints.catalogPoint t else ((extraCatalog[t-541]?).getD (0,0)).1
def catalogValue (t : Nat) : Nat := if t < 541 then NinthSpanPoints.catalogValue t else ((extraCatalog[t-541]?).getD (0,0)).2
def regionIndex (t : Nat) : Nat := (catalogPoint t + 16384) >>> 15
def regionLower (t : Nat) : Nat := rgA AMW.Cert.PC8CLData.REG (regionIndex t)
def regionUpper (t : Nat) : Nat := rgB AMW.Cert.PC8CLData.REG (regionIndex t)
def catalogCheck (t : Nat) : Bool := decide (catalogValue t < 2^96) && PointSoundness.tangentCheck (regionLower t) (regionUpper t) (catalogPoint t) (catalogValue t)
attribute [local irreducible] extraCatalog AMW.Cert.PC8CLData.PT

private theorem extra_block_0 : allFrom 541 16 catalogCheck = true := by decide +kernel
private theorem extra_block_16 : allFrom 557 16 catalogCheck = true := by decide +kernel
private theorem extra_block_32 : allFrom 573 16 catalogCheck = true := by decide +kernel
private theorem extra_block_48 : allFrom 589 16 catalogCheck = true := by decide +kernel
private theorem extra_block_64 : allFrom 605 16 catalogCheck = true := by decide +kernel
private theorem extra_block_80 : allFrom 621 16 catalogCheck = true := by decide +kernel
private theorem extra_block_96 : allFrom 637 16 catalogCheck = true := by decide +kernel
private theorem extra_block_112 : allFrom 653 16 catalogCheck = true := by decide +kernel
private theorem extra_block_128 : allFrom 669 16 catalogCheck = true := by decide +kernel
private theorem extra_block_144 : allFrom 685 16 catalogCheck = true := by decide +kernel
private theorem extra_block_160 : allFrom 701 16 catalogCheck = true := by decide +kernel
private theorem extra_block_176 : allFrom 717 4 catalogCheck = true := by decide +kernel

private theorem extra_all : allFrom 541 180 catalogCheck = true := by
  have h0 := extra_block_0
  have h1 : allFrom 541 32 catalogCheck = true := allFrom_add h0 extra_block_16
  have h2 : allFrom 541 48 catalogCheck = true := allFrom_add h1 extra_block_32
  have h3 : allFrom 541 64 catalogCheck = true := allFrom_add h2 extra_block_48
  have h4 : allFrom 541 80 catalogCheck = true := allFrom_add h3 extra_block_64
  have h5 : allFrom 541 96 catalogCheck = true := allFrom_add h4 extra_block_80
  have h6 : allFrom 541 112 catalogCheck = true := allFrom_add h5 extra_block_96
  have h7 : allFrom 541 128 catalogCheck = true := allFrom_add h6 extra_block_112
  have h8 : allFrom 541 144 catalogCheck = true := allFrom_add h7 extra_block_128
  have h9 : allFrom 541 160 catalogCheck = true := allFrom_add h8 extra_block_144
  have h10 : allFrom 541 176 catalogCheck = true := allFrom_add h9 extra_block_160
  have h11 : allFrom 541 180 catalogCheck = true := allFrom_add h10 extra_block_176
  exact h11

theorem catalogChecks (t : Nat) (ht : t < 721) : catalogCheck t = true := by
  by_cases ho : t < 541
  · simpa only [catalogCheck,catalogValue,catalogPoint,if_pos ho,regionLower,regionUpper,regionIndex,
      NinthSpanPoints.catalogCheck,NinthSpanPoints.regionLower,NinthSpanPoints.regionUpper,NinthSpanPoints.regionIndex] using NinthSpanPoints.catalogChecks t ho
  · have he : t - 541 < 180 := by omega
    have h := allFrom_spec extra_all (t-541) he
    simpa only [Nat.add_sub_of_le (by omega : 541 ≤ t)] using h

theorem catalogValue_lt (t : Nat) (ht : t < 721) : catalogValue t < 2^96 := by
  have hc := catalogChecks t ht
  simp only [catalogCheck, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.1

theorem catalogTangentCheck (t : Nat) (ht : t < 721) :
    PointSoundness.tangentCheck (regionLower t) (regionUpper t)
      (catalogPoint t) (catalogValue t) = true := by
  have hc := catalogChecks t ht
  simp only [catalogCheck, Bool.and_eq_true] at hc
  exact hc.2

theorem catalogPack_eq (t : Nat) (ht : t < 721) :
    catalogValue t = AMW.Cert.PC8CLData.PT (catalogPoint t) := by
  exact PointSoundness.tangentCheck_pack_eq (catalogTangentCheck t ht)

theorem catalogTVal (t : Nat) (ht : t < 721) :
    TVal AMW.Cert.PC8CLData.PT (regionLower t) (regionUpper t) (catalogPoint t) := by
  exact PointSoundness.tangentCheck_sound (catalogTangentCheck t ht)

/-- Both affine lines lie below a genuine tangent throughout a closed interval.
The two exact anchor endpoints may lie between entries of the original table. -/
theorem safe_anchor_cuts {w : ℝ → ℝ} {v d dm dp q l u x : ℝ}
    (hdm : dm ≤ d) (hdp : d ≤ dp)
    (hlq : l ≤ q) (hqu : q ≤ u) (hlx : l ≤ x) (hxu : x ≤ u)
    (htangent : v + d * (x - q) ≤ w x) :
    v + dp * (l - q) + dm * (x - l) ≤ w x ∧
      v + dm * (u - q) + dp * (x - u) ≤ w x := by
  have h1 := mul_nonneg (sub_nonneg.mpr hdm) (sub_nonneg.mpr hlx)
  have h2 := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hlq)
  have h3 := mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hxu)
  have h4 := mul_nonneg (sub_nonneg.mpr hdm) (sub_nonneg.mpr hqu)
  constructor <;> nlinarith

/-- Transport an inherited genuine tangent to exact reanchoring endpoints.
The conclusion uses precisely the integral row normalization of the new data. -/
theorem oldTVal_reanchor_scaled {f : Nat → Nat} {L U p : Nat}
    (ht : TVal f L U p) {L5 U5 : Int}
    (hL : 5*(L : Int) ≤ L5) (hU : U5 ≤ 5*(U : Int))
    {s : ℝ} (hlo : (L5:ℝ)/(5*SC) ≤ s) (hhi : s ≤ (U5:ℝ)/(5*SC)) :
    let value := f p
    let V : ℝ := lo32 value
    let dm : ℝ := (lo32 (hi32 value):ℝ)-2000000000
    let dp : ℝ := 2000000000-(hi32 (hi32 value):ℝ)
    let l5 : Int := min L5 (5*(p:Int))
    let u5 : Int := max U5 (5*(p:Int))
    50*dm*SC*s-5*10000000000*SC*wfun s ≤
      -5*V*SC+50*dp*(p:ℝ)-10*(dp-dm)*(l5:ℝ) ∧
    50*dp*SC*s-5*10000000000*SC*wfun s ≤
      -5*V*SC+50*dm*(p:ℝ)-10*(dm-dp)*(u5:ℝ) := by
  dsimp only
  obtain ⟨hLp,hpU,hdm,hdp,hval⟩ := ht
  have hsL : (L:ℝ)/SC ≤ s := by
    have hc : 5*(L:ℝ) ≤ (L5:ℝ) := by exact_mod_cast hL
    norm_num [SC] at hlo ⊢
    linarith
  have hsU : s ≤ (U:ℝ)/SC := by
    have hc : (U5:ℝ) ≤ 5*(U:ℝ) := by exact_mod_cast hU
    norm_num [SC] at hhi ⊢
    linarith
  have h1 : ((lo32 (hi32 (f p)):ℝ)-2000000000)/1000000000 ≤
      w1 ((p:ℝ)/SC) := by linarith
  have h2 : w1 ((p:ℝ)/SC) ≤
      (2000000000-(hi32 (hi32 (f p)):ℝ))/1000000000 := by linarith
  have hpl : ((min L5 (5*(p:Int)):Int):ℝ)/(5*SC) ≤ (p:ℝ)/SC := by
    norm_num [SC]
    have hc := min_le_right (L5:ℝ) (5*(p:ℝ))
    linarith only [hc]
  have hpu : (p:ℝ)/SC ≤ ((max U5 (5*(p:Int)):Int):ℝ)/(5*SC) := by
    norm_num [SC]
    have hc := le_max_right (U5:ℝ) (5*(p:ℝ))
    linarith only [hc]
  have hxl : ((min L5 (5*(p:Int)):Int):ℝ)/(5*SC) ≤ s := by
    norm_num [SC] at hlo ⊢
    have hc := min_le_left (L5:ℝ) (5*(p:ℝ))
    linarith only [hc,hlo]
  have hxu : s ≤ ((max U5 (5*(p:Int)):Int):ℝ)/(5*SC) := by
    norm_num [SC] at hhi ⊢
    have hc := le_max_left (U5:ℝ) (5*(p:ℝ))
    linarith only [hc,hhi]
  have hc := safe_anchor_cuts h1 h2 hpl hpu hxl hxu (hval s hsL hsU)
  have hm1 := mul_le_mul_of_nonneg_left hc.1
    (by norm_num : (0:ℝ) ≤ 1638400000000000)
  have hm2 := mul_le_mul_of_nonneg_left hc.2
    (by norm_num : (0:ℝ) ≤ 1638400000000000)
  norm_num [SC] at hm1 hm2 ⊢
  constructor <;> nlinarith [hm1,hm2]

/-- Exact original convex-region containment, with no rounded endpoints.
The packed point identity was checked once in the 721-entry catalog. -/
def directCheck (L5 U5 : Int) (t : Nat) : Bool :=
  decide (t < 721 ∧
    5*(regionLower t:Int) ≤ min L5 (5*(catalogPoint t:Int)) ∧
    max U5 (5*(catalogPoint t:Int)) ≤ 5*(regionUpper t:Int))

theorem direct_reanchor_scaled {L5 U5 : Int} {t : Nat}
    (hcheck : directCheck L5 U5 t = true) {s : ℝ}
    (hlo : (L5:ℝ)/(5*SC) ≤ s) (hhi : s ≤ (U5:ℝ)/(5*SC)) :
    let p := catalogPoint t
    let value := catalogValue t
    let V : ℝ := lo32 value
    let dm : ℝ := (lo32 (hi32 value):ℝ)-2000000000
    let dp : ℝ := 2000000000-(hi32 (hi32 value):ℝ)
    let l5 : Int := min L5 (5*(p:Int))
    let u5 : Int := max U5 (5*(p:Int))
    50*dm*SC*s-5*10000000000*SC*wfun s ≤
      -5*V*SC+50*dp*(p:ℝ)-10*(dp-dm)*(l5:ℝ) ∧
    50*dp*SC*s-5*10000000000*SC*wfun s ≤
      -5*V*SC+50*dm*(p:ℝ)-10*(dm-dp)*(u5:ℝ) := by
  have h : t < 721 ∧
      5*(regionLower t:Int) ≤ min L5 (5*(catalogPoint t:Int)) ∧
      max U5 (5*(catalogPoint t:Int)) ≤ 5*(regionUpper t:Int) :=
    of_decide_eq_true hcheck
  have hL : 5*(regionLower t:Int) ≤ L5 :=
    h.2.1.trans (min_le_left _ _)
  have hU : U5 ≤ 5*(regionUpper t:Int) :=
    (le_max_left _ _).trans h.2.2
  have hr := oldTVal_reanchor_scaled (catalogTVal t h.1) hL hU hlo hhi
  dsimp only at hr ⊢
  rw [←catalogPack_eq t h.1] at hr
  exact hr

end
end RHWeil.RecordSubmission.JointFramePairPoints
#print axioms RHWeil.RecordSubmission.JointFramePairPoints.catalogValue_lt
#print axioms RHWeil.RecordSubmission.JointFramePairPoints.catalogPack_eq
#print axioms RHWeil.RecordSubmission.JointFramePairPoints.catalogTVal
#print axioms RHWeil.RecordSubmission.JointFramePairPoints.oldTVal_reanchor_scaled
#print axioms RHWeil.RecordSubmission.JointFramePairPoints.direct_reanchor_scaled
