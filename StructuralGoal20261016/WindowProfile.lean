/- SPDX-License-Identifier: Apache-2.0
Actual 24-mode admissible window, including positive-variation budget.
Derivative and rational variation proofs adapt the attributed AMW proofs.
The 257 sine table entries are checked with Core's rational Taylor theorem;
the data generator is not trusted. No new zero-proportion is asserted here.
-/
import StructuralGoal20261016.WindowKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW Zeta23
namespace StructuralGoal20261016.WindowProfile

def coeffQ (j : ℕ) : ℚ := if j = 0 then 1 else
 (StructuralW10Followup20261016.NewWindows.nums24 (j-1) : ℚ) / 1000000000
def freq (j : ℕ) : ℝ := if j = 0 then Real.sqrt 2 else 2 * π * j
def V (s : ℝ) : ℝ := ∑ j ∈ Finset.range 25, (coeffQ j : ℝ) * Real.cos (freq j*s)

theorem coeffQ_zero : (coeffQ 0 : ℝ) = 1 := by norm_num [coeffQ]
theorem freq_zero : freq 0 = Real.sqrt 2 := by simp [freq]

theorem V_eq (s : ℝ) : V s = WindowEnergy.v 24 WindowKernel.d24 s := by
 rw [V, Finset.sum_range_succ', coeffQ_zero, freq_zero, one_mul, add_comm]
 unfold WindowEnergy.v
 congr 1
 apply Finset.sum_congr rfl
 intro j _
 simp [coeffQ, freq, WindowKernel.d24, AMW.ek]
 <;> ring

theorem V_eq_v24 (s : ℝ) : V s = StructuralW10Followup20261016.NewWindows.v24 s := by
 rw [V_eq, WindowKernel.v24_eq]

theorem V_continuous : Continuous V := by
 unfold V
 fun_prop
theorem V_contDiff : ContDiff ℝ ⊤ V := by
 unfold V
 exact ContDiff.sum fun j _ => contDiff_const.mul
   (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
theorem V_even (s : ℝ) : V (-s) = V s := by
 simp only [V, mul_neg, Real.cos_neg]
theorem V_zero : V 0 = 1011052017 / 1000000000 := by
 norm_num [V, coeffQ, freq, StructuralW10Followup20261016.NewWindows.nums24,
   Finset.sum_range_succ]
theorem V_ge_core {s : ℝ} (hs : |s| ≤ 1/2) : 67/100 ≤ V s := by
 rw [V_eq_v24]
 exact StructuralW10Followup20261016.WindowProfileGeneral.profile_ge_core _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 hs
theorem V_pos_wide {s : ℝ} (hs : |s| ≤ 3/5) : 0 < V s := by
 rw [V_eq_v24]
 exact StructuralW10Followup20261016.NewWindows.v24_positive hs
theorem V_le (s : ℝ) : V s ≤ 5/4 := by
 rw [V_eq_v24]
 have hp := StructuralW10Followup20261016.WindowProfileGeneral.abs_perturb_le _
   StructuralW10Followup20261016.NewWindows.sum_abs_c24 s
 have hc := Real.cos_le_one (Real.sqrt 2*s)
 unfold StructuralW10Followup20261016.NewWindows.v24
   StructuralW10Followup20261016.WindowProfileGeneral.profile
 linarith only [(abs_le.mp hp).2, hc]

def Vd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 25, -((coeffQ j : ℝ) * freq j * Real.sin (freq j * s))
def Vdd (s : ℝ) : ℝ := ∑ j ∈ Finset.range 25, -((coeffQ j : ℝ) * freq j ^ 2 * Real.cos (freq j * s))
theorem hasDerivAt_V (s : ℝ) : HasDerivAt V (Vd s) s := by
 unfold V Vd
 have h : ∀ j ∈ Finset.range 25, HasDerivAt (fun s => (coeffQ j : ℝ) * Real.cos (freq j * s))
     (-((coeffQ j : ℝ) * freq j * Real.sin (freq j * s))) s := by
   intro j _
   have h1 : HasDerivAt (fun s => freq j * s) (freq j) s := by
     simpa using (hasDerivAt_id s).const_mul (freq j)
   have h2 := ((Real.hasDerivAt_cos (freq j * s)).comp s h1).const_mul (coeffQ j : ℝ)
   exact h2.congr_deriv (by ring)
 have := HasDerivAt.fun_sum h
 simpa using this
theorem hasDerivAt_Vd (s : ℝ) : HasDerivAt Vd (Vdd s) s := by
 unfold Vd Vdd
 have h : ∀ j ∈ Finset.range 25, HasDerivAt (fun s => -((coeffQ j : ℝ) * freq j * Real.sin (freq j * s)))
     (-((coeffQ j : ℝ) * freq j ^ 2 * Real.cos (freq j * s))) s := by
   intro j _
   have h1 : HasDerivAt (fun s => freq j * s) (freq j) s := by
     simpa using (hasDerivAt_id s).const_mul (freq j)
   have h2 := (((Real.hasDerivAt_sin (freq j * s)).comp s h1).const_mul
     ((coeffQ j : ℝ) * freq j)).neg
   exact h2.congr_deriv (by ring)
 have := HasDerivAt.fun_sum h
 simpa using this
theorem freq_nonneg (j : ℕ) : 0 ≤ freq j := by
 unfold freq; split_ifs <;> positivity
theorem freq_le (j : ℕ) : freq j ≤ if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ) := by
 by_cases h : j = 0
 · subst h
   rw [if_pos rfl, freq_zero, Real.sqrt_le_left (by norm_num)]; norm_num
 · rw [if_neg h]
   unfold freq
   rw [if_neg h]
   have := Real.pi_lt_d2
   have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
   nlinarith
theorem abs_Vd_le (s : ℝ) : |Vd s| ≤ 5 := by
 unfold Vd
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 have hb : ∀ j ∈ Finset.range 25, |-((coeffQ j : ℝ) * freq j * Real.sin (freq j * s))|
     ≤ |(coeffQ j : ℝ)| * (if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ)) := by
   intro j _
   rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (freq_nonneg j)]
   calc |(coeffQ j : ℝ)| * freq j * |Real.sin (freq j * s)| ≤ |(coeffQ j : ℝ)| * freq j * 1 :=
         mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity [freq_nonneg j])
     _ ≤ |(coeffQ j : ℝ)| * (if j = 0 then (3 / 2 : ℝ) else (63 / 10 : ℝ) * (j : ℝ)) := by
         rw [mul_one]; exact mul_le_mul_of_nonneg_left (freq_le j) (abs_nonneg _)
 refine (Finset.sum_le_sum hb).trans ?_
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeffQ, StructuralW10Followup20261016.NewWindows.nums24]
 norm_num [abs_div]
theorem freq_sq_le (j : ℕ) :
   freq j ^ 2 ≤ if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2 := by
 by_cases h : j = 0
 · subst h
   rw [if_pos rfl, freq_zero, Real.sq_sqrt (by norm_num)]
 · rw [if_neg h]
   unfold freq
   rw [if_neg h]
   have h1 := Real.pi_lt_d2
   have h0 := Real.pi_pos
   have : π ^ 2 ≤ (3.15 : ℝ) ^ 2 := pow_le_pow_left₀ h0.le h1.le 2
   have hj2 : (0 : ℝ) ≤ (j : ℝ) ^ 2 := sq_nonneg _
   have e : (2 * π * (j : ℝ)) ^ 2 = 4 * π ^ 2 * (j : ℝ) ^ 2 := by ring
   rw [e]
   nlinarith
theorem abs_Vdd_le (s : ℝ) : |Vdd s| ≤ 160 := by
 unfold Vdd
 refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
 have hb : ∀ j ∈ Finset.range 25, |-((coeffQ j : ℝ) * freq j ^ 2 * Real.cos (freq j * s))|
     ≤ |(coeffQ j : ℝ)| * (if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2) := by
   intro j _
   rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (freq j))]
   calc |(coeffQ j : ℝ)| * freq j ^ 2 * |Real.cos (freq j * s)| ≤ |(coeffQ j : ℝ)| * freq j ^ 2 * 1 :=
         mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
     _ ≤ |(coeffQ j : ℝ)| * (if j = 0 then (2 : ℝ) else (397 / 10 : ℝ) * (j : ℝ) ^ 2) := by
         rw [mul_one]; exact mul_le_mul_of_nonneg_left (freq_sq_le j) (abs_nonneg _)
 refine (Finset.sum_le_sum hb).trans ?_
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, coeffQ, StructuralW10Followup20261016.NewWindows.nums24]
 norm_num [abs_div]
def sinTabZ : List (ℤ × ℤ) := [(-100000, 100001), (61258846, 61458847), (122615382, 122815383), (183967299, 184167300), (245312285, 245512286), (306648031, 306848032), (367972229, 368172230), (429282569, 429482570), (490576743, 490776744), (551852443, 552052444), (613107363, 613307364), (674339195, 674539196), (735545635, 735745636), (796724379, 796924380), (857873123, 858073124), (918989564, 919189565), (980071403, 980271404), (1041116338, 1041316339), (1102122072, 1102322073), (1163086309, 1163286310), (1224006751, 1224206752), (1284881107, 1285081108), (1345707085, 1345907086), (1406482393, 1406682394), (1467204744, 1467404745), (1527871852, 1528071853), (1588481433, 1588681434), (1649031204, 1649231205), (1709518887, 1709718888), (1769942204, 1770142205), (1830298879, 1830498880), (1890586641, 1890786642), (1950803220, 1951003221), (2010946348, 2011146349), (2071013761, 2071213762), (2131003199, 2131203200), (2190912401, 2191112402), (2250739113, 2250939114), (2310481082, 2310681083), (2370136059, 2370336060), (2429701799, 2429901800), (2489176057, 2489376058), (2548556596, 2548756597), (2607841179, 2608041180), (2667027574, 2667227575), (2726113554, 2726313555), (2785096893, 2785296894), (2843975372, 2844175373), (2902746772, 2902946773), (2961408882, 2961608883), (3019959493, 3020159494), (3078396400, 3078596401), (3136717403, 3136917404), (3194920308, 3195120309), (3253002921, 3253202922), (3310963057, 3311163058), (3368798533, 3368998534), (3426507173, 3426707174), (3484086802, 3484286803), (3541535254, 3541735255), (3598850365, 3599050366), (3656029978, 3656229979), (3713071939, 3713271940), (3769974102, 3770174103), (3826734323, 3826934324), (3883350466, 3883550467), (3939820400, 3940020401), (3996141998, 3996341999), (4052313140, 4052513141), (4108331710, 4108531711), (4164195600, 4164395601), (4219902707, 4220102708), (4275450934, 4275650935), (4330838188, 4331038189), (4386062385, 4386262386), (4441121445, 4441321446), (4496013296, 4496213297), (4550735871, 4550935872), (4605287109, 4605487110), (4659664957, 4659864958), (4713867368, 4714067369), (4767892300, 4768092301), (4821737720, 4821937721), (4875401601, 4875601602), (4928881922, 4929081923), (4982176669, 4982376670), (5035283837, 5035483838), (5088201425, 5088401426), (5140927441, 5141127442), (5193459901, 5193659902), (5245796826, 5245996827), (5297936246, 5298136247), (5349876198, 5350076199), (5401614727, 5401814728), (5453149884, 5453349885), (5504479729, 5504679730), (5555602330, 5555802331), (5606515761, 5606715762), (5657218107, 5657418108), (5707707458, 5707907459), (5757981914, 5758181915), (5808039580, 5808239581), (5857878574, 5858078575), (5907497018, 5907697019), (5956893044, 5957093045), (6006064793, 6006264794), (6055010414, 6055210415), (6103728062, 6103928063), (6152215905, 6152415906), (6200472117, 6200672118), (6248494881, 6248694882), (6296282389, 6296482390), (6343832841, 6344032842), (6391144448, 6391344449), (6438215428, 6438415429), (6485044010, 6485244011), (6531628429, 6531828430), (6577966932, 6578166933), (6624057775, 6624257776), (6669899223, 6670099224), (6715489548, 6715689549), (6760827035, 6761027036), (6805909977, 6806109978), (6850736677, 6850936678), (6895305447, 6895505448), (6939614608, 6939814609), (6983662494, 6983862495), (7027447444, 7027647445), (7070967811, 7071167812), (7114221957, 7114421958), (7157208252, 7157408253), (7199925079, 7200125080), (7242370829, 7242570830), (7284543904, 7284743905), (7326442716, 7326642717), (7368065688, 7368265689), (7409411253, 7409611254), (7450477854, 7450677855), (7491263945, 7491463946), (7531767990, 7531967991), (7571988465, 7572188466), (7611923854, 7612123855), (7651572656, 7651772657), (7690933376, 7691133377), (7730004533, 7730204534), (7768784656, 7768984657), (7807272285, 7807472286), (7845465971, 7845665972), (7883364276, 7883564277), (7920965773, 7921165774), (7958269046, 7958469047), (7995272691, 7995472692), (8031975314, 8032175315), (8068375535, 8068575536), (8104471982, 8104671983), (8140263297, 8140463298), (8175748131, 8175948132), (8210925149, 8211125150), (8245793027, 8245993028), (8280350452, 8280550453), (8314596123, 8314796124), (8348528749, 8348728750), (8382147055, 8382347056), (8415449774, 8415649775), (8448435652, 8448635653), (8481103448, 8481303449), (8513451931, 8513651932), (8545479883, 8545679884), (8577186100, 8577386101), (8608569386, 8608769387), (8639628561, 8639828562), (8670362455, 8670562456), (8700769911, 8700969912), (8730849784, 8731049785), (8760600941, 8760800942), (8790022264, 8790222265), (8819112643, 8819312644), (8847870984, 8848070985), (8876296204, 8876496205), (8904387232, 8904587233), (8932143011, 8932343012), (8959562497, 8959762498), (8986644656, 8986844657), (9013388470, 9013588471), (9039792931, 9039992932), (9065857045, 9066057046), (9091579830, 9091779831), (9116960320, 9117160321), (9141997557, 9142197558), (9166690599, 9166890600), (9191038516, 9191238517), (9215040393, 9215240394), (9238695325, 9238895326), (9262002421, 9262202422), (9284960804, 9285160805), (9307569610, 9307769611), (9329827988, 9330027989), (9351735099, 9351935100), (9373290119, 9373490120), (9394492236, 9394692237), (9415340651, 9415540652), (9435834581, 9436034582), (9455973253, 9456173254), (9475755910, 9475955911), (9495181805, 9495381806), (9514250209, 9514450210), (9532960403, 9533160404), (9551311683, 9551511684), (9569303357, 9569503358), (9586934748, 9587134749), (9604205194, 9604405195), (9621114042, 9621314043), (9637660657, 9637860658), (9653844416, 9654044417), (9669664710, 9669864711), (9685120942, 9685320943), (9700212531, 9700412532), (9714938909, 9715138910), (9729299522, 9729499523), (9743293827, 9743493828), (9756921300, 9757121301), (9770181426, 9770381427), (9783073707, 9783273708), (9795597656, 9795797657), (9807752804, 9807952805), (9819538691, 9819738692), (9830954874, 9831154875), (9842000923, 9842200924), (9852676423, 9852876424), (9862980972, 9863180973), (9872914181, 9873114182), (9882475677, 9882675678), (9891665099, 9891865100), (9900482102, 9900682103), (9908926354, 9909126355), (9916997536, 9917197537), (9924695345, 9924895346), (9932019492, 9932219493), (9938969700, 9939169701), (9945545707, 9945745708), (9951747266, 9951947267), (9957574144, 9957774145), (9963026121, 9963226122), (9968102992, 9968302993), (9972804566, 9973004567), (9977130666, 9977330667), (9981081129, 9981281130), (9984655805, 9984855806), (9987854562, 9988054563), (9990677277, 9990877278), (9993123845, 9993323846), (9995194175, 9995394176), (9996888186, 9997088187), (9998205817, 9998405818), (9999147018, 9999347019), (9999711752, 9999911753), (9999900000, 10000100001)]
def tabI (q : ℕ) : ℚ × ℚ :=
 (((sinTabZ.getD q (0, 0)).1 : ℚ) / 10000000000, ((sinTabZ.getD q (0, 0)).2 : ℚ) / 10000000000)
def tabOk : Bool :=
 allQ (fun q => sinPiOk ((q : ℚ) / 512) && decide ((tabI q).1 ≤ (sinPiI ((q : ℚ) / 512)).1)
   && decide ((sinPiI ((q : ℚ) / 512)).2 ≤ (tabI q).2)) 257
def ineg (I : ℚ × ℚ) : ℚ × ℚ := (-I.2, -I.1)
def sinLook (r : ℕ) : ℚ × ℚ :=
 if r % 1024 ≤ 256 then tabI (r % 1024)
 else if r % 1024 ≤ 512 then tabI (512 - r % 1024)
 else if r % 1024 ≤ 768 then ineg (tabI (r % 1024 - 512))
 else ineg (tabI (1024 - r % 1024))
def midQ (i : ℕ) : ℚ := (2 * i + 1) / 1024
def termU (i j : ℕ) : ℚ :=
 if j = 0 then -(s2LoQ * max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)))
 else if 0 ≤ -(2 * j * coeffQ j) then -(2 * j * coeffQ j) * (piMul (sinLook (j * (2 * i + 1)))).2
 else -(2 * j * coeffQ j) * (piMul (sinLook (j * (2 * i + 1)))).1
def termOk (i : ℕ) : Bool := decide (0 ≤ fl (s2LoQ * midQ i)) && decide (s2HiQ * midQ i ≤ 1)
def cellU (i : ℕ) : ℚ := sumQ (termU i) 25 + 160 / 1024
def pvCheck (ρ : ℚ) : Bool :=
 tabOk && allQ termOk 256 && decide (sumQ (fun i => max (cellU i) 0) 256 / 640 ≤ ρ)
theorem tabI_sound (h : tabOk = true) {q : ℕ} (hq : q < 257) :
   InI (tabI q) (Real.sin (Real.pi * ((q : ℝ) / 512))) := by
 rw [tabOk, allQ_iff] at h
 have hq' := h q hq
 simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
 obtain ⟨⟨hok, h1⟩, h2⟩ := hq'
 have hs := sinPiI_sound _ hok
 push_cast at hs
 exact ⟨(Rat.cast_le.mpr h1).trans hs.1, hs.2.trans (Rat.cast_le.mpr h2)⟩
theorem ineg_sound {I : ℚ × ℚ} {x : ℝ} (h : InI I x) : InI (ineg I) (-x) := by
 obtain ⟨h1, h2⟩ := h
 unfold ineg InI; push_cast; exact ⟨neg_le_neg h2, neg_le_neg h1⟩
theorem sinLook_sound (h : tabOk = true) (r : ℕ) :
   InI (sinLook r) (Real.sin (Real.pi * ((r : ℝ) / 512))) := by
 have hper : Real.sin (Real.pi * ((r : ℝ) / 512)) = Real.sin (Real.pi * (((r % 1024 : ℕ) : ℝ) / 512)) := by
   have hr : (r : ℝ) = ((r % 1024 : ℕ) : ℝ) + ((r / 1024 : ℕ) : ℝ) * 1024 := by
     exact_mod_cast (by omega : r = r % 1024 + r / 1024 * 1024)
   rw [hr, show Real.pi * ((((r % 1024 : ℕ) : ℝ) + ((r / 1024 : ℕ) : ℝ) * 1024) / 512)
     = Real.pi * (((r % 1024 : ℕ) : ℝ) / 512) + ((r / 1024 : ℕ) : ℝ) * (2 * Real.pi) by ring]
   exact Real.sin_add_nat_mul_two_pi _ _
 rw [hper]
 unfold sinLook
 have hq256 : r % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
 generalize r % 1024 = q at hq256 ⊢
 split_ifs with h1 h2 h3
 · exact tabI_sound h (by omega)
 · have e : Real.sin (Real.pi * ((q : ℝ) / 512)) = Real.sin (Real.pi * (((512 - q : ℕ) : ℝ) / 512)) := by
     rw [Nat.cast_sub h2, show Real.pi * ((((512 : ℕ) : ℝ) - (q : ℝ)) / 512)
       = Real.pi - Real.pi * ((q : ℝ) / 512) by push_cast; ring, Real.sin_pi_sub]
   rw [e]; exact tabI_sound h (by omega)
 · have e : Real.sin (Real.pi * ((q : ℝ) / 512)) = -Real.sin (Real.pi * (((q - 512 : ℕ) : ℝ) / 512)) := by
     rw [Nat.cast_sub (by omega : 512 ≤ q), show Real.pi * (((q : ℝ) - ((512 : ℕ) : ℝ)) / 512)
       = Real.pi * ((q : ℝ) / 512) - Real.pi by push_cast; ring, Real.sin_sub_pi]; ring
   rw [e]; exact ineg_sound (tabI_sound h (by omega))
 · have e : Real.sin (Real.pi * ((q : ℝ) / 512)) = -Real.sin (Real.pi * (((1024 - q : ℕ) : ℝ) / 512)) := by
     rw [Nat.cast_sub (by omega : q ≤ 1024), show Real.pi * ((((1024 : ℕ) : ℝ) - (q : ℝ)) / 512)
       = 2 * Real.pi - Real.pi * ((q : ℝ) / 512) by push_cast; ring, Real.sin_two_pi_sub]; ring
   rw [e]; exact ineg_sound (tabI_sound h (by omega))
theorem termU_sound (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) (j : ℕ) :
   -((coeffQ j : ℝ) * freq j * Real.sin (freq j * (midQ i : ℝ))) ≤ ((termU i j : ℚ) : ℝ) := by
 unfold termU
 have hm0 : (0:ℚ) ≤ midQ i := by unfold midQ; positivity
 by_cases hj : j = 0
 · subst hj
   simp only [termOk, Bool.and_eq_true, decide_eq_true_eq] at hok
   simp only [if_true]
   obtain ⟨h0, h1⟩ := hok
   rw [coeffQ_zero, freq_zero, one_mul]
   have hm' : (0:ℝ) ≤ midQ i := by exact_mod_cast hm0
   have hs2 := s2LoQ_le
   have hθ0 : 0 ≤ Real.sqrt 2 * midQ i := mul_nonneg (Real.sqrt_nonneg 2) hm'
   have hθ1 : Real.sqrt 2 * midQ i ≤ 1 := by
     have : ((s2HiQ * midQ i : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h1
     push_cast at this
     nlinarith [s2HiQ_ge]
   have hl0 : (0:ℝ) ≤ ((fl (s2LoQ * midQ i) : ℚ) : ℝ) := by exact_mod_cast h0
   have hlθ : ((fl (s2LoQ * midQ i) : ℚ) : ℝ) ≤ Real.sqrt 2 * midQ i :=
     (fl_le _).trans (by push_cast; exact mul_le_mul_of_nonneg_right hs2 hm')
   have hsin := sin_ge_of hl0 hlθ hθ1
   have hsin0 : 0 ≤ Real.sin (Real.sqrt 2 * midQ i) :=
     Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (hθ1.trans (by linarith [Real.pi_gt_three]))
   have hlb : ((max 0 (fl (tSinQ (fl (s2LoQ * midQ i)) - errQ)) : ℚ) : ℝ)
       ≤ Real.sin (Real.sqrt 2 * midQ i) := by
     push_cast
     exact max_le hsin0 ((fl_le _).trans (by exact_mod_cast hsin))
   have hs2lo0 : (0:ℝ) ≤ ((s2LoQ : ℚ) : ℝ) := by simp only [s2LoQ]; push_cast; norm_num
   push_cast at hlb ⊢
   nlinarith
 · simp only [hj, if_false]
   have hω : freq j = 2 * Real.pi * j := by simp [freq, hj]
   have hS := piMul_sound (sinLook_sound htab (j * (2 * i + 1)))
   have e : -((coeffQ j : ℝ) * freq j * Real.sin (freq j * (midQ i : ℝ)))
       = ((-(2 * j * coeffQ j) : ℚ) : ℝ)
         * (Real.pi * Real.sin (Real.pi * (((j * (2 * i + 1) : ℕ) : ℝ) / 512))) := by
     rw [hω]; simp only [midQ]; push_cast; ring_nf
   rw [e]
   obtain ⟨h1, h2⟩ := hS
   split_ifs with he
   · have he' : (0:ℝ) ≤ ((-(2 * j * coeffQ j) : ℚ) : ℝ) := by exact_mod_cast he
     push_cast at he' h2 ⊢
     exact mul_le_mul_of_nonneg_left h2 he'
   · have he' : ((-(2 * j * coeffQ j) : ℚ) : ℝ) ≤ 0 := by push_neg at he; exact_mod_cast he.le
     push_cast at he' h1 ⊢
     exact mul_le_mul_of_nonpos_left h1 he'
theorem Vd_mid_le (htab : tabOk = true) {i : ℕ} (hok : termOk i = true) :
   Vd (midQ i) ≤ ((sumQ (termU i) 25 : ℚ) : ℝ) := by
 rw [sumQ_eq, Rat.cast_sum, Vd]
 exact Finset.sum_le_sum fun j _ => termU_sound htab hok j
theorem Vd_lipschitz (x y : ℝ) : Vd y ≤ Vd x + 160 * |y - x| := by
 have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Vd) (s := Set.univ) (C := 160)
   (fun x _ => (hasDerivAt_Vd x).differentiableAt)
   (fun x _ => by rw [Real.norm_eq_abs, (hasDerivAt_Vd x).deriv]; exact abs_Vdd_le x)
   convex_univ (Set.mem_univ x) (Set.mem_univ y)
 rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
 linarith [le_abs_self (Vd y - Vd x)]
theorem deriv_V_div : deriv (fun s => V s / MAM) = fun s => Vd s / MAM :=
 funext fun s => ((hasDerivAt_V s).div_const MAM).deriv
theorem posVar_of_check {ρ : ℚ} (h : pvCheck ρ = true) :
   ∫ s in (0:ℝ)..(1 / 2), max (deriv (fun s => V s / MAM) s) 0 ≤ (ρ : ℝ) := by
 simp only [pvCheck, Bool.and_eq_true, decide_eq_true_eq] at h
 obtain ⟨⟨htab, hcells⟩, hsum⟩ := h
 rw [allQ_iff] at hcells
 rw [deriv_V_div]
 have hM : (0:ℝ) < MAM := MAM_pos
 set a : ℕ → ℝ := fun k => (k : ℝ) / 512 with ha
 have hcont : Continuous fun s => max (Vd s / MAM) 0 :=
   (((continuous_iff_continuousAt.mpr fun x => (hasDerivAt_Vd x).continuousAt)).div_const MAM).max
     continuous_const
 have hcell : ∀ i < 256, ∫ s in a i..a (i + 1), max (Vd s / MAM) 0
     ≤ 1 / 512 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
   intro i hi
   have hab : a i ≤ a (i + 1) := by simp only [ha]; gcongr; push_cast; linarith
   have hmid : ((midQ i : ℚ) : ℝ) = (2 * i + 1) / 1024 := by simp only [midQ]; push_cast; ring
   have hvm := Vd_mid_le htab (hcells i hi)
   have hpt : ∀ s ∈ Set.Icc (a i) (a (i + 1)), max (Vd s / MAM) 0
       ≤ ((max (cellU i) 0 : ℚ) : ℝ) / MAM := by
     intro s hs
     have hd : |s - (midQ i : ℝ)| ≤ 1 / 1024 := by
       rw [hmid, abs_le]
       simp only [ha, Set.mem_Icc] at hs
       push_cast at hs
       obtain ⟨hs1, hs2⟩ := hs
       constructor <;> linarith
     have hlip := Vd_lipschitz (midQ i : ℝ) s
     have hU : Vd s ≤ ((cellU i : ℚ) : ℝ) := by
       simp only [cellU]; push_cast
       linarith
     push_cast
     exact max_le ((div_le_div_of_nonneg_right hU hM.le).trans
       (div_le_div_of_nonneg_right (le_max_left _ _) hM.le)) (div_nonneg (le_max_right _ _) hM.le)
   calc ∫ s in a i..a (i + 1), max (Vd s / MAM) 0
       ≤ ∫ s in a i..a (i + 1), ((max (cellU i) 0 : ℚ) : ℝ) / MAM :=
         intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable _ _)
           (continuous_const.intervalIntegrable _ _) hpt
     _ = 1 / 512 * (((max (cellU i) 0 : ℚ) : ℝ) / MAM) := by
         rw [intervalIntegral.integral_const, smul_eq_mul]
         simp only [ha]; push_cast; ring
 have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
   (f := fun s => max (Vd s / MAM) 0) (a := a) (n := 256) (fun k _ => hcont.intervalIntegrable _ _)
 have ha0 : a 0 = 0 := by simp [ha]
 have haN : a 256 = 1 / 2 := by simp only [ha]; norm_num
 rw [ha0, haN] at hsplit
 rw [← hsplit]
 refine (Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)).trans ?_
 have hq : ((sumQ (fun i => max (cellU i) 0) 256 / 640 : ℚ) : ℝ) ≤ (ρ : ℝ) := by
   exact_mod_cast hsum
 refine le_of_eq_of_le ?_ hq
 rw [sumQ_eq, ← Finset.mul_sum, ← Finset.sum_div]
 push_cast
 simp only [MAM]
 ring
set_option maxRecDepth 100000 in
theorem pvCheck_v24 : pvCheck (9 / 200) = true := by decide +kernel

theorem deriv2_V_div : deriv (deriv (fun s => V s / MAM)) = fun s => Vdd s / MAM := by
 rw [deriv_V_div]
 exact funext fun s => ((hasDerivAt_Vd s).div_const MAM).deriv

theorem V_zero_div_le : V 0 / MAM ≤ 81/100 := by
 rw [V_zero, MAM]
 norm_num

theorem actual_profile : AMW.Profile (fun s => V s / MAM) (1/10) 4 128 (9/200) where
 δ_pos := by norm_num
 A₁_nonneg := by norm_num
 A₂_nonneg := by norm_num
 even := fun s => by simp only [V_even]
 contDiff := (V_contDiff.of_le le_top).div_const MAM
 pos := fun s hs => div_pos (V_pos_wide (by linarith)) MAM_pos
 ge_quarter := fun s hs => by
   have := V_ge_core hs
   rw [MAM, le_div_iff₀ (by norm_num)]
   linarith
 le_one := fun s _ => by rw [div_le_one MAM_pos]; exact V_le s
 deriv_le := fun s _ => by
   rw [deriv_V_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
   linarith [abs_Vd_le s]
 deriv2_le := fun s _ => by
   rw [deriv2_V_div, abs_div, abs_of_pos MAM_pos, div_le_iff₀ MAM_pos, MAM]
   linarith [abs_Vdd_le s]
 posVar := by
   have h := posVar_of_check pvCheck_v24
   push_cast at h
   exact h
 budget := by
   have h0 : Real.sqrt (V 0 / MAM) ≤ 9/10 := by
     rw [show (9/10 : ℝ) = Real.sqrt (81/100) by
       rw [show (81/100 : ℝ) = (9/10)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
     exact Real.sqrt_le_sqrt V_zero_div_le
   linarith
 budget_sq := by linarith [V_zero_div_le]

def phi (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ :=
 AMW.phiM (AMW.fP (fun s => V s / MAM) L) ϱ L w

theorem actual_admWindow {ϱ : ℝ → ℝ} {L w : ℝ}
 (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8*w ≤ L) :
 AdmWindow (phi ϱ L w) L w (AMW.cMod ϱ 4 (128+2*4^2)) :=
 AMW.admWindow_fP actual_profile hϱ hw hwL

#print axioms V_eq_v24
#print axioms abs_Vdd_le
#print axioms pvCheck_v24
#print axioms actual_profile
#print axioms actual_admWindow
end StructuralGoal20261016.WindowProfile
end
