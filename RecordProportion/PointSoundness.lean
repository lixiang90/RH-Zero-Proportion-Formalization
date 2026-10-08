import RecordProportion.ImportedAM
import RecordProportion.FiniteCertificateData

/- Every point value and every full-interval tangent is checked against the
original globally proved AM table. The closed blocks contain ordinary kernel
proofs, without a runtime or external-computation axiom. -/
namespace RHWeil.RecordSubmission.PointSoundness

open FiniteCertificateData
open AMW.Cert.Pyr AMW.Cert.PyrD

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

attribute [local irreducible] FiniteCertificateData.cells FiniteCertificateData.pairPacks
  FiniteCertificateData.catalog FiniteCertificateData.pointPacket AMW.Cert.PC8CLData.PT

theorem bits_lt_two_pow (word offset width : Nat) : bits word offset width < 2^width := by
  unfold bits
  rw [Nat.shiftLeft_eq, one_mul]
  apply Nat.and_lt_two_pow
  exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)

theorem bits_zero_32 (value : Nat) : bits value 0 32 = AMW.Cert.PyrD.lo32 value := by
  simp [bits, AMW.Cert.PyrD.lo32]

theorem bits_32_32 (value : Nat) : bits value 32 32 = AMW.Cert.PyrD.lo32 (AMW.Cert.PyrD.hi32 value) := by
  rfl

theorem bits_64_32 {value : Nat} (hv : value < 2^96) :
    bits value 64 32 = AMW.Cert.PyrD.hi32 (AMW.Cert.PyrD.hi32 value) := by
  have hs : value >>> 64 < 2^32 := by
    rw [Nat.shiftRight_eq_div_pow]
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^64)).2
    norm_num at hv ⊢
    exact hv
  unfold bits AMW.Cert.PyrD.hi32
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_of_lt_two_pow hs]
  exact Nat.shiftRight_add value 32 32

theorem pointValue_lt (index : Nat) : pointValue index < 2^96 :=
  bits_lt_two_pow _ _ _

theorem catalog_value_lt (packet : Nat) : bits packet 20 96 < 2^96 :=
  bits_lt_two_pow _ _ _

noncomputable def constantCheck (label i j : Nat) : Bool :=
  decide (bits (termAtom label i j) 35 32 ≤
    lb AMW.Cert.PC8CLData.TOP AMW.Cert.PC8CLData.BK (tightLower label i j)
      (AMW.Cert.PCell.uc (tightLower label i j) (tightUpper label i j)))

noncomputable def tangentCheck (L U p value : Nat) : Bool :=
  decide (value = AMW.Cert.PC8CLData.PT p) &&
  tcheckPZ AMW.Cert.PC8CLData.REG AMW.Cert.PC8CLData.TOP AMW.Cert.PC8CLData.BK
    128 L U p value
    (treadU AMW.Cert.PC8CLData.REG AMW.Cert.PC8CLData.TOPD AMW.Cert.PC8CLData.BKD U p)
    (treadD AMW.Cert.PC8CLData.REG AMW.Cert.PC8CLData.TOPD AMW.Cert.PC8CLData.BKD L p)

noncomputable def termCheck (label i j : Nat) : Bool :=
  constantCheck label i j &&
  (oldPointIndices (termAtom label i j)).all fun index =>
    tangentCheck (tightLower label i j) (tightUpper label i j)
      (pointPosition index) (pointValue index)

noncomputable def frameCheck (label : Nat) : Bool :=
  terms.all fun term => termCheck label term.1 term.2.1

noncomputable def extraOccurrenceCheck (left right word k : Nat) : Bool :=
  let atom := bits word (15*k) 15
  let offset := bits atom 0 1
  let i := bits atom 1 3
  let j := bits atom 4 3
  let packet := (catalog[bits atom 7 8]?).getD 0
  let p := bits packet 0 20
  let value := bits packet 20 96
  let label := if offset = 0 then left else right
  tangentCheck (min (tightLower label i j) p)
    (max (tightUpper label i j) p) p value

noncomputable def extraCheck (index : Nat) : Bool :=
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  (List.range packet.2.2.2.2.1).all fun k =>
    extraOccurrenceCheck packet.1 packet.2.1 packet.2.2.2.2.2 k

theorem constantCheck_sound {label i j : Nat} (h : constantCheck label i j = true)
    {s : ℝ} (hlo : (tightLower label i j : ℝ) / AMW.Cert.SC ≤ s)
    (hhi : s ≤ (tightUpper label i j : ℝ) / AMW.Cert.SC) :
    (bits (termAtom label i j) 35 32 : ℝ) / 10000000000 ≤ AMW.wfunAM s := by
  have hn : bits (termAtom label i j) 35 32 ≤
      lb AMW.Cert.PC8CLData.TOP AMW.Cert.PC8CLData.BK (tightLower label i j)
        (AMW.Cert.PCell.uc (tightLower label i j) (tightUpper label i j)) :=
    of_decide_eq_true h
  have hc : (bits (termAtom label i j) 35 32 : ℝ) ≤
      (lb AMW.Cert.PC8CLData.TOP AMW.Cert.PC8CLData.BK (tightLower label i j)
        (AMW.Cert.PCell.uc (tightLower label i j) (tightUpper label i j)) : ℝ) :=
    by exact_mod_cast hn
  have hu : s ≤
      (AMW.Cert.PCell.uc (tightLower label i j) (tightUpper label i j) : ℝ) /
        AMW.Cert.SC := by
    apply hhi.trans
    apply div_le_div_of_nonneg_right _ (by norm_num [AMW.Cert.SC])
    exact_mod_cast AMW.Cert.PCell.le_uc (tightLower label i j) (tightUpper label i j)
  exact (div_le_div_of_nonneg_right hc (by norm_num)).trans
    (AMW.Cert.PC8CLData.lbS _ _ s hlo hu)

theorem tangentCheck_pack_eq {L U p value : Nat} (h : tangentCheck L U p value = true) :
    value = AMW.Cert.PC8CLData.PT p := by
  simp only [tangentCheck, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem tangentCheck_sound {L U p value : Nat} (h : tangentCheck L U p value = true) :
    TVal AMW.Cert.PC8CLData.PT L U p := by
  have heq := tangentCheck_pack_eq h
  simp only [tangentCheck, Bool.and_eq_true] at h
  have ht := h.2
  simp only [heq] at ht
  exact tangent_valZ AMW.Cert.PC8CLData.lbS AMW.Cert.PC8CLData.lbD
    AMW.Cert.PC8CLData.ptS AMW.Cert.PC8CLData.hR (by decide) ht

theorem termCheck_constant {label i j : Nat} (h : termCheck label i j = true) :
    constantCheck label i j = true := by
  simp only [termCheck, Bool.and_eq_true] at h
  exact h.1

theorem termCheck_tangent {label i j index : Nat} (h : termCheck label i j = true)
    (hi : index ∈ oldPointIndices (termAtom label i j)) :
    tangentCheck (tightLower label i j) (tightUpper label i j)
      (pointPosition index) (pointValue index) = true := by
  simp only [termCheck, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.2 index hi

theorem frameCheck_term {label : Nat} (h : frameCheck label = true)
    {t : Nat × Nat × Nat} (ht : t ∈ terms) : termCheck label t.1 t.2.1 = true := by
  exact List.all_eq_true.mp h t ht


/- Ordinary top-level closed blocks keep the frontend state bounded. -/
private theorem frame_block_0 : allFrom 0 16 frameCheck = true := by decide +kernel
private theorem frame_block_1 : allFrom 16 16 frameCheck = true := by decide +kernel
private theorem frame_block_2 : allFrom 32 16 frameCheck = true := by decide +kernel
private theorem frame_block_3 : allFrom 48 16 frameCheck = true := by decide +kernel
private theorem frame_block_4 : allFrom 64 16 frameCheck = true := by decide +kernel
private theorem frame_block_5 : allFrom 80 16 frameCheck = true := by decide +kernel
private theorem frame_block_6 : allFrom 96 16 frameCheck = true := by decide +kernel
private theorem frame_block_7 : allFrom 112 16 frameCheck = true := by decide +kernel
private theorem frame_block_8 : allFrom 128 16 frameCheck = true := by decide +kernel
private theorem frame_block_9 : allFrom 144 16 frameCheck = true := by decide +kernel
private theorem frame_block_10 : allFrom 160 16 frameCheck = true := by decide +kernel
private theorem frame_block_11 : allFrom 176 16 frameCheck = true := by decide +kernel
private theorem frame_block_12 : allFrom 192 16 frameCheck = true := by decide +kernel
private theorem frame_block_13 : allFrom 208 16 frameCheck = true := by decide +kernel
private theorem frame_block_14 : allFrom 224 16 frameCheck = true := by decide +kernel
private theorem frame_block_15 : allFrom 240 16 frameCheck = true := by decide +kernel
private theorem frame_block_16 : allFrom 256 16 frameCheck = true := by decide +kernel
private theorem frame_block_17 : allFrom 272 16 frameCheck = true := by decide +kernel
private theorem frame_block_18 : allFrom 288 16 frameCheck = true := by decide +kernel
private theorem frame_block_19 : allFrom 304 16 frameCheck = true := by decide +kernel
private theorem frame_block_20 : allFrom 320 16 frameCheck = true := by decide +kernel
private theorem frame_block_21 : allFrom 336 16 frameCheck = true := by decide +kernel
private theorem frame_block_22 : allFrom 352 16 frameCheck = true := by decide +kernel
private theorem frame_block_23 : allFrom 368 16 frameCheck = true := by decide +kernel
private theorem frame_block_24 : allFrom 384 16 frameCheck = true := by decide +kernel
private theorem frame_block_25 : allFrom 400 16 frameCheck = true := by decide +kernel
private theorem frame_block_26 : allFrom 416 16 frameCheck = true := by decide +kernel
private theorem frame_block_27 : allFrom 432 16 frameCheck = true := by decide +kernel
private theorem frame_block_28 : allFrom 448 16 frameCheck = true := by decide +kernel
private theorem frame_block_29 : allFrom 464 16 frameCheck = true := by decide +kernel
private theorem frame_block_30 : allFrom 480 2 frameCheck = true := by decide +kernel
private theorem frame_all : allFrom 0 482 frameCheck = true := by
  have h0 : allFrom 0 16 frameCheck = true := frame_block_0
  have h1 : allFrom 0 32 frameCheck = true := allFrom_add h0 frame_block_1
  have h2 : allFrom 0 48 frameCheck = true := allFrom_add h1 frame_block_2
  have h3 : allFrom 0 64 frameCheck = true := allFrom_add h2 frame_block_3
  have h4 : allFrom 0 80 frameCheck = true := allFrom_add h3 frame_block_4
  have h5 : allFrom 0 96 frameCheck = true := allFrom_add h4 frame_block_5
  have h6 : allFrom 0 112 frameCheck = true := allFrom_add h5 frame_block_6
  have h7 : allFrom 0 128 frameCheck = true := allFrom_add h6 frame_block_7
  have h8 : allFrom 0 144 frameCheck = true := allFrom_add h7 frame_block_8
  have h9 : allFrom 0 160 frameCheck = true := allFrom_add h8 frame_block_9
  have h10 : allFrom 0 176 frameCheck = true := allFrom_add h9 frame_block_10
  have h11 : allFrom 0 192 frameCheck = true := allFrom_add h10 frame_block_11
  have h12 : allFrom 0 208 frameCheck = true := allFrom_add h11 frame_block_12
  have h13 : allFrom 0 224 frameCheck = true := allFrom_add h12 frame_block_13
  have h14 : allFrom 0 240 frameCheck = true := allFrom_add h13 frame_block_14
  have h15 : allFrom 0 256 frameCheck = true := allFrom_add h14 frame_block_15
  have h16 : allFrom 0 272 frameCheck = true := allFrom_add h15 frame_block_16
  have h17 : allFrom 0 288 frameCheck = true := allFrom_add h16 frame_block_17
  have h18 : allFrom 0 304 frameCheck = true := allFrom_add h17 frame_block_18
  have h19 : allFrom 0 320 frameCheck = true := allFrom_add h18 frame_block_19
  have h20 : allFrom 0 336 frameCheck = true := allFrom_add h19 frame_block_20
  have h21 : allFrom 0 352 frameCheck = true := allFrom_add h20 frame_block_21
  have h22 : allFrom 0 368 frameCheck = true := allFrom_add h21 frame_block_22
  have h23 : allFrom 0 384 frameCheck = true := allFrom_add h22 frame_block_23
  have h24 : allFrom 0 400 frameCheck = true := allFrom_add h23 frame_block_24
  have h25 : allFrom 0 416 frameCheck = true := allFrom_add h24 frame_block_25
  have h26 : allFrom 0 432 frameCheck = true := allFrom_add h25 frame_block_26
  have h27 : allFrom 0 448 frameCheck = true := allFrom_add h26 frame_block_27
  have h28 : allFrom 0 464 frameCheck = true := allFrom_add h27 frame_block_28
  have h29 : allFrom 0 480 frameCheck = true := allFrom_add h28 frame_block_29
  have h30 : allFrom 0 482 frameCheck = true := allFrom_add h29 frame_block_30
  exact h30

theorem frameChecks (index : Nat) (hi : index < 482) : frameCheck index = true := by
  simpa only [Nat.zero_add] using allFrom_spec frame_all index hi

private theorem extra_block_0 : allFrom 0 32 extraCheck = true := by decide +kernel
private theorem extra_block_1 : allFrom 32 32 extraCheck = true := by decide +kernel
private theorem extra_block_2 : allFrom 64 32 extraCheck = true := by decide +kernel
private theorem extra_block_3 : allFrom 96 32 extraCheck = true := by decide +kernel
private theorem extra_block_4 : allFrom 128 32 extraCheck = true := by decide +kernel
private theorem extra_block_5 : allFrom 160 32 extraCheck = true := by decide +kernel
private theorem extra_block_6 : allFrom 192 32 extraCheck = true := by decide +kernel
private theorem extra_block_7 : allFrom 224 32 extraCheck = true := by decide +kernel
private theorem extra_block_8 : allFrom 256 32 extraCheck = true := by decide +kernel
private theorem extra_block_9 : allFrom 288 32 extraCheck = true := by decide +kernel
private theorem extra_block_10 : allFrom 320 32 extraCheck = true := by decide +kernel
private theorem extra_block_11 : allFrom 352 32 extraCheck = true := by decide +kernel
private theorem extra_block_12 : allFrom 384 32 extraCheck = true := by decide +kernel
private theorem extra_block_13 : allFrom 416 32 extraCheck = true := by decide +kernel
private theorem extra_block_14 : allFrom 448 32 extraCheck = true := by decide +kernel
private theorem extra_block_15 : allFrom 480 32 extraCheck = true := by decide +kernel
private theorem extra_block_16 : allFrom 512 32 extraCheck = true := by decide +kernel
private theorem extra_block_17 : allFrom 544 32 extraCheck = true := by decide +kernel
private theorem extra_block_18 : allFrom 576 32 extraCheck = true := by decide +kernel
private theorem extra_block_19 : allFrom 608 32 extraCheck = true := by decide +kernel
private theorem extra_block_20 : allFrom 640 32 extraCheck = true := by decide +kernel
private theorem extra_block_21 : allFrom 672 32 extraCheck = true := by decide +kernel
private theorem extra_block_22 : allFrom 704 32 extraCheck = true := by decide +kernel
private theorem extra_block_23 : allFrom 736 32 extraCheck = true := by decide +kernel
private theorem extra_block_24 : allFrom 768 32 extraCheck = true := by decide +kernel
private theorem extra_block_25 : allFrom 800 32 extraCheck = true := by decide +kernel
private theorem extra_block_26 : allFrom 832 32 extraCheck = true := by decide +kernel
private theorem extra_block_27 : allFrom 864 32 extraCheck = true := by decide +kernel
private theorem extra_block_28 : allFrom 896 32 extraCheck = true := by decide +kernel
private theorem extra_block_29 : allFrom 928 32 extraCheck = true := by decide +kernel
private theorem extra_block_30 : allFrom 960 32 extraCheck = true := by decide +kernel
private theorem extra_block_31 : allFrom 992 32 extraCheck = true := by decide +kernel
private theorem extra_block_32 : allFrom 1024 32 extraCheck = true := by decide +kernel
private theorem extra_block_33 : allFrom 1056 32 extraCheck = true := by decide +kernel
private theorem extra_block_34 : allFrom 1088 32 extraCheck = true := by decide +kernel
private theorem extra_block_35 : allFrom 1120 32 extraCheck = true := by decide +kernel
private theorem extra_block_36 : allFrom 1152 32 extraCheck = true := by decide +kernel
private theorem extra_block_37 : allFrom 1184 32 extraCheck = true := by decide +kernel
private theorem extra_block_38 : allFrom 1216 8 extraCheck = true := by decide +kernel
private theorem extra_all : allFrom 0 1224 extraCheck = true := by
  have h0 : allFrom 0 32 extraCheck = true := extra_block_0
  have h1 : allFrom 0 64 extraCheck = true := allFrom_add h0 extra_block_1
  have h2 : allFrom 0 96 extraCheck = true := allFrom_add h1 extra_block_2
  have h3 : allFrom 0 128 extraCheck = true := allFrom_add h2 extra_block_3
  have h4 : allFrom 0 160 extraCheck = true := allFrom_add h3 extra_block_4
  have h5 : allFrom 0 192 extraCheck = true := allFrom_add h4 extra_block_5
  have h6 : allFrom 0 224 extraCheck = true := allFrom_add h5 extra_block_6
  have h7 : allFrom 0 256 extraCheck = true := allFrom_add h6 extra_block_7
  have h8 : allFrom 0 288 extraCheck = true := allFrom_add h7 extra_block_8
  have h9 : allFrom 0 320 extraCheck = true := allFrom_add h8 extra_block_9
  have h10 : allFrom 0 352 extraCheck = true := allFrom_add h9 extra_block_10
  have h11 : allFrom 0 384 extraCheck = true := allFrom_add h10 extra_block_11
  have h12 : allFrom 0 416 extraCheck = true := allFrom_add h11 extra_block_12
  have h13 : allFrom 0 448 extraCheck = true := allFrom_add h12 extra_block_13
  have h14 : allFrom 0 480 extraCheck = true := allFrom_add h13 extra_block_14
  have h15 : allFrom 0 512 extraCheck = true := allFrom_add h14 extra_block_15
  have h16 : allFrom 0 544 extraCheck = true := allFrom_add h15 extra_block_16
  have h17 : allFrom 0 576 extraCheck = true := allFrom_add h16 extra_block_17
  have h18 : allFrom 0 608 extraCheck = true := allFrom_add h17 extra_block_18
  have h19 : allFrom 0 640 extraCheck = true := allFrom_add h18 extra_block_19
  have h20 : allFrom 0 672 extraCheck = true := allFrom_add h19 extra_block_20
  have h21 : allFrom 0 704 extraCheck = true := allFrom_add h20 extra_block_21
  have h22 : allFrom 0 736 extraCheck = true := allFrom_add h21 extra_block_22
  have h23 : allFrom 0 768 extraCheck = true := allFrom_add h22 extra_block_23
  have h24 : allFrom 0 800 extraCheck = true := allFrom_add h23 extra_block_24
  have h25 : allFrom 0 832 extraCheck = true := allFrom_add h24 extra_block_25
  have h26 : allFrom 0 864 extraCheck = true := allFrom_add h25 extra_block_26
  have h27 : allFrom 0 896 extraCheck = true := allFrom_add h26 extra_block_27
  have h28 : allFrom 0 928 extraCheck = true := allFrom_add h27 extra_block_28
  have h29 : allFrom 0 960 extraCheck = true := allFrom_add h28 extra_block_29
  have h30 : allFrom 0 992 extraCheck = true := allFrom_add h29 extra_block_30
  have h31 : allFrom 0 1024 extraCheck = true := allFrom_add h30 extra_block_31
  have h32 : allFrom 0 1056 extraCheck = true := allFrom_add h31 extra_block_32
  have h33 : allFrom 0 1088 extraCheck = true := allFrom_add h32 extra_block_33
  have h34 : allFrom 0 1120 extraCheck = true := allFrom_add h33 extra_block_34
  have h35 : allFrom 0 1152 extraCheck = true := allFrom_add h34 extra_block_35
  have h36 : allFrom 0 1184 extraCheck = true := allFrom_add h35 extra_block_36
  have h37 : allFrom 0 1216 extraCheck = true := allFrom_add h36 extra_block_37
  have h38 : allFrom 0 1224 extraCheck = true := allFrom_add h37 extra_block_38
  exact h38

theorem extraChecks (index : Nat) (hi : index < 1224) : extraCheck index = true := by
  simpa only [Nat.zero_add] using allFrom_spec extra_all index hi

theorem old_constant_bound {label i j weight : Nat} (hl : label < 482)
    (ht : (i,j,weight) ∈ terms) {s : ℝ}
    (hlo : (tightLower label i j : ℝ) / AMW.Cert.SC ≤ s)
    (hhi : s ≤ (tightUpper label i j : ℝ) / AMW.Cert.SC) :
    (bits (termAtom label i j) 35 32 : ℝ) / 10000000000 ≤ AMW.wfunAM s := by
  exact constantCheck_sound
    (termCheck_constant (frameCheck_term (frameChecks label hl) ht)) hlo hhi

theorem old_tangent_value {label i j weight index : Nat} (hl : label < 482)
    (ht : (i,j,weight) ∈ terms)
    (hi : index ∈ oldPointIndices (termAtom label i j)) :
    TVal AMW.Cert.PC8CLData.PT (tightLower label i j) (tightUpper label i j)
      (pointPosition index) := by
  have hf : termCheck label i j = true :=
    frameCheck_term (label := label) (t := (i,j,weight)) (frameChecks label hl) ht
  have hp : tangentCheck (tightLower label i j) (tightUpper label i j)
      (pointPosition index) (pointValue index) = true :=
    termCheck_tangent (label := label) (i := i) (j := j) (index := index) hf hi
  exact tangentCheck_sound (L := tightLower label i j) (U := tightUpper label i j)
    (p := pointPosition index) (value := pointValue index) hp

theorem old_point_value_eq {label i j weight index : Nat} (hl : label < 482)
    (ht : (i,j,weight) ∈ terms)
    (hi : index ∈ oldPointIndices (termAtom label i j)) :
    pointValue index = AMW.Cert.PC8CLData.PT (pointPosition index) := by
  have hf : termCheck label i j = true :=
    frameCheck_term (label := label) (t := (i,j,weight)) (frameChecks label hl) ht
  have hp : tangentCheck (tightLower label i j) (tightUpper label i j)
      (pointPosition index) (pointValue index) = true :=
    termCheck_tangent (label := label) (i := i) (j := j) (index := index) hf hi
  exact tangentCheck_pack_eq (L := tightLower label i j) (U := tightUpper label i j)
    (p := pointPosition index) (value := pointValue index) hp

theorem extraCheck_occurrence {index k : Nat} (h : extraCheck index = true)
    (hk : k < ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.2.2.2.1) :
    extraOccurrenceCheck
      ((pairPacks[index]?).getD (0,0,0,0,0,0)).1
      ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1
      ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.2.2.2.2 k = true := by
  simp only [extraCheck, List.all_eq_true] at h
  exact h k (List.mem_range.mpr hk)

theorem extra_tangent_value {index k : Nat} (hi : index < 1224)
    (hk : k < ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.2.2.2.1) :
    let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
    let atom := bits pair.2.2.2.2.2 (15*k) 15
    let offset := bits atom 0 1
    let i := bits atom 1 3
    let j := bits atom 4 3
    let packet := (catalog[bits atom 7 8]?).getD 0
    let p := bits packet 0 20
    let label := if offset = 0 then pair.1 else pair.2.1
    TVal AMW.Cert.PC8CLData.PT (min (tightLower label i j) p)
      (max (tightUpper label i j) p) p := by
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let atom := bits pair.2.2.2.2.2 (15*k) 15
  let offset := bits atom 0 1
  let i := bits atom 1 3
  let j := bits atom 4 3
  let packet := (catalog[bits atom 7 8]?).getD 0
  let p := bits packet 0 20
  let value := bits packet 20 96
  let label := if offset = 0 then pair.1 else pair.2.1
  have hc := extraCheck_occurrence (index := index) (k := k) (extraChecks index hi) hk
  dsimp only [extraOccurrenceCheck] at hc
  exact tangentCheck_sound (L := min (tightLower label i j) p)
    (U := max (tightUpper label i j) p) (p := p) (value := value) hc

theorem extra_point_value_eq {index k : Nat} (hi : index < 1224)
    (hk : k < ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.2.2.2.1) :
    let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
    let atom := bits pair.2.2.2.2.2 (15*k) 15
    let packet := (catalog[bits atom 7 8]?).getD 0
    bits packet 20 96 = AMW.Cert.PC8CLData.PT (bits packet 0 20) := by
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let atom := bits pair.2.2.2.2.2 (15*k) 15
  let offset := bits atom 0 1
  let i := bits atom 1 3
  let j := bits atom 4 3
  let packet := (catalog[bits atom 7 8]?).getD 0
  let p := bits packet 0 20
  let value := bits packet 20 96
  let label := if offset = 0 then pair.1 else pair.2.1
  have hc := extraCheck_occurrence (index := index) (k := k) (extraChecks index hi) hk
  dsimp only [extraOccurrenceCheck] at hc
  exact tangentCheck_pack_eq (L := min (tightLower label i j) p)
    (U := max (tightUpper label i j) p) (p := p) (value := value) hc

/- The added tangents use only spans already present in the original weight list. -/
noncomputable def extraSpanCheck (index : Nat) : Bool :=
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  (List.range pair.2.2.2.2.1).all fun k =>
    let atom := bits pair.2.2.2.2.2 (15*k) 15
    terms.any fun term => decide (term.1 = bits atom 1 3 ∧ term.2.1 = bits atom 4 3)

noncomputable def extraSpanBlock (block : Nat) : Bool :=
  (List.range 32).all fun offset =>
    let index := 32*block+offset
    if index < 1224 then extraSpanCheck index else true

private theorem extra_span_block_0 : extraSpanBlock 0 = true := by decide +kernel
private theorem extra_span_block_1 : extraSpanBlock 1 = true := by decide +kernel
private theorem extra_span_block_2 : extraSpanBlock 2 = true := by decide +kernel
private theorem extra_span_block_3 : extraSpanBlock 3 = true := by decide +kernel
private theorem extra_span_block_4 : extraSpanBlock 4 = true := by decide +kernel
private theorem extra_span_block_5 : extraSpanBlock 5 = true := by decide +kernel
private theorem extra_span_block_6 : extraSpanBlock 6 = true := by decide +kernel
private theorem extra_span_block_7 : extraSpanBlock 7 = true := by decide +kernel
private theorem extra_span_block_8 : extraSpanBlock 8 = true := by decide +kernel
private theorem extra_span_block_9 : extraSpanBlock 9 = true := by decide +kernel
private theorem extra_span_block_10 : extraSpanBlock 10 = true := by decide +kernel
private theorem extra_span_block_11 : extraSpanBlock 11 = true := by decide +kernel
private theorem extra_span_block_12 : extraSpanBlock 12 = true := by decide +kernel
private theorem extra_span_block_13 : extraSpanBlock 13 = true := by decide +kernel
private theorem extra_span_block_14 : extraSpanBlock 14 = true := by decide +kernel
private theorem extra_span_block_15 : extraSpanBlock 15 = true := by decide +kernel
private theorem extra_span_block_16 : extraSpanBlock 16 = true := by decide +kernel
private theorem extra_span_block_17 : extraSpanBlock 17 = true := by decide +kernel
private theorem extra_span_block_18 : extraSpanBlock 18 = true := by decide +kernel
private theorem extra_span_block_19 : extraSpanBlock 19 = true := by decide +kernel
private theorem extra_span_block_20 : extraSpanBlock 20 = true := by decide +kernel
private theorem extra_span_block_21 : extraSpanBlock 21 = true := by decide +kernel
private theorem extra_span_block_22 : extraSpanBlock 22 = true := by decide +kernel
private theorem extra_span_block_23 : extraSpanBlock 23 = true := by decide +kernel
private theorem extra_span_block_24 : extraSpanBlock 24 = true := by decide +kernel
private theorem extra_span_block_25 : extraSpanBlock 25 = true := by decide +kernel
private theorem extra_span_block_26 : extraSpanBlock 26 = true := by decide +kernel
private theorem extra_span_block_27 : extraSpanBlock 27 = true := by decide +kernel
private theorem extra_span_block_28 : extraSpanBlock 28 = true := by decide +kernel
private theorem extra_span_block_29 : extraSpanBlock 29 = true := by decide +kernel
private theorem extra_span_block_30 : extraSpanBlock 30 = true := by decide +kernel
private theorem extra_span_block_31 : extraSpanBlock 31 = true := by decide +kernel
private theorem extra_span_block_32 : extraSpanBlock 32 = true := by decide +kernel
private theorem extra_span_block_33 : extraSpanBlock 33 = true := by decide +kernel
private theorem extra_span_block_34 : extraSpanBlock 34 = true := by decide +kernel
private theorem extra_span_block_35 : extraSpanBlock 35 = true := by decide +kernel
private theorem extra_span_block_36 : extraSpanBlock 36 = true := by decide +kernel
private theorem extra_span_block_37 : extraSpanBlock 37 = true := by decide +kernel
private theorem extra_span_block_38 : extraSpanBlock 38 = true := by decide +kernel

private theorem extraSpanBlock_checked (block : Nat) (hb : block < 39) :
    extraSpanBlock block = true := by
  match block with
  | 0 => exact extra_span_block_0
  | 1 => exact extra_span_block_1
  | 2 => exact extra_span_block_2
  | 3 => exact extra_span_block_3
  | 4 => exact extra_span_block_4
  | 5 => exact extra_span_block_5
  | 6 => exact extra_span_block_6
  | 7 => exact extra_span_block_7
  | 8 => exact extra_span_block_8
  | 9 => exact extra_span_block_9
  | 10 => exact extra_span_block_10
  | 11 => exact extra_span_block_11
  | 12 => exact extra_span_block_12
  | 13 => exact extra_span_block_13
  | 14 => exact extra_span_block_14
  | 15 => exact extra_span_block_15
  | 16 => exact extra_span_block_16
  | 17 => exact extra_span_block_17
  | 18 => exact extra_span_block_18
  | 19 => exact extra_span_block_19
  | 20 => exact extra_span_block_20
  | 21 => exact extra_span_block_21
  | 22 => exact extra_span_block_22
  | 23 => exact extra_span_block_23
  | 24 => exact extra_span_block_24
  | 25 => exact extra_span_block_25
  | 26 => exact extra_span_block_26
  | 27 => exact extra_span_block_27
  | 28 => exact extra_span_block_28
  | 29 => exact extra_span_block_29
  | 30 => exact extra_span_block_30
  | 31 => exact extra_span_block_31
  | 32 => exact extra_span_block_32
  | 33 => exact extra_span_block_33
  | 34 => exact extra_span_block_34
  | 35 => exact extra_span_block_35
  | 36 => exact extra_span_block_36
  | 37 => exact extra_span_block_37
  | 38 => exact extra_span_block_38
  | n + 39 => omega

theorem extraSpanChecks (index : Nat) (hi : index < 1224) : extraSpanCheck index = true := by
  have hp := extraSpanBlock_checked (index/32) (by omega)
  have hm : index%32 ∈ List.range 32 := List.mem_range.mpr (Nat.mod_lt _ (by decide))
  have ht := (List.all_eq_true.mp hp) (index%32) hm
  have he : 32*(index/32)+index%32=index := by omega
  simpa only [he,if_pos hi] using ht

theorem extra_span_valid {index k : Nat} (hi : index < 1224)
    (hk : k < ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.2.2.2.1) :
    let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
    let atom := bits pair.2.2.2.2.2 (15*k) 15
    ∃ weight, (bits atom 1 3,bits atom 4 3,weight) ∈ terms := by
  have hc := extraSpanChecks index hi
  dsimp only [extraSpanCheck] at hc
  have ht := (List.all_eq_true.mp hc) k (List.mem_range.mpr hk)
  rcases List.any_eq_true.mp ht with ⟨term,hm,he⟩
  have hs : term.1 = bits (bits ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.2.2.2.2
      (15*k) 15) 1 3 ∧ term.2.1 = bits (bits ((pairPacks[index]?).getD
      (0,0,0,0,0,0)).2.2.2.2.2 (15*k) 15) 4 3 := of_decide_eq_true he
  rcases term with ⟨i,j,weight⟩
  dsimp at hs
  rcases hs with ⟨rfl,rfl⟩
  exact ⟨weight,hm⟩

end RHWeil.RecordSubmission.PointSoundness
