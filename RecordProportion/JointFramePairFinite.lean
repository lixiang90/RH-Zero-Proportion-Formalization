import RecordProportion.FiniteCertificate
import RecordProportion.JointFramePairFiniteData

/- Additive c448 pair proof. The old c260 data, theorem, and submission remain intact.
Every finite check is ordinary kernel reduction; the proof is over real gaps. -/
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RHWeil.RecordSubmission.JointFramePairFinite
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC8CL
open RHWeil.RecordSubmission.FiniteCertificateData
open RHWeil.RecordSubmission.FiniteCertificate
open RHWeil.RecordSubmission.JointFramePairData

theorem bool_and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa only [Bool.and_eq_true] using h

theorem spanInitial_entry (left right : Nat) (lo up : Int) (i j : Nat)
    (hi : i < 9) (hj : j < 9) :
    ((spanInitial left right lo up)[9*i+j]?).getD 0 =
      if 9*i+j = 8 then min (((pairClosure left right)[9*i+j]?).getD 0) up
      else if 9*i+j = 72 then min (((pairClosure left right)[9*i+j]?).getD 0) (-lo)
      else ((pairClosure left right)[9*i+j]?).getD 0 := by
  have hs : 9*i+j < 81 := by omega
  simp [spanInitial,hs]

theorem spanInitial_real {g : Nat → Real} {left right : Nat} {lo up : Int}
    (hc : RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
      (pairClosure left right))
    (hlo : (lo:Real) ≤ gapPotential g 8-gapPotential g 0)
    (hup : gapPotential g 8-gapPotential g 0 ≤ (up:Real)) :
    RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
      (spanInitial left right lo up) := by
  intro i hi j hj
  rw [spanInitial_entry left right lo up i j hi hj]
  by_cases h8 : 9*i+j = 8
  · have hi0 : i = 0 := by omega
    have hj8 : j = 8 := by omega
    subst i; subst j
    change gapPotential g 8-gapPotential g 0 ≤
      ((min (((pairClosure left right)[8]?).getD 0) up:Int):Real)
    rw [Int.cast_min]
    exact le_min (hc 0 (by decide) 8 (by decide)) hup
  · by_cases h72 : 9*i+j = 72
    · have hi8 : i = 8 := by omega
      have hj0 : j = 0 := by omega
      subst i; subst j
      change gapPotential g 0-gapPotential g 8 ≤
        ((min (((pairClosure left right)[72]?).getD 0) (-lo):Int):Real)
      rw [Int.cast_min,Int.cast_neg]
      apply le_min (hc 8 (by decide) 0 (by decide))
      linarith
    · simp only [if_neg h8,if_neg h72]
      exact hc i hi j hj

theorem branchGuard_fields {index : Nat} (h : branchGuard index = true) :
    let b := branch index
    b.left < 482 ∧ b.right < 482 ∧ b.lower ≤ b.upper ∧ b.bounds.size = 81 ∧
      b.paths.size = 81 :=
  of_decide_eq_true (bool_and_true h).1

theorem branchGuard_added {index : Nat} (h : branchGuard index = true)
    {a : Added} (ha : a ∈ (branch index).added) : addedCheck (branch index) a = true :=
  (List.all_eq_true.mp (bool_and_true (bool_and_true h).2).2) a ha

theorem branchClosure_real {g : Nat → Real} {index : Nat}
    (hguard : branchGuard index = true)
    (hc : RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
      (pairClosure (branch index).left (branch index).right))
    (hlo : ((branch index).lower:Real) ≤ gapPotential g 8-gapPotential g 0)
    (hhi : gapPotential g 8-gapPotential g 0 ≤ ((branch index).upper:Real)) :
    RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g) (branch index).bounds := by
  have hedge : ∀ i < 9, ∀ j < 9,
      gapPotential g j-gapPotential g i ≤ (branchEdge (branch index) i j:Real) := by
    intro i hi j hj
    have hprimitive : gapPotential g j-gapPotential g i ≤
        (primitiveBound (branch index).left (branch index).right i j:Real) := by
      apply (hc i hi j hj).trans
      exact_mod_cast pairClosure_le_primitive (branch index).left (branch index).right i j hi hj
    by_cases h08 : i = 0 ∧ j = 8
    · rcases h08 with ⟨rfl,rfl⟩
      change gapPotential g 8-gapPotential g 0 ≤
        ((min (primitiveBound (branch index).left (branch index).right 0 8) (branch index).upper:Int):Real)
      rw [Int.cast_min]
      exact le_min hprimitive hhi
    · by_cases h80 : i = 8 ∧ j = 0
      · rcases h80 with ⟨rfl,rfl⟩
        change gapPotential g 0-gapPotential g 8 ≤
          ((min (primitiveBound (branch index).left (branch index).right 8 0) (-(branch index).lower):Int):Real)
        rw [Int.cast_min,Int.cast_neg]
        apply le_min hprimitive
        linarith
      · simpa only [branchEdge,if_neg h08,if_neg h80] using hprimitive
  intro i hi j hj
  have hs : 9*i+j < 81 := by omega
  have hpaths := (bool_and_true (bool_and_true hguard).2).1
  have hpath := (List.all_eq_true.mp hpaths) (9*i+j) (List.mem_range.mpr hs)
  have hd : (9*i+j)/9=i := by omega
  have hm : (9*i+j)%9=j := by omega
  simp only [branchPathCheck,hd,hm] at hpath
  exact NinthSpanPaths.check_real_bound hpath hedge

theorem closedSpan_bounds {g : Nat → Real} {b : Branch} {i j : Nat}
    (hc : RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g) b.bounds)
    (hi : i ≤ j) (hj : j ≤ 8) :
    (spanLower b i j:Real)/(5*SC) ≤ gsum g i j ∧
      gsum g i j ≤ (spanUpper b i j:Real)/(5*SC) := by
  have hfor := hc i (by omega) j (by omega)
  have hrev := hc j (by omega) i (by omega)
  have hd := gapPotential_difference g i j hi
  simp only [spanLower,spanUpper,Int.cast_neg]
  norm_num [SC] at hd ⊢
  constructor <;> nlinarith

theorem branch_box {g : Nat → Real} {b : Branch}
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell b.left) g)
    (hr : InCell 7 PR (lowCell b.right) (fun r => g (r+1)))
    (hc : RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g) b.bounds)
    (c : Nat) (hcol : c < 42) :
    (boxLo b c:Real) ≤ actualValue g c ∧ actualValue g c ≤ (boxHi b c:Real) := by
  by_cases hs : c < 8
  · have hd := gapPotential_difference g c (c+1) (by omega)
    simp only [gsum_range,Nat.add_sub_cancel,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,Nat.add_zero] at hd
    have hfor := hc c (by omega) (c+1) (by omega)
    have hrev := hc (c+1) (by omega) c (by omega)
    have ht := htheta c hs
    simp only [boxLo,boxHi,actualValue,RHWeilRecord.RowEvaluation.actualValue,
      spanLower,spanUpper,if_pos hs,Int.cast_max,Int.cast_neg,Int.cast_mul,Int.cast_ofNat]
    norm_num [SC] at hd ⊢
    constructor
    · constructor <;> nlinarith
    · nlinarith
  · have hb := actualValue_box htheta hl hr c hcol
    simpa only [boxLo,boxHi,integerBoxLo,integerBoxHi,if_neg hs] using hb

def ReanchorCuts (a : Added) (L5 U5 : Int) (s : Real) : Prop :=
  let p := addedPoint a
  let value := addedValue a
  let V : Real := lo32 value
  let dm : Real := (lo32 (hi32 value):Real)-2000000000
  let dp : Real := 2000000000-(hi32 (hi32 value):Real)
  let l5 : Int := min L5 (5*(p:Int))
  let u5 : Int := max U5 (5*(p:Int))
  50*dm*SC*s-5*10000000000*SC*wfun s ≤
    -5*V*SC+50*dp*(p:Real)-10*(dp-dm)*(l5:Real) ∧
  50*dp*SC*s-5*10000000000*SC*wfun s ≤
    -5*V*SC+50*dm*(p:Real)-10*(dm-dp)*(u5:Real)

theorem added_tangent_cuts {b : Branch} {a : Added} {s : Real}
    (hleft : b.left < 482) (hright : b.right < 482)
    (hcheck : addedCheck b a = true) (hn : ¬(a.kind = 0 ∨ a.kind = 1))
    (hlo : (spanLower b a.first a.last:Real)/(5*SC) ≤ s)
    (hhi : s ≤ (spanUpper b a.first a.last:Real)/(5*SC)) :
    ReanchorCuts a (spanLower b a.first a.last) (spanUpper b a.first a.last) s := by
  have hrest := (bool_and_true hcheck).2
  simp only [if_neg hn] at hrest
  have hh := (bool_and_true hrest).2
  by_cases hk : a.kind = 2
  · rw [if_pos hk] at hh
    simpa only [ReanchorCuts,addedPoint,addedValue,if_pos hk] using
      JointFramePairPoints.direct_reanchor_scaled hh hlo hhi
  · rw [if_neg hk] at hh
    obtain ⟨hk3,hoff,hfirst,hlast,hterm,hpoint,hL,hU⟩ := of_decide_eq_true hh
    have hlab : addedLabel b a < 482 := by
      simp only [addedLabel]
      split_ifs <;> assumption
    have ht := PointSoundness.old_tangent_value hlab hterm hpoint
    have hpack := PointSoundness.old_point_value_eq hlab hterm hpoint
    have htcut := JointFramePairPoints.oldTVal_reanchor_scaled ht hL hU hlo hhi
    dsimp only at htcut
    rw [←hpack] at htcut
    simpa only [ReanchorCuts,addedPoint,addedValue,if_neg hk] using htcut

theorem addedRow_sound {g : Nat → Real} {b : Branch} {a : Added}
    (hleft : b.left < 482) (hright : b.right < 482)
    (hcheck : addedCheck b a = true)
    (hc : RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g) b.bounds) :
    (∑ c ∈ Finset.range 42, ((addedRow b a).coeff c:Real)*actualValue g c) ≤
      ((addedRow b a).bound:Real) := by
  have hshape : a.first < a.last ∧ a.last ≤ 8 :=
    of_decide_eq_true (bool_and_true hcheck).1
  have hfor := hc a.first (by omega) a.last (by omega)
  have hrev := hc a.last (by omega) a.first (by omega)
  have hd := gapPotential_difference g a.first a.last (by omega)
  by_cases hk0 : a.kind = 0
  · simp only [addedRow,if_pos hk0]
    change (∑ c ∈ Finset.range 42, (_:IntegerRow).coeff c *
      RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
    rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ hshape.2 (Or.inl rfl),row_gsum_eq]
    norm_num [spanUpper,SC] at hd ⊢
    nlinarith
  · by_cases hk1 : a.kind = 1
    · simp only [addedRow,if_neg hk0,if_pos hk1]
      change (∑ c ∈ Finset.range 42, (_:IntegerRow).coeff c *
        RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
      rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ hshape.2 (Or.inl rfl),row_gsum_eq]
      norm_num [spanLower,SC] at hd ⊢
      nlinarith
    · have hn : ¬(a.kind = 0 ∨ a.kind = 1) := by tauto
      have hrest := (bool_and_true hcheck).2
      simp only [if_neg hn] at hrest
      have hsquare : (a.first,a.last) ∈ squareSpans :=
        of_decide_eq_true (bool_and_true hrest).1
      have hsq := RHWeilRecord.RowEvaluation.squareColumn_eval wfun g a.first a.last hsquare
      have hb := closedSpan_bounds hc (by omega : a.first ≤ a.last) hshape.2
      have hcuts := added_tangent_cuts hleft hright hcheck hn hb.1 hb.2
      change (∑ c ∈ Finset.range 42, ((addedRow b a).coeff c:Real) *
        RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
      have hlast : (addedRow b a).last ≤ 8 := by
        simp only [addedRow,if_neg hk0,if_neg hk1]
        split_ifs <;> exact hshape.2
      have hz : (addedRow b a).zcoef = 0 ∨
          8 ≤ (addedRow b a).square ∧ (addedRow b a).square < 42 := by
        simp only [addedRow,if_neg hk0,if_neg hk1]
        split_ifs <;> exact Or.inr ⟨hsq.1,hsq.2.1⟩
      rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ hlast hz]
      cases hside : a.rightCut
      all_goals
        simp only [addedRow,if_neg hk0,if_neg hk1,hside,Bool.false_eq_true,
          ↓reduceIte]
        rw [hsq.2.2,row_gsum_eq]
        dsimp only [ReanchorCuts] at hcuts
        norm_num [SC,RHWeilRecord.RowEvaluation.kernelScale] at hcuts ⊢
        nlinarith [hcuts.1,hcuts.2]

theorem branchRows_sound {g : Nat → Real} {index : Nat}
    (hguard : branchGuard index = true)
    (hl : InCell 7 PR (lowCell (branch index).left) g)
    (hr : InCell 7 PR (lowCell (branch index).right) (fun r => g (r+1)))
    (hc : RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g) (branch index).bounds) :
    ∀ row ∈ branchRows (branch index),
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real) := by
  have hshape := branchGuard_fields hguard
  intro row hm
  simp only [branchRows,List.mem_append] at hm
  rcases hm with (hm|hm)|hm
  · exact frameRows_sound hshape.1 (by decide) (by simpa only [Nat.add_zero] using hl) row hm
  · exact frameRows_sound hshape.2.1 (by decide) hr row hm
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact addedRow_sound hshape.1 hshape.2.1 (branchGuard_added hguard ha) hc

theorem branch_real_bound {g : Nat → Real} {index : Nat}
    (hguard : branchGuard index = true) (hnumeric : branchNumeric index = true)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell (branch index).left) g)
    (hr : InCell 7 PR (lowCell (branch index).right) (fun r => g (r+1)))
    (hlo : ((branch index).lower:Real) ≤ gapPotential g 8-gapPotential g 0)
    (hhi : gapPotential g 8-gapPotential g 0 ≤ ((branch index).upper:Real)) :
    (805448:Real)/100000000 ≤ scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  let b := branch index
  have hc := branchClosure_real hguard (closedPotentialBound htheta hl hr) hlo hhi
  have hrows := branchRows_sound hguard hl hr hc
  have hlam : ∀ r ∈ branchMultipliers b, 0 ≤ r.2 := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    dsimp only
    split_ifs <;> positivity
  have hselected : ∀ r ∈ branchMultipliers b,
      (∑ c ∈ Finset.range 42, (r.1.coeff c:Real)*actualValue g c) ≤ (r.1.bound:Real) := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact selectedRow_sound hrows p.1
  have hnumeric' : newIntegerTarget ≤ branchLower b := of_decide_eq_true hnumeric
  have hbound := RHWeilRecord.SparseDualSoundness.threshold_sound 42 (branchMultipliers b)
    (fun c => 10000000000*objectiveCoeff c) (actualValue g) (fun r c => r.1.coeff c)
    (fun r => r.1.bound) (fun r => r.2) (boxLo b) (boxHi b)
    newIntegerTarget hnumeric' hlam hselected
    (fun c hcol => (branch_box htheta hl hr hc c hcol).1)
    (fun c hcol => (branch_box htheta hl hr hc c hcol).2)
  simp only [newIntegerTarget,Int.cast_mul,Int.cast_ofNat] at hbound
  simp_rw [mul_assoc] at hbound
  rw [←Finset.mul_sum,integerObjective_identity] at hbound
  norm_num [kernelScale] at hbound ⊢
  nlinarith

/-- Closed coverage uses overlaps, so a split endpoint belongs to both adjacent
branches. Repeating a last branch handles patches with fewer than three pieces. -/
theorem patch_real_bound {g : Nat → Real} {index : Nat} (hi : index < 57)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell (patch index).left) g)
    (hr : InCell 7 PR (lowCell (patch index).right) (fun r => g (r+1))) :
    (805448:Real)/100000000 ≤ scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  let p := patch index
  obtain ⟨hpl,hpr,hb0,hb1,hb2,h0l,h0r,h1l,h1r,h2l,h2r,hlo,hup,h01,h12⟩ :=
    of_decide_eq_true (allPatchShapes index hi)
  have hc := closedPotentialBound htheta hl hr
  have hSlo : ((branch p.branch0).lower:Real) ≤ gapPotential g 8-gapPotential g 0 := by
    have h := NinthSpanPaths.check_real_bound (p:=gapPotential g) hlo
      (fun i hi j hj => primitiveBound_sound htheta hl hr hi hj)
    norm_num at h ⊢
    linarith
  have hShi : gapPotential g 8-gapPotential g 0 ≤ ((branch p.branch2).upper:Real) := by
    exact NinthSpanPaths.check_real_bound hup (fun i hi j hj => primitiveBound_sound htheta hl hr hi hj)
  have h01' : ((branch p.branch1).lower:Real) ≤ ((branch p.branch0).upper:Real) := by
    exact_mod_cast h01
  have h12' : ((branch p.branch2).lower:Real) ≤ ((branch p.branch1).upper:Real) := by
    exact_mod_cast h12
  by_cases h0 : gapPotential g 8-gapPotential g 0 ≤ ((branch p.branch0).upper:Real)
  · apply branch_real_bound (allBranchGuards _ hb0) (allBranchNumeric _ hb0) htheta
      (by simpa only [h0l] using hl) (by simpa only [h0r] using hr) hSlo h0
  · by_cases h1 : gapPotential g 8-gapPotential g 0 ≤ ((branch p.branch1).upper:Real)
    · apply branch_real_bound (allBranchGuards _ hb1) (allBranchNumeric _ hb1) htheta
        (by simpa only [h1l] using hl) (by simpa only [h1r] using hr) _ h1
      linarith
    · apply branch_real_bound (allBranchGuards _ hb2) (allBranchNumeric _ hb2) htheta
        (by simpa only [h2l] using hl) (by simpa only [h2r] using hr) _ hShi
      linarith

-- The old sparse duals are rechecked at the stronger threshold, while their
-- complete row soundness and residual-box semantics are reused unchanged.
theorem strong_representative_bound {g : Nat → Real} {index : Nat}
    (hi : index < 1224)
    (hc : strongIntegerCheck index = true)
    (hl : ((pairPacks[index]?).getD (0,0,0,0,0,0)).1 < 482)
    (hr : ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1 < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).1) g)
    (hgr : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1)
      (fun r => g (r+1))) :
    (805448:Real)/100000000 ≤
      scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let rows := frameRows pair.1 0 ++ frameRows pair.2.1 1 ++
    extraRows pair.1 pair.2.1 pair.2.2.2.2.1 pair.2.2.2.2.2
  let multipliers := (decodeMultipliers pair.2.2.1 pair.2.2.2.1).map fun p =>
    let row := rows.getD p.1 default
    let lambda : Int := p.2 * (if row.geometric then 10000000000 else 1)
    (row,lambda)
  let lo := fun column =>
    if column < 8 then max (4*32768) (-((pairClosure pair.1 pair.2.1)[9*(column+1)+column]?).getD 0) else 0
  let up := fun column =>
    if column < 8 then ((pairClosure pair.1 pair.2.1)[9*column+column+1]?).getD 0 else 5*10000000000*32768
  have hrows : ∀ row ∈ rows,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real) := by
    intro row hm
    simp only [rows,List.mem_append] at hm
    rcases hm with (hm|hm)|hm
    · exact frameRows_sound hl (by decide) (by simpa only [Nat.add_zero] using hgl) row hm
    · exact frameRows_sound hr (by decide) hgr row hm
    · exact extraRows_sound hi hl hr hgl hgr row hm
  have hlam : ∀ r ∈ multipliers, 0 ≤ r.2 := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    dsimp only
    split_ifs <;> positivity
  have hselected : ∀ r ∈ multipliers,
      (∑ c ∈ Finset.range 42, (r.1.coeff c:Real)*actualValue g c) ≤ (r.1.bound:Real) := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact selectedRow_sound hrows p.1
  have hbox := actualValue_box htheta hgl hgr
  have hnumeric : 2*805448*(5*10000000000*32768)*1000000000 ≤ integerCertificateLower index :=
    of_decide_eq_true hc
  have heq : integerCertificateLower index = RHWeilRecord.SparseDualSoundness.checkerL 42 multipliers
      (fun c => 1000000000*objectiveCoeff c) (fun r c => r.1.coeff c)
      (fun r => r.1.bound) (fun r => r.2) lo up := rfl
  rw [heq] at hnumeric
  have hbound := RHWeilRecord.SparseDualSoundness.threshold_sound 42 multipliers
    (fun c => 1000000000*objectiveCoeff c) (actualValue g) (fun r c => r.1.coeff c)
    (fun r => r.1.bound) (fun r => r.2) lo up
    (2*805448*(5*10000000000*32768)*1000000000) hnumeric hlam hselected
    (fun c hc => (hbox c hc).1) (fun c hc => (hbox c hc).2)
  simp only [Int.cast_mul,Int.cast_ofNat] at hbound
  simp_rw [mul_assoc] at hbound
  rw [←Finset.mul_sum,integerObjective_identity] at hbound
  norm_num [kernelScale] at hbound ⊢
  nlinarith


/-- Adjacent path witnesses certify the stronger old residual boxes directly
over real gaps; no inequality from a path to an optimal Floyd bound is used. -/
theorem oldPath_box {g : Nat → Real} {index : Nat}
    (hc : oldPathCheck index = true)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hl : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).1) g)
    (hr : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1)
      (fun r => g (r+1)))
    (c : Nat) (hcol : c < 42) :
    (oldPathLo index c:Real) ≤ actualValue g c ∧
      actualValue g c ≤ (oldPathHi index c:Real) := by
  by_cases hs : c < 8
  · have hp := List.all_eq_true.mp (bool_and_true hc).2
    have hf := hp (2*c) (List.mem_range.mpr (by omega))
    have hb := hp (2*c+1) (List.mem_range.mpr (by omega))
    have hd0 : (2*c)/2=c := by omega
    have hm0 : (2*c)%2=0 := by omega
    have hd1 : (2*c+1)/2=c := by omega
    have hm1 : (2*c+1)%2=1 := by omega
    simp only [oldPathSlotCheck,hd0,hm0,if_pos rfl] at hf
    simp only [oldPathSlotCheck,hd1,hm1,if_neg (by decide : ¬(1:Nat)=0)] at hb
    have hfor := NinthSpanPaths.check_real_bound (p:=gapPotential g) hf
      (fun i hi j hj => primitiveBound_sound htheta hl hr hi hj)
    have hrev := NinthSpanPaths.check_real_bound (p:=gapPotential g) hb
      (fun i hi j hj => primitiveBound_sound htheta hl hr hi hj)
    change gapPotential g (c+1)-gapPotential g c ≤
      (((oldBox index).bounds[2*c]?).getD 0:Int) at hfor
    have hd := gapPotential_difference g c (c+1) (by omega)
    simp only [gsum_range,Nat.add_sub_cancel,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,Nat.add_zero] at hd
    have ht := htheta c hs
    simp only [oldPathLo,oldPathHi,actualValue,RHWeilRecord.RowEvaluation.actualValue,
      if_pos hs,Int.cast_max,Int.cast_neg,Int.cast_mul,Int.cast_ofNat]
    norm_num [SC] at hd ⊢
    constructor
    · constructor <;> nlinarith
    · nlinarith
  · have hb := actualValue_box htheta hl hr c hcol
    simpa only [oldPathLo,oldPathHi,integerBoxLo,integerBoxHi,if_neg hs] using hb

theorem path_representative_bound {g : Nat → Real} {index : Nat}
    (hi : index < 1224)
    (hc : strongPathCheck index = true)
    (hl : ((pairPacks[index]?).getD (0,0,0,0,0,0)).1 < 482)
    (hr : ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1 < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).1) g)
    (hgr : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1)
      (fun r => g (r+1))) :
    (805448:Real)/100000000 ≤
      scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  let pair := (pairPacks[index]?).getD (0,0,0,0,0,0)
  have hrows : ∀ row ∈ oldRows index,
      (∑ c ∈ Finset.range 42, (row.coeff c:Real)*actualValue g c) ≤ (row.bound:Real) := by
    intro row hm
    simp only [oldRows,List.mem_append] at hm
    rcases hm with (hm|hm)|hm
    · exact frameRows_sound hl (by decide) (by simpa only [Nat.add_zero] using hgl) row hm
    · exact frameRows_sound hr (by decide) hgr row hm
    · exact extraRows_sound hi hl hr hgl hgr row hm
  have hlam : ∀ r ∈ oldMultipliers index, 0 ≤ r.2 := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    dsimp only
    split_ifs <;> positivity
  have hselected : ∀ r ∈ oldMultipliers index,
      (∑ c ∈ Finset.range 42, (r.1.coeff c:Real)*actualValue g c) ≤ (r.1.bound:Real) := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact selectedRow_sound hrows p.1
  have hnumeric : 2*805448*(5*10000000000*32768)*1000000000 ≤ oldPathLower index :=
    of_decide_eq_true (bool_and_true hc).2
  have hbound := RHWeilRecord.SparseDualSoundness.threshold_sound 42 (oldMultipliers index)
    (fun c => 1000000000*objectiveCoeff c) (actualValue g) (fun r c => r.1.coeff c)
    (fun r => r.1.bound) (fun r => r.2) (oldPathLo index) (oldPathHi index)
    (2*805448*(5*10000000000*32768)*1000000000) hnumeric hlam hselected
    (fun c hcol => (oldPath_box (bool_and_true hc).1 htheta hgl hgr c hcol).1)
    (fun c hcol => (oldPath_box (bool_and_true hc).1 htheta hgl hgr c hcol).2)
  simp only [Int.cast_mul,Int.cast_ofNat] at hbound
  simp_rw [mul_assoc] at hbound
  rw [←Finset.mul_sum,integerObjective_identity] at hbound
  norm_num [kernelScale] at hbound ⊢
  nlinarith


theorem representative_bound {g : Nat → Real} {index : Nat}
    (hi : index < 1224)
    (hl : ((pairPacks[index]?).getD (0,0,0,0,0,0)).1 < 482)
    (hr : ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1 < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).1) g)
    (hgr : InCell 7 PR (lowCell ((pairPacks[index]?).getD (0,0,0,0,0,0)).2.1)
      (fun r => g (r+1))) :
    (805448:Real)/100000000 ≤
      scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  by_cases hp : repRoute index < 57
  · have hs := of_decide_eq_true (allRepRoutes index hi)
    rcases hs with he | ⟨hroute,hleft,hright⟩
    · omega
    · exact patch_real_bound hp htheta
        (by simpa only [hleft] using hgl) (by simpa only [hright] using hgr)
  · have hn := allOldOrPatch index hi
    have hn' : strongBasicCheck index = true ∨ strongPathCheck index = true := by
      simpa only [oldOrPatch,decide_eq_false hp,Bool.false_or,Bool.or_eq_true] using hn
    rcases hn' with hbasic | hpath
    · exact strong_representative_bound hi (strongCheck_of_basic hbasic) hl hr htheta hgl hgr
    · exact path_representative_bound hi hpath hl hr htheta hgl hgr

theorem low_pair_bound (g : Nat → Real) (left right : Nat)
    (hl : left < 482) (hr : right < 482)
    (htheta : ∀ r < 8, (4:Real)/5 ≤ g r)
    (hgl : InCell 7 PR (lowCell left) g)
    (hgr : InCell 7 PR (lowCell right) (fun r => g (r+1))) :
    (805448:Real)/100000000 ≤
      scalarF9 (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  have hinit := initialPotentialBound htheta hgl hgr
  change RHWeilRecord.FloydSoundness.RealPotentialBound (gapPotential g)
    (initialPairBounds left right) at hinit
  obtain ⟨index,hi,heindex⟩ := RHWeilRecord.GeometryCoverage.physical_pair_covered hl hr hinit
  have hoc := orbit_coverage index hi
  simp only [orbitCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hoc
  let rep := orbitIndexAt index / 2
  have hrep : rep < 1224 := hoc.1
  let packet := (pairPacks[rep]?).getD (0,0,0,0,0,0)
  have hs := representative_packet_shape rep hrep
  change packet.1 < 482 ∧ packet.2.1 < 482 ∧
    representativeLabel rep = pairLabel packet.1 packet.2.1 at hs
  have he := hoc.2
  rw [heindex] at he
  by_cases heven : orbitIndexAt index % 2 = 0
  · rw [if_pos heven,hs.2.2] at he
    have hlabels := RHWeilRecord.GeometryCoverage.pairLabel_injective hl hr hs.1 hs.2.1 he
    have hcells0 : InCell 7 PR (lowCell packet.1) g := by simpa only [hlabels.1] using hgl
    have hcells1 : InCell 7 PR (lowCell packet.2.1) (fun r => g (r+1)) := by
      simpa only [hlabels.2] using hgr
    exact representative_bound hrep hs.1 hs.2.1 htheta hcells0 hcells1
  · rw [if_neg heven,hs.2.2,RHWeilRecord.GeometryCoverage.reflectedPair_pairLabel hs.1 hs.2.1] at he
    have hlabels := RHWeilRecord.GeometryCoverage.pairLabel_injective hl hr
      (reflectionLabel_lt hs.2.1) (reflectionLabel_lt hs.1) he
    have hrevcells := reverseEight_cells hl hr hgl hgr
    have href0 : reflectionLabel right = packet.1 := by
      rw [hlabels.2,reflectionLabel_involution hs.1]
    have href1 : reflectionLabel left = packet.2.1 := by
      rw [hlabels.1,reflectionLabel_involution hs.2.1]
    have ht : ∀ r < 8, (4:Real)/5 ≤ reverseEight g r := by
      intro r hr
      exact htheta (7-r) (by omega)
    have hcells0 : InCell 7 PR (lowCell packet.1) (reverseEight g) := by
      simpa only [href0] using hrevcells.1
    have hcells1 : InCell 7 PR (lowCell packet.2.1) (fun r => reverseEight g (r+1)) := by
      simpa only [href1] using hrevcells.2
    have hb := representative_bound hrep hs.1 hs.2.1 ht hcells0 hcells1
    rw [reverseEight_scalar] at hb
    exact hb


open RHWeil.RecordSubmission.JointFramePairFrame

theorem framePrimitive_sound {g : Nat → Real} {label : Nat}
    (htheta : ∀ r < 7, (4:Real)/5 ≤ g r)
    (hcell : InCell 7 PR (lowCell label) g) :
    ∀ i < 8, ∀ j < 8,
      gapPotential g j-gapPotential g i ≤ (framePrimitive label i j:Real) := by
  intro i hi j hj
  by_cases heq : i=j
  · subst j
    simp [framePrimitive]
  have hraw : gapPotential g j-gapPotential g i ≤ ((if i < j then 5*(cellUpper label i j:Int) else -5*(cellLower label j i:Int):Int):Real) := by
    by_cases hij : i < j
    · have hb := lowCell_spanbounds label g hcell i j hij (by omega)
      have hd := gapPotential_difference g i j hij.le
      simp only [if_pos hij,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
      norm_num [SC] at hb hd
      nlinarith [hb.2]
    · have hji : j < i := by omega
      have hb := lowCell_spanbounds label g hcell j i hji (by omega)
      have hd := gapPotential_difference g j i hji.le
      simp only [if_neg hij,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast]
      norm_num [SC] at hb hd
      nlinarith [hb.1]
  by_cases hadj : i=j+1
  · have hd := gapPotential_difference g j i (by omega)
    have ht := htheta j (by omega)
    subst i
    simp only [gsum_range,Nat.add_sub_cancel,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,Nat.add_zero] at hd
    simp only [framePrimitive,if_neg heq,ite_true,Int.cast_min]
    apply le_min hraw
    norm_num [SC] at hd ⊢
    nlinarith
  · simpa only [framePrimitive,if_neg heq,if_neg hadj] using hraw

theorem frameGuard_fields {index : Nat} (h : frameGuard index=true) :
    let b:=frameBranch index
    b.label < 241 ∧ b.splitFirst < b.splitLast ∧ b.splitLast ≤ 7 ∧
      b.lower ≤ b.upper ∧ b.bounds.size=64 ∧ b.paths.size=64 :=
  of_decide_eq_true (bool_and_true (bool_and_true (bool_and_true h).1).1).1

theorem frameGuard_added {index : Nat} (h : frameGuard index=true)
    {a : Added} (ha : a∈(frameBranch index).added) :
    frameAddedCheck (frameBranch index) a=true :=
  (List.all_eq_true.mp (bool_and_true (bool_and_true h).1).2) a ha

theorem frameClosure_real {g : Nat → Real} {index : Nat}
    (hguard : frameGuard index=true)
    (htheta : ∀ r < 7,(4:Real)/5 ≤ g r)
    (hcell : InCell 7 PR (lowCell (frameBranch index).label) g)
    (hlo : ((frameBranch index).lower:Real) ≤ gapPotential g (frameBranch index).splitLast-gapPotential g (frameBranch index).splitFirst)
    (hhi : gapPotential g (frameBranch index).splitLast-gapPotential g (frameBranch index).splitFirst ≤ ((frameBranch index).upper:Real)) :
    FramePotentialBound (gapPotential g) (frameBranch index).bounds := by
  have hedge : ∀ i < 8,∀ j < 8,
      gapPotential g j-gapPotential g i ≤ (frameEdge (frameBranch index) i j:Real) := by
    intro i hi j hj
    have hp := framePrimitive_sound htheta hcell i hi j hj
    by_cases hfor : i=(frameBranch index).splitFirst ∧ j=(frameBranch index).splitLast
    · rcases hfor with ⟨rfl,rfl⟩
      simp only [frameEdge,and_self,ite_true,Int.cast_min]
      exact le_min hp hhi
    · by_cases hrev : i=(frameBranch index).splitLast ∧ j=(frameBranch index).splitFirst
      · rcases hrev with ⟨rfl,rfl⟩
        simp only [frameEdge,if_neg hfor,and_self,ite_true,Int.cast_min,Int.cast_neg]
        apply le_min hp
        linarith
      · simpa only [frameEdge,if_neg hfor,if_neg hrev] using hp
  intro i hi j hj
  have hs : 8*i+j < 64 := by omega
  have hpaths := (bool_and_true (bool_and_true (bool_and_true hguard).1).1).2
  have hpath := (List.all_eq_true.mp hpaths) (8*i+j) (List.mem_range.mpr hs)
  have hd : (8*i+j)/8=i := by omega
  have hm : (8*i+j)%8=j := by omega
  simp only [framePathCheck,hd,hm] at hpath
  exact JointFramePairPaths.check_real_bound hpath hedge

theorem frame_closedSpan_bounds {g : Nat → Real} {b : FrameBranch} {i j : Nat}
    (hc : FramePotentialBound (gapPotential g) b.bounds) (hi : i ≤ j) (hj : j ≤ 7) :
    (frameSpanLower b i j:Real)/(5*SC) ≤ gsum g i j ∧
      gsum g i j ≤ (frameSpanUpper b i j:Real)/(5*SC) := by
  have hfor := hc i (by omega) j (by omega)
  have hrev := hc j (by omega) i (by omega)
  have hd := gapPotential_difference g i j hi
  simp only [frameSpanLower,frameSpanUpper,Int.cast_neg]
  norm_num [SC] at hd ⊢
  constructor <;> nlinarith

theorem frame_span_square {i j weight : Nat}
    (h : (i,j,weight)∈terms ∨ (i,j)∈terms.map (fun t=>(t.1,t.2.1))) :
    (i,j)∈squareSpans ∧ 8 ≤ squareColumn i j ∧ squareColumn i j < 34 := by
  have hm : (i,j)∈terms.map (fun t=>(t.1,t.2.1)) := by
    rcases h with h|h
    · exact List.mem_map.mpr ⟨(i,j,weight),h,rfl⟩
    · exact h
  have ht : (terms.map (fun t=>(t.1,t.2.1))).all
      (fun p=>decide (p∈squareSpans ∧ 8 ≤ squareColumn p.1 p.2 ∧ squareColumn p.1 p.2 < 34))=true := by decide
  exact of_decide_eq_true ((List.all_eq_true.mp ht) (i,j) hm)

theorem frame_added_tangent_cuts {b : FrameBranch} {a : Added} {s : Real}
    (hlabel : b.label < 241) (hcheck : frameAddedCheck b a=true)
    (hn : ¬(a.kind=0 ∨ a.kind=1))
    (hlo : (frameSpanLower b a.first a.last:Real)/(5*SC) ≤ s)
    (hhi : s ≤ (frameSpanUpper b a.first a.last:Real)/(5*SC)) :
    ReanchorCuts a (frameSpanLower b a.first a.last) (frameSpanUpper b a.first a.last) s := by
  have hrest := (bool_and_true hcheck).2
  simp only [if_neg hn] at hrest
  have hh := (bool_and_true hrest).2
  by_cases hk : a.kind=2
  · rw [if_pos hk] at hh
    simpa only [ReanchorCuts,addedPoint,addedValue,if_pos hk] using
      JointFramePairPoints.direct_reanchor_scaled hh hlo hhi
  · rw [if_neg hk] at hh
    obtain ⟨hk3,hoff,hfirst,hlast,hterm,hpoint,hL,hU⟩:=of_decide_eq_true hh
    have hlab : b.label < 482 := by omega
    have ht := PointSoundness.old_tangent_value hlab hterm hpoint
    have hpack := PointSoundness.old_point_value_eq hlab hterm hpoint
    have hcuts := JointFramePairPoints.oldTVal_reanchor_scaled ht hL hU hlo hhi
    dsimp only at hcuts
    rw [←hpack] at hcuts
    simpa only [ReanchorCuts,addedPoint,addedValue,if_neg hk] using hcuts

theorem frame_addedRow_sound {g : Nat → Real} {b : FrameBranch} {a : Added}
    (hlabel : b.label < 241) (hcheck : frameAddedCheck b a=true)
    (hc : FramePotentialBound (gapPotential g) b.bounds) :
    (∑ c∈Finset.range 33,(frameCoeff (frameAddedRow b a) c:Real)*frameValue g c) ≤ ((frameAddedRow b a).bound:Real) := by
  have hshape : a.first < a.last ∧ a.last ≤ 7 := of_decide_eq_true (bool_and_true hcheck).1
  have hfor := hc a.first (by omega) a.last (by omega)
  have hrev := hc a.last (by omega) a.first (by omega)
  have hd := gapPotential_difference g a.first a.last (by omega)
  by_cases hk0 : a.kind=0
  · simp only [frameAddedRow,if_pos hk0]
    rw [frame_rowDot_transport42 g _ hshape.2 (Or.inl rfl)]
    change (∑ c∈Finset.range 42,(_:IntegerRow).coeff c*
      RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
    rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ (by change a.last ≤ 8; omega) (Or.inl rfl),row_gsum_eq]
    norm_num [frameSpanUpper,SC] at hd ⊢
    nlinarith
  · by_cases hk1 : a.kind=1
    · simp only [frameAddedRow,if_neg hk0,if_pos hk1]
      rw [frame_rowDot_transport42 g _ hshape.2 (Or.inl rfl)]
      change (∑ c∈Finset.range 42,(_:IntegerRow).coeff c*
        RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
      rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ (by change a.last ≤ 8; omega) (Or.inl rfl),row_gsum_eq]
      norm_num [frameSpanLower,SC] at hd ⊢
      nlinarith
    · have hn : ¬(a.kind=0 ∨ a.kind=1) := by tauto
      have hrest := (bool_and_true hcheck).2
      simp only [if_neg hn] at hrest
      have hsq := frame_span_square (of_decide_eq_true (bool_and_true hrest).1)
      have hsqval := RHWeilRecord.RowEvaluation.squareColumn_eval wfun g a.first a.last hsq.1
      have hb := frame_closedSpan_bounds hc (by omega : a.first ≤ a.last) hshape.2
      have hcuts := frame_added_tangent_cuts hlabel hcheck hn hb.1 hb.2
      have hlast : (frameAddedRow b a).last ≤ 7 := by
        simp only [frameAddedRow,if_neg hk0,if_neg hk1]
        split_ifs <;> exact hshape.2
      have hz : (frameAddedRow b a).zcoef=0 ∨
          8 ≤ (frameAddedRow b a).square ∧ (frameAddedRow b a).square < 34 := by
        simp only [frameAddedRow,if_neg hk0,if_neg hk1]
        split_ifs <;> exact Or.inr hsq.2
      rw [frame_rowDot_transport42 g _ hlast hz]
      change (∑ c∈Finset.range 42,((frameAddedRow b a).coeff c:Real)*
        RHWeilRecord.RowEvaluation.actualValue wfun g c) ≤ _
      have hz42 : (frameAddedRow b a).zcoef=0 ∨
          8 ≤ (frameAddedRow b a).square ∧ (frameAddedRow b a).square < 42 := by
        rcases hz with hz|hz
        · exact Or.inl hz
        · exact Or.inr ⟨hz.1,by omega⟩
      rw [RHWeilRecord.RowEvaluation.rowDot_eval wfun g _ (by omega) hz42]
      cases hside : a.rightCut
      all_goals
        simp only [frameAddedRow,if_neg hk0,if_neg hk1,hside,Bool.false_eq_true,↓reduceIte]
        rw [hsqval.2.2,row_gsum_eq]
        dsimp only [ReanchorCuts] at hcuts
        norm_num [SC,RHWeilRecord.RowEvaluation.kernelScale] at hcuts ⊢
        nlinarith [hcuts.1,hcuts.2]

theorem frameRows_sound {g : Nat → Real} {index : Nat}
    (hguard : frameGuard index=true)
    (hcell : InCell 7 PR (lowCell (frameBranch index).label) g)
    (hc : FramePotentialBound (gapPotential g) (frameBranch index).bounds) :
    ∀ row∈frameRowsFor (frameBranch index),
      (∑ c∈Finset.range 33,(frameCoeff row c:Real)*frameValue g c) ≤ (row.bound:Real) := by
  have hshape := frameGuard_fields hguard
  have hbaselines := (bool_and_true hguard).2
  intro row hm
  simp only [frameRowsFor,List.mem_append] at hm
  rcases hm with hm|hm
  · have hbase := of_decide_eq_true ((List.all_eq_true.mp hbaselines) row hm)
    apply frame_row_sound hbase.1 hbase.2
    exact RHWeil.RecordSubmission.FiniteCertificate.frameRows_sound (by omega : (frameBranch index).label < 482) (by decide : 0 < 2)
      (by simpa only [Nat.add_zero] using hcell) row hm
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact frame_addedRow_sound hshape.1 (frameGuard_added hguard ha) hc

theorem frame_selectedRow_sound {g : Nat → Real} {rows : List IntegerRow}
    (hrows : ∀ row∈rows,
      (∑ c∈Finset.range 33,(frameCoeff row c:Real)*frameValue g c) ≤ (row.bound:Real))
    (index : Nat) :
    (∑ c∈Finset.range 33,(frameCoeff (rows.getD index default) c:Real)*frameValue g c) ≤ ((rows.getD index default).bound:Real) := by
  by_cases hi : index < rows.length
  · rw [List.getD_eq_getElem rows default hi]
    exact hrows _ (List.getElem_mem hi)
  · rw [List.getD_eq_default rows default (Nat.le_of_not_lt hi)]
    have hb : (default:IntegerRow).bound=0 := rfl
    have hz : ∀ c,(default:IntegerRow).coeff c=0 := by
      intro c
      change (if c < 8 then if 0 ≤ c ∧ c < 0 then (0:Int) else 0 else if c=0 then 0 else 0)=0
      simp
    simp [hb,frameCoeff,hz]

theorem frame_box {g : Nat → Real} {b : FrameBranch}
    (htheta : ∀ r < 7,(4:Real)/5 ≤ g r)
    (hc : FramePotentialBound (gapPotential g) b.bounds) (c : Nat) (hcol : c < 33) :
    (frameBoxLo b c:Real) ≤ frameValue g c ∧ frameValue g c ≤ (frameBoxHi b c:Real) := by
  by_cases hs : c < 7
  · have hd := gapPotential_difference g c (c+1) (by omega)
    simp only [gsum_range,Nat.add_sub_cancel,Finset.sum_range_succ,
      Finset.sum_range_zero,zero_add,Nat.add_zero] at hd
    have hfor := hc c (by omega) (c+1) (by omega)
    have hrev := hc (c+1) (by omega) c (by omega)
    have ht := htheta c hs
    simp only [frameBoxLo,frameBoxHi,frameValue,frameEmbed,if_pos hs,actualValue,
      RHWeilRecord.RowEvaluation.actualValue,show c < 8 by omega,if_pos,
      frameSpanLower,frameSpanUpper,Int.cast_max,Int.cast_neg,Int.cast_mul,Int.cast_ofNat]
    norm_num [SC] at hd ⊢
    constructor
    · constructor <;> nlinarith
    · nlinarith
  · have hnot : ¬c+1 < 8 := by omega
    simp only [frameBoxLo,frameBoxHi,frameValue,frameEmbed,if_neg hs,actualValue,
      RHWeilRecord.RowEvaluation.actualValue,if_neg hnot]
    have hnon : 0 ≤ wfun (RHWeilRecord.RowEvaluation.gsum g
      (squareSpans.getD (c+1-8) (0,0)).1 (squareSpans.getD (c+1-8) (0,0)).2) := sq_nonneg _
    have hup : wfun (RHWeilRecord.RowEvaluation.gsum g
      (squareSpans.getD (c+1-8) (0,0)).1 (squareSpans.getD (c+1-8) (0,0)).2) ≤ 1 := AMW.wfunAM_le_one _
    norm_num [RHWeilRecord.RowEvaluation.kernelScale] at hnon hup ⊢
    constructor <;> nlinarith

theorem frame_branch_real_bound {g : Nat → Real} {index : Nat}
    (hguard : frameGuard index=true) (hnumeric : frameNumeric index=true)
    (htheta : ∀ r < 7,(4:Real)/5 ≤ g r)
    (hcell : InCell 7 PR (lowCell (frameBranch index).label) g)
    (hlo : ((frameBranch index).lower:Real) ≤ gapPotential g (frameBranch index).splitLast-gapPotential g (frameBranch index).splitFirst)
    (hhi : gapPotential g (frameBranch index).splitLast-gapPotential g (frameBranch index).splitFirst ≤ ((frameBranch index).upper:Real)) :
    (805094:Real) ≤ Fg 7 BS TS g := by
  let b:=frameBranch index
  have hc := frameClosure_real hguard htheta hcell hlo hhi
  have hrows := frameRows_sound hguard hcell hc
  have hlam : ∀ r∈frameMultipliers b,0 ≤ r.2 := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    dsimp only
    split_ifs <;> positivity
  have hselected : ∀ r∈frameMultipliers b,
      (∑ c∈Finset.range 33,(frameCoeff r.1 c:Real)*frameValue g c) ≤ (r.1.bound:Real) := by
    intro r hm
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact frame_selectedRow_sound hrows p.1
  have hnumeric' : 805094*(5*10000000000*32768)*10000000000 ≤ frameLower b :=
    of_decide_eq_true hnumeric
  have hbound := RHWeilRecord.SparseDualSoundness.threshold_sound 33 (frameMultipliers b)
    (fun c=>10000000000*frameObjectiveCoeff c) (frameValue g)
    (fun r c=>frameCoeff r.1 c) (fun r=>r.1.bound) (fun r=>r.2)
    (frameBoxLo b) (frameBoxHi b)
    (805094*(5*10000000000*32768)*10000000000) hnumeric' hlam hselected
    (fun c hcol=>(frame_box htheta hc c hcol).1)
    (fun c hcol=>(frame_box htheta hc c hcol).2)
  simp only [Int.cast_mul,Int.cast_ofNat] at hbound
  simp_rw [mul_assoc] at hbound
  rw [←Finset.mul_sum,frameObjective_identity] at hbound
  norm_num [kernelScale] at hbound ⊢
  nlinarith

theorem frame_representative_bound (g : Nat → Real) (label : Nat) (hl : label < 241)
    (htheta : ∀ r < 7,(4:Real)/5 ≤ g r)
    (hcell : InCell 7 PR (lowCell label) g) :
    (805094:Real) ≤ Fg 7 BS TS g := by
  let p:=framePatch label
  obtain ⟨helabel,hpl,hb0,hb1,hb2,hb3,h0l,h1l,h2l,h3l,
    h0f,h1f,h2f,h3f,h0e,h1e,h2e,h3e,hlo,hup,h01,h12,h23⟩ :=
      of_decide_eq_true (allFramePatchShapes label hl)
  have hedge := framePrimitive_sound htheta hcell
  have hSlo : ((frameBranch p.branch0).lower:Real) ≤ gapPotential g p.splitLast-gapPotential g p.splitFirst := by
    have h := JointFramePairPaths.check_real_bound (p:=gapPotential g) hlo
      (by simpa only [helabel] using hedge)
    norm_num at h ⊢
    linarith
  have hShi : gapPotential g p.splitLast-gapPotential g p.splitFirst ≤ ((frameBranch p.branch3).upper:Real) := by
    exact JointFramePairPaths.check_real_bound hup (by simpa only [helabel] using hedge)
  have h01' : ((frameBranch p.branch1).lower:Real) ≤ ((frameBranch p.branch0).upper:Real) := by exact_mod_cast h01
  have h12' : ((frameBranch p.branch2).lower:Real) ≤ ((frameBranch p.branch1).upper:Real) := by exact_mod_cast h12
  have h23' : ((frameBranch p.branch3).lower:Real) ≤ ((frameBranch p.branch2).upper:Real) := by exact_mod_cast h23
  by_cases h0 : gapPotential g p.splitLast-gapPotential g p.splitFirst ≤ ((frameBranch p.branch0).upper:Real)
  · apply frame_branch_real_bound (allFrameGuards _ hb0) (allFrameNumeric _ hb0) htheta
      (by simpa only [h0l,helabel] using hcell)
      (by simpa only [h0f,h0e] using hSlo) (by simpa only [h0f,h0e] using h0)
  · by_cases h1 : gapPotential g p.splitLast-gapPotential g p.splitFirst ≤ ((frameBranch p.branch1).upper:Real)
    · apply frame_branch_real_bound (allFrameGuards _ hb1) (allFrameNumeric _ hb1) htheta
        (by simpa only [h1l,helabel] using hcell)
        _ (by simpa only [h1f,h1e] using h1)
      rw [h1f,h1e]
      linarith
    · by_cases h2 : gapPotential g p.splitLast-gapPotential g p.splitFirst ≤ ((frameBranch p.branch2).upper:Real)
      · apply frame_branch_real_bound (allFrameGuards _ hb2) (allFrameNumeric _ hb2) htheta
          (by simpa only [h2l,helabel] using hcell)
          _ (by simpa only [h2f,h2e] using h2)
        rw [h2f,h2e]
        linarith
      · apply frame_branch_real_bound (allFrameGuards _ hb3) (allFrameNumeric _ hb3) htheta
          (by simpa only [h3l,helabel] using hcell)
          _ (by simpa only [h3f,h3e] using hShi)
        rw [h3f,h3e]
        linarith

theorem frame_low_bound (g : Nat → Real) (label : Nat) (hl : label < 482)
    (htheta : ∀ r < 7,(4:Real)/5 ≤ g r)
    (hcell : InCell 7 PR (lowCell label) g) :
    (805094:Real) ≤ Fg 7 BS TS g := by
  by_cases hsmall : label < 241
  · exact frame_representative_bound g label hsmall htheta hcell
  · have href : reflectionLabel label < 241 := by
      simp only [reflectionLabel,if_neg hsmall]
      omega
    have hrevc := InCell_reflection (lowCell label) g hcell
    rw [←lowCell_reflection_all hl] at hrevc
    have hthetar : ∀ r < 7,(4:Real)/5 ≤ reverseSeven g r := by
      intro r hr
      exact htheta (6-r) (by omega)
    have h := frame_representative_bound (reverseSeven g) (reflectionLabel label) href hthetar hrevc
    rw [Fg_reflection] at h
    exact h

theorem frame_lower (g : Nat → Real) (htheta : ∀ r < 7,(4:Real)/5 ≤ g r) :
    (805094:Real) ≤ Fg 7 BS TS g := by
  rcases strong_or_low_full g htheta with hstrong|hlow
  · norm_num at hstrong ⊢
    linarith
  · obtain ⟨label,hl,hcell⟩:=hlow
    exact frame_low_bound g label hl htheta hcell

end RHWeil.RecordSubmission.JointFramePairFinite
end
#print axioms RHWeil.RecordSubmission.JointFramePairFinite.frame_lower
#print axioms RHWeil.RecordSubmission.JointFramePairFinite.low_pair_bound
