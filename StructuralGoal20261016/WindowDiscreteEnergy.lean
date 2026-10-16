/- SPDX-License-Identifier: Apache-2.0
New-kernel capacity, band and separated remainder payments.
Adapted from BridgeW/OpethN in the attributed Core and the repository's
Coboundary module. Every energy premise uses shared WindowGapEnergy.Fw.
No local-floor or improved zero-proportion theorem is asserted here.
-/
import StructuralGoal20261016.WindowGapEnergy
import StructuralResearch20261016.Coboundary
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
open OpethN
namespace StructuralGoal20261016.WindowDiscreteEnergy

def kfun (x : ℝ) : ℝ := WindowKernel.k 24 WindowKernel.d24 x
def wfun (x : ℝ) : ℝ := WindowKernel.w 24 WindowKernel.d24 x
theorem kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
 unfold kfun WindowKernel.k
 rw [WindowKernel.K_neg]
theorem wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
 unfold wfun WindowKernel.w
 change kfun (-x)^2 = kfun x^2
 rw [kfun_neg]
theorem wfun_sub_comm (a b : ℝ) : wfun (a-b) = wfun (b-a) := by
 rw [← wfun_neg, neg_sub]
theorem wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _
theorem abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := WindowKernel.k24_abs_le_one x
theorem wfun_sub_le_norm_sq {g : ℂ} {t δ : ℝ}
 (h : ‖g-(kfun t : ℂ)‖ ≤ δ) : wfun t - 2*δ ≤ ‖g‖^2 := by
 have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
 have htri : abs (‖g‖-|kfun t|) ≤ δ := by
   rw [← hk]
   exact (abs_norm_sub_norm_le g _).trans h
 have hsq := sq_sub_two_mul_le_sq (abs_nonneg _) (abs_kfun_le_one t) (norm_nonneg g) htri
 rw [sq_abs] at hsq
 exact hsq

variable {n : ℕ}
lemma Fw_windowGaps (W : WCert n) (Y : ℕ → ℝ) (i : ℕ) :
   WindowGapEnergy.Fw W (windowGaps n Y i)
     = ∑ r : Fin (n - 1), W.b r * (Y (i + ((r : ℕ) + 1)) - Y (i + r))
       + ∑ a : Fin n, ∑ b : Fin n,
           if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
 unfold WindowGapEnergy.Fw
 have hq : (∑ a : Fin n, ∑ b : Fin n,
       if (a : ℕ) < (b : ℕ) then
         W.a a b * wfun (ptsN n (windowGaps n Y i) b - ptsN n (windowGaps n Y i) a) else 0)
     = ∑ a : Fin n, ∑ b : Fin n,
         if (a : ℕ) < (b : ℕ) then W.a a b * wfun (Y (i + b) - Y (i + a)) else 0 := by
   refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
   rw [ptsN_windowGaps, ptsN_windowGaps,
     show Y (i + ↑b) - Y i - (Y (i + ↑a) - Y i) = Y (i + ↑b) - Y (i + ↑a) by ring]
 simp only [wfun] at hq
 rw [hq]
 rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def SeparatedSummedCertificate {n : ℕ} (W : WCert n) (c C sep : ℝ) : Prop :=
 ∀ {m : ℕ}, n ≤ m → ∀ y : Fin m → ℝ, StrictMono y →
   (∀ i j, i ≠ j → sep ≤ |y i-y j|) →
   c*((m : ℝ)-((n-1 : ℕ) : ℝ))-C ≤
     ∑ i ∈ range (m-(n-1)), WindowGapEnergy.Fw W (windowGaps n (sortedExt y) i)

theorem summed_of_pointwise {n : ℕ} (hn : 2 ≤ n) (W : WCert n) {c sep : ℝ}
 (hfloor : ∀ g : Fin (n-1) → ℝ, (∀ i, sep ≤ g i) → c ≤ WindowGapEnergy.Fw W g) :
 SeparatedSummedCertificate W c 0 sep := by
 intro m hm y hy hsep
 have hwin : ∀ i ∈ range (m-(n-1)),
     c ≤ WindowGapEnergy.Fw W (windowGaps n (sortedExt y) i) := by
   intro i hi
   have hi' := Finset.mem_range.mp hi
   apply hfloor
   intro r
   have hr := r.isLt
   have hhi : i+((r : ℕ)+1) < m := by omega
   have hlo : i+(r : ℕ) < m := by omega
   change sep ≤ sortedExt y (i+((r : ℕ)+1))-sortedExt y (i+(r : ℕ))
   rw [sortedExt_of_lt y hhi, sortedExt_of_lt y hlo]
   have hp := hsep ⟨i+((r : ℕ)+1),hhi⟩ ⟨i+(r : ℕ),hlo⟩
     (by intro h; have := Fin.mk.inj_iff.mp h; omega)
   rw [abs_of_nonneg (sub_nonneg.mpr (hy.monotone (by
     change i+(r:ℕ) ≤ i+((r:ℕ)+1)
     omega)))] at hp
   exact hp
 have hs := Finset.sum_le_sum hwin
 rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
 have hc : ((m-(n-1) : ℕ) : ℝ) = (m : ℝ)-((n-1 : ℕ) : ℝ) := by
   rw [Nat.cast_sub (by omega : n-1 ≤ m)]
 rw [hc] at hs
 simpa only [sub_zero, mul_comm c] using hs

lemma window_pairs_le_band {n m : ℕ} (hn : 2 ≤ n) (hm : n ≤ m) (W : WCert n) (hW : W.Adm)
   (x : ι → ℝ) (hx : Function.Injective x) (hS : (univ.image x).card = m) :
   ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
       (if (a : ℕ) < (b : ℕ) then
         W.a a b * wfun (sortedExt ((univ.image x).orderEmbOfFin hS) (i + b)
               - sortedExt ((univ.image x).orderEmbOfFin hS) (i + a))
       else 0)
     ≤ ∑ r : Fin m × Fin m, (if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
         then wfun ((univ.image x).orderEmbOfFin hS r.1 - (univ.image x).orderEmbOfFin hS r.2) else 0) := by
 classical
 set y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS) with hydef
 set Y := sortedExt y with hYdef
 have hm0 : 0 < m := by omega
 set T : Finset (ℕ × (Fin n × Fin n)) :=
   (range (m - (n - 1)) ×ˢ (univ : Finset (Fin n × Fin n))).filter fun t => (t.2.1 : ℕ) < t.2.2
   with hTdef
 set f : ℕ × (Fin n × Fin n) → ℝ := fun t =>
   W.a t.2.1 t.2.2 * wfun (Y (t.1 + t.2.2) - Y (t.1 + t.2.1)) with hfdef
 have hLHS : ∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
     (if (a : ℕ) < (b : ℕ) then
       W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)
     = ∑ t ∈ T, f t := by
   rw [hTdef, sum_filter, sum_product]
   refine sum_congr rfl fun i _ => ?_
   exact (Fintype.sum_prod_type' (f := fun (a b : Fin n) => if (a : ℕ) < (b : ℕ) then
     W.a a b * wfun (Y (i + b) - Y (i + a)) else 0)).symm
 rw [hLHS]
 set φ : ℕ × (Fin n × Fin n) → ℕ × ℕ := fun t => (t.1 + t.2.1, t.1 + t.2.2) with hφdef
 set I := T.image φ with hIdef
 have hmem : ∀ t ∈ T, t.1 < m - (n - 1) ∧ (t.2.1 : ℕ) < t.2.2 := by
   intro t ht
   simp only [hTdef, mem_filter, mem_product, mem_range, mem_univ, and_true] at ht
   exact ht
 have hI : ∀ q ∈ I, q.1 < q.2 ∧ q.2 < m ∧ q.2 - q.1 < n := by
   intro q hq
   obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
   obtain ⟨h1, h2⟩ := hmem t ht
   have hb := t.2.2.2
   simp only [hφdef]
   omega
 rw [← sum_fiberwise_of_maps_to (g := φ) (t := I) (fun t ht => mem_image_of_mem φ ht)]
 have hfib : ∀ q ∈ I, ∑ t ∈ T with φ t = q, f t ≤ 2 * wfun (Y q.2 - Y q.1) := by
   intro q hq
   obtain ⟨hq1, hq2, hq3⟩ := hI q hq
   set r := q.2 - q.1 with hrdef
   have hconst : ∀ t ∈ T.filter (fun t => φ t = q),
       f t = W.a t.2.1 t.2.2 * wfun (Y q.2 - Y q.1) := by
     intro t ht
     rw [mem_filter] at ht
     obtain ⟨ht, hφt⟩ := ht
     have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst hφt
     have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd hφt
     simp only [hfdef]
     rw [e1, e2]
   rw [sum_congr rfl hconst, ← sum_mul]
   set ψ : ℕ × (Fin n × Fin n) → Fin n × Fin n := fun t => t.2 with hψdef
   have hψinj : Set.InjOn ψ (T.filter (fun t => φ t = q)) := by
     intro t ht t' ht' hee
     rw [mem_coe, mem_filter] at ht ht'
     have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
     have e1' : t'.1 + (t'.2.1 : ℕ) = q.1 := congrArg Prod.fst ht'.2
     simp only [hψdef] at hee
     have ha : (t.2.1 : ℕ) = t'.2.1 := by rw [hee]
     have hi : t.1 = t'.1 := by omega
     exact Prod.ext hi hee
   have hsub : (T.filter (fun t => φ t = q)).image ψ
       ⊆ (univ ×ˢ univ).filter fun p : Fin n × Fin n =>
           (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r := by
     intro p hp
     obtain ⟨t, ht, rfl⟩ := mem_image.mp hp
     rw [mem_filter] at ht
     have e1 : t.1 + (t.2.1 : ℕ) = q.1 := congrArg Prod.fst ht.2
     have e2 : t.1 + (t.2.2 : ℕ) = q.2 := congrArg Prod.snd ht.2
     obtain ⟨-, hlt⟩ := hmem t ht.1
     rw [mem_filter, mem_product]
     refine ⟨⟨mem_univ _, mem_univ _⟩, hlt, ?_⟩
     simp only [hψdef]
     omega
   have hmass : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2 ≤ 2 := by
     have h1 : ∑ t ∈ T.filter (fun t => φ t = q), W.a t.2.1 t.2.2
         = ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2 := by
       rw [sum_image hψinj]
     have h2 : ∑ p ∈ (T.filter (fun t => φ t = q)).image ψ, W.a p.1 p.2
         ≤ ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
             (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2 :=
       sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hW.a_nonneg p.1 p.2
     have h3 : ∑ p ∈ (univ ×ˢ univ).filter (fun p : Fin n × Fin n =>
             (p.1 : ℕ) < (p.2 : ℕ) ∧ (p.2 : ℕ) - (p.1 : ℕ) = r), W.a p.1 p.2
         = W.spanMass r := by
       unfold WCert.spanMass
       rw [sum_filter, sum_product]
     rw [h1]
     exact h2.trans (h3 ▸ hW.capacity r)
   exact mul_le_mul_of_nonneg_right hmass (wfun_nonneg _)
 refine (sum_le_sum hfib).trans ?_
 set G : Fin m × Fin m → ℝ := fun r => if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧ (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1)
   then wfun (y r.1 - y r.2) else 0 with hGdef
 set toFin : ℕ → Fin m := fun n => if h : n < m then ⟨n, h⟩ else ⟨0, hm0⟩ with htoFin
 have htoFin_lt : ∀ n (h : n < m), toFin n = ⟨n, h⟩ := by
   intro n h; simp only [htoFin, dif_pos h]
 set ψ₁ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.1, toFin q.2) with hψ₁
 set ψ₂ : ℕ × ℕ → Fin m × Fin m := fun q => (toFin q.2, toFin q.1) with hψ₂
 have hG1 : ∀ q ∈ I, G (ψ₁ q) = wfun (Y q.2 - Y q.1) := by
   intro q hq
   obtain ⟨hq1, hq2, hq3⟩ := hI q hq
   have hq1m : q.1 < m := by omega
   simp only [hGdef, hψ₁, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
     sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
   rw [if_pos ⟨by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne, by omega, by omega⟩,
     wfun_sub_comm]
 have hG2 : ∀ q ∈ I, G (ψ₂ q) = wfun (Y q.2 - Y q.1) := by
   intro q hq
   obtain ⟨hq1, hq2, hq3⟩ := hI q hq
   have hq1m : q.1 < m := by omega
   simp only [hGdef, hψ₂, htoFin_lt _ hq1m, htoFin_lt _ hq2, hYdef,
     sortedExt_of_lt y hq1m, sortedExt_of_lt y hq2]
   rw [if_pos ⟨by intro h; exact absurd (Fin.mk.inj_iff.mp h) hq1.ne', by omega, by omega⟩]
 have hsplit : ∑ q ∈ I, 2 * wfun (Y q.2 - Y q.1) = ∑ q ∈ I, G (ψ₁ q) + ∑ q ∈ I, G (ψ₂ q) := by
   rw [← sum_add_distrib]
   refine sum_congr rfl fun q hq => ?_
   rw [hG1 q hq, hG2 q hq]; ring
 have hinj₁ : Set.InjOn ψ₁ I := by
   intro q hq q' hq' h
   obtain ⟨hq1, hq2, -⟩ := hI q hq
   obtain ⟨hq1', hq2', -⟩ := hI q' hq'
   simp only [hψ₁, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
     htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
   exact Prod.ext h.1 h.2
 have hinj₂ : Set.InjOn ψ₂ I := by
   intro q hq q' hq' h
   obtain ⟨hq1, hq2, -⟩ := hI q hq
   obtain ⟨hq1', hq2', -⟩ := hI q' hq'
   simp only [hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
     htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at h
   exact Prod.ext h.2 h.1
 have hdisj : Disjoint (I.image ψ₁) (I.image ψ₂) := by
   rw [disjoint_left]
   intro r hr1 hr2
   obtain ⟨q, hq, rfl⟩ := mem_image.mp hr1
   obtain ⟨q', hq', hqq'⟩ := mem_image.mp hr2
   obtain ⟨hq1, hq2, -⟩ := hI q hq
   obtain ⟨hq1', hq2', -⟩ := hI q' hq'
   simp only [hψ₁, hψ₂, htoFin_lt _ (by omega : q.1 < m), htoFin_lt _ hq2,
     htoFin_lt _ (by omega : q'.1 < m), htoFin_lt _ hq2', Prod.mk.injEq, Fin.mk.injEq] at hqq'
   omega
 have hGnn : ∀ r, 0 ≤ G r := by
   intro r; simp only [hGdef]; split_ifs
   · exact wfun_nonneg _
   · exact le_rfl
 rw [hsplit, ← sum_image hinj₁, ← sum_image hinj₂, ← sum_union hdisj]
 exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun r _ _ => hGnn r
theorem band_close_n (n : ℕ) {x : ι → ℝ} (hx : Function.Injective x)
    {m : ℕ} (hS : (univ.image x).card = m) (hcard : Fintype.card ι = m)
    (G : Matrix ι ι ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    (∑ r : Fin m × Fin m,
      if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
        wfun ((univ.image x).orderEmbOfFin hS r.1 -
          (univ.image x).orderEmbOfFin hS r.2) else 0)
      ≤ offDiagSqOn G univ + 4 * ((n - 1 : ℕ) : ℝ) * δ * m := by
  classical
  set e := Equiv.ofBijective _ (sRank_bijective hx hS hcard) with he
  set R : ι → ℕ := fun i => (sRank x hS i : ℕ) with hR
  set C : ι → ι → Prop := fun i j =>
    i ≠ j ∧ R i ≤ R j + (n - 1) ∧ R j ≤ R i + (n - 1) with hC
  set F : ι → ι → ℝ := fun i j =>
    if C i j then wfun (x i - x j) else 0 with hF
  have hsum : (∑ r : Fin m × Fin m,
      if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
        wfun ((univ.image x).orderEmbOfFin hS r.1 -
          (univ.image x).orderEmbOfFin hS r.2) else 0) =
      ∑ i, ∑ j, F i j := by
    rw [Fintype.sum_prod_type, ← e.sum_comp]
    apply sum_congr rfl
    intro i _
    rw [← e.sum_comp]
    apply sum_congr rfl
    intro j _
    simp only [he, Equiv.ofBijective_apply, sRank_val, hF, hC, hR,
      ne_eq, (sRank_injective hx hS).eq_iff]
  have hnear (i : ι) : (univ.filter (C i)).card ≤ 2 * (n - 1) := by
    have hinj : (univ.filter (C i)).card ≤
        (univ.filter fun j : Fin m => sRank x hS i ≠ j ∧
          (sRank x hS i : ℕ) ≤ (j : ℕ) + (n - 1) ∧
          (j : ℕ) ≤ (sRank x hS i : ℕ) + (n - 1)).card := by
      apply card_le_card_of_injOn (fun j : ι => sRank x hS j)
      · intro j hj
        have hj' := (mem_filter.mp (mem_coe.mp hj)).2
        refine mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, ?_⟩)
        exact ⟨fun h => hj'.1 (sRank_injective hx hS h), hj'.2⟩
      · intro a _ b _ hab
        exact sRank_injective hx hS hab
    exact hinj.trans (card_near_le_k m (n - 1) (sRank x hS i))
  have hterm (i j : ι) : F i j ≤
      (if i ≠ j then ‖G i j‖ ^ 2 else 0) +
        (if C i j then 2 * δ else 0) := by
    change (if C i j then wfun (x i - x j) else 0) ≤
      (if i ≠ j then ‖G i j‖ ^ 2 else 0) + (if C i j then 2 * δ else 0)
    by_cases hc : C i j
    · simp only [if_pos hc, if_pos hc.1]
      exact sub_le_iff_le_add.mp (wfun_sub_le_norm_sq (hclose i j hc.1))
    · simp only [if_neg hc, add_zero]
      split_ifs <;> positivity
  have hcount (i : ι) :
      (∑ j, if C i j then 2 * δ else 0) ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hc : ((univ.filter (C i)).card : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnear i
    have h2δ : (0 : ℝ) ≤ 2 * δ := mul_nonneg (by norm_num) hδ
    have h := mul_le_mul_of_nonneg_right hc h2δ
    nlinarith only [h]
  rw [hsum]
  calc
    (∑ i, ∑ j, F i j) ≤ ∑ i, ∑ j,
        ((if i ≠ j then ‖G i j‖ ^ 2 else 0) +
          (if C i j then 2 * δ else 0)) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hterm i j))
    _ = offDiagSqOn G univ + ∑ i, ∑ j,
        (if C i j then 2 * δ else 0) := by
      simp only [sum_add_distrib, offDiagSqOn, ne_eq, ite_not]
    _ ≤ offDiagSqOn G univ + ∑ _i : ι, 4 * ((n - 1 : ℕ) : ℝ) * δ :=
      add_le_add le_rfl (sum_le_sum (fun i _ => hcount i))
    _ = offDiagSqOn G univ + 4 * ((n - 1 : ℕ) : ℝ) * δ * m := by
      rw [sum_const, card_univ, hcard, nsmul_eq_mul]
      ring
theorem block_energy_band_of_sum {c C : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m)
    (hSum : c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      ∑ i ∈ range (m - (n - 1)), WindowGapEnergy.Fw W
        (windowGaps n (sortedExt ((univ.image x).orderEmbOfFin hS)) i)) :
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      (∑ r : Fin m × Fin m,
        if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
          wfun ((univ.image x).orderEmbOfFin hS r.1 -
            (univ.image x).orderEmbOfFin hS r.2) else 0)
        + blkPress W.b x univ := by
  classical
  let y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS)
  have hsum := hSum
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum
  have hlin :
      (∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1),
        W.b r * (sortedExt y (i + ((r : ℕ) + 1)) - sortedExt y (i + r))) =
        blkPress W.b x univ := by
    rw [sum_comm]
    unfold blkPress
    rw [hS]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
  have hquad := window_pairs_le_band hn hm W hW x hx hS
  change (∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then
        W.a a b * wfun (sortedExt y (i + b) - sortedExt y (i + a)) else 0) ≤ _ at hquad
  linarith

theorem block_energy_band_separated {c C sep : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm) (hCert : SeparatedSummedCertificate W c C sep)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m)
    (hsep : ∀ i j, i ≠ j → sep ≤ |x i - x j|) :
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      (∑ r : Fin m × Fin m,
        if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
          wfun ((univ.image x).orderEmbOfFin hS r.1 -
            (univ.image x).orderEmbOfFin hS r.2) else 0)
        + blkPress W.b x univ :=
  block_energy_band_of_sum hn W hW hm x hx hS
    (hCert hm _ ((univ.image x).orderEmbOfFin hS).strictMono (StructuralResearch20261016.Coboundary.sorted_separated hS hsep))

theorem remainder_bound_separated_summed {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c C sep : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C sep)
    (hsep : ∀ i j, i ≠ j → sep ≤ |x i - x j|)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ i, hG.eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG := by
  classical
  let m := Fintype.card ι
  have hcard : Fintype.card ι = m := rfl
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  by_cases hm : n ≤ m
  · have he := block_energy_band_separated hn W hW hCert hm x hx hS hsep
    have hb := band_close_n n hx hS hcard G hδ hclose
    have hp := OpethN.pressure_le_n hm hS W hW.b_nonneg hspan
    have hd := Opeth.AMSparseDefect.offdiag_le_defect_of_spectrum_le_two hG hcap
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG
    nlinarith only [he, hb, hp, hd]
  · have hmk : (m : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m ≤ n - 1)
    have hcm := mul_le_mul_of_nonneg_left hmk hc
    have hbr : 0 ≤ W.B * R := mul_nonneg (WCert.B_nonneg hW) hR
    have hdm : 0 ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ * (m : ℝ) := by positivity
    have hd := Opeth.AMSparseDefect.defect_nonneg hG
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG
    nlinarith only [hcm, hbr, hdm, hd, hC]

theorem block_remainder_bound_separated {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c C sep : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C sep)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (B : Finset ι)
    (hsep : ∀ i j : B, i ≠ j → sep ≤ |x i - x j|)
    (hcap : ∀ i, (hG.submatrix (Subtype.val : B → ι)).eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (B.card : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ blockDefect hG B := by
  classical
  have hxB : Function.Injective (fun i : B => x i) := fun i j h =>
    Subtype.ext (hx h)
  have hcloseB : ∀ i j : B, i ≠ j →
      ‖G.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) i j -
        (kfun (x i - x j) : ℂ)‖ ≤ δ := fun i j hij =>
    hclose i j (fun h => hij (Subtype.ext h))
  have h := remainder_bound_separated_summed hn hxB
    (hG.submatrix (Subtype.val : B → ι)) hc hC W hW hCert hsep
    hδ hcloseB hcap hR (fun i j => hspan i j)
  simpa only [Fintype.card_coe, blockDefect] using h


#print axioms summed_of_pointwise
#print axioms remainder_bound_separated_summed
#print axioms block_remainder_bound_separated
end StructuralGoal20261016.WindowDiscreteEnergy
end
