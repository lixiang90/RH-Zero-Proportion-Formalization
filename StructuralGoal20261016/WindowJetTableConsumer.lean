/- SPDX-License-Identifier: Apache-2.0
Stepwise rational table certificates for actual normalized integer jets.
Only finite rational comparisons are checked by computation; the analytic
meaning of each recurrence and convolution is proved in ordinary Lean.
-/
import StructuralGoal20261016.WindowIntegerKernelRecipe
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowJetTableConsumer
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe WindowIntegerKernelRecipe

def covers (I J : QI) : Bool := decide (J.1 ≤ I.1 ∧ I.2 ≤ J.2)
theorem covers_sound {I J : QI} {x : ℝ} (h : covers I J = true)
 (hx : Holds I x) : Holds J x := by
 have he : J.1 ≤ I.1 ∧ I.2 ≤ J.2 := of_decide_eq_true h
 exact widen hx he.1 he.2

theorem e_table_sound (E : ℕ → QI) (h0 : covers (point 1) (E 0) = true)
 (hs : ∀ r < 23, covers (rdiv (rmul (E r) piI) (point (r+2))) (E (r+1)) = true) :
 ∀ r ≤ 23, Holds (E r) (WindowNormalizedJets.e r) := by
 intro r hr
 induction r with
 | zero =>
   apply covers_sound h0
   norm_num [point,Holds,WindowNormalizedJets.e]
 | succ r ih =>
   rw [e_succ]
   apply covers_sound (hs r (by omega))
   apply rdiv_sound (rmul_sound (ih (by omega)) piI_sound)
   · simpa only [Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,
       Nat.cast_add,Nat.cast_ofNat] using point_sound (r+2:ℚ)
   · left
     dsimp [point]
     positivity

def bStep (E : ℕ → QI) (Z S C B : QI) (r : ℕ) : QI :=
 rmul (rdiv piI Z) (rsub (rmul (E r) (phaseI S C r).2) B)

theorem b_table_sound (E B : ℕ → QI) {Z S C : QI} {z : ℝ}
 (hE : ∀ r ≤ 23, Holds (E r) (WindowNormalizedJets.e r))
 (hz : Holds Z z) (hsin : Holds S (Real.sin z)) (hcos : Holds C (Real.cos z))
 (hnz : 0 < Z.1 ∨ Z.2 < 0)
 (h0 : covers (rdiv S Z) (B 0) = true)
 (hs : ∀ r < 23, covers (bStep E Z S C (B r) r) (B (r+1)) = true) :
 ∀ r ≤ 23, Holds (B r) (b r z) := by
 intro r hr
 induction r with
 | zero =>
   apply covers_sound h0
   have h := rdiv_sound hsin hz hnz
   simpa only [b,c,WindowSincJet.sincMoment_zero_order,Nat.factorial_zero,
     Nat.cast_one,div_one,pow_zero,one_mul,Real.sinc_of_ne_zero (nonzero hz hnz)] using h
 | succ r ih =>
   rw [b_succ (nonzero hz hnz)]
   exact covers_sound (hs r (by omega))
     (rmul_sound (rdiv_sound piI_sound hz hnz)
       (rsub_sound (rmul_sound (hE r (by omega)) (phaseI_sound hsin hcos r).2) (ih (by omega))))

theorem pole_table_sound (E B : ℕ → QI)
 (hE : ∀ r ≤ 23, Holds (E r) (WindowNormalizedJets.e r))
 (hc : ∀ r ≤ 23, covers (rmul (E r) (phaseI (point 0) (point 1) r).2) (B r) = true) :
 ∀ r ≤ 23, Holds (B r) (b r 0) := by
 intro r hr
 rw [b_zero]
 apply covers_sound (hc r hr)
 apply rmul_sound (hE r hr)
 have h := (phaseI_sound
   (show Holds (point 0) (Real.sin 0) by norm_num [Holds,point])
   (show Holds (point 1) (Real.cos 0) by norm_num [Holds,point]) r).2
 simpa only [zero_add] using h

def kOp (B : ℕ → Bool → ℕ → QI) (C : ℤ → ℕ → QI) (n r : ℕ) : QI :=
 rdiv (radd (radd (B n false r) (B n true r))
   (sumI (fun j => radd
     (rmul (point (coeffQ j)) (C ((n:ℤ)-((j:ℤ)+1)) r))
     (rmul (point (coeffQ j)) (C ((n:ℤ)+((j:ℤ)+1)) r))) 24))
   (rmul (point 2) normI)

theorem kOp_sound (B : ℕ → Bool → ℕ → QI) (C : ℤ → ℕ → QI)
 {n r : ℕ} (hn : n < 33)
 (hB : ∀ s : Bool, Holds (B n s r) (b r (baseZ n s)))
 (hC : ∀ m : ℤ, -24 ≤ m → m ≤ 56 → Holds (C m r) (b r (π*(m:ℝ)))) :
 Holds (kOp B C n r) (kc 24 WindowKernel.d24 r (n:ℝ)) := by
 rw [kc_eq_finite_b]
 apply rdiv_sound
 · apply radd_sound
   · have h := radd_sound (hB false) (hB true)
     simpa [baseZ,sub_eq_add_neg] using h
   · apply sumI_sound
     intro j hj
     have hd : Holds (point (coeffQ j)) (WindowKernel.d24 j) := by
       convert point_sound (coeffQ j) using 1 <;> norm_num [coeffQ,WindowKernel.d24]
     have h := radd_sound
       (rmul_sound hd (hC ((n:ℤ)-((j:ℤ)+1)) (by omega) (by omega)))
       (rmul_sound hd (hC ((n:ℤ)+((j:ℤ)+1)) (by omega) (by omega)))
     convert h using 1 <;> push_cast <;> ring
 · exact rmul_sound (by norm_num [Holds,point]) normI_sound
 · exact normalization_guard

def wOp (K : ℕ → QI) (r : ℕ) : QI := sumI (fun j => rmul (K j) (K (r-j))) (r+1)

theorem wOp_sound (K : ℕ → QI) {n r : ℕ}
 (hK : ∀ j ≤ r, Holds (K j) (kc 24 WindowKernel.d24 j (n:ℝ))) :
 Holds (wOp K r) (wc 24 WindowKernel.d24 r (n:ℝ)) := by
 rw [wc_convolution]
 exact sumI_sound _ _ _ (fun j hj => rmul_sound (hK j (by omega)) (hK (r-j) (by omega)))

#print axioms b_table_sound
#print axioms kOp_sound
#print axioms wOp_sound
end StructuralGoal20261016.WindowJetTableConsumer
end
