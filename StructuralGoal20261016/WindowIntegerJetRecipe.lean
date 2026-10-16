/- SPDX-License-Identifier: Apache-2.0
Rounded normalized sinc recurrence used by the integer-centred jet oracle.
This is a soundness proof for the finite arithmetic recipe; all constants
come from separately proved elementary real enclosures.
-/
import StructuralGoal20261016.WindowRationalInterval
import StructuralGoal20261016.WindowNormalizedJets
import StructuralGoal20261016.WindowBasicEnclosures
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowIntegerJetRecipe
open WindowRationalInterval WindowNormalizedJets

def piI : QI := (314159265358979323846/10^20,314159265358979323847/10^20)
def thetaI : QI := (707106781186547524400844362104/10^30,707106781186547524400844362105/10^30)
def sinI : QI := (649636939080062444129454621098/10^30,649636939080062444132/10^21)
def cosI : QI := (760244597075630151252/10^21,760244597075630151253567702555/10^30)
def normI : QI := rdiv sinI thetaI

theorem piI_sound : Holds piI π := by
 unfold Holds piI
 push_cast
 exact WindowBasicEnclosures.pi_interval

theorem thetaI_sound : Holds thetaI (Real.sqrt 2/2) := by
 unfold Holds thetaI
 push_cast
 exact WindowBasicEnclosures.theta_interval

theorem sinI_sound : Holds sinI (Real.sin (Real.sqrt 2/2)) := by
 unfold Holds sinI
 push_cast
 exact ⟨WindowBasicEnclosures.sin_theta_lower, WindowBasicEnclosures.sin_theta_upper⟩

theorem cosI_sound : Holds cosI (Real.cos (Real.sqrt 2/2)) := by
 unfold Holds cosI
 push_cast
 exact ⟨WindowBasicEnclosures.cos_theta_lower, WindowBasicEnclosures.cos_theta_upper⟩

theorem normI_sound : Holds normI AMW.K0AM := by
 rw [K0AM_eq_ratio]
 exact rdiv_sound sinI_sound thetaI_sound (by norm_num [thetaI])

def phaseI (S C : QI) : ℕ → QI × QI
 | 0 => (S,C)
 | r+1 => ((phaseI S C r).2,rneg (phaseI S C r).1)

theorem phaseI_sound {S C : QI} {z : ℝ}
 (hs : Holds S (Real.sin z)) (hc : Holds C (Real.cos z)) (r : ℕ) :
 Holds (phaseI S C r).1 (Real.sin (z+(r:ℝ)*π/2)) ∧
 Holds (phaseI S C r).2 (Real.cos (z+(r:ℝ)*π/2)) := by
 induction r with
 | zero => simpa only [phaseI, Nat.cast_zero, zero_mul, zero_div, add_zero] using And.intro hs hc
 | succ r ih =>
   have he : z+((r+1:ℕ):ℝ)*π/2 = (z+(r:ℝ)*π/2)+π/2 := by push_cast; ring
   rw [he, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
   exact ⟨ih.2,rneg_sound ih.1⟩

def eI : ℕ → QI
 | 0 => point 1
 | r+1 => rdiv (rmul (eI r) piI) (point (r+2))

theorem eI_sound (r : ℕ) : Holds (eI r) (WindowNormalizedJets.e r) := by
 induction r with
 | zero => norm_num [eI,WindowNormalizedJets.e,point,Holds]
 | succ r ih =>
   rw [e_succ]
   apply rdiv_sound (rmul_sound ih piI_sound)
   · simpa only [Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,
       Nat.cast_add,Nat.cast_ofNat] using point_sound (r+2:ℚ)
   · left
     dsimp [point]
     positivity

def bI (Z S C : QI) : ℕ → QI
 | 0 => rdiv S Z
 | r+1 => rmul (rdiv piI Z) (rsub (rmul (eI r) (phaseI S C r).2) (bI Z S C r))

theorem bI_sound {Z S C : QI} {z : ℝ} (hz : Holds Z z)
 (hs : Holds S (Real.sin z)) (hc : Holds C (Real.cos z))
 (hnz : 0 < Z.1 ∨ Z.2 < 0) (r : ℕ) : Holds (bI Z S C r) (b r z) := by
 induction r with
 | zero =>
   have h := rdiv_sound hs hz hnz
   simpa only [bI,b,c,WindowSincJet.sincMoment_zero_order,
     Nat.factorial_zero,Nat.cast_one,div_one,pow_zero,one_mul,
     Real.sinc_of_ne_zero (nonzero hz hnz)] using h
 | succ r ih =>
   rw [b_succ (nonzero hz hnz)]
   exact rmul_sound (rdiv_sound piI_sound hz hnz)
     (rsub_sound (rmul_sound (eI_sound r) (phaseI_sound hs hc r).2) ih)

def poleI (r : ℕ) : QI := rmul (eI r) (phaseI (point 0) (point 1) r).2

theorem poleI_sound (r : ℕ) : Holds (poleI r) (b r 0) := by
 rw [b_zero]
 apply rmul_sound (eI_sound r)
 have h := (phaseI_sound
   (show Holds (point 0) (Real.sin 0) by norm_num [Holds,point])
   (show Holds (point 1) (Real.cos 0) by norm_num [Holds,point]) r).2
 simpa only [zero_add] using h

theorem integer_sin_cos (m : ℤ) (t : ℝ) :
 Real.sin (π*(m:ℝ)+t) = (-1:ℝ)^m*Real.sin t ∧
 Real.cos (π*(m:ℝ)+t) = (-1:ℝ)^m*Real.cos t := by
 rw [mul_comm π]
 simp only [Real.sin_add,Real.cos_add,Real.sin_int_mul_pi,Real.cos_int_mul_pi,
   zero_mul,mul_zero,zero_add,sub_zero]
 trivial

#print axioms normI_sound
#print axioms bI_sound
#print axioms poleI_sound
end StructuralGoal20261016.WindowIntegerJetRecipe
end
