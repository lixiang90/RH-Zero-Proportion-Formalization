/- SPDX-License-Identifier: Apache-2.0
All original quantized derivative and third-derivative bounds on the
separated domain. Cell k is [k/64,(k+1)/64]; only k>=61 is consumed by
the separation 123/128. No endpoint constants are replaced.
-/
import StructuralGoal20261016.WindowGridChecks00
import StructuralGoal20261016.WindowGridChecks01
import StructuralGoal20261016.WindowGridChecks02
import StructuralGoal20261016.WindowGridChecks03
import StructuralGoal20261016.WindowGridChecks04
import StructuralGoal20261016.WindowGridChecks05
import StructuralGoal20261016.WindowGridChecks06
import StructuralGoal20261016.WindowGridChecks07
import StructuralGoal20261016.WindowGridChecks08
import StructuralGoal20261016.WindowGridChecks09
import StructuralGoal20261016.WindowGridChecks10
import StructuralGoal20261016.WindowGridChecks11
import StructuralGoal20261016.WindowGridChecks12
import StructuralGoal20261016.WindowGridChecks13
import StructuralGoal20261016.WindowGridChecks14
import StructuralGoal20261016.WindowGridChecks15
import StructuralGoal20261016.WindowGridChecks16
import StructuralGoal20261016.WindowGridChecks17
import StructuralGoal20261016.WindowGridChecks18
import StructuralGoal20261016.WindowGridChecks19
import StructuralGoal20261016.WindowGridChecks20
import StructuralGoal20261016.WindowGridChecks21
import StructuralGoal20261016.WindowGridChecks22
import StructuralGoal20261016.WindowGridChecks23
import StructuralGoal20261016.WindowGridChecks24
import StructuralGoal20261016.WindowGridChecks25
import StructuralGoal20261016.WindowGridChecks26
import StructuralGoal20261016.WindowGridChecks27
import StructuralGoal20261016.WindowGridChecks28
import StructuralGoal20261016.WindowGridChecks29
import StructuralGoal20261016.WindowGridChecks30
import StructuralGoal20261016.WindowGridChecks31
import StructuralGoal20261016.WindowGridChecks32
import StructuralGoal20261016.WindowGridChecks33
import StructuralGoal20261016.WindowGridChecks34
import StructuralGoal20261016.WindowGridChecks35
import StructuralGoal20261016.WindowGridChecks36
import StructuralGoal20261016.WindowGridChecks37
import StructuralGoal20261016.WindowGridChecks38
import StructuralGoal20261016.WindowGridChecks39
import StructuralGoal20261016.WindowGridChecks40
import StructuralGoal20261016.WindowGridChecks41
import StructuralGoal20261016.WindowGridChecks42
import StructuralGoal20261016.WindowGridChecks43
import StructuralGoal20261016.WindowGridChecks44
import StructuralGoal20261016.WindowGridChecks45
import StructuralGoal20261016.WindowGridChecks46
import StructuralGoal20261016.WindowGridChecks47
import StructuralGoal20261016.WindowGridChecks48
import StructuralGoal20261016.WindowGridChecks49
import StructuralGoal20261016.WindowGridChecks50
import StructuralGoal20261016.WindowGridChecks51
import StructuralGoal20261016.WindowGridChecks52
import StructuralGoal20261016.WindowGridChecks53
import StructuralGoal20261016.WindowGridChecks54
import StructuralGoal20261016.WindowGridChecks55
import StructuralGoal20261016.WindowGridChecks56
import StructuralGoal20261016.WindowGridChecks57
import StructuralGoal20261016.WindowGridChecks58
import StructuralGoal20261016.WindowGridChecks59
import StructuralGoal20261016.WindowGridChecks60
import StructuralGoal20261016.WindowGridChecks61
import StructuralGoal20261016.WindowGridChecks62
import StructuralGoal20261016.WindowGridRange
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowGridAll
open WindowGridCertificate WindowGridCertificateData WindowGridChecks

theorem checks : ∀ g : Fin 63, ∀ j : Fin 32, (g:ℕ)*32+(j:ℕ) < 1987 →
 check (61+(g:ℕ)*32+(j:ℕ)) (row ((g:ℕ)*32+(j:ℕ))) = true := by
 intro g
 fin_cases g
 · exact checks00
 · exact checks01
 · exact checks02
 · exact checks03
 · exact checks04
 · exact checks05
 · exact checks06
 · exact checks07
 · exact checks08
 · exact checks09
 · exact checks10
 · exact checks11
 · exact checks12
 · exact checks13
 · exact checks14
 · exact checks15
 · exact checks16
 · exact checks17
 · exact checks18
 · exact checks19
 · exact checks20
 · exact checks21
 · exact checks22
 · exact checks23
 · exact checks24
 · exact checks25
 · exact checks26
 · exact checks27
 · exact checks28
 · exact checks29
 · exact checks30
 · exact checks31
 · exact checks32
 · exact checks33
 · exact checks34
 · exact checks35
 · exact checks36
 · exact checks37
 · exact checks38
 · exact checks39
 · exact checks40
 · exact checks41
 · exact checks42
 · exact checks43
 · exact checks44
 · exact checks45
 · exact checks46
 · exact checks47
 · exact checks48
 · exact checks49
 · exact checks50
 · exact checks51
 · exact checks52
 · exact checks53
 · exact checks54
 · exact checks55
 · exact checks56
 · exact checks57
 · exact checks58
 · exact checks59
 · exact checks60
 · exact checks61
 · exact checks62

theorem valid_index (i : ℕ) (hi : i < 1987) : Valid (61+i) (row i) := by
 have hg : i/32 < 63 := by omega
 have hj : i%32 < 32 := Nat.mod_lt i (by decide)
 have he : i/32*32+i%32 = i := by omega
 have hc := checks ⟨i/32,hg⟩ ⟨i%32,hj⟩
   (by change i/32*32+i%32 < 1987; omega)
 change check (61+i/32*32+i%32) (row (i/32*32+i%32)) = true at hc
 have he' : 61+i/32*32+i%32 = 61+i := by omega
 rw [he,he'] at hc
 exact WindowGridCertificate.sound hc

theorem valid (k : ℕ) (hk0 : 61 ≤ k) (hk1 : k < 2048) : Valid k (row (k-61)) := by
 have h := valid_index (k-61) (by omega)
 have he : 61+(k-61) = k := by omega
 rwa [he] at h

theorem derivative (k : ℕ) (hk0 : 61 ≤ k) (hk1 : k < 2048)
 {x : ℝ} (hx : x ∈ Icc (left k:ℝ) (right k:ℝ)) :
 ((row (k-61)).lower:ℝ)/10^15 ≤ WindowGapEnergy.w1 x ∧
 WindowGapEnergy.w1 x ≤ ((row (k-61)).upper:ℝ)/10^15 :=
 ⟨(valid k hk0 hk1 x hx).1,(valid k hk0 hk1 x hx).2.1⟩

theorem third (k : ℕ) (hk0 : 61 ≤ k) (hk1 : k < 2048)
 {x : ℝ} (hx : x ∈ Icc (left k:ℝ) (right k:ℝ)) :
 |iteratedDeriv 3 WindowScalarMinorant.f x| ≤ ((row (k-61)).third:ℝ)/10^15 :=
 (valid k hk0 hk1 x hx).2.2

theorem gridSound : WindowGridRange.GridSound := fun k hk0 hk1 => valid k hk0 hk1

theorem range_sound {k0 k1 : ℕ} {a b L U M : ℚ}
 (hc : WindowGridRange.check k0 k1 a b L U M = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ WindowGapEnergy.w1 x ∧ WindowGapEnergy.w1 x ≤ (U:ℝ) ∧
 |iteratedDeriv 3 WindowScalarMinorant.f x| ≤ (M:ℝ) :=
 WindowGridRange.sound gridSound hc hx

set_option pp.fullNames true
#print axioms valid
#print axioms derivative
#print axioms third
#print axioms range_sound
end StructuralGoal20261016.WindowGridAll
end
