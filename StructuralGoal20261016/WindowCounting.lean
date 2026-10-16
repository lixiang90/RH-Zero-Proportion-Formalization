/- SPDX-License-Identifier: Apache-2.0
The actual new-window dyadic and cumulative zero-counting bridge.
The proof adapts the attributed generic RefinedCounting arithmetic. The
actual Fourier energy, finite-height traces, tail, strips and spectrum are
proved upstream; only the named scalar pair and gap certificates remain.
-/
import StructuralGoal20261016.WindowCountingDefect
import StructuralGoal20261016.WindowCountingGeometry
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Filter Topology Zeta23
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
open scoped BigOperators
namespace StructuralGoal20261016.WindowCounting
open Classical
theorem defect_to_dyadic (Z : ZeroConfig) (H : PaperInputs Z) {n : ℕ} (hn : 2 ≤ n)
    {c B hw : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hB : 0 ≤ B) (hfloor : hw ≤ WindowEnergy.H 24 WindowKernel.d24)
    (hdef : WindowCountingDefect.ActualDefectEstimate Z n c B) :
    ∀ ε > (0 : ℝ), ∀ᶠ T in atTop,
      ((hw - B) / (1 - c) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  have hk0 : 0 < k := by linarith
  have hmu : 0 < 1 - c := sub_pos.mpr hc1
  set C : ℝ := 4 * k + 2 + c + B with hCdef
  have hC : 0 < C := by
    dsimp [C]
    linarith
  set δ : ℝ := min (c / (8 * k)) ((1 - c) * ε / C) with hδdef
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hc0 (by positivity)) (div_pos (mul_pos hmu hε) hC)
  have hδcap : δ ≤ c / (8 * k) := min_le_left _ _
  have hδeps : δ ≤ (1 - c) * ε / C := min_le_right _ _
  have hbudget : C * δ ≤ (1 - c) * ε := by
    have h := (le_div_iff₀ hC).mp hδeps
    linarith only [h]
  have hcoef : 0 ≤ c - 4 * k * δ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * k)).mp hδcap
    nlinarith only [h, hc0]
  filter_upwards [hdef δ hδ, WindowCountingGeometry.deleted_strips Z H δ hδ,
    WindowCountingGeometry.span_retained_le Z H δ hδ, WindowCountingBase.actual_tail_passage Z H δ hδ,
    (Zeta23.Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop (k * c / δ)]
    with T hd hstrip hspan htail hNlarge
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ)
  set m : ℝ := ((retained Z (WindowCountingBase.mtParams T) T).card : ℝ)
  set R : ℝ := spanOf (xret Z (WindowCountingBase.mtParams T) T) Finset.univ
  set D : ℝ := Dcirc Z (WindowCountingBase.mtParams T) T
  change (c - 4 * k * δ) * m - B * R - k * c ≤ D at hd
  change n0 - δ * N ≤ m at hstrip
  change R ≤ (1 + δ) * N at hspan
  change (WindowEnergy.H 24 WindowKernel.d24 - δ) * N + D ≤ n0 at htail
  change k * c / δ ≤ N at hNlarge
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hn0N : n0 ≤ N := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    change (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ)
    exact_mod_cast h
  have hn := mul_le_mul_of_nonneg_left hstrip hcoef
  have hR := mul_le_mul_of_nonneg_left hspan hB
  have herr := mul_le_mul_of_nonneg_left hn0N
    (show 0 ≤ 4 * k * δ by positivity)
  have hδ2N : 0 ≤ 4 * k * δ * δ * N := by positivity
  have hD : c * n0 - B * N - (4 * k + c + B) * δ * N - k * c ≤ D := by
    nlinarith only [hd, hn, hR, herr, hδ2N]
  have hend : k * c ≤ δ * N := by
    have h := (div_le_iff₀ hδ).mp hNlarge
    nlinarith only [h]
  have hHW : hw * N ≤ WindowEnergy.H 24 WindowKernel.d24 * N :=
    mul_le_mul_of_nonneg_right hfloor hN0
  have hmain : ((hw : ℝ) - B - C * δ) * N ≤ (1 - c) * n0 := by
    dsimp [C]
    nlinarith only [hD, htail, hend, hHW]
  have hid : (1 - c) * ((hw - B) / (1 - c)) = hw - B := by
    field_simp
  have hcoeff : (1 - c) * ((hw - B) / (1 - c) - ε) ≤
      (hw : ℝ) - B - C * δ := by
    rw [mul_sub, hid]
    linarith only [hbudget]
  have hscaled : (1 - c) * (((hw - B) / (1 - c) - ε) * N) ≤ (1 - c) * n0 := by
    calc
      _ = ((1 - c) * ((hw - B) / (1 - c) - ε)) * N := by ring
      _ ≤ ((hw : ℝ) - B - C * δ) * N :=
        mul_le_mul_of_nonneg_right hcoeff hN0
      _ ≤ _ := hmain
  exact le_of_mul_le_mul_left hscaled hmu

theorem simple_dyadic {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
 {c C B hw sep : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
 (hc64 : c ≤ 1/64) (hsep : 17/20 ≤ sep)
 (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
 (hB : W.B = B) (hfloor : hw ≤ WindowEnergy.H 24 WindowKernel.d24)
 (hCert : WindowDiscreteEnergy.SeparatedSummedCertificate W c C sep) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0simple T (2*T) := by
 have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
 have hdef := WindowCountingDefect.actual_defect_estimate zetaZeroConfig hn W hW
   hc.le hC hCc hc64 hsep hB hPair hCert
 intro ε hε
 obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp
   (defect_to_dyadic zetaZeroConfig paperInputs_zeta (by omega : 2 ≤ n+1)
     hc (by linarith) hB0 hfloor hdef ε hε)
 exact ⟨T₀,fun T hT => by simpa only [zetaZeroConfig_N,zetaZeroConfig_N0s] using hT₀ T hT⟩

theorem simple_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
 {c C B hw sep : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
 (hc64 : c ≤ 1/64) (hsep : 17/20 ≤ sep)
 (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
 (hB : W.B = B) (hfloor : hw ≤ WindowEnergy.H 24 WindowKernel.d24)
 (hCert : WindowDiscreteEnergy.SeparatedSummedCertificate W c C sep) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0simple 0 T :=
 Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
   (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam)
   (simple_dyadic hn W hW hc hC hCc hc64 hsep hPair hB hfloor hCert)

theorem distinct_dyadic {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
 {c C B hw sep : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
 (hc64 : c ≤ 1/64) (hsep : 17/20 ≤ sep)
 (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
 (hB : W.B = B) (hfloor : hw ≤ WindowEnergy.H 24 WindowKernel.d24)
 (hCert : WindowDiscreteEnergy.SeparatedSummedCertificate W c C sep) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount T (2*T):ℝ) ≤ Zeta23.N0star T (2*T) := by
 intro ε hε
 obtain ⟨T₀,hT₀⟩ := simple_dyadic hn W hW hc hC hCc hc64 hsep hPair hB hfloor hCert ε hε
 refine ⟨T₀,fun T hT => (hT₀ T hT).trans ?_⟩
 exact_mod_cast AMW.N0simple_le_N0star' T (2*T)

theorem distinct_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
 {c C B hw sep : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
 (hc64 : c ≤ 1/64) (hsep : 17/20 ≤ sep)
 (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
 (hB : W.B = B) (hfloor : hw ≤ WindowEnergy.H 24 WindowKernel.d24)
 (hCert : WindowDiscreteEnergy.SeparatedSummedCertificate W c C sep) :
 ∀ ε > (0:ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
 ((hw-B)/(1-c)-ε)*(Zeta23.Ncount 0 T:ℝ) ≤ Zeta23.N0star 0 T :=
 Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
   (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam)
   (distinct_dyadic hn W hW hc hC hCc hc64 hsep hPair hB hfloor hCert)

set_option pp.fullNames true
#print axioms defect_to_dyadic
#print axioms simple_dyadic
#print axioms simple_cumulative
#print axioms distinct_dyadic
#print axioms distinct_cumulative
end StructuralGoal20261016.WindowCounting
end
