import StructuralS1RM20261018.CurrentPrefix
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
namespace StructuralS1RM20261018.QuantizedComponent

def kappa : ℕ := 335544320000000000
def dLo (f : ℕ → ℕ) (p : ℕ) : ℤ := (lo32 (hi32 (f p)) : ℤ) - 2000000000
def dHi (f : ℕ → ℕ) (p : ℕ) : ℤ := 2000000000 - (hi32 (hi32 (f p)) : ℤ)
def slope (f : ℕ → ℕ) (p : ℕ) : ℤ := 512 * dLo f p
def intercept (f : ℕ → ℕ) (L0 p : ℕ) : ℤ :=
  32768 * 1024 * (lo32 (f p) : ℤ) -
    10240 * (dLo f p * (L0 : ℤ) + dHi f p * ((p : ℤ) - L0))

def ell (f : ℕ → ℕ) (L0 p : ℕ) (s : ℝ) : ℝ :=
  (lo32 (f p) : ℝ) / 10000000000 +
    ((lo32 (hi32 (f p)) : ℝ) - 2000000000) / 1000000000 * (s - (L0 : ℝ) / 32768) -
    (2000000000 - (hi32 (hi32 (f p)) : ℝ)) / 1000000000 * ((p : ℝ) / 32768 - (L0 : ℝ) / 32768)

theorem ell_le {f : ℕ → ℕ} {L0 L U p : ℕ} (ht : TVal f L U p)
    (hL0 : L0 ≤ L) (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ell f L0 p s ≤ wfun s := by
  obtain ⟨hLp, hpU, hlo, hhi, htan⟩ := ht
  have hSC : (SC : ℝ) = 32768 := by norm_num [SC]
  have hs : 0 ≤ s - (L0 : ℝ) / 32768 := by
    have h : (L0 : ℝ) / 32768 ≤ (L : ℝ) / 32768 := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hL0) (by norm_num)
    rw [hSC] at hs1
    linarith
  have hp : 0 ≤ (p : ℝ) / 32768 - (L0 : ℝ) / 32768 := by
    have h : L0 ≤ p := hL0.trans hLp
    have h' : (L0 : ℝ) ≤ p := by exact_mod_cast h
    linarith
  rw [hSC] at hlo hhi
  have hl : 0 ≤ w1 ((p : ℝ) / 32768) -
      ((lo32 (hi32 (f p)) : ℝ) - 2000000000) / 1000000000 := by linarith
  have hu : 0 ≤ (2000000000 - (hi32 (hi32 (f p)) : ℝ)) / 1000000000 -
      w1 ((p : ℝ) / 32768) := by linarith
  have he1 := mul_nonneg hl hs
  have he2 := mul_nonneg hu hp
  have hv := htan s hs1 hs2
  rw [hSC] at hv
  unfold ell
  nlinarith

theorem scaled_anchor {f : ℕ → ℕ} {L0 L U p : ℕ} (ht : TVal f L U p)
    (hL0 : L0 ≤ L) (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    (slope f p : ℝ) * (20 * 32768 * s) + (intercept f L0 p : ℝ) ≤
      (kappa : ℝ) * wfun s := by
  have h := mul_le_mul_of_nonneg_left (ell_le ht hL0 s hs1 hs2)
    (show (0 : ℝ) ≤ kappa by norm_num [kappa])
  convert h using 1 <;>
    simp only [ell, slope, intercept, dLo, dHi, kappa] <;> push_cast <;> ring

theorem scaled_constant {top : ℕ} {bk : ℕ → ℕ} (hlb : LBSound top bk)
    (L U : ℕ) (s : ℝ) (hs1 : (L : ℝ) / SC ≤ s) (hs2 : s ≤ (U : ℝ) / SC) :
    ((32768 * 1024 * lb top bk L U : ℕ) : ℝ) ≤ (kappa : ℝ) * wfun s := by
  have h := hlb L U s hs1 hs2
  have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ kappa by norm_num [kappa])
  norm_num [kappa] at h' ⊢
  nlinarith

set_option pp.fullNames true
#print axioms ell_le
#print axioms scaled_anchor
#print axioms scaled_constant
end StructuralS1RM20261018.QuantizedComponent
end
