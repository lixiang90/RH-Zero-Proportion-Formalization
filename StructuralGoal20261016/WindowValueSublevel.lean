/- SPDX-License-Identifier: Apache-2.0
Concrete energy-sublevel contraction certificates for actual Fw24.
The scalar lines, capacities, integer forest flow and outward rounding
are all checked. Contraction preserves Fw24<c points in the original
cell; it does not claim to preserve arbitrary points of that cell.
-/
import StructuralGoal20261016.WindowScalarLine
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowValueSublevel
open WindowValueFlow
variable {m : ℕ}

def objective (o : Fin 9 → ℤ) (g : Fin 9 → ℝ) : ℝ :=
  32768*(∑ r, (o r:ℝ)*g r)

def augmentedConstant (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → Plane) (p : ℤ) : ℤ := p*32768*intercept lam s

def augmentedCoefficient (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → Plane) (o : Fin 9 → ℤ) (p K : ℤ) (r : Fin 9) : ℤ :=
  p*32768*coefficient lam s r+K*denominator*o r

theorem augmented_expansion (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → Plane) (o : Fin 9 → ℤ) (p K : ℤ) (g : Fin 9 → ℝ) :
    (augmentedConstant lam s p:ℝ)+
      32768*(∑ r, (augmentedCoefficient lam s o p K r:ℝ)*g r) =
    (p:ℝ)*32768*((denominator:ℝ)*minorant lam s g)+
      (K:ℝ)*(denominator:ℝ)*objective o g := by
  rw [affine_expansion]
  unfold augmentedConstant augmentedCoefficient objective
  push_cast
  have h1 : (∑ r, (p:ℝ)*32768*(coefficient lam s r:ℝ)*g r) =
      (p:ℝ)*32768*(∑ r, (coefficient lam s r:ℝ)*g r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have h2 : (∑ r, (K:ℝ)*(denominator:ℝ)*(o r:ℝ)*g r) =
      (K:ℝ)*(denominator:ℝ)*(∑ r, (o r:ℝ)*g r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  simp only [add_mul,Finset.sum_add_distrib]
  rw [h1,h2]
  ring

abbrev Numeric (p K cN minimum bound : ℤ) : Prop :=
  0 ≤ p ∧ 0 < K ∧ K*denominator*bound ≤ minimum-p*32768*cN

def check (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → WindowScalarLine.Support)
    (o : Fin 9 → ℤ) (p K cN minimum bound : ℤ) (edges : List FlowBasisCodec.Edge) : Bool :=
  ((WindowScalarLine.scalarCheck cell lam s && massCheck lam) &&
    decide (Numeric p K cN minimum bound)) &&
    FlowBasisCodec.checkBasis edges cell
      (WindowDifferenceCell.divergence (augmentedCoefficient lam (WindowScalarLine.planes cell s) o p K))
      (augmentedConstant lam (WindowScalarLine.planes cell s) p) minimum

theorem lower (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → WindowScalarLine.Support)
    (o : Fin 9 → ℤ) (p K cN minimum bound : ℤ) (edges : List FlowBasisCodec.Edge)
    (g : Fin 9 → ℝ) (hg : WindowDifferenceCell.Contains cell g)
    (hbelow : WindowGapEnergy.Fw24 g < (cN:ℝ)/(denominator:ℝ))
    (hc : check cell lam s o p K cN minimum bound edges = true) :
    (bound:ℝ) ≤ objective o g := by
  have hh : ((WindowScalarLine.scalarCheck cell lam s = true ∧ massCheck lam = true) ∧
      decide (Numeric p K cN minimum bound) = true) ∧
      FlowBasisCodec.checkBasis edges cell
        (WindowDifferenceCell.divergence (augmentedCoefficient lam (WindowScalarLine.planes cell s) o p K))
        (augmentedConstant lam (WindowScalarLine.planes cell s) p) minimum = true := by
    simpa only [check,Bool.and_eq_true] using hc
  have hs : ∀ t k, lam t k ≠ 0 → WindowScalarLine.check (s t k)
      (WindowScalarLine.lower cell t) (WindowScalarLine.upper cell t) = true :=
    of_decide_eq_true hh.1.1.1
  have hm := minorant_le lam (WindowScalarLine.planes cell s) g hh.1.1.2
    (fun t k hk => WindowScalarLine.sound (hs t k hk) (WindowScalarLine.span_bounds hg t))
  have hn : Numeric p K cN minimum bound := of_decide_eq_true hh.1.2
  have hf := WindowDifferenceCell.flow_gap_bound cell g hg edges
    (augmentedCoefficient lam (WindowScalarLine.planes cell s) o p K)
    (augmentedConstant lam (WindowScalarLine.planes cell s) p) minimum hh.2
  rw [augmented_expansion] at hf
  have hd : (0:ℝ) < (denominator:ℝ) := by norm_num [denominator]
  have hp : (0:ℝ) ≤ (p:ℝ) := by exact_mod_cast hn.1
  have hK : (0:ℝ) < (K:ℝ) := by exact_mod_cast hn.2.1
  have hr : (K:ℝ)*(denominator:ℝ)*(bound:ℝ) ≤
      (minimum:ℝ)-(p:ℝ)*32768*(cN:ℝ) := by exact_mod_cast hn.2.2
  have hA : (denominator:ℝ)*minorant lam (WindowScalarLine.planes cell s) g ≤ (cN:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hm hd.le
    have hb := (lt_div_iff₀ hd).mp hbelow
    nlinarith
  have hpay := mul_le_mul_of_nonneg_left hA (mul_nonneg hp (by norm_num : (0:ℝ) ≤ 32768))
  have hscale : (0:ℝ) < (K:ℝ)*(denominator:ℝ) := mul_pos hK hd
  nlinarith

set_option pp.fullNames true
#print axioms augmented_expansion
#print axioms lower
end StructuralGoal20261016.WindowValueSublevel
end
