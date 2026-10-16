/- SPDX-License-Identifier: Apache-2.0
Concrete scalar-oracle dispatch for actual value-LP certificates.
Zero, convex-core tangents and k-based constant supports are checked on
the exact span interval of the difference cell before their integer
planes are mixed. Every analytic input is supplied by proved consumers.
-/
import StructuralGoal20261016.WindowValueFlow
import StructuralGoal20261016.WindowSupportCertificate
import StructuralGoal20261016.WindowConstantSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowScalarLine
open WindowGramTransfer

inductive Support where
  | zero
  | tangent (s : WindowSupportCertificate.Support)
  | constant (s : WindowConstantSupport.Support)

def plane (s : Support) (l : ℤ) : WindowValueFlow.Plane := match s with
  | .zero => ⟨0,0⟩
  | .tangent a => ⟨WindowSupportCertificate.constant a l,WindowSupportCertificate.coefficient a⟩
  | .constant a => ⟨32768*a.value,0⟩

def check (s : Support) (l u : ℤ) : Bool := match s with
  | .zero => true
  | .tangent a => WindowSupportCertificate.check a l u
  | .constant a => WindowConstantSupport.check a l u

theorem sound {s : Support} {l u : ℤ} (hc : check s l u = true)
    {x : ℝ} (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    WindowValueFlow.line (plane s l) x ≤ WindowKernel.w 24 WindowKernel.d24 x := by
  cases s with
  | zero =>
    have h0 : (0:ℝ) ≤ WindowKernel.w 24 WindowKernel.d24 x := by
      unfold WindowKernel.w
      exact sq_nonneg _
    simpa only [plane,WindowValueFlow.line,Int.cast_zero,mul_zero,zero_mul,
      add_zero,zero_div] using h0
  | tangent a => exact WindowSupportCertificate.integer_line_sound hc hx
  | constant a =>
    simpa only [plane,WindowValueFlow.line,Int.cast_zero] using
      WindowConstantSupport.integer_line_sound hc hx

def lower (cell : DifferenceCell.Cell 10) (t : Fin 41) : ℤ :=
  -cell (pairJ t) (pairI t)
def upper (cell : DifferenceCell.Cell 10) (t : Fin 41) : ℤ :=
  cell (pairI t) (pairJ t)

theorem span_bounds {cell : DifferenceCell.Cell 10} {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g) (t : Fin 41) :
    (lower cell t:ℝ)/32768 ≤ span g t ∧ span g t ≤ (upper cell t:ℝ)/32768 := by
  have hL := hg (pairJ t) (pairI t)
  have hU := hg (pairI t) (pairJ t)
  change 32768*Zeta23Ext.Bridge.ptsN 10 g (pairI t)-
    32768*Zeta23Ext.Bridge.ptsN 10 g (pairJ t) ≤ (cell (pairJ t) (pairI t):ℝ) at hL
  change 32768*Zeta23Ext.Bridge.ptsN 10 g (pairJ t)-
    32768*Zeta23Ext.Bridge.ptsN 10 g (pairI t) ≤ (cell (pairI t) (pairJ t):ℝ) at hU
  unfold lower upper span
  push_cast
  constructor <;> linarith

variable {m : ℕ}

def planes (cell : DifferenceCell.Cell 10) (s : Fin 41 → Fin m → Support) :
    Fin 41 → Fin m → WindowValueFlow.Plane := fun t k => plane (s t k) (lower cell t)

def scalarCheck (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → Support) : Bool := decide (
  ∀ t k, lam t k ≠ 0 → check (s t k) (lower cell t) (upper cell t) = true)

def valueCheck (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → Support) (edges : List FlowBasisCodec.Edge) (target : ℤ) : Bool :=
  scalarCheck cell lam s && WindowValueFlow.flowCheck cell lam (planes cell s) edges target

theorem value_bound (cell : DifferenceCell.Cell 10) (lam : Fin 41 → Fin m → ℤ)
    (s : Fin 41 → Fin m → Support) (edges : List FlowBasisCodec.Edge) (target : ℤ)
    (g : Fin 9 → ℝ) (hg : WindowDifferenceCell.Contains cell g)
    (hc : valueCheck cell lam s edges target = true) :
    (target:ℝ)/(WindowValueFlow.denominator:ℝ) ≤ WindowGapEnergy.Fw24 g := by
  have hh : scalarCheck cell lam s = true ∧
      WindowValueFlow.flowCheck cell lam (planes cell s) edges target = true := by
    simpa only [valueCheck,Bool.and_eq_true] using hc
  have hs : ∀ t k, lam t k ≠ 0 → check (s t k) (lower cell t) (upper cell t) = true :=
    of_decide_eq_true hh.1
  apply WindowValueFlow.value_bound cell lam (planes cell s) edges target g hg hh.2
  intro t k hk
  exact sound (hs t k hk) (span_bounds hg t)

set_option pp.fullNames true
#print axioms sound
#print axioms span_bounds
#print axioms value_bound
end StructuralGoal20261016.WindowScalarLine
end
