/- SPDX-License-Identifier: Apache-2.0
Bregman lower bounds with finite value/slope uncertainty. The slope error
is paid only against |x-p-eta|, retaining affine-feedback cancellation.
-/
import StructuralGoal20261016.WindowScalarBregman
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Set
namespace StructuralGoal20261016.WindowScalarBregmanPacket
open WindowScalarBregman

theorem lower {a b p x m M V S E R : ℝ} (η : ℝ)
    (hp : p ∈ Icc a b) (hx : x ∈ Icc a b) (hM : m < M)
    (hsecond : ∀ y ∈ Icc a b,
      m ≤ iteratedDeriv 2 f y ∧ iteratedDeriv 2 f y ≤ M)
    (hV : V ≤ f p) (hE : 0 ≤ E)
    (hS : |iteratedDeriv 1 f p-S| ≤ E) (hR : |(x-p)-η| ≤ R) :
    V+S*(x-p)+m*(x-p)^2/2+
      η*(iteratedDeriv 1 f x-S-m*(x-p))-(M-m)*η^2/2-E*R ≤ f x := by
  have hb := affine_lower η hp hx hM hsecond
  have he : |(iteratedDeriv 1 f p-S)*((x-p)-η)| ≤ E*R := by
    rw [abs_mul]
    exact mul_le_mul hS hR (abs_nonneg _) hE
  nlinarith only [hb,hV,(abs_le.mp he).1]

theorem error_radius_of_interval {d η l u R : ℝ}
    (hl : l ≤ d-η) (hu : d-η ≤ u) (hR0 : -R ≤ l) (hR1 : u ≤ R) :
    |d-η| ≤ R :=
  abs_le.mpr ⟨hR0.trans hl,hu.trans hR1⟩

set_option pp.fullNames true
#print axioms lower
#print axioms error_radius_of_interval
end StructuralGoal20261016.WindowScalarBregmanPacket
end
