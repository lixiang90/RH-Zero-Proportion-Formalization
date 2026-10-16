/- SPDX-License-Identifier: Apache-2.0
Actual dynamically selected LP supports for the redesigned kernel.
The Gram-anchor table does not cover all LP anchors. Each support here
checks its own actual value/slope jets and both optional zero extensions.
-/
import StructuralGoal20261016.WindowFixedPoint
import StructuralGoal20261016.WindowFixedTablesAll
import StructuralGoal20261016.WindowConvexityAll
import StructuralGoal20261016.WindowQuantizedSupport
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowSupportCertificate
open WindowScalarMinorant WindowJetTableData

structure Support where
  center : ℕ
  anchor : ℤ
  value : ℤ
  slope : ℤ
  error : ℤ

def point (s : Support) : ℚ := (s.anchor:ℚ)/32768
def value (s : Support) : ℚ := (s.value:ℚ)/10000000000
def slope (s : Support) : ℚ := (s.slope:ℚ)/1000000000
def error (s : Support) : ℚ := (s.error:ℚ)/1000000000
def coreLeft (s : Support) : ℚ := (s.center:ℚ)-6881/32768
def coreRight (s : Support) : ℚ := (s.center:ℚ)+6881/32768

abbrev Checks (s : Support) (l u : ℤ) : Prop :=
  1 ≤ s.center ∧ s.center ≤ 16 ∧ l ≤ u ∧
  coreLeft s ≤ point s ∧ point s ≤ coreRight s ∧
  0 ≤ error s ∧ 0 ≤ WindowConvexityAll.lower s.center ∧
  WindowFixedPoint.valueCheck s.center (point s) (value s) = true ∧
  WindowFixedPoint.slopeCheck s.center (point s)
    (slope s+error s/2) (error s/2) = true ∧
  (coreLeft s ≤ (l:ℚ)/32768 ∨
    (0 ≤ slope s+error s ∧ value s+(slope s+error s)*(coreLeft s-point s) ≤ 0)) ∧
  ((u:ℚ)/32768 ≤ coreRight s ∨
    (slope s ≤ 0 ∧ value s+slope s*(coreRight s-point s) ≤ 0))

def check (s : Support) (l u : ℤ) : Bool := decide (Checks s l u)

def affine (s : Support) (l : ℤ) (x : ℝ) : ℝ :=
  WindowQuantizedSupport.line (point s) (value s) (slope s) (error s) ((l:ℝ)/32768) x

def constant (s : Support) (l : ℤ) : ℤ :=
  32768*s.value-10*s.slope*s.anchor-10*s.error*max (s.anchor-l) 0
def coefficient (s : Support) : ℤ := 10*s.slope

theorem affine_eq (s : Support) (l : ℤ) (x : ℝ) :
    affine s l x = ((constant s l:ℝ)+32768*(coefficient s:ℝ)*x)/(10000000000*32768) := by
  by_cases h : 0 ≤ s.anchor-l
  · have hR : (0:ℝ) ≤ (s.anchor:ℝ)-(l:ℝ) := by exact_mod_cast h
    have hQ : (0:ℝ) ≤ (point s:ℝ)-(l:ℝ)/32768 := by
      unfold point
      push_cast
      linarith
    simp only [affine,WindowQuantizedSupport.line,max_eq_left hQ,
      constant,coefficient,max_eq_left h]
    unfold point value slope error
    push_cast
    ring
  · have hR : (s.anchor:ℝ)-(l:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    have hQ : (point s:ℝ)-(l:ℝ)/32768 ≤ 0 := by
      unfold point
      push_cast
      linarith
    simp only [affine,WindowQuantizedSupport.line,max_eq_right hQ,
      constant,coefficient,max_eq_right (le_of_not_ge h)]
    unfold point value slope error
    push_cast
    ring

theorem sound {s : Support} {l u : ℤ} (hc : check s l u = true)
    {x : ℝ} (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    affine s l x ≤ f x := by
  have hh : Checks s l u := of_decide_eq_true hc
  rcases hh with ⟨hn0,hn1,_,hpl,hpu,hE,hcurv,hV,hD,hleft,hright⟩
  have hW := fun j hj => WindowFixedTablesAll.w_sound hn0 (by omega) j hj
  have hv := WindowFixedPoint.value_sound hW hV
  have hd := WindowFixedPoint.slope_sound hW hD
  have hp : (point s:ℝ) ∈ Icc (coreLeft s:ℝ) (coreRight s:ℝ) := by
    exact ⟨by exact_mod_cast hpl,by exact_mod_cast hpu⟩
  have he : (0:ℝ) ≤ (error s:ℝ) := by exact_mod_cast hE
  have hdl : (slope s:ℝ) ≤ iteratedDeriv 1 f (point s) := by
    push_cast at hd
    linarith [(abs_le.mp hd).1]
  have hdu : iteratedDeriv 1 f (point s) ≤ (slope s:ℝ)+(error s:ℝ) := by
    push_cast at hd
    linarith [(abs_le.mp hd).2]
  have hs : ∀ y ∈ Icc (coreLeft s:ℝ) (coreRight s:ℝ), 0 ≤ iteratedDeriv 2 f y := by
    intro y hy
    have hy' : y ∈ Icc ((s.center:ℝ)-21/100) ((s.center:ℝ)+21/100) := by
      dsimp [coreLeft,coreRight] at hy
      push_cast at hy
      constructor <;> linarith [hy.1,hy.2]
    have hb := WindowConvexityAll.lower_sound hn0 hn1 y hy'
    have h0 : (0:ℝ) ≤ (WindowConvexityAll.lower s.center:ℝ) := by exact_mod_cast hcurv
    exact h0.trans hb
  apply WindowQuantizedSupport.zero_extension hp hx.1 hv he hdl hdu hs
  · intro hxa
    rcases hleft with hleft | hleft
    · have hb : (coreLeft s:ℝ) ≤ (l:ℝ)/32768 := by exact_mod_cast hleft
      exact False.elim (by linarith [hx.1])
    · have hs' : (0:ℝ) ≤ ((slope s+error s:ℚ):ℝ) := by exact_mod_cast hleft.1
      have hv' : ((value s+(slope s+error s)*(coreLeft s-point s):ℚ):ℝ) ≤ 0 := by
        exact_mod_cast hleft.2
      push_cast at hs' hv'
      exact ⟨hs',hv'⟩
  · intro hxb
    rcases hright with hright | hright
    · have hb : (u:ℝ)/32768 ≤ (coreRight s:ℝ) := by exact_mod_cast hright
      exact False.elim (by linarith [hx.2])
    · have hs' : (slope s:ℝ) ≤ 0 := by exact_mod_cast hright.1
      have hv' : ((value s+slope s*(coreRight s-point s):ℚ):ℝ) ≤ 0 := by
        exact_mod_cast hright.2
      push_cast at hv'
      exact ⟨hs',hv'⟩

theorem integer_line_sound {s : Support} {l u : ℤ} (hc : check s l u = true)
    {x : ℝ} (hx : (l:ℝ)/32768 ≤ x ∧ x ≤ (u:ℝ)/32768) :
    ((constant s l:ℝ)+32768*(coefficient s:ℝ)*x)/(10000000000*32768) ≤ f x := by
  rw [← affine_eq]
  exact sound hc hx

set_option pp.fullNames true
#print axioms affine_eq
#print axioms sound
#print axioms integer_line_sound
end StructuralGoal20261016.WindowSupportCertificate
end
