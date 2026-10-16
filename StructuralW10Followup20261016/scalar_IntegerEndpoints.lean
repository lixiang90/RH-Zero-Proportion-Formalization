/- SPDX-License-Identifier: Apache-2.0
Cleared-denominator endpoint comparisons avoid repeated rational polynomial
normalization. The mathematical comparison is unchanged.
-/
import StructuralW10Followup20261016.scalar_FastChecker
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralW10Followup20261016.Scalar

def cleared (a b c x : ℚ) : ℤ :=
  a.num*(b.den : ℤ)*c.den*x.num^2+
  b.num*(a.den : ℤ)*c.den*x.num*x.den+
  c.num*(a.den : ℤ)*b.den*(x.den : ℤ)^2

theorem cleared_sound (a b c x : ℚ) (h : cleared a b c x≤0) :
    a*x^2+b*x+c≤0 := by
  have ha : (0 : ℚ)<a.den := by exact_mod_cast a.den_pos
  have hb : (0 : ℚ)<b.den := by exact_mod_cast b.den_pos
  have hc : (0 : ℚ)<c.den := by exact_mod_cast c.den_pos
  have hx : (0 : ℚ)<x.den := by exact_mod_cast x.den_pos
  have hid : (a.den : ℚ)*b.den*c.den*(x.den : ℚ)^2*(a*x^2+b*x+c)=
      (cleared a b c x : ℚ) := by
    conv_lhs =>
      arg 2
      rw [← a.num_div_den,← b.num_div_den,← c.num_div_den,← x.num_div_den]
    unfold cleared
    push_cast
    field_simp
    <;> ring
  have hh : (a.den : ℚ)*b.den*c.den*(x.den : ℚ)^2*(a*x^2+b*x+c)≤0 := by
    rw [hid]
    exact_mod_cast h
  by_contra hbad
  have hpos := mul_pos (show (0 : ℚ)<(a.den : ℚ)*b.den*c.den*(x.den : ℚ)^2 by positivity)
    (lt_of_not_ge hbad)
  exact (not_lt_of_ge hh) hpos

def lSlope (p : Piece) : ℚ := if p.word=0 then 0 else slope p.word
def lIntercept (base : ℚ) (p : Piece) : ℚ := if p.word=0 then 0 else intercept base p.point p.word

theorem line_split (base : ℚ) (p : Piece) (x : ℚ) :
    line base p x=lSlope p*x+lIntercept base p := by
  by_cases h : p.word=0 <;> simp [line,lSlope,lIntercept,h]

def integerEndpointCheck (q : Quad) (base : ℚ) : ℚ → List Piece → Bool
  | _, [] => true
  | left,p::ps => decide (cleared q.a (q.b-lSlope p) (q.c-lIntercept base p) left≤0 ∧
      cleared q.a (q.b-lSlope p) (q.c-lIntercept base p) p.right≤0) &&
      integerEndpointCheck q base p.right ps

theorem integer_endpoints_sound (q : Quad) (base left : ℚ) (ps : List Piece)
    (h : integerEndpointCheck q base left ps=true) : endpointCheck q base left ps=true := by
  induction ps generalizing left with
  | nil => rfl
  | cons p ps ih =>
      simp only [integerEndpointCheck,Bool.and_eq_true,decide_eq_true_eq] at h
      simp only [endpointCheck,Bool.and_eq_true,decide_eq_true_eq]
      refine ⟨⟨?_,?_⟩,ih p.right h.2⟩
      · have hh := cleared_sound q.a (q.b-lSlope p) (q.c-lIntercept base p) left h.1.1
        rw [line_split]
        unfold eval
        linarith only [hh]
      · have hh := cleared_sound q.a (q.b-lSlope p) (q.c-lIntercept base p) p.right h.1.2
        rw [line_split]
        unfold eval
        linarith only [hh]

#print axioms cleared_sound
#print axioms integer_endpoints_sound
end StructuralW10Followup20261016.Scalar
end
