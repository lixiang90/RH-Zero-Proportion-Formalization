/- SPDX-License-Identifier: Apache-2.0
Exact rational piece covers connect convex polynomial minorants to the frozen
kernel, using no new analytic assumption. No global basin coverage is asserted.
-/
import StructuralW10Unconditional20261016.InheritedEnvelope
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
namespace StructuralW10Followup20261016.Scalar
open StructuralW10Unconditional20261016

structure Quad where
  a : ℚ
  b : ℚ
  c : ℚ
  deriving Inhabited

def eval (q : Quad) (x : ℚ) : ℚ := q.a*x^2+q.b*x+q.c
def evalR (q : Quad) (x : ℝ) : ℝ := (q.a : ℝ)*x^2+(q.b : ℝ)*x+q.c

structure Piece where
  right : ℚ
  point : ℕ
  word : ℕ
  deriving Inhabited

def slope (word : ℕ) : ℚ :=
  ((lo32 (hi32 (trip word)) : ℚ)-2000000000)/1000000000
def err (word : ℕ) : ℚ :=
  (4000000000-(lo32 (hi32 (trip word)) : ℚ)-(hi32 (hi32 (trip word)) : ℚ))/1000000000
def intercept (base : ℚ) (p word : ℕ) : ℚ :=
  (lo32 (trip word) : ℚ)/10000000000-slope word*((p : ℚ)/32768)-
    err word*max ((p : ℚ)/32768-base) 0
def line (base : ℚ) (p : Piece) (x : ℚ) : ℚ :=
  if p.word=0 then 0 else slope p.word*x+intercept base p.point p.word

def valid (base top : ℚ) (p : Piece) : Prop :=
  p.word=0 ∨ (PC9QB6MData.PT p.point=p.word ∧ ivB p.word≠0 ∧
    (ivA p.word : ℚ)/32768≤base ∧ top≤(ivB p.word : ℚ)/32768)
instance (base top : ℚ) (p : Piece) : Decidable (valid base top p) := by
  unfold valid
  infer_instance

theorem line_sound {base top : ℚ} {p : Piece} (h : valid base top p)
    {x : ℝ} (hl : (base : ℝ)≤x) (hu : x≤(top : ℝ)) :
    (if p.word=0 then 0 else (slope p.word : ℝ)*x+(intercept base p.point p.word : ℝ))≤wfun x := by
  rcases h with hz | ⟨heq,hb,ha,hb'⟩
  · simp only [hz,ite_true]
    exact wfun_nonneg x
  · have hn : p.word≠0 := by
      intro hz
      exact hb (by rw [hz]; rfl)
    simp only [hn,ite_false]
    have h1 : (ivA p.word : ℝ)/SC≤(base : ℝ) := by
      change (ivA p.word : ℝ)/32768≤(base : ℝ)
      simpa using (Rat.cast_le (K := ℝ)).mpr ha
    have h2 : (top : ℝ)≤(ivB p.word : ℝ)/SC := by
      change (top : ℝ)≤(ivB p.word : ℝ)/32768
      simpa using (Rat.cast_le (K := ℝ)).mpr hb'
    have hh := InheritedEnvelope.pvi_affine (heq ▸ PC9QB6MData.ptS p.point) hb h1 h2 hl hu
    convert hh using 1 <;>
      simp [InheritedEnvelope.affine,InheritedEnvelope.pointValue,
        InheritedEnvelope.pointSlope,InheritedEnvelope.pointError,
        intercept,slope,err,SC,Rat.cast_max] <;> ring

def check (q : Quad) (base top : ℚ) : ℚ → List Piece → Bool
  | _, [] => false
  | left, p::ps => decide (left≤p.right ∧ p.right≤top ∧ valid base top p ∧
      eval q left≤line base p left ∧ eval q p.right≤line base p p.right) &&
      (decide (p.right=top) || check q base top p.right ps)

theorem eval_cast (q : Quad) (x : ℚ) : (eval q x : ℝ)=evalR q (x : ℝ) := by
  simp [eval,evalR]

theorem line_cast (base : ℚ) (p : Piece) (x : ℚ) : (line base p x : ℝ)=
    if p.word=0 then 0 else (slope p.word : ℝ)*(x : ℝ)+(intercept base p.point p.word : ℝ) := by
  split_ifs <;> simp_all [line]

theorem check_sound (q : Quad) (base top left : ℚ) (ps : List Piece)
    (ha : 0≤q.a) (h : check q base top left ps=true) {x : ℝ}
    (hb : (base : ℝ)≤x) (hl : (left : ℝ)≤x) (hu : x≤(top : ℝ)) :
    evalR q x≤wfun x := by
  induction ps generalizing left with
  | nil =>
      simp only [check,Bool.false_eq_true] at h
  | cons p ps ih =>
      simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
      obtain ⟨⟨hlo,hup,hv,he0,he1⟩,ht⟩ := h
      by_cases hxr : x≤(p.right : ℝ)
      · have he0' : evalR q (left : ℝ)≤
            if p.word=0 then 0 else (slope p.word : ℝ)*(left : ℝ)+(intercept base p.point p.word : ℝ) := by
          rw [← eval_cast,← line_cast]
          exact_mod_cast he0
        have he1' : evalR q (p.right : ℝ)≤
            if p.word=0 then 0 else (slope p.word : ℝ)*(p.right : ℝ)+(intercept base p.point p.word : ℝ) := by
          rw [← eval_cast,← line_cast]
          exact_mod_cast he1
        have har : (0 : ℝ)≤q.a := by exact_mod_cast ha
        by_cases hz : p.word=0
        · simp only [hz,ite_true] at he0' he1'
          have hh := QuadraticEnvelope.below_line (s:=0) (v:=0) har hl hxr
            (by simpa [QuadraticEnvelope.quad,QuadraticEnvelope.line,evalR] using he0')
            (by simpa [QuadraticEnvelope.quad,QuadraticEnvelope.line,evalR] using he1')
          have hh' : evalR q x≤0 := by simpa [QuadraticEnvelope.quad,QuadraticEnvelope.line,evalR] using hh
          exact hh'.trans (by simpa [hz] using line_sound hv hb hu)
        · simp only [hz,ite_false] at he0' he1'
          have hh := QuadraticEnvelope.below_line (s:=(slope p.word : ℝ))
            (v:=(intercept base p.point p.word : ℝ)) har hl hxr
            (by simpa [QuadraticEnvelope.quad,QuadraticEnvelope.line,evalR] using he0')
            (by simpa [QuadraticEnvelope.quad,QuadraticEnvelope.line,evalR] using he1')
          have hh' : evalR q x≤(slope p.word : ℝ)*x+(intercept base p.point p.word : ℝ) := by
            simpa [QuadraticEnvelope.quad,QuadraticEnvelope.line,evalR] using hh
          exact hh'.trans (by simpa [hz] using line_sound hv hb hu)
      · have hn : p.right≠top := by
          intro he
          exact hxr (he ▸ hu)
        have ht' : check q base top p.right ps=true := by
          simpa only [hn,decide_false,Bool.false_or] using ht
        exact ih p.right ht' (le_of_lt (lt_of_not_ge hxr))

#print axioms line_sound
#print axioms check_sound

end StructuralW10Followup20261016.Scalar
end
