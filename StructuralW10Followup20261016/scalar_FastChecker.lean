/- SPDX-License-Identifier: Apache-2.0
Separate immutable analytic-table support checks from polynomial endpoint
checks, so multiple quadratics reuse exactly the same checked support cover.
-/
import StructuralW10Followup20261016.scalar_Checker
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralW10Followup20261016.Scalar

def supportCheck (base top : ℚ) : ℚ → List Piece → Bool
  | _, [] => false
  | left, p::ps => decide (left≤p.right ∧ p.right≤top ∧ valid base top p) &&
      (decide (p.right=top) || supportCheck base top p.right ps)

def endpointCheck (q : Quad) (base : ℚ) : ℚ → List Piece → Bool
  | _, [] => true
  | left,p::ps => decide (eval q left≤line base p left ∧
      eval q p.right≤line base p p.right) && endpointCheck q base p.right ps

theorem join_checks (q : Quad) (base top left : ℚ) (ps : List Piece)
    (hs : supportCheck base top left ps=true)
    (hq : endpointCheck q base left ps=true) : check q base top left ps=true := by
  induction ps generalizing left with
  | nil => simp [supportCheck] at hs
  | cons p ps ih =>
      simp only [supportCheck,Bool.and_eq_true,decide_eq_true_eq] at hs
      simp only [endpointCheck,Bool.and_eq_true,decide_eq_true_eq] at hq
      simp only [check,Bool.and_eq_true,decide_eq_true_eq]
      refine ⟨⟨hs.1.1,hs.1.2.1,hs.1.2.2,hq.1.1,hq.1.2⟩,?_⟩
      by_cases he : p.right=top
      · simp [he]
      · have ht : supportCheck base top p.right ps=true := by simpa [he] using hs.2
        have hi := ih p.right ht hq.2
        simp only [hi, Bool.or_true]

theorem split_check_sound (q : Quad) (base top left : ℚ) (ps : List Piece)
    (ha : 0≤q.a) (hs : supportCheck base top left ps=true)
    (hq : endpointCheck q base left ps=true) {x : ℝ}
    (hb : (base : ℝ)≤x) (hl : (left : ℝ)≤x) (hu : x≤(top : ℝ)) :
    evalR q x≤AMW.Cert.wfun x :=
  check_sound q base top left ps ha (join_checks q base top left ps hs hq) hb hl hu

#print axioms join_checks
#print axioms split_check_sound
end StructuralW10Followup20261016.Scalar
end
