/- SPDX-License-Identifier: Apache-2.0
Rational four-block polynomials in the actual 464-variable moment lift.
Finite index alignment is separated from algebraic sum identities. Grouped
RLT expansion uses genuine normalized-gap products and the actual old Form.
No scalar input, local exclusion, or coverage theorem is assumed here.
-/
import StructuralGoal20261016.WindowMomentLayout
import StructuralGoal20261016.WindowMomentRLT
import StructuralGoal20261016.WindowMomentRounding
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentPolynomial
open WindowMomentLayout

structure RatForm where
  gap : Fin 9 → ℚ
  scalar : Fin 41 → ℚ
  h : Fin 45 → ℚ
  q : Fin 9 → Fin 41 → ℚ
  bound : ℚ

def dotQ {ι : Type*} [Fintype ι] (a : ι → ℚ) (x : ι → ℝ) : ℝ :=
  ∑ i, (a i:ℝ)*x i

def realVector (q : Fin 9 → ℚ) : Fin 9 → ℝ := fun r => q r

abbrev Block := Fin 9 ⊕ (Fin 41 ⊕ (Fin 45 ⊕ (Fin 9 × Fin 41)))

def encode : Block → Fin 464
  | .inl r => gapIndex r
  | .inr (.inl e) => uIndex e
  | .inr (.inr (.inl e)) => hIndex e
  | .inr (.inr (.inr p)) => qIndex p.1 p.2

def decode (i : Fin 464) : Block :=
  if h0 : (i:ℕ) < 9 then .inl ⟨i,by omega⟩
  else if h1 : (i:ℕ) < 50 then .inr (.inl ⟨(i:ℕ)-9,by omega⟩)
  else if h2 : (i:ℕ) < 95 then .inr (.inr (.inl ⟨(i:ℕ)-50,by omega⟩))
  else .inr (.inr (.inr (⟨((i:ℕ)-95)/41,by omega⟩,⟨((i:ℕ)-95)%41,by omega⟩)))

theorem decode_encode : ∀ b : Block, decode (encode b) = b := by decide +kernel
theorem encode_decode : ∀ i : Fin 464, encode (decode i) = i := by decide +kernel

def blockEquiv : Block ≃ Fin 464 where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

def blockCoeff (a : RatForm) : Block → ℚ
  | .inl r => a.gap r
  | .inr (.inl e) => a.scalar e
  | .inr (.inr (.inl e)) => a.h e
  | .inr (.inr (.inr p)) => a.q p.1 p.2

def flatten (a : RatForm) (i : Fin 464) : ℚ := blockCoeff a (decode i)

theorem flatten_encode (a : RatForm) (b : Block) :
    flatten a (encode b) = blockCoeff a b := by
  unfold flatten
  rw [decode_encode]

theorem sum_blocks (f : Fin 464 → ℝ) :
    (∑ i, f i) =
      (∑ r, f (gapIndex r))+
        ((∑ e, f (uIndex e))+((∑ e, f (hIndex e))+
          ∑ r, ∑ e, f (qIndex r e))) := by
  have he := Fintype.sum_equiv blockEquiv
    (fun b : Block => f (encode b)) f (fun _ => rfl)
  rw [← he]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,encode]

def eval (a : RatForm) (center radius g : Fin 9 → ℝ) : ℝ :=
  WindowMomentRounding.rationalEval (flatten a) (actual center radius g)

def blockEval (a : RatForm) (center radius g : Fin 9 → ℝ) : ℝ :=
  dotQ a.gap g+
    (dotQ a.scalar (u g)+
      (dotQ a.h (fun e => normalized center radius g (hFirst e)*
          normalized center radius g (hSecond e))+
        ∑ s, dotQ (a.q s) (fun e => normalized center radius g s*u g e)))

theorem eval_actual (a : RatForm) (center radius g : Fin 9 → ℝ) :
    eval a center radius g = blockEval a center radius g := by
  unfold eval WindowMomentRounding.rationalEval
  rw [sum_blocks]
  have hg (r : Fin 9) : flatten a (gapIndex r) = a.gap r :=
    flatten_encode a (.inl r)
  have hu (e : Fin 41) : flatten a (uIndex e) = a.scalar e :=
    flatten_encode a (.inr (.inl e))
  have hh (e : Fin 45) : flatten a (hIndex e) = a.h e :=
    flatten_encode a (.inr (.inr (.inl e)))
  have hq (s : Fin 9) (e : Fin 41) : flatten a (qIndex s e) = a.q s e :=
    flatten_encode a (.inr (.inr (.inr (s,e))))
  simp only [hg,hu,hh,hq,actual_gap,actual_u,actual_h,actual_q,blockEval,dotQ]

def oldForm (a : WindowLiftedFarkas.Form) : RatForm where
  gap := fun r => a.gap r
  scalar := fun e => a.scalar e
  h := fun _ => 0
  q := fun _ _ => 0
  bound := a.bound

theorem oldForm_eval (a : WindowLiftedFarkas.Form) (center radius g : Fin 9 → ℝ) :
    eval (oldForm a) center radius g = WindowLiftedFarkas.eval a g := by
  rw [eval_actual]
  simp [blockEval,dotQ,oldForm,u,WindowLiftedFarkas.eval]

def hLookup : Fin 9 → Fin 9 → Fin 45 :=
  ![![0,1,2,3,4,5,6,7,8],
    ![1,9,10,11,12,13,14,15,16],
    ![2,10,17,18,19,20,21,22,23],
    ![3,11,18,24,25,26,27,28,29],
    ![4,12,19,25,30,31,32,33,34],
    ![5,13,20,26,31,35,36,37,38],
    ![6,14,21,27,32,36,39,40,41],
    ![7,15,22,28,33,37,40,42,43],
    ![8,16,23,29,34,38,41,43,44]]

theorem hLookup_alignment : ∀ s r : Fin 9,
    (hFirst (hLookup s r) = s ∧ hSecond (hLookup s r) = r) ∨
      (hFirst (hLookup s r) = r ∧ hSecond (hLookup s r) = s) := by decide +kernel

theorem hLookup_product (y : Fin 9 → ℝ) (s r : Fin 9) :
    y (hFirst (hLookup s r))*y (hSecond (hLookup s r)) = y s*y r := by
  rcases hLookup_alignment s r with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2,mul_comm]

def collectH (M : Fin 9 → Fin 9 → ℚ) (e : Fin 45) : ℚ :=
  ∑ p : Fin 9 × Fin 9, if hLookup p.1 p.2 = e then M p.1 p.2 else 0

theorem collect_dot {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (index : ι → κ) (a : ι → ℚ) (z : κ → ℝ) :
    (∑ j, (((∑ i, if index i = j then a i else 0):ℚ):ℝ)*z j) =
      ∑ i, (a i:ℝ)*z (index i) := by
  classical
  have hc (j : κ) : (((∑ i, if index i = j then a i else 0):ℚ):ℝ) =
      ∑ i, if index i = j then (a i:ℝ) else 0 := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [hc,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  simp

theorem collectH_eval (M : Fin 9 → Fin 9 → ℚ) (y : Fin 9 → ℝ) :
    dotQ (collectH M) (fun e => y (hFirst e)*y (hSecond e)) =
      ∑ s, ∑ r, (M s r:ℝ)*(y s*y r) := by
  unfold dotQ collectH
  rw [collect_dot]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  rw [hLookup_product]

theorem dot_add {ι : Type*} [Fintype ι] (a b : ι → ℚ) (x : ι → ℝ) :
    dotQ (fun i => a i+b i) x = dotQ a x+dotQ b x := by
  simp only [dotQ,Rat.cast_add,add_mul,Finset.sum_add_distrib]

theorem dot_smul {ι : Type*} [Fintype ι] (c : ℚ) (a : ι → ℚ) (x : ι → ℝ) :
    dotQ (fun i => c*a i) x = (c:ℝ)*dotQ a x := by
  simp only [dotQ,Rat.cast_mul,mul_assoc,Finset.mul_sum]

def gapCentre (a : WindowLiftedFarkas.Form) (center : Fin 9 → ℚ) : ℚ :=
  (∑ r, (a.gap r:ℚ)*center r)-(a.bound:ℚ)

/-- Exact coefficients of (old_eval-old_bound)*(A+sum b_s*y_s). -/
def grouped (a : WindowLiftedFarkas.Form) (center radius : Fin 9 → ℚ)
    (A : ℚ) (b : Fin 9 → ℚ) : RatForm where
  gap := fun r => A*(a.gap r:ℚ)+b r*gapCentre a center/radius r
  scalar := fun e => A*(a.scalar e:ℚ)
  h := collectH (fun s r => b s*(a.gap r:ℚ)*radius r)
  q := fun s e => b s*(a.scalar e:ℚ)
  bound := A*(a.bound:ℚ)+∑ r, b r*gapCentre a center*center r/radius r

theorem grouped_identity (a : WindowLiftedFarkas.Form) (center radius : Fin 9 → ℚ)
    (A : ℚ) (b : Fin 9 → ℚ) (g : Fin 9 → ℝ)
    (hr : ∀ r, radius r ≠ 0) :
    eval (grouped a center radius A b) (realVector center) (realVector radius) g-
        ((grouped a center radius A b).bound:ℝ) =
      (WindowLiftedFarkas.eval a g-(a.bound:ℝ))*
        WindowMomentRLT.multiplier (A:ℝ) (realVector b)
          (normalized (realVector center) (realVector radius) g) := by
  let y := normalized (realVector center) (realVector radius) g
  let K := gapCentre a center
  let G := dotQ (fun r => (a.gap r:ℚ)) g
  let U := dotQ (fun e => (a.scalar e:ℚ)) (u g)
  let T := ∑ r, (a.gap r:ℝ)*(radius r:ℝ)*y r
  let Y := dotQ b y
  have hy (r : Fin 9) : (radius r:ℝ)*y r = g r-(center r:ℝ) := by
    have hn : (radius r:ℝ) ≠ 0 := by exact_mod_cast hr r
    dsimp [y,normalized,realVector]
    field_simp [hn]
  have hT : T = G-∑ r, (a.gap r:ℝ)*(center r:ℝ) := by
    dsimp only [T,G,dotQ]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_assoc,hy]
    push_cast
    ring
  have hK : (K:ℝ) = (∑ r, (a.gap r:ℝ)*(center r:ℝ))-(a.bound:ℝ) := by
    dsimp [K,gapCentre]
    push_cast <;> rfl
  have hOld : WindowLiftedFarkas.eval a g-(a.bound:ℝ) = (K:ℝ)+T+U := by
    rw [hK,hT]
    dsimp [WindowLiftedFarkas.eval,G,U,dotQ,u]
    push_cast
    ring
  have hlinear :
      dotQ (fun r => b r*K/radius r) g-
        ((∑ r, b r*K*center r/radius r:ℚ):ℝ) = (K:ℝ)*Y := by
    dsimp [dotQ,Y]
    push_cast
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [y,normalized,realVector]
    ring
  have hH :
      dotQ (collectH (fun s r => b s*(a.gap r:ℚ)*radius r))
        (fun e => y (hFirst e)*y (hSecond e)) = Y*T := by
    rw [collectH_eval]
    dsimp [Y,T,dotQ]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    push_cast
    ring
  have hQ :
      (∑ s, dotQ (fun e => b s*(a.scalar e:ℚ)) (fun e => y s*u g e)) = Y*U := by
    dsimp [dotQ,Y,U]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    push_cast
    ring
  rw [eval_actual]
  change
    (dotQ (fun r => A*(a.gap r:ℚ)+b r*K/radius r) g+
      (dotQ (fun e => A*(a.scalar e:ℚ)) (u g)+
        (dotQ (collectH (fun s r => b s*(a.gap r:ℚ)*radius r))
          (fun e => y (hFirst e)*y (hSecond e))+
          ∑ s, dotQ (fun e => b s*(a.scalar e:ℚ)) (fun e => y s*u g e))))-
      ((A*(a.bound:ℚ)+∑ r, b r*K*center r/radius r:ℚ):ℝ) = _
  rw [dot_add,dot_smul,dot_smul,hH,hQ]
  have hb : ((A*(a.bound:ℚ)+∑ r, b r*K*center r/radius r:ℚ):ℝ) =
      (A:ℝ)*(a.bound:ℝ)+((∑ r, b r*K*center r/radius r:ℚ):ℝ) := by
    push_cast <;> rfl
  rw [hb]
  have hle : WindowLiftedFarkas.eval a g = G+U := by
    simp only [G,U,dotQ,u,WindowLiftedFarkas.eval,Rat.cast_intCast]
  unfold WindowMomentRLT.multiplier
  change _ = (WindowLiftedFarkas.eval a g-(a.bound:ℝ))*((A:ℝ)+Y)
  rw [hle]
  have hOld' : G+U-(a.bound:ℝ) = (K:ℝ)+T+U := by
    rw [← hle]
    exact hOld
  have hlinear' : dotQ (fun r => b r*K/radius r) g =
      (K:ℝ)*Y+((∑ r, b r*K*center r/radius r:ℚ):ℝ) := by
    linarith only [hlinear]
  have hT' : T = G-(a.bound:ℝ)-(K:ℝ) := by
    linarith only [hOld']
  change ((A:ℝ)*G+dotQ (fun r => b r*K/radius r) g)+
    ((A:ℝ)*U+(Y*T+Y*U))-
    ((A:ℝ)*(a.bound:ℝ)+((∑ r, b r*K*center r/radius r:ℚ):ℝ)) =
      (G+U-(a.bound:ℝ))*((A:ℝ)+Y)
  rw [hlinear',hT']
  ring

theorem grouped_nonpos (a : WindowLiftedFarkas.Form) (center radius : Fin 9 → ℚ)
    (A : ℚ) (b : Fin 9 → ℚ) (g : Fin 9 → ℝ)
    (hA : (∑ r, |(b r:ℝ)|) ≤ (A:ℝ))
    (hr : ∀ r, (0:ℝ) < (radius r:ℝ))
    (hg : ∀ r, (center r:ℝ)-(radius r:ℝ) ≤ g r ∧
      g r ≤ (center r:ℝ)+(radius r:ℝ))
    (hrow : WindowLiftedFarkas.eval a g ≤ (a.bound:ℝ)) :
    eval (grouped a center radius A b) (realVector center) (realVector radius) g ≤
      ((grouped a center radius A b).bound:ℝ) := by
  have hn : ∀ r, radius r ≠ 0 := by
    intro r h
    have hh := hr r
    rw [h] at hh
    norm_num at hh
  have hi := grouped_identity a center radius A b g hn
  have hp := WindowMomentRLT.actual_nonpos hA hr hg hrow
  have he : eval (grouped a center radius A b) (realVector center) (realVector radius) g-
      ((grouped a center radius A b).bound:ℝ) ≤ 0 := by
    rw [hi]
    exact hp
  linarith

set_option pp.fullNames true
#print axioms decode_encode
#print axioms encode_decode
#print axioms sum_blocks
#print axioms eval_actual
#print axioms oldForm_eval
#print axioms hLookup_alignment
#print axioms collectH_eval
#print axioms grouped_identity
#print axioms grouped_nonpos
end StructuralGoal20261016.WindowMomentPolynomial
end

