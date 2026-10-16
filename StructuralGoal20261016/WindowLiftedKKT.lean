/- SPDX-License-Identifier: Apache-2.0
Actual lifted derivative-graph certificates. Each row is a difference-cell
inequality, a checked derivative slab, a checked graph facet, or a genuine
orthant KKT inequality. Their integer combination is checked by the residual
paid Farkas/forest-flow consumer. Artificial cell faces never imply KKT zeros.
-/
import StructuralGoal20261016.WindowLiftedFarkas
import StructuralGoal20261016.WindowFirstOrderCertificate
import StructuralGoal20261016.WindowDerivativeGraph
import StructuralGoal20261016.WindowCellCuts
import StructuralGoal20261016.WindowKKTInstance
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowLiftedKKT
open WindowGramTransfer WindowDirectionalFlow
open WindowLiftedFarkas (Form eval)
open StructuralW10Followup20261016.NewLedger (W)

def sign (upper : Bool) : ℤ := if upper then 1 else -1

def spanForm (e : Fin 41) (A U B : ℤ) : Form where
  gap := fun r => A*incidence e r
  scalar := fun f => if f = e then U else 0
  bound := B

theorem incidence_dot (e : Fin 41) (g : Fin 9 → ℝ) :
    (∑ r, (incidence e r:ℝ)*g r) = span g e := by
  rw [WindowDirectionalAffine.span_eq_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [incidence_cast]
  ring

theorem spanForm_eval (e : Fin 41) (A U B : ℤ) (g : Fin 9 → ℝ) :
    eval (spanForm e A U B) g =
      (A:ℝ)*span g e+(U:ℝ)*WindowGapEnergy.w1 (span g e) := by
  have hgap : (∑ r, ((A*incidence e r:ℤ):ℝ)*g r) =
      (A:ℝ)*(∑ r, (incidence e r:ℝ)*g r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    push_cast
    ring
  unfold eval spanForm
  dsimp only
  rw [hgap,incidence_dot]
  simp

def dbmForm (cell : DifferenceCell.Cell 10) (i j : Fin 10) : Form where
  gap := fun r => denominator*WindowCellCuts.negativeIncidence j i r
  scalar := fun _ => 0
  bound := 2*DS*D*cell i j

theorem dbm_eval (cell : DifferenceCell.Cell 10) (i j : Fin 10) (g : Fin 9 → ℝ) :
    eval (dbmForm cell i j) g =
      (2*(DS:ℝ)*(D:ℝ))*(WindowDifferenceCell.positions g j-WindowDifferenceCell.positions g i) := by
  have hgap : (∑ r, ((denominator*WindowCellCuts.negativeIncidence j i r:ℤ):ℝ)*g r) =
      (denominator:ℝ)*(∑ r, (WindowCellCuts.negativeIncidence j i r:ℝ)*g r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    push_cast
    ring
  unfold eval dbmForm
  dsimp only
  simp only [Int.cast_zero,zero_mul,Finset.sum_const_zero,add_zero]
  rw [hgap]
  have he := WindowCellCuts.objective_eq j i g
  unfold WindowValueSublevel.objective at he
  norm_num [denominator,SC,DS,D]
  nlinarith [he]

def slabForm (e : Fin 41) (upper : Bool) (row : Row) : Form :=
  spanForm e (-sign upper*2*SC*row.slope*D) (sign upper*denominator)
    (D*(sign upper*(2*SC*row.value-row.slope*row.anchor)+2*SC*row.error))

theorem slab_numeric (upper : Bool) (row : Row) (x : ℝ)
    (h : |WindowGapEnergy.w1 x-((row.value:ℝ)/(DS:ℝ)+
      (row.slope:ℝ)/(DS:ℝ)*(x-(row.anchor:ℝ)/(2*(SC:ℝ))))| ≤ (row.error:ℝ)/(DS:ℝ)) :
    ((-sign upper*2*SC*row.slope*D:ℤ):ℝ)*x+
      ((sign upper*denominator:ℤ):ℝ)*WindowGapEnergy.w1 x ≤
      ((D*(sign upper*(2*SC*row.value-row.slope*row.anchor)+2*SC*row.error):ℤ):ℝ) := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  cases upper <;> norm_num [sign,SC,DS,D,denominator] at * <;> nlinarith

def facetForm (e : Fin 41) (upper : Bool) (S C : ℤ) : Form :=
  spanForm e (-sign upper*2*SC*S*D) (sign upper*denominator) (sign upper*2*D*C)

def kktForm (r : Fin 9) (upper : Bool) : Form where
  gap := fun _ => 0
  scalar := fun e => sign upper*2*SC*DS*weightInt e*incidence e r
  bound := -sign upper*2*SC*DS*pressureInt r

theorem basis_span (r : Fin 9) (e : Fin 41) :
    span (WindowGapEnergy.basis (n := 10) r) e = (incidence e r:ℝ) := by
  rw [WindowDirectionalAffine.span_eq_sum]
  simp [WindowGapEnergy.basis,← incidence_cast]

theorem gradient_expansion (g : Fin 9 → ℝ) (r : Fin 9) :
    (2*(SC:ℝ)*(DS:ℝ)*(D:ℝ))*WindowGapEnergy.gradient W g r =
      2*(SC:ℝ)*(DS:ℝ)*(pressureInt r:ℝ)+
      ∑ e, ((2*SC*DS*weightInt e*incidence e r:ℤ):ℝ)*WindowGapEnergy.w1 (span g e) := by
  have hp : pressure (WindowGapEnergy.basis (n := 10) r) = W.b r := by
    simp [pressure,WindowGapEnergy.basis]
  unfold WindowGapEnergy.gradient
  rw [WindowDirectionalAffine.directional_eq,hp,← pressure_cast]
  simp_rw [basis_span,← weight_cast]
  rw [mul_add,Finset.mul_sum]
  congr 1
  · norm_num [D]
    ring
  · apply Finset.sum_congr rfl
    intro e _
    push_cast
    norm_num [D]
    ring

theorem kkt_eval (r : Fin 9) (upper : Bool) (g : Fin 9 → ℝ) :
    eval (kktForm r upper) g =
      (sign upper:ℝ)*(2*(SC:ℝ)*(DS:ℝ)*(D:ℝ))*WindowGapEnergy.gradient W g r-
        (sign upper:ℝ)*2*(SC:ℝ)*(DS:ℝ)*(pressureInt r:ℝ) := by
  have hs : (∑ e, ((sign upper*2*SC*DS*weightInt e*incidence e r:ℤ):ℝ)*
      WindowGapEnergy.w1 (span g e)) =
      (sign upper:ℝ)*(∑ e, ((2*SC*DS*weightInt e*incidence e r:ℤ):ℝ)*
        WindowGapEnergy.w1 (span g e)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    push_cast
    ring
  unfold eval kktForm
  dsimp only
  simp only [Int.cast_zero,zero_mul,Finset.sum_const_zero,zero_add]
  rw [hs]
  have he := gradient_expansion g r
  have he' : (∑ e, ((2*SC*DS*weightInt e*incidence e r:ℤ):ℝ)*
      WindowGapEnergy.w1 (span g e)) =
      (2*(SC:ℝ)*(DS:ℝ)*(D:ℝ))*WindowGapEnergy.gradient W g r-
        2*(SC:ℝ)*(DS:ℝ)*(pressureInt r:ℝ) := by linarith
  rw [he']
  ring

inductive Atom where
  | dbm (i j : Fin 10)
  | slab (e : Fin 41) (upper : Bool) (s : WindowFirstOrderCertificate.Scalar)
  | facet (e : Fin 41) (upper : Bool) (S C : ℤ) (k0 k1 : ℕ)
  | kkt (r : Fin 9) (upper : Bool)

def form (cell : DifferenceCell.Cell 10) : Atom → Form
  | .dbm i j => dbmForm cell i j
  | .slab e upper s => slabForm e upper s.row
  | .facet e upper S C _ _ => facetForm e upper S C
  | .kkt r upper => kktForm r upper

def checkAtom (sep : ℚ) (cell : DifferenceCell.Cell 10) : Atom → Bool
  | .dbm _ _ => true
  | .slab e _ s => WindowFirstOrderCertificate.checkScalar cell e s
  | .facet e upper S C k0 k1 =>
      if upper then WindowDerivativeGraph.upperCheck (WindowScalarLine.lower cell e)
        (WindowScalarLine.upper cell e) k0 k1 S C
      else WindowDerivativeGraph.lowerCheck (WindowScalarLine.lower cell e)
        (WindowScalarLine.upper cell e) k0 k1 S C
  | .kkt r upper => if upper then decide (sep*32768 < -(cell r.succ r.castSucc:ℚ)) else true

theorem atom_sound {sep : ℚ} {cell : DifferenceCell.Cell 10} (a : Atom)
    (hc : checkAtom sep cell a = true) {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.Relevant (sep:ℝ) g)
    (hcell : WindowDifferenceCell.Contains cell g) :
    eval (form cell a) g ≤ ((form cell a).bound:ℝ) := by
  cases a with
  | dbm i j =>
    change eval (dbmForm cell i j) g ≤ ((2*DS*D*cell i j:ℤ):ℝ)
    rw [dbm_eval]
    have hh := hcell i j
    have hp := mul_le_mul_of_nonneg_left hh (by norm_num [DS,D] : (0:ℝ) ≤ 2*(DS:ℝ)*(D:ℝ))
    simpa only [Int.cast_mul,Int.cast_ofNat] using hp
  | slab e upper s =>
    have hb := WindowScalarLine.span_bounds hcell e
    have hx : WindowGramTransfer.span g e ∈ Set.Icc
        (WindowFirstOrderCertificate.leftQ cell e:ℝ) (WindowFirstOrderCertificate.rightQ cell e:ℝ) := by
      unfold WindowFirstOrderCertificate.leftQ WindowFirstOrderCertificate.rightQ
      push_cast
      exact hb
    have hs := WindowFirstOrderCertificate.scalar_valid hc hx
    change eval (slabForm e upper s.row) g ≤ _
    rw [slabForm,spanForm_eval]
    exact slab_numeric upper s.row (span g e) hs
  | facet e upper S C k0 k1 =>
    have hb := WindowScalarLine.span_bounds hcell e
    change eval (facetForm e upper S C) g ≤ ((sign upper*2*D*C:ℤ):ℝ)
    rw [facetForm,spanForm_eval]
    cases upper
    · have hs := WindowDerivativeGraph.lower_sound hc hb
      have hp := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 20000000000)
      norm_num [sign,SC,DS,D,denominator] at *
      nlinarith
    · have hs := WindowDerivativeGraph.upper_sound hc hb
      have hp := mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 20000000000)
      norm_num [sign,SC,DS,D,denominator] at *
      nlinarith
  | kkt r upper =>
    have hk := WindowKKTInstance.of_relevant hg
    change eval (kktForm r upper) g ≤ ((-sign upper*2*SC*DS*pressureInt r:ℤ):ℝ)
    rw [kkt_eval]
    cases upper
    · have hn := hk.1 r
      norm_num [sign,SC,DS,D] at *
      nlinarith
    · have hi : (sep:ℝ) < g r := WindowCellCuts.interior_of_bound hcell r (of_decide_eq_true hc)
      have hz := hk.2 r hi
      rw [hz]
      norm_num [sign,SC,DS,D]

def check {n : ℕ} (sep : ℚ) (cell : DifferenceCell.Cell 10) (a : Fin n → Atom)
    (mu : Fin n → ℤ) (minimum : ℤ) (edges : List FlowBasisCodec.Edge) : Bool :=
  decide (∀ i, checkAtom sep cell (a i) = true) &&
    WindowLiftedFarkas.check cell (fun i => form cell (a i)) mu minimum edges

theorem exclude {n : ℕ} {sep : ℚ} {cell : DifferenceCell.Cell 10} (a : Fin n → Atom)
    (mu : Fin n → ℤ) (minimum : ℤ) (edges : List FlowBasisCodec.Edge)
    (hc : check sep cell a mu minimum edges = true) {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.Relevant (sep:ℝ) g)
    (hcell : WindowDifferenceCell.Contains cell g) : False := by
  have hh : decide (∀ i, checkAtom sep cell (a i) = true) = true ∧
      WindowLiftedFarkas.check cell (fun i => form cell (a i)) mu minimum edges = true := by
    simpa only [check,Bool.and_eq_true] using hc
  have ha : ∀ i, checkAtom sep cell (a i) = true := of_decide_eq_true hh.1
  exact WindowLiftedFarkas.exclude cell (fun i => form cell (a i)) mu minimum edges hh.2 hcell
    (fun i => atom_sound (a i) (ha i) hg hcell)

set_option pp.fullNames true
#print axioms gradient_expansion
#print axioms atom_sound
#print axioms exclude
end StructuralGoal20261016.WindowLiftedKKT
end
