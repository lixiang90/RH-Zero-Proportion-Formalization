import GramDefect20261015.Core

/- Generic coverage extension for the existing nine-point geometry.
   This module proves no new numerical energy floor. It imports all frozen
   state, closure, split, bit-reader, and tangent definitions unchanged.
   The geometric proof pattern is inherited from the attributed Core.lean.
   Every new local leaf checker must supply its own CovK premise. -/
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open AMW.Cert.PC9QB6M
namespace StructuralResearch20261016.GenericCover

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def CovK (P : (ℕ → ℝ) → Prop) (k : ST) : Prop :=
  ∀ s, U k s ≠ 0 → CovBy 8 PR P (toCl s)
def WalkOK (P : (ℕ → ℝ) → Prop) (f : WF) : Prop := ∀ pos, CovK P (f pos)

theorem zK_ok (P : (ℕ → ℝ) → Prop) : CovK P zK :=
  fun _ h => absurd rfl h

theorem ofCl_ok {P : (ℕ → ℝ) → Prop} {k : ST} (hk : CovK P k) {c : Cl} {m : ℕ}
    (h1 : c.L.length = 8) (h2 : c.U.length = 8)
    (h3 : c.A.length = 28) (h4 : c.B.length = 28)
    (h : U k (ofCl c m) ≠ 0) : CovBy 8 PR P c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h

theorem cuH_ok {P : (ℕ → ℝ) → Prop} {k : ST} (hk : CovK P k)
    (X Y : List ℕ) (s : St) (h : cuL k X Y s ≠ 0) :
    CovBy 8 PR P (cuB 8 PR (toCl s) X Y) :=
  ofCl_ok hk (by simp [cuB]) (by simp [cuB]) (by simp [cuB, PR])
    (by simp [cuB, PR]) (m := s.M) (by rw [← cuL_eq]; exact h)

theorem spH_ok {P : (ℕ → ℝ) → Prop} {ih : WF} (hih : WalkOK P ih)
    {pos : ℕ} (i j : ℕ) (hij : i < j) (hj : j ≤ 8) {s : St} {q : ℕ}
    (h : Bool.rec (motive := fun _ => ℕ)
      (cuL (ih (cuL (ih pos) (colB 8 SL (toCl s) i)
        (rowB 8 SL (toCl s) (Nat.add BB q) j) s))
        (colB 8 SL (toCl s) j) (rowB 8 SL (toCl s) (Nat.sub BB q) i) s) 0
      (Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i)
        (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0) ≠ 0) :
    CovBy 8 PR P (toCl s) := by
  have hc := cov_splitB (P := P) (c := toCl s) hSL hPR hij hj q
  cases hp : Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i)
      (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0
  · rw [hp] at h
    exact hc (cuH_ok (hih _) _ _ s fun h0 => by
      rw [h0] at hp; exact absurd hp (by decide)) (cuH_ok (hih _) _ _ s h)
  · rw [hp] at h; exact absurd rfl h

section
variable {P : (ℕ → ℝ) → Prop} {ih : WF} (hih : WalkOK P ih) (md pos : ℕ)
include hih
theorem gsplit0_ok : CovK P (gsplit0 ih md pos) :=
  fun s h => spH_ok hih 0 1 (by decide) (by decide) (s := s) h
theorem gsplit1_ok : CovK P (gsplit1 ih md pos) :=
  fun s h => spH_ok hih 1 2 (by decide) (by decide) (s := s) h
theorem gsplit2_ok : CovK P (gsplit2 ih md pos) :=
  fun s h => spH_ok hih 2 3 (by decide) (by decide) (s := s) h
theorem gsplit3_ok : CovK P (gsplit3 ih md pos) :=
  fun s h => spH_ok hih 3 4 (by decide) (by decide) (s := s) h
theorem gsplit4_ok : CovK P (gsplit4 ih md pos) :=
  fun s h => spH_ok hih 4 5 (by decide) (by decide) (s := s) h
theorem gsplit5_ok : CovK P (gsplit5 ih md pos) :=
  fun s h => spH_ok hih 5 6 (by decide) (by decide) (s := s) h
theorem gsplit6_ok : CovK P (gsplit6 ih md pos) :=
  fun s h => spH_ok hih 6 7 (by decide) (by decide) (s := s) h
theorem gsplit7_ok : CovK P (gsplit7 ih md pos) :=
  fun s h => spH_ok hih 7 8 (by decide) (by decide) (s := s) h
theorem ssplit02_ok : CovK P (ssplit02 ih md pos) :=
  fun s h => spH_ok hih 0 2 (by decide) (by decide) (s := s) h
theorem ssplit03_ok : CovK P (ssplit03 ih md pos) :=
  fun s h => spH_ok hih 0 3 (by decide) (by decide) (s := s) h
theorem ssplit04_ok : CovK P (ssplit04 ih md pos) :=
  fun s h => spH_ok hih 0 4 (by decide) (by decide) (s := s) h
theorem ssplit05_ok : CovK P (ssplit05 ih md pos) :=
  fun s h => spH_ok hih 0 5 (by decide) (by decide) (s := s) h
theorem ssplit06_ok : CovK P (ssplit06 ih md pos) :=
  fun s h => spH_ok hih 0 6 (by decide) (by decide) (s := s) h
theorem ssplit07_ok : CovK P (ssplit07 ih md pos) :=
  fun s h => spH_ok hih 0 7 (by decide) (by decide) (s := s) h
theorem ssplit08_ok : CovK P (ssplit08 ih md pos) :=
  fun s h => spH_ok hih 0 8 (by decide) (by decide) (s := s) h
theorem ssplit13_ok : CovK P (ssplit13 ih md pos) :=
  fun s h => spH_ok hih 1 3 (by decide) (by decide) (s := s) h
theorem ssplit14_ok : CovK P (ssplit14 ih md pos) :=
  fun s h => spH_ok hih 1 4 (by decide) (by decide) (s := s) h
theorem ssplit15_ok : CovK P (ssplit15 ih md pos) :=
  fun s h => spH_ok hih 1 5 (by decide) (by decide) (s := s) h
theorem ssplit16_ok : CovK P (ssplit16 ih md pos) :=
  fun s h => spH_ok hih 1 6 (by decide) (by decide) (s := s) h
theorem ssplit17_ok : CovK P (ssplit17 ih md pos) :=
  fun s h => spH_ok hih 1 7 (by decide) (by decide) (s := s) h
theorem ssplit18_ok : CovK P (ssplit18 ih md pos) :=
  fun s h => spH_ok hih 1 8 (by decide) (by decide) (s := s) h
theorem ssplit24_ok : CovK P (ssplit24 ih md pos) :=
  fun s h => spH_ok hih 2 4 (by decide) (by decide) (s := s) h
theorem ssplit25_ok : CovK P (ssplit25 ih md pos) :=
  fun s h => spH_ok hih 2 5 (by decide) (by decide) (s := s) h
theorem ssplit26_ok : CovK P (ssplit26 ih md pos) :=
  fun s h => spH_ok hih 2 6 (by decide) (by decide) (s := s) h
theorem ssplit27_ok : CovK P (ssplit27 ih md pos) :=
  fun s h => spH_ok hih 2 7 (by decide) (by decide) (s := s) h
theorem ssplit28_ok : CovK P (ssplit28 ih md pos) :=
  fun s h => spH_ok hih 2 8 (by decide) (by decide) (s := s) h
theorem ssplit35_ok : CovK P (ssplit35 ih md pos) :=
  fun s h => spH_ok hih 3 5 (by decide) (by decide) (s := s) h
theorem ssplit36_ok : CovK P (ssplit36 ih md pos) :=
  fun s h => spH_ok hih 3 6 (by decide) (by decide) (s := s) h
theorem ssplit37_ok : CovK P (ssplit37 ih md pos) :=
  fun s h => spH_ok hih 3 7 (by decide) (by decide) (s := s) h
theorem ssplit38_ok : CovK P (ssplit38 ih md pos) :=
  fun s h => spH_ok hih 3 8 (by decide) (by decide) (s := s) h
theorem ssplit46_ok : CovK P (ssplit46 ih md pos) :=
  fun s h => spH_ok hih 4 6 (by decide) (by decide) (s := s) h
theorem ssplit47_ok : CovK P (ssplit47 ih md pos) :=
  fun s h => spH_ok hih 4 7 (by decide) (by decide) (s := s) h
theorem ssplit48_ok : CovK P (ssplit48 ih md pos) :=
  fun s h => spH_ok hih 4 8 (by decide) (by decide) (s := s) h
theorem ssplit57_ok : CovK P (ssplit57 ih md pos) :=
  fun s h => spH_ok hih 5 7 (by decide) (by decide) (s := s) h
theorem ssplit58_ok : CovK P (ssplit58 ih md pos) :=
  fun s h => spH_ok hih 5 8 (by decide) (by decide) (s := s) h
theorem ssplit68_ok : CovK P (ssplit68 ih md pos) :=
  fun s h => spH_ok hih 6 8 (by decide) (by decide) (s := s) h
end

theorem splitAx_ok {P : (ℕ → ℝ) → Prop} {ih : WF} (hih : WalkOK P ih)
    (md pos ax : ℕ) : CovK P (splitAx ih md pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok P) (fun _ => ssplit68_ok hih md pos)) (fun _ => ssplit58_ok hih md pos)) (fun _ => ssplit57_ok hih md pos)) (fun _ => ssplit48_ok hih md pos)) (fun _ => ssplit47_ok hih md pos)) (fun _ => ssplit46_ok hih md pos)) (fun _ => ssplit38_ok hih md pos)) (fun _ => ssplit37_ok hih md pos)) (fun _ => ssplit36_ok hih md pos)) (fun _ => ssplit35_ok hih md pos)) (fun _ => ssplit28_ok hih md pos)) (fun _ => ssplit27_ok hih md pos)) (fun _ => ssplit26_ok hih md pos)) (fun _ => ssplit25_ok hih md pos)) (fun _ => ssplit24_ok hih md pos)) (fun _ => ssplit18_ok hih md pos)) (fun _ => ssplit17_ok hih md pos)) (fun _ => ssplit16_ok hih md pos)) (fun _ => ssplit15_ok hih md pos)) (fun _ => ssplit14_ok hih md pos)) (fun _ => ssplit13_ok hih md pos)) (fun _ => ssplit08_ok hih md pos)) (fun _ => ssplit07_ok hih md pos)) (fun _ => ssplit06_ok hih md pos)) (fun _ => ssplit05_ok hih md pos)) (fun _ => ssplit04_ok hih md pos)) (fun _ => ssplit03_ok hih md pos)) (fun _ => ssplit02_ok hih md pos)) (fun _ => gsplit7_ok hih md pos)) (fun _ => gsplit6_ok hih md pos)) (fun _ => gsplit5_ok hih md pos)) (fun _ => gsplit4_ok hih md pos)) (fun _ => gsplit3_ok hih md pos)) (fun _ => gsplit2_ok hih md pos)) (fun _ => gsplit1_ok hih md pos)) (fun _ => gsplit0_ok hih md pos) 

theorem tm_ok {P : (ℕ → ℝ) → Prop} {k : ST} (hk : CovK P k) : CovK P (tm k) :=
  fun s h g hg => by
    have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by
      simp only [U, tm, forceR_eq] at h
      exact h
    exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl)
      ((imap_length _ _ _).trans rfl) h' g (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2

/-- A leaf callback includes all numerical checks and pointer advancement.
    Its sole trusted interface is the separately proved `CovK` premise. -/
def node (bits : ℕ → ℕ) (leaf : ℕ → ST) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leaf pos)
    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) 7) 1) (Nat.add pos 8)
      (Nat.land (Nat.shiftRight (bits pos) 1) 63))
    (Nat.beq (Nat.land (bits pos) 1) 1)

def walkC (bits : ℕ → ℕ) (leaf : ℕ → ST) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK)
    (fun _ ih pos => node bits leaf ih pos) fuel
def walk (bits : ℕ → ℕ) (leaf : ℕ → ST) (fuel : ℕ) : WF :=
  fun pos => tm (walkC bits leaf fuel pos)

theorem node_ok {P : (ℕ → ℝ) → Prop} (bits : ℕ → ℕ) {leaf : ℕ → ST}
    (hleaf : ∀ pos, CovK P (leaf pos)) {ih : WF} (hih : WalkOK P ih) (pos : ℕ) :
    CovK P (node bits leaf ih pos) :=
  brec_dep (fun _ => hleaf pos) (fun _ => splitAx_ok hih _ _ _)

theorem walkC_ok {P : (ℕ → ℝ) → Prop} (bits : ℕ → ℕ) {leaf : ℕ → ST}
    (hleaf : ∀ pos, CovK P (leaf pos)) : ∀ fuel, WalkOK P (walkC bits leaf fuel)
  | 0 => fun _ => zK_ok P
  | n + 1 => fun pos => node_ok bits hleaf (walkC_ok bits hleaf n) pos

theorem walk_ok {P : (ℕ → ℝ) → Prop} (bits : ℕ → ℕ) {leaf : ℕ → ST}
    (hleaf : ∀ pos, CovK P (leaf pos)) (fuel : ℕ) : WalkOK P (walk bits leaf fuel) :=
  fun pos => tm_ok (walkC_ok bits hleaf fuel pos)

theorem covered_of_walk {P : (ℕ → ℝ) → Prop} (bits : ℕ → ℕ) {leaf : ℕ → ST}
    (hleaf : ∀ pos, CovK P (leaf pos)) (fuel pos e : ℕ) (s : St)
    (h : U (walk bits leaf fuel pos) s = e) (he : e ≠ 0) : CovBy 8 PR P (toCl s) :=
  walk_ok bits hleaf fuel pos s (h ▸ he)

/-- Reflection must carry both potential orientations unless the new energy
    itself has separately been proved reflection invariant. -/
def reverse (g : Fin 8 → ℝ) : Fin 8 → ℝ := fun i => g i.rev
def ReflectionClause (P : (Fin 8 → ℝ) → Prop) (g : Fin 8 → ℝ) : Prop :=
  (P g ∧ P (reverse g)) ∨ g 7 < g 0

theorem reverse_reverse (g : Fin 8 → ℝ) : reverse (reverse g) = g := by
  funext i
  simp [reverse]

theorem of_reflection_clause {A P : (Fin 8 → ℝ) → Prop}
    (hA : ∀ g, A g → A (reverse g))
    (h : ∀ g, A g → ReflectionClause P g) {g : Fin 8 → ℝ} (hg : A g) : P g := by
  rcases h g hg with hc | hbad
  · exact hc.1
  rcases h (reverse g) (hA g hg) with hr | hr
  · simpa only [reverse_reverse] using hr.2
  · have hh : g 0 < g 7 := by simpa [reverse] using hr
    linarith

end StructuralResearch20261016.GenericCover
#print axioms StructuralResearch20261016.GenericCover.covered_of_walk
#print axioms StructuralResearch20261016.GenericCover.of_reflection_clause
