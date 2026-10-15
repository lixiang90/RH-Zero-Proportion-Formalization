"""Generate predicate-polymorphic soundness for the imported frozen geometry.

No frozen definitions or certificates are copied or modified. The 36 small
split wrappers reuse the imported geometry operators and the generic PCell
cov_splitB theorem. Concrete new leaf soundness remains an explicit premise.
"""
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def main():
    text='''import GramDefect20261015.Core

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
'''
    pairs=[(i,i+1) for i in range(8)]+[(i,j) for i in range(7) for j in range(i+2,9)]
    names=[]
    for i,j in pairs:
        name=f'gsplit{i}' if j==i+1 else f'ssplit{i}{j}'
        names.append(name)
        text+=f'theorem {name}_ok : CovK P ({name} ih md pos) :=\n'
        text+=f'  fun s h => spH_ok hih {i} {j} (by decide) (by decide) (s := s) h\n'
    text+='end\n\n'
    term='zK_ok P'
    for name in reversed(names):term=f'brec_dep (fun _ => {term}) (fun _ => {name}_ok hih md pos)'
    text+='''theorem splitAx_ok {P : (ℕ → ℝ) → Prop} {ih : WF} (hih : WalkOK P ih)
    (md pos ax : ℕ) : CovK P (splitAx ih md pos ax) :=
  '''+term+''' 

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
'''
    out=ROOT/'StructuralResearch20261016/GenericCover.lean';out.write_text(text,encoding='utf-8')
    print(out)

if __name__=='__main__':main()
