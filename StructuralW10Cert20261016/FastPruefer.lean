/- SPDX-License-Identifier: Apache-2.0
Fast reconstruction of an arbitrary nonnegative dual certificate from a
labelled tree. The original executable leaf checker remains the sole judge
of every numerical certificate; this data interpreter adds no hypotheses.
-/
import StructuralW10Cert20261016.LeafDispatch

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
namespace StructuralW10Cert20261016.FastPruefer
open LocalChecker

def forceInt {α : Sort _} (z : ℤ) (k : ℤ → α) : α :=
  match z with
  | .ofNat n => k (.ofNat n)
  | .negSucc n => k (.negSucc n)

def forceInts {α : Sort _} : List ℤ → (List ℤ → α) → α
  | [], k => k []
  | z :: zs, k => forceInt z (fun z => forceInts zs (fun zs => k (z :: zs)))

def forceTerms {α : Sort _} : List Term → (List Term → α) → α
  | [], f => f []
  | (k,m,p,r) :: ts, f =>
    forceT k fun k => forceT m fun m => forceT p fun p => forceT r fun r =>
      forceTerms ts (fun ts => f ((k,m,p,r) :: ts))

theorem forceTerms_eq {α : Sort _} (ts : List Term) (f : List Term → α) :
    forceTerms ts f = f ts := by
  induction ts generalizing f with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨k,m,p,r⟩
    simp only [forceTerms, forceT_eq, ih]

def pointSlope (p : ℕ) : ℤ :=
  (lo32 (hi32 (tf AMW.Cert.PC9QB6MData.PT p)) : ℤ) - 2000000000

def termSlope (FS : List Term) (t : ℕ) : ℤ :=
  let k := tI FS t
  let m := tJ FS t
  let left := mw1 k m
  let right := mw2 k m
  (tA TS t : ℤ) *
    ((if left = 0 then 0 else (left : ℤ) * pointSlope (tA FS t)) +
     (if right = 0 then 0 else (right : ℤ) * pointSlope (tK FS t)))

def addSlope (i j : ℕ) (slope : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | r, x :: xs => (if i ≤ r ∧ r < j then x + slope else x) :: addSlope i j slope (r+1) xs

/-- One pass through the 39 terms reads each active point at most once. -/
def gapCoeffs (FS : List Term) : List ℤ :=
  (List.range 39).foldl (fun xs t =>
    forceInt (termSlope FS t) (fun slope => addSlope (tI TS t) (tJ TS t) slope 0 xs))
    (BS.map (fun b => 1024000000000 * (b : ℤ)))

def updateDiv (leaf parent : ℕ) (signed : ℤ) : ℕ → List ℤ → List ℤ
  | _, [] => []
  | r, x :: xs =>
    (if r = leaf then 0 else if r = parent then x + signed else x) ::
      updateDiv leaf parent signed (r+1) xs

def edgeMove (a b : ℕ) (signed : ℤ) : List DualMove :=
  let i := min a b
  let j := max a b
  if i + 1 < j then
    let y := signed.natAbs
    if y = 0 then [] else
      let k := i * (17 - i) / 2 + (j - i - 2)
      if (a < b ∧ 0 ≤ signed) ∨ (b < a ∧ signed < 0) then [(k, 0, y)]
      else [(k, y, 0)]
  else []

/-- Peeling a leaf transfers its entire divergence to its parent. -/
def peel : List ℕ → List ℕ → List ℤ → List DualMove
  | [], a :: b :: _, div => edgeMove a b (div.getD a 0)
  | [], _, _ => []
  | p :: ps, verts, div =>
    let leaf := (verts.find? (fun v => !(p :: ps).contains v)).getD 0
    forceInt (div.getD leaf 0) fun signed =>
      edgeMove leaf p signed ++
        peel ps (verts.erase leaf) (updateDiv leaf p signed 0 div)

def moves (FS : List Term) (code : ℕ) : List DualMove :=
  forceInts (gapCoeffs FS) fun coeffs =>
    let div := (List.range 10).map (fun v =>
      if v = 0 then -(coeffs.getD 0 0)
      else if v = 9 then coeffs.getD 8 0
      else coeffs.getD (v-1) 0 - coeffs.getD v 0)
    peel ((List.range 8).map (fun i => (code / (10 ^ i)) % 10)) (List.range 10) div

def checkTreeCode (c : Cl) (support treecode : ℕ) : Bool :=
  forceTerms (RelCompactLeaf.decodeTerms c support) fun FS => checkLeaf c FS (moves FS treecode)

theorem checkTreeCode_sound {c : Cl} {support treecode : ℕ}
    (h : checkTreeCode c support treecode = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := by
  simp only [checkTreeCode, forceTerms_eq] at h
  exact checkLeaf_sound h

def checkPacked (c : Cl) (word : ℕ) : Bool :=
  checkTreeCode c (word / 100000000) (word % 100000000)

theorem checkPacked_sound {c : Cl} {word : ℕ} (h : checkPacked c word = true) :
    CovBy 9 PR (Pg cN 9 BS TS) c := checkTreeCode_sound h

def dispatch (payload : ℕ → ℕ) (c : Cl) (id : ℕ) : Bool :=
  if id ≤ 45 then LeafDispatch.check payload c id
  else checkPacked c (payload (id-46))

theorem dispatch_sound (payload : ℕ → ℕ) (c : Cl) (id : ℕ)
    (h : dispatch payload c id = true) : CovBy 9 PR (Pg cN 9 BS TS) c := by
  unfold dispatch at h
  split_ifs at h
  · exact LeafDispatch.check_sound payload c id h
  · exact checkPacked_sound h

#print axioms checkTreeCode_sound
#print axioms dispatch_sound
end StructuralW10Cert20261016.FastPruefer
end
