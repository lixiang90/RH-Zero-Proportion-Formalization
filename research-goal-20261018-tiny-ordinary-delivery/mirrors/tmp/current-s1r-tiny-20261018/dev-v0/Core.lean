/-
SPDX-License-Identifier: Apache-2.0
PREPARATION ONLY, not compiled.
Versioned development split of frozen Tiny Core 9fbdf3f2...: the imported
CurrentPrefix is the already-proved actual current s1R prefix, including its
original attribution and modification notices. The new concrete PC9Tiny
namespace re-proves all strengthened TinyGoal walk/cut/leaf statements.
Only the existing LB/PT tables are aliases; no strengthened coverage is
imported from the old c9 Covered/CovK interface. The packed certificate
payloads/cursors and every numeric check are retained.

The inherited AMFinal/public candidate wrapper is archived separately. It
does not match this machine's trusted CandidateSpec and is not compiled.
No trusted constants are defined or changed here. Final deployment requires
the actual tiny rational and a newly trusted preparation/verification job.
All original third-party notices and full license texts are retained below
and in the imported prefix source; neither local proof counts nor this
split are a completed website submission.
-/
import StructuralS1RM20261018.CurrentPrefix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section
namespace AMW.Cert.PC9Tiny
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
-- Modified by the GP-4 session (rhajp): window s1R (cAMn, H, window tables, pvCheck at 128 cells and dependent literals), nine-point weights, floor, tangent table, cover and walks regenerated; κ and the literals above were the earlier file's.
noncomputable def cN : ℕ := 893616123055294719
noncomputable def tinyDeltaN : ℕ := 389500523
noncomputable def tinyTauN : ℕ := cN + 2 * tinyDeltaN
noncomputable def SIG : ℕ := 1562500000000000000000000000
noncomputable def PR : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (3, 5), (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (4, 8), (5, 7), (5, 8), (6, 8)]
theorem hPR : PRok 8 PR := by decide
noncomputable def BS : List ℕ := [28195867368000000, 50516979727000000, 69185101351000000, 80158024056000000, 80158024056000000, 69185101351000000, 50516979727000000, 28195867368000000]
noncomputable def TS : List Term := [(0, 1, 12145025938708000000, 0), (0, 3, 8651269219434000000, 1), (0, 4, 17776096184552000000, 2), (0, 5, 36889575523970000000, 3), (0, 6, 90239673332399000000, 4), (0, 7, 100000000000000000000, 5), (0, 8, 200000000000000000000, 6), (1, 2, 22223820732794000000, 0), (1, 3, 21042948716829000000, 7), (1, 4, 41416939206756000000, 8), (1, 5, 46995446251313000000, 9), (1, 6, 63110424476029000000, 10), (1, 7, 19520653335201000000, 11), (1, 8, 100000000000000000000, 12), (2, 3, 31202320231433000000, 0), (2, 4, 47970464688707000000, 13), (2, 5, 49931791573808000000, 14), (2, 6, 70456915128268000000, 15), (2, 7, 63110424476029000000, 16), (2, 8, 90239673332399000000, 17), (3, 4, 34428833097063000000, 0), (3, 5, 61973173188925000000, 18), (3, 6, 49931791573808000000, 19), (3, 7, 46995446251313000000, 20), (3, 8, 36889575523970000000, 21), (4, 5, 34428833097063000000, 0), (4, 6, 47970464688707000000, 22), (4, 7, 41416939206756000000, 23), (4, 8, 17776096184552000000, 24), (5, 6, 31202320231433000000, 0), (5, 7, 21042948716829000000, 25), (5, 8, 8651269219434000000, 26), (6, 7, 22223820732794000000, 0), (7, 8, 12145025938708000000, 0)]
theorem hTS : TSok 8 PR TS := by decide
noncomputable def SL : List ℕ := [0, 0, 8, 9, 10, 11, 12, 13, 14, 0, 0, 1, 15, 16, 17, 18, 19, 20, 0, 0, 0, 2, 21, 22, 23, 24, 25, 0, 0, 0, 0, 3, 26, 27, 28, 29, 0, 0, 0, 0, 0, 4, 30, 31, 32, 0, 0, 0, 0, 0, 0, 5, 33, 34, 0, 0, 0, 0, 0, 0, 0, 6, 35, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem hSL : SLok 8 PR SL := by decide
noncomputable def BND : List ℕ := [16384, 40384, 56768, 73728, 89920, 106240, 122304, 138496, 155136, 171456, 187776, 203904, 220224, 236480, 253120, 269440, 285696, 301888, 318464, 334912, 351744, 368320, 384896, 401280, 417728, 434048, 450496, 466816, 483264, 499584, 516032, 524288]
noncomputable def SA : ℕ := 100000000000000000000
noncomputable def G (g0 g1 g2 g3 g4 g5 g6 g7 : ℝ) : ℝ :=
  (28195867368000000 / (SA:ℝ)) * g0 + (50516979727000000 / (SA:ℝ)) * g1 + (69185101351000000 / (SA:ℝ)) * g2 + (80158024056000000 / (SA:ℝ)) * g3 + (80158024056000000 / (SA:ℝ)) * g4 + (69185101351000000 / (SA:ℝ)) * g5 + (50516979727000000 / (SA:ℝ)) * g6 + (28195867368000000 / (SA:ℝ)) * g7
    + (12145025938708000000 / (SA:ℝ)) * wfun (g0) + (0 / (SA:ℝ)) * wfun (g0 + g1) + (8651269219434000000 / (SA:ℝ)) * wfun (g0 + g1 + g2) + (17776096184552000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3) + (36889575523970000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4) + (90239673332399000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5) + (100000000000000000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6) + (200000000000000000000 / (SA:ℝ)) * wfun (g0 + g1 + g2 + g3 + g4 + g5 + g6 + g7) + (22223820732794000000 / (SA:ℝ)) * wfun (g1) + (21042948716829000000 / (SA:ℝ)) * wfun (g1 + g2) + (41416939206756000000 / (SA:ℝ)) * wfun (g1 + g2 + g3) + (46995446251313000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4) + (63110424476029000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5) + (19520653335201000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6) + (100000000000000000000 / (SA:ℝ)) * wfun (g1 + g2 + g3 + g4 + g5 + g6 + g7) + (31202320231433000000 / (SA:ℝ)) * wfun (g2) + (47970464688707000000 / (SA:ℝ)) * wfun (g2 + g3) + (49931791573808000000 / (SA:ℝ)) * wfun (g2 + g3 + g4) + (70456915128268000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5) + (63110424476029000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6) + (90239673332399000000 / (SA:ℝ)) * wfun (g2 + g3 + g4 + g5 + g6 + g7) + (34428833097063000000 / (SA:ℝ)) * wfun (g3) + (61973173188925000000 / (SA:ℝ)) * wfun (g3 + g4) + (49931791573808000000 / (SA:ℝ)) * wfun (g3 + g4 + g5) + (46995446251313000000 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6) + (36889575523970000000 / (SA:ℝ)) * wfun (g3 + g4 + g5 + g6 + g7) + (34428833097063000000 / (SA:ℝ)) * wfun (g4) + (47970464688707000000 / (SA:ℝ)) * wfun (g4 + g5) + (41416939206756000000 / (SA:ℝ)) * wfun (g4 + g5 + g6) + (17776096184552000000 / (SA:ℝ)) * wfun (g4 + g5 + g6 + g7) + (31202320231433000000 / (SA:ℝ)) * wfun (g5) + (21042948716829000000 / (SA:ℝ)) * wfun (g5 + g6) + (8651269219434000000 / (SA:ℝ)) * wfun (g5 + g6 + g7) + (22223820732794000000 / (SA:ℝ)) * wfun (g6) + (0 / (SA:ℝ)) * wfun (g6 + g7) + (12145025938708000000 / (SA:ℝ)) * wfun (g7)
theorem Fg_G (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : Fg 8 BS TS (fun r => [x0, x1, x2, x3, x4, x5, x6, x7].getD r 0) = (SA : ℝ) * G x0 x1 x2 x3 x4 x5 x6 x7 := by
  simp [Fg, BS, TS, tA, tI, tJ, gsum_range, G, SA, Finset.sum_range_succ]
  ring
structure St where
  (l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M : ℕ)
noncomputable def toCl (s : St) : Cl :=
  ⟨[s.l0, s.l1, s.l2, s.l3, s.l4, s.l5, s.l6, s.l7], [s.u0, s.u1, s.u2, s.u3, s.u4, s.u5, s.u6, s.u7],
   [s.A02, s.A03, s.A04, s.A05, s.A06, s.A07, s.A08, s.A13, s.A14, s.A15, s.A16, s.A17, s.A18, s.A24, s.A25, s.A26, s.A27, s.A28, s.A35, s.A36, s.A37, s.A38, s.A46, s.A47, s.A48, s.A57, s.A58, s.A68], [s.B02, s.B03, s.B04, s.B05, s.B06, s.B07, s.B08, s.B13, s.B14, s.B15, s.B16, s.B17, s.B18, s.B24, s.B25, s.B26, s.B27, s.B28, s.B35, s.B36, s.B37, s.B38, s.B46, s.B47, s.B48, s.B57, s.B58, s.B68]⟩
noncomputable def ofCl (c : Cl) (m : ℕ) : St :=
  ⟨c.L.getD 0 0, c.U.getD 0 0, c.L.getD 1 0, c.U.getD 1 0, c.L.getD 2 0, c.U.getD 2 0, c.L.getD 3 0, c.U.getD 3 0, c.L.getD 4 0, c.U.getD 4 0, c.L.getD 5 0, c.U.getD 5 0, c.L.getD 6 0, c.U.getD 6 0, c.L.getD 7 0, c.U.getD 7 0, c.A.getD 0 0, c.B.getD 0 0, c.A.getD 1 0, c.B.getD 1 0, c.A.getD 2 0, c.B.getD 2 0, c.A.getD 3 0, c.B.getD 3 0, c.A.getD 4 0, c.B.getD 4 0, c.A.getD 5 0, c.B.getD 5 0, c.A.getD 6 0, c.B.getD 6 0, c.A.getD 7 0, c.B.getD 7 0, c.A.getD 8 0, c.B.getD 8 0, c.A.getD 9 0, c.B.getD 9 0, c.A.getD 10 0, c.B.getD 10 0, c.A.getD 11 0, c.B.getD 11 0, c.A.getD 12 0, c.B.getD 12 0, c.A.getD 13 0, c.B.getD 13 0, c.A.getD 14 0, c.B.getD 14 0, c.A.getD 15 0, c.B.getD 15 0, c.A.getD 16 0, c.B.getD 16 0, c.A.getD 17 0, c.B.getD 17 0, c.A.getD 18 0, c.B.getD 18 0, c.A.getD 19 0, c.B.getD 19 0, c.A.getD 20 0, c.B.getD 20 0, c.A.getD 21 0, c.B.getD 21 0, c.A.getD 22 0, c.B.getD 22 0, c.A.getD 23 0, c.B.getD 23 0, c.A.getD 24 0, c.B.getD 24 0, c.A.getD 25 0, c.B.getD 25 0, c.A.getD 26 0, c.B.getD 26 0, c.A.getD 27 0, c.B.getD 27 0, m⟩
theorem toCl_ofCl (c : Cl) (m : ℕ) (h1 : c.L.length = 8) (h2 : c.U.length = 8) (h3 : c.A.length = 28) (h4 : c.B.length = 28) :
    toCl (ofCl c m) = c := by
  obtain ⟨L, U, A, B⟩ := c
  show Cl.mk _ _ _ _ = _
  congr 1
  exacts [list_of_getD L _ h1, list_of_getD U _ h2, list_of_getD A _ h3, list_of_getD B _ h4]
noncomputable def tinyExceptionState : St := ⟨64168, 65648, 33989, 34980, 64287, 65278, 34192, 35097, 64031, 65033, 65043, 66904, 33724, 34464, 64461, 67523, 98157, 100628, 162444, 165906, 196636, 200776, 260667, 264807, 326501, 331243, 360965, 364967, 425426, 429428, 98276, 100258, 132468, 135128, 196499, 199159, 261542, 265595, 295317, 299319, 359778, 363780, 98479, 100148, 162510, 164179, 227553, 230615, 261277, 264339, 325738, 328800, 98223, 99892, 163266, 166328, 196990, 200052, 261451, 264513, 129074, 131937, 162798, 165860, 227259, 230321, 98767, 101368, 163228, 166290, 98185, 101247, 0⟩
noncomputable def tinyExceptionCell : Cl := toCl tinyExceptionState
noncomputable def stEq (a b : St) : Bool := Nat.beq a.l0 b.l0 && Nat.beq a.u0 b.u0 && Nat.beq a.l1 b.l1 && Nat.beq a.u1 b.u1 && Nat.beq a.l2 b.l2 && Nat.beq a.u2 b.u2 && Nat.beq a.l3 b.l3 && Nat.beq a.u3 b.u3 && Nat.beq a.l4 b.l4 && Nat.beq a.u4 b.u4 && Nat.beq a.l5 b.l5 && Nat.beq a.u5 b.u5 && Nat.beq a.l6 b.l6 && Nat.beq a.u6 b.u6 && Nat.beq a.l7 b.l7 && Nat.beq a.u7 b.u7 && Nat.beq a.A02 b.A02 && Nat.beq a.B02 b.B02 && Nat.beq a.A03 b.A03 && Nat.beq a.B03 b.B03 && Nat.beq a.A04 b.A04 && Nat.beq a.B04 b.B04 && Nat.beq a.A05 b.A05 && Nat.beq a.B05 b.B05 && Nat.beq a.A06 b.A06 && Nat.beq a.B06 b.B06 && Nat.beq a.A07 b.A07 && Nat.beq a.B07 b.B07 && Nat.beq a.A08 b.A08 && Nat.beq a.B08 b.B08 && Nat.beq a.A13 b.A13 && Nat.beq a.B13 b.B13 && Nat.beq a.A14 b.A14 && Nat.beq a.B14 b.B14 && Nat.beq a.A15 b.A15 && Nat.beq a.B15 b.B15 && Nat.beq a.A16 b.A16 && Nat.beq a.B16 b.B16 && Nat.beq a.A17 b.A17 && Nat.beq a.B17 b.B17 && Nat.beq a.A18 b.A18 && Nat.beq a.B18 b.B18 && Nat.beq a.A24 b.A24 && Nat.beq a.B24 b.B24 && Nat.beq a.A25 b.A25 && Nat.beq a.B25 b.B25 && Nat.beq a.A26 b.A26 && Nat.beq a.B26 b.B26 && Nat.beq a.A27 b.A27 && Nat.beq a.B27 b.B27 && Nat.beq a.A28 b.A28 && Nat.beq a.B28 b.B28 && Nat.beq a.A35 b.A35 && Nat.beq a.B35 b.B35 && Nat.beq a.A36 b.A36 && Nat.beq a.B36 b.B36 && Nat.beq a.A37 b.A37 && Nat.beq a.B37 b.B37 && Nat.beq a.A38 b.A38 && Nat.beq a.B38 b.B38 && Nat.beq a.A46 b.A46 && Nat.beq a.B46 b.B46 && Nat.beq a.A47 b.A47 && Nat.beq a.B47 b.B47 && Nat.beq a.A48 b.A48 && Nat.beq a.B48 b.B48 && Nat.beq a.A57 b.A57 && Nat.beq a.B57 b.B57 && Nat.beq a.A58 b.A58 && Nat.beq a.B58 b.B58 && Nat.beq a.A68 b.A68 && Nat.beq a.B68 b.B68 && Nat.beq a.M b.M
theorem St_eq {a b : St} (h : stEq a b = true) : a = b := by
  cases a; cases b
  simp only [stEq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩, h25⟩, h26⟩, h27⟩, h28⟩, h29⟩, h30⟩, h31⟩, h32⟩, h33⟩, h34⟩, h35⟩, h36⟩, h37⟩, h38⟩, h39⟩, h40⟩, h41⟩, h42⟩, h43⟩, h44⟩, h45⟩, h46⟩, h47⟩, h48⟩, h49⟩, h50⟩, h51⟩, h52⟩, h53⟩, h54⟩, h55⟩, h56⟩, h57⟩, h58⟩, h59⟩, h60⟩, h61⟩, h62⟩, h63⟩, h64⟩, h65⟩, h66⟩, h67⟩, h68⟩, h69⟩, h70⟩, h71⟩, h72⟩ := h
  subst_vars; rfl
noncomputable def tinyTarget (s : St) : ℕ :=
  if stEq s tinyExceptionState = true then cN else tinyTauN
noncomputable def TinyGoal (g : ℕ → ℝ) : Prop :=
  Pg tinyTauN 8 BS TS g ∨ (InCell 8 PR tinyExceptionCell g ∧ Pg cN 8 BS TS g)
abbrev Covered : Cl → Prop := CovBy 8 PR TinyGoal
theorem tiny_forget {g : ℕ → ℝ} (h : TinyGoal g) : Pg cN 8 BS TS g := by
  rcases h with h | h
  · rcases h with h | h
    · left
      exact le_trans (by norm_num [cN, tinyTauN, tinyDeltaN]) h
    · exact Or.inr h
  · exact h.2
theorem tiny_target_sound {s : St} {g : ℕ → ℝ}
    (hg : InCell 8 PR (toCl s) g) (h : Pg (tinyTarget s) 8 BS TS g) : TinyGoal g := by
  by_cases hs : stEq s tinyExceptionState = true
  · have heq : s = tinyExceptionState := St_eq hs
    right
    refine ⟨?_, ?_⟩
    · simpa only [tinyExceptionCell, heq] using hg
    · simpa [tinyTarget, hs] using h
  · left
    simpa [tinyTarget, hs] using h
abbrev ST : Type := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
noncomputable def U (k : ST) (s : St) : ℕ := k s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.l7 s.u7 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A08 s.B08 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A18 s.B18 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A28 s.B28 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A38 s.B38 s.A46 s.B46 s.A47 s.B47 s.A48 s.B48 s.A57 s.B57 s.A58 s.B58 s.A68 s.B68 s.M
noncomputable def CovK (k : ST) : Prop := ∀ s, U k s ≠ 0 → Covered (toCl s)
abbrev WF : Type := ℕ → ST
noncomputable def WalkOK (f : WF) : Prop := ∀ pos, CovK (f pos)
noncomputable def zK : ST := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
theorem zK_ok : CovK zK := fun _ h => absurd rfl h
theorem ofCl_ok {k : ST} (hk : CovK k) {c : Cl} {m : ℕ} (h1 : c.L.length = 8) (h2 : c.U.length = 8) (h3 : c.A.length = 28)
    (h4 : c.B.length = 28) (h : U k (ofCl c m) ≠ 0) : Covered c :=
  toCl_ofCl c m h1 h2 h3 h4 ▸ hk _ h
noncomputable def cuH (k : ST) (x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  k (nmax a (Nat.sub 8796093022208 (Nat.add x1 y0)))
    (nmin b (Nat.sub (Nat.add x0 y1) 8796093022208))
    (nmax c (Nat.sub 8796093022208 (Nat.add x2 y1)))
    (nmin d (Nat.sub (Nat.add x1 y2) 8796093022208))
    (nmax e (Nat.sub 8796093022208 (Nat.add x3 y2)))
    (nmin f (Nat.sub (Nat.add x2 y3) 8796093022208))
    (nmax g (Nat.sub 8796093022208 (Nat.add x4 y3)))
    (nmin h (Nat.sub (Nat.add x3 y4) 8796093022208))
    (nmax i (Nat.sub 8796093022208 (Nat.add x5 y4)))
    (nmin j (Nat.sub (Nat.add x4 y5) 8796093022208))
    (nmax l (Nat.sub 8796093022208 (Nat.add x6 y5)))
    (nmin m (Nat.sub (Nat.add x5 y6) 8796093022208))
    (nmax n (Nat.sub 8796093022208 (Nat.add x7 y6)))
    (nmin o (Nat.sub (Nat.add x6 y7) 8796093022208))
    (nmax r (Nat.sub 8796093022208 (Nat.add x8 y7)))
    (nmin s (Nat.sub (Nat.add x7 y8) 8796093022208))
    (nmax t (Nat.sub 8796093022208 (Nat.add x2 y0)))
    (nmin u (Nat.sub (Nat.add x0 y2) 8796093022208))
    (nmax v (Nat.sub 8796093022208 (Nat.add x3 y0)))
    (nmin w (Nat.sub (Nat.add x0 y3) 8796093022208))
    (nmax x (Nat.sub 8796093022208 (Nat.add x4 y0)))
    (nmin y (Nat.sub (Nat.add x0 y4) 8796093022208))
    (nmax z (Nat.sub 8796093022208 (Nat.add x5 y0)))
    (nmin A (Nat.sub (Nat.add x0 y5) 8796093022208))
    (nmax B (Nat.sub 8796093022208 (Nat.add x6 y0)))
    (nmin C (Nat.sub (Nat.add x0 y6) 8796093022208))
    (nmax D (Nat.sub 8796093022208 (Nat.add x7 y0)))
    (nmin E (Nat.sub (Nat.add x0 y7) 8796093022208))
    (nmax F (Nat.sub 8796093022208 (Nat.add x8 y0)))
    (nmin G (Nat.sub (Nat.add x0 y8) 8796093022208))
    (nmax H (Nat.sub 8796093022208 (Nat.add x3 y1)))
    (nmin I (Nat.sub (Nat.add x1 y3) 8796093022208))
    (nmax J (Nat.sub 8796093022208 (Nat.add x4 y1)))
    (nmin K (Nat.sub (Nat.add x1 y4) 8796093022208))
    (nmax L (Nat.sub 8796093022208 (Nat.add x5 y1)))
    (nmin M (Nat.sub (Nat.add x1 y5) 8796093022208))
    (nmax N (Nat.sub 8796093022208 (Nat.add x6 y1)))
    (nmin O (Nat.sub (Nat.add x1 y6) 8796093022208))
    (nmax P (Nat.sub 8796093022208 (Nat.add x7 y1)))
    (nmin Q (Nat.sub (Nat.add x1 y7) 8796093022208))
    (nmax R (Nat.sub 8796093022208 (Nat.add x8 y1)))
    (nmin S (Nat.sub (Nat.add x1 y8) 8796093022208))
    (nmax T (Nat.sub 8796093022208 (Nat.add x4 y2)))
    (nmin U (Nat.sub (Nat.add x2 y4) 8796093022208))
    (nmax V (Nat.sub 8796093022208 (Nat.add x5 y2)))
    (nmin W (Nat.sub (Nat.add x2 y5) 8796093022208))
    (nmax X (Nat.sub 8796093022208 (Nat.add x6 y2)))
    (nmin Y (Nat.sub (Nat.add x2 y6) 8796093022208))
    (nmax Z (Nat.sub 8796093022208 (Nat.add x7 y2)))
    (nmin aa (Nat.sub (Nat.add x2 y7) 8796093022208))
    (nmax ab (Nat.sub 8796093022208 (Nat.add x8 y2)))
    (nmin ac (Nat.sub (Nat.add x2 y8) 8796093022208))
    (nmax ad (Nat.sub 8796093022208 (Nat.add x5 y3)))
    (nmin ae (Nat.sub (Nat.add x3 y5) 8796093022208))
    (nmax af (Nat.sub 8796093022208 (Nat.add x6 y3)))
    (nmin ag (Nat.sub (Nat.add x3 y6) 8796093022208))
    (nmax ah (Nat.sub 8796093022208 (Nat.add x7 y3)))
    (nmin ai (Nat.sub (Nat.add x3 y7) 8796093022208))
    (nmax aj (Nat.sub 8796093022208 (Nat.add x8 y3)))
    (nmin al (Nat.sub (Nat.add x3 y8) 8796093022208))
    (nmax am (Nat.sub 8796093022208 (Nat.add x6 y4)))
    (nmin an (Nat.sub (Nat.add x4 y6) 8796093022208))
    (nmax ao (Nat.sub 8796093022208 (Nat.add x7 y4)))
    (nmin ar (Nat.sub (Nat.add x4 y7) 8796093022208))
    (nmax au (Nat.sub 8796093022208 (Nat.add x8 y4)))
    (nmin av (Nat.sub (Nat.add x4 y8) 8796093022208))
    (nmax aw (Nat.sub 8796093022208 (Nat.add x7 y5)))
    (nmin ax (Nat.sub (Nat.add x5 y7) 8796093022208))
    (nmax ay (Nat.sub 8796093022208 (Nat.add x8 y5)))
    (nmin az (Nat.sub (Nat.add x5 y8) 8796093022208))
    (nmax ba (Nat.sub 8796093022208 (Nat.add x8 y6)))
    (nmin bb (Nat.sub (Nat.add x6 y8) 8796093022208))
    bc
noncomputable def cuL (k : ST) (X Y : List ℕ) (s : St) : ℕ :=
  cuH k (X.getD 0 0) (X.getD 1 0) (X.getD 2 0) (X.getD 3 0) (X.getD 4 0) (X.getD 5 0) (X.getD 6 0) (X.getD 7 0) (X.getD 8 0) (Y.getD 0 0) (Y.getD 1 0) (Y.getD 2 0) (Y.getD 3 0) (Y.getD 4 0) (Y.getD 5 0) (Y.getD 6 0) (Y.getD 7 0) (Y.getD 8 0)
    s.l0 s.u0 s.l1 s.u1 s.l2 s.u2 s.l3 s.u3 s.l4 s.u4 s.l5 s.u5 s.l6 s.u6 s.l7 s.u7 s.A02 s.B02 s.A03 s.B03 s.A04 s.B04 s.A05 s.B05 s.A06 s.B06 s.A07 s.B07 s.A08 s.B08 s.A13 s.B13 s.A14 s.B14 s.A15 s.B15 s.A16 s.B16 s.A17 s.B17 s.A18 s.B18 s.A24 s.B24 s.A25 s.B25 s.A26 s.B26 s.A27 s.B27 s.A28 s.B28 s.A35 s.B35 s.A36 s.B36 s.A37 s.B37 s.A38 s.B38 s.A46 s.B46 s.A47 s.B47 s.A48 s.B48 s.A57 s.B57 s.A58 s.B58 s.A68 s.B68 s.M
theorem cuL_eq (k : ST) (X Y : List ℕ) (s : St) : cuL k X Y s = U k (ofCl (cuB 8 PR (toCl s) X Y) s.M) := by
  simp only [cuL, U, ofCl, cuB, toCl, PR, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero, pI, pJ]
  rfl
theorem cuH_ok {k : ST} (hk : CovK k) (X Y : List ℕ) (s : St) (h : cuL k X Y s ≠ 0) :
    Covered (cuB 8 PR (toCl s) X Y) :=
  ofCl_ok hk (by simp [cuB]) (by simp [cuB]) (by simp [cuB, PR]) (by simp [cuB, PR]) (m := s.M) (by rw [← cuL_eq]; exact h)
theorem spH_ok {ih : WF} (hih : WalkOK ih) {pos : ℕ} (i j : ℕ) (hij : i < j) (hj : j ≤ 8) {s : St} {q : ℕ}
    (h : Bool.rec (motive := fun _ => ℕ)
      (cuL (ih (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s)) (colB 8 SL (toCl s) j) (rowB 8 SL (toCl s) (Nat.sub BB q) i) s) 0
      (Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0) ≠ 0) : Covered (toCl s) := by
  have hc := cov_splitB (P := TinyGoal) (c := toCl s) hSL hPR hij hj q
  cases hp : Nat.beq (cuL (ih pos) (colB 8 SL (toCl s) i) (rowB 8 SL (toCl s) (Nat.add BB q) j) s) 0
  · rw [hp] at h
    exact hc (cuH_ok (hih _) _ _ s fun h0 => by rw [h0] at hp; exact absurd hp (by decide)) (cuH_ok (hih _) _ _ s h)
  · rw [hp] at h; exact absurd rfl h
noncomputable def colK0 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk qb (Nat.sub qb a) (Nat.sub qb t) (Nat.sub qb v) (Nat.sub qb x) (Nat.sub qb z) (Nat.sub qb B) (Nat.sub qb D) (Nat.sub qb F)
noncomputable def colK1 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb b) qb (Nat.sub qb c) (Nat.sub qb H) (Nat.sub qb J) (Nat.sub qb L) (Nat.sub qb N) (Nat.sub qb P) (Nat.sub qb R)
noncomputable def colK2 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb u) (Nat.add qb d) qb (Nat.sub qb e) (Nat.sub qb T) (Nat.sub qb V) (Nat.sub qb X) (Nat.sub qb Z) (Nat.sub qb ab)
noncomputable def colK3 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb w) (Nat.add qb I) (Nat.add qb f) qb (Nat.sub qb g) (Nat.sub qb ad) (Nat.sub qb af) (Nat.sub qb ah) (Nat.sub qb aj)
noncomputable def colK4 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb y) (Nat.add qb K) (Nat.add qb U) (Nat.add qb h) qb (Nat.sub qb i) (Nat.sub qb am) (Nat.sub qb ao) (Nat.sub qb au)
noncomputable def colK5 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb A) (Nat.add qb M) (Nat.add qb W) (Nat.add qb ae) (Nat.add qb j) qb (Nat.sub qb l) (Nat.sub qb aw) (Nat.sub qb ay)
noncomputable def colK6 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb C) (Nat.add qb O) (Nat.add qb Y) (Nat.add qb ag) (Nat.add qb an) (Nat.add qb m) qb (Nat.sub qb n) (Nat.sub qb ba)
noncomputable def colK7 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb E) (Nat.add qb Q) (Nat.add qb aa) (Nat.add qb ai) (Nat.add qb ar) (Nat.add qb ax) (Nat.add qb o) qb (Nat.sub qb r)
noncomputable def colK8 (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  let qb := 4398046511104; kk (Nat.add qb G) (Nat.add qb S) (Nat.add qb ac) (Nat.add qb al) (Nat.add qb av) (Nat.add qb az) (Nat.add qb bb) (Nat.add qb s) qb
noncomputable def rowK0 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk ee (Nat.add ee b) (Nat.add ee u) (Nat.add ee w) (Nat.add ee y) (Nat.add ee A) (Nat.add ee C) (Nat.add ee E) (Nat.add ee G)
noncomputable def rowK1 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee a) ee (Nat.add ee d) (Nat.add ee I) (Nat.add ee K) (Nat.add ee M) (Nat.add ee O) (Nat.add ee Q) (Nat.add ee S)
noncomputable def rowK2 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee t) (Nat.sub ee c) ee (Nat.add ee f) (Nat.add ee U) (Nat.add ee W) (Nat.add ee Y) (Nat.add ee aa) (Nat.add ee ac)
noncomputable def rowK3 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee v) (Nat.sub ee H) (Nat.sub ee e) ee (Nat.add ee h) (Nat.add ee ae) (Nat.add ee ag) (Nat.add ee ai) (Nat.add ee al)
noncomputable def rowK4 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee x) (Nat.sub ee J) (Nat.sub ee T) (Nat.sub ee g) ee (Nat.add ee j) (Nat.add ee an) (Nat.add ee ar) (Nat.add ee av)
noncomputable def rowK5 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee z) (Nat.sub ee L) (Nat.sub ee V) (Nat.sub ee ad) (Nat.sub ee i) ee (Nat.add ee m) (Nat.add ee ax) (Nat.add ee az)
noncomputable def rowK6 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee B) (Nat.sub ee N) (Nat.sub ee X) (Nat.sub ee af) (Nat.sub ee am) (Nat.sub ee l) ee (Nat.add ee o) (Nat.add ee bb)
noncomputable def rowK7 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee D) (Nat.sub ee P) (Nat.sub ee Z) (Nat.sub ee ah) (Nat.sub ee ao) (Nat.sub ee aw) (Nat.sub ee n) ee (Nat.add ee s)
noncomputable def rowK8 (ee : ℕ) (kk : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  kk (Nat.sub ee F) (Nat.sub ee R) (Nat.sub ee ab) (Nat.sub ee aj) (Nat.sub ee au) (Nat.sub ee ay) (Nat.sub ee ba) (Nat.sub ee r) ee
noncomputable def splG (ih : WF) (pos : ℕ) (qs : ST) (cA : (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST) (rA : ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST) (cB : (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST)
    (rB : ℕ → (ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ) → ST) : ST := fun a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc =>
  let q := qs a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc; let qe := Nat.add 4398046511104 q; let qf := Nat.sub 4398046511104 q;
  let pp := cA (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => rA qe (fun y0 y1 y2 y3 y4 y5 y6 y7 y8 => cuH (ih pos) x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc
  Bool.rec (motive := fun _ => ℕ) (cB (fun x0 x1 x2 x3 x4 x5 x6 x7 x8 => rB qf (fun y0 y1 y2 y3 y4 y5 y6 y7 y8 => cuH (ih pp) x0 x1 x2 x3 x4 x5 x6 x7 x8 y0 y1 y2 y3 y4 y5 y6 y7 y8 a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc) 0 (Nat.beq pp 0)
noncomputable def qs_gsplit0 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add a b) 1) (bcutL BND 64 a b) (Nat.beq md 1)
noncomputable def gsplit0 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit0 md) colK0 rowK1 colK1 rowK0
noncomputable def qs_gsplit1 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add c d) 1) (bcutL BND 64 c d) (Nat.beq md 1)
noncomputable def gsplit1 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit1 md) colK1 rowK2 colK2 rowK1
noncomputable def qs_gsplit2 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add e f) 1) (bcutL BND 64 e f) (Nat.beq md 1)
noncomputable def gsplit2 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit2 md) colK2 rowK3 colK3 rowK2
noncomputable def qs_gsplit3 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add g h) 1) (bcutL BND 64 g h) (Nat.beq md 1)
noncomputable def gsplit3 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit3 md) colK3 rowK4 colK4 rowK3
noncomputable def qs_gsplit4 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add i j) 1) (bcutL BND 64 i j) (Nat.beq md 1)
noncomputable def gsplit4 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit4 md) colK4 rowK5 colK5 rowK4
noncomputable def qs_gsplit5 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add l m) 1) (bcutL BND 64 l m) (Nat.beq md 1)
noncomputable def gsplit5 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit5 md) colK5 rowK6 colK6 rowK5
noncomputable def qs_gsplit6 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add n o) 1) (bcutL BND 64 n o) (Nat.beq md 1)
noncomputable def gsplit6 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit6 md) colK6 rowK7 colK7 rowK6
noncomputable def qs_gsplit7 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add r s) 1) (bcutL BND 64 r s) (Nat.beq md 1)
noncomputable def gsplit7 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_gsplit7 md) colK7 rowK8 colK8 rowK7
noncomputable def qs_ssplit02 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add t u) 1) (bcutL BND 64 t u) (Nat.beq md 1)
noncomputable def ssplit02 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit02 md) colK0 rowK2 colK2 rowK0
noncomputable def qs_ssplit03 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add v w) 1) (bcutL BND 64 v w) (Nat.beq md 1)
noncomputable def ssplit03 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit03 md) colK0 rowK3 colK3 rowK0
noncomputable def qs_ssplit04 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add x y) 1) (bcutL BND 64 x y) (Nat.beq md 1)
noncomputable def ssplit04 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit04 md) colK0 rowK4 colK4 rowK0
noncomputable def qs_ssplit05 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add z A) 1) (bcutL BND 64 z A) (Nat.beq md 1)
noncomputable def ssplit05 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit05 md) colK0 rowK5 colK5 rowK0
noncomputable def qs_ssplit06 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add B C) 1) (bcutL BND 64 B C) (Nat.beq md 1)
noncomputable def ssplit06 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit06 md) colK0 rowK6 colK6 rowK0
noncomputable def qs_ssplit07 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add D E) 1) (bcutL BND 64 D E) (Nat.beq md 1)
noncomputable def ssplit07 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit07 md) colK0 rowK7 colK7 rowK0
noncomputable def qs_ssplit08 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add F G) 1) (bcutL BND 64 F G) (Nat.beq md 1)
noncomputable def ssplit08 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit08 md) colK0 rowK8 colK8 rowK0
noncomputable def qs_ssplit13 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add H I) 1) (bcutL BND 64 H I) (Nat.beq md 1)
noncomputable def ssplit13 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit13 md) colK1 rowK3 colK3 rowK1
noncomputable def qs_ssplit14 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add J K) 1) (bcutL BND 64 J K) (Nat.beq md 1)
noncomputable def ssplit14 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit14 md) colK1 rowK4 colK4 rowK1
noncomputable def qs_ssplit15 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add L M) 1) (bcutL BND 64 L M) (Nat.beq md 1)
noncomputable def ssplit15 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit15 md) colK1 rowK5 colK5 rowK1
noncomputable def qs_ssplit16 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add N O) 1) (bcutL BND 64 N O) (Nat.beq md 1)
noncomputable def ssplit16 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit16 md) colK1 rowK6 colK6 rowK1
noncomputable def qs_ssplit17 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add P Q) 1) (bcutL BND 64 P Q) (Nat.beq md 1)
noncomputable def ssplit17 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit17 md) colK1 rowK7 colK7 rowK1
noncomputable def qs_ssplit18 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add R S) 1) (bcutL BND 64 R S) (Nat.beq md 1)
noncomputable def ssplit18 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit18 md) colK1 rowK8 colK8 rowK1
noncomputable def qs_ssplit24 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add T U) 1) (bcutL BND 64 T U) (Nat.beq md 1)
noncomputable def ssplit24 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit24 md) colK2 rowK4 colK4 rowK2
noncomputable def qs_ssplit25 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add V W) 1) (bcutL BND 64 V W) (Nat.beq md 1)
noncomputable def ssplit25 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit25 md) colK2 rowK5 colK5 rowK2
noncomputable def qs_ssplit26 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add X Y) 1) (bcutL BND 64 X Y) (Nat.beq md 1)
noncomputable def ssplit26 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit26 md) colK2 rowK6 colK6 rowK2
noncomputable def qs_ssplit27 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add Z aa) 1) (bcutL BND 64 Z aa) (Nat.beq md 1)
noncomputable def ssplit27 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit27 md) colK2 rowK7 colK7 rowK2
noncomputable def qs_ssplit28 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ab ac) 1) (bcutL BND 64 ab ac) (Nat.beq md 1)
noncomputable def ssplit28 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit28 md) colK2 rowK8 colK8 rowK2
noncomputable def qs_ssplit35 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ad ae) 1) (bcutL BND 64 ad ae) (Nat.beq md 1)
noncomputable def ssplit35 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit35 md) colK3 rowK5 colK5 rowK3
noncomputable def qs_ssplit36 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add af ag) 1) (bcutL BND 64 af ag) (Nat.beq md 1)
noncomputable def ssplit36 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit36 md) colK3 rowK6 colK6 rowK3
noncomputable def qs_ssplit37 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ah ai) 1) (bcutL BND 64 ah ai) (Nat.beq md 1)
noncomputable def ssplit37 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit37 md) colK3 rowK7 colK7 rowK3
noncomputable def qs_ssplit38 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add aj al) 1) (bcutL BND 64 aj al) (Nat.beq md 1)
noncomputable def ssplit38 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit38 md) colK3 rowK8 colK8 rowK3
noncomputable def qs_ssplit46 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add am an) 1) (bcutL BND 64 am an) (Nat.beq md 1)
noncomputable def ssplit46 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit46 md) colK4 rowK6 colK6 rowK4
noncomputable def qs_ssplit47 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ao ar) 1) (bcutL BND 64 ao ar) (Nat.beq md 1)
noncomputable def ssplit47 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit47 md) colK4 rowK7 colK7 rowK4
noncomputable def qs_ssplit48 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add au av) 1) (bcutL BND 64 au av) (Nat.beq md 1)
noncomputable def ssplit48 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit48 md) colK4 rowK8 colK8 rowK4
noncomputable def qs_ssplit57 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add aw ax) 1) (bcutL BND 64 aw ax) (Nat.beq md 1)
noncomputable def ssplit57 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit57 md) colK5 rowK7 colK7 rowK5
noncomputable def qs_ssplit58 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ay az) 1) (bcutL BND 64 ay az) (Nat.beq md 1)
noncomputable def ssplit58 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit58 md) colK5 rowK8 colK8 rowK5
noncomputable def qs_ssplit68 (md a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ := Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight (Nat.add ba bb) 1) (bcutL BND 64 ba bb) (Nat.beq md 1)
noncomputable def ssplit68 (ih : WF) (md pos : ℕ) : ST := splG ih pos (qs_ssplit68 md) colK6 rowK8 colK8 rowK6
section
variable {ih : WF} (hih : WalkOK ih) (md pos : ℕ)
include hih
theorem gsplit0_ok : CovK (gsplit0 ih md pos) := fun s h => spH_ok hih 0 1 (by decide) (by decide) (s := s) h
theorem gsplit1_ok : CovK (gsplit1 ih md pos) := fun s h => spH_ok hih 1 2 (by decide) (by decide) (s := s) h
theorem gsplit2_ok : CovK (gsplit2 ih md pos) := fun s h => spH_ok hih 2 3 (by decide) (by decide) (s := s) h
theorem gsplit3_ok : CovK (gsplit3 ih md pos) := fun s h => spH_ok hih 3 4 (by decide) (by decide) (s := s) h
theorem gsplit4_ok : CovK (gsplit4 ih md pos) := fun s h => spH_ok hih 4 5 (by decide) (by decide) (s := s) h
theorem gsplit5_ok : CovK (gsplit5 ih md pos) := fun s h => spH_ok hih 5 6 (by decide) (by decide) (s := s) h
theorem gsplit6_ok : CovK (gsplit6 ih md pos) := fun s h => spH_ok hih 6 7 (by decide) (by decide) (s := s) h
theorem gsplit7_ok : CovK (gsplit7 ih md pos) := fun s h => spH_ok hih 7 8 (by decide) (by decide) (s := s) h
theorem ssplit02_ok : CovK (ssplit02 ih md pos) := fun s h => spH_ok hih 0 2 (by decide) (by decide) (s := s) h
theorem ssplit03_ok : CovK (ssplit03 ih md pos) := fun s h => spH_ok hih 0 3 (by decide) (by decide) (s := s) h
theorem ssplit04_ok : CovK (ssplit04 ih md pos) := fun s h => spH_ok hih 0 4 (by decide) (by decide) (s := s) h
theorem ssplit05_ok : CovK (ssplit05 ih md pos) := fun s h => spH_ok hih 0 5 (by decide) (by decide) (s := s) h
theorem ssplit06_ok : CovK (ssplit06 ih md pos) := fun s h => spH_ok hih 0 6 (by decide) (by decide) (s := s) h
theorem ssplit07_ok : CovK (ssplit07 ih md pos) := fun s h => spH_ok hih 0 7 (by decide) (by decide) (s := s) h
theorem ssplit08_ok : CovK (ssplit08 ih md pos) := fun s h => spH_ok hih 0 8 (by decide) (by decide) (s := s) h
theorem ssplit13_ok : CovK (ssplit13 ih md pos) := fun s h => spH_ok hih 1 3 (by decide) (by decide) (s := s) h
theorem ssplit14_ok : CovK (ssplit14 ih md pos) := fun s h => spH_ok hih 1 4 (by decide) (by decide) (s := s) h
theorem ssplit15_ok : CovK (ssplit15 ih md pos) := fun s h => spH_ok hih 1 5 (by decide) (by decide) (s := s) h
theorem ssplit16_ok : CovK (ssplit16 ih md pos) := fun s h => spH_ok hih 1 6 (by decide) (by decide) (s := s) h
theorem ssplit17_ok : CovK (ssplit17 ih md pos) := fun s h => spH_ok hih 1 7 (by decide) (by decide) (s := s) h
theorem ssplit18_ok : CovK (ssplit18 ih md pos) := fun s h => spH_ok hih 1 8 (by decide) (by decide) (s := s) h
theorem ssplit24_ok : CovK (ssplit24 ih md pos) := fun s h => spH_ok hih 2 4 (by decide) (by decide) (s := s) h
theorem ssplit25_ok : CovK (ssplit25 ih md pos) := fun s h => spH_ok hih 2 5 (by decide) (by decide) (s := s) h
theorem ssplit26_ok : CovK (ssplit26 ih md pos) := fun s h => spH_ok hih 2 6 (by decide) (by decide) (s := s) h
theorem ssplit27_ok : CovK (ssplit27 ih md pos) := fun s h => spH_ok hih 2 7 (by decide) (by decide) (s := s) h
theorem ssplit28_ok : CovK (ssplit28 ih md pos) := fun s h => spH_ok hih 2 8 (by decide) (by decide) (s := s) h
theorem ssplit35_ok : CovK (ssplit35 ih md pos) := fun s h => spH_ok hih 3 5 (by decide) (by decide) (s := s) h
theorem ssplit36_ok : CovK (ssplit36 ih md pos) := fun s h => spH_ok hih 3 6 (by decide) (by decide) (s := s) h
theorem ssplit37_ok : CovK (ssplit37 ih md pos) := fun s h => spH_ok hih 3 7 (by decide) (by decide) (s := s) h
theorem ssplit38_ok : CovK (ssplit38 ih md pos) := fun s h => spH_ok hih 3 8 (by decide) (by decide) (s := s) h
theorem ssplit46_ok : CovK (ssplit46 ih md pos) := fun s h => spH_ok hih 4 6 (by decide) (by decide) (s := s) h
theorem ssplit47_ok : CovK (ssplit47 ih md pos) := fun s h => spH_ok hih 4 7 (by decide) (by decide) (s := s) h
theorem ssplit48_ok : CovK (ssplit48 ih md pos) := fun s h => spH_ok hih 4 8 (by decide) (by decide) (s := s) h
theorem ssplit57_ok : CovK (ssplit57 ih md pos) := fun s h => spH_ok hih 5 7 (by decide) (by decide) (s := s) h
theorem ssplit58_ok : CovK (ssplit58 ih md pos) := fun s h => spH_ok hih 5 8 (by decide) (by decide) (s := s) h
theorem ssplit68_ok : CovK (ssplit68 ih md pos) := fun s h => spH_ok hih 6 8 (by decide) (by decide) (s := s) h
end
noncomputable def splitAx (ih : WF) (md pos ax : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (Bool.rec (motive := fun _ => ST) (zK) (ssplit68 ih md pos) (Nat.beq ax 35)) (ssplit58 ih md pos) (Nat.beq ax 34)) (ssplit57 ih md pos) (Nat.beq ax 33)) (ssplit48 ih md pos) (Nat.beq ax 32)) (ssplit47 ih md pos) (Nat.beq ax 31)) (ssplit46 ih md pos) (Nat.beq ax 30)) (ssplit38 ih md pos) (Nat.beq ax 29)) (ssplit37 ih md pos) (Nat.beq ax 28)) (ssplit36 ih md pos) (Nat.beq ax 27)) (ssplit35 ih md pos) (Nat.beq ax 26)) (ssplit28 ih md pos) (Nat.beq ax 25)) (ssplit27 ih md pos) (Nat.beq ax 24)) (ssplit26 ih md pos) (Nat.beq ax 23)) (ssplit25 ih md pos) (Nat.beq ax 22)) (ssplit24 ih md pos) (Nat.beq ax 21)) (ssplit18 ih md pos) (Nat.beq ax 20)) (ssplit17 ih md pos) (Nat.beq ax 19)) (ssplit16 ih md pos) (Nat.beq ax 18)) (ssplit15 ih md pos) (Nat.beq ax 17)) (ssplit14 ih md pos) (Nat.beq ax 16)) (ssplit13 ih md pos) (Nat.beq ax 15)) (ssplit08 ih md pos) (Nat.beq ax 14)) (ssplit07 ih md pos) (Nat.beq ax 13)) (ssplit06 ih md pos) (Nat.beq ax 12)) (ssplit05 ih md pos) (Nat.beq ax 11)) (ssplit04 ih md pos) (Nat.beq ax 10)) (ssplit03 ih md pos) (Nat.beq ax 9)) (ssplit02 ih md pos) (Nat.beq ax 8)) (gsplit7 ih md pos) (Nat.beq ax 7)) (gsplit6 ih md pos) (Nat.beq ax 6)) (gsplit5 ih md pos) (Nat.beq ax 5)) (gsplit4 ih md pos) (Nat.beq ax 4)) (gsplit3 ih md pos) (Nat.beq ax 3)) (gsplit2 ih md pos) (Nat.beq ax 2)) (gsplit1 ih md pos) (Nat.beq ax 1)) (gsplit0 ih md pos) (Nat.beq ax 0)
theorem splitAx_ok {ih : WF} (hih : WalkOK ih) (md pos ax : ℕ) : CovK (splitAx ih md pos ax) :=
  brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => brec_dep (fun _ => zK_ok) (fun _ => ssplit68_ok hih md pos)) (fun _ => ssplit58_ok hih md pos)) (fun _ => ssplit57_ok hih md pos)) (fun _ => ssplit48_ok hih md pos)) (fun _ => ssplit47_ok hih md pos)) (fun _ => ssplit46_ok hih md pos)) (fun _ => ssplit38_ok hih md pos)) (fun _ => ssplit37_ok hih md pos)) (fun _ => ssplit36_ok hih md pos)) (fun _ => ssplit35_ok hih md pos)) (fun _ => ssplit28_ok hih md pos)) (fun _ => ssplit27_ok hih md pos)) (fun _ => ssplit26_ok hih md pos)) (fun _ => ssplit25_ok hih md pos)) (fun _ => ssplit24_ok hih md pos)) (fun _ => ssplit18_ok hih md pos)) (fun _ => ssplit17_ok hih md pos)) (fun _ => ssplit16_ok hih md pos)) (fun _ => ssplit15_ok hih md pos)) (fun _ => ssplit14_ok hih md pos)) (fun _ => ssplit13_ok hih md pos)) (fun _ => ssplit08_ok hih md pos)) (fun _ => ssplit07_ok hih md pos)) (fun _ => ssplit06_ok hih md pos)) (fun _ => ssplit05_ok hih md pos)) (fun _ => ssplit04_ok hih md pos)) (fun _ => ssplit03_ok hih md pos)) (fun _ => ssplit02_ok hih md pos)) (fun _ => gsplit7_ok hih md pos)) (fun _ => gsplit6_ok hih md pos)) (fun _ => gsplit5_ok hih md pos)) (fun _ => gsplit4_ok hih md pos)) (fun _ => gsplit3_ok hih md pos)) (fun _ => gsplit2_ok hih md pos)) (fun _ => gsplit1_ok hih md pos)) (fun _ => gsplit0_ok hih md pos)
noncomputable def tm (k : ST) (a b c d e f g h i j l m n o r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z aa ab ac ad ae af ag ah ai aj al am an ao ar au av aw ax ay az ba bb bc : ℕ) : ℕ :=
  forceR (nmax t (Nat.add a c)) fun t' => forceR (nmin u (Nat.add b d)) fun u' =>
  forceR (nmax v (Nat.add (Nat.add a c) e)) fun v' => forceR (nmin w (Nat.add (Nat.add b d) f)) fun w' =>
  forceR (nmax x (Nat.add (Nat.add (Nat.add a c) e) g)) fun x' => forceR (nmin y (Nat.add (Nat.add (Nat.add b d) f) h)) fun y' =>
  forceR (nmax z (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i)) fun z' => forceR (nmin A (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j)) fun A' =>
  forceR (nmax B (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l)) fun B' => forceR (nmin C (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m)) fun C' =>
  forceR (nmax D (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n)) fun D' => forceR (nmin E (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o)) fun E' =>
  forceR (nmax F (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add a c) e) g) i) l) n) r)) fun F' => forceR (nmin G (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add b d) f) h) j) m) o) s)) fun G' =>
  forceR (nmax H (Nat.add c e)) fun H' => forceR (nmin I (Nat.add d f)) fun I' =>
  forceR (nmax J (Nat.add (Nat.add c e) g)) fun J' => forceR (nmin K (Nat.add (Nat.add d f) h)) fun K' =>
  forceR (nmax L (Nat.add (Nat.add (Nat.add c e) g) i)) fun L' => forceR (nmin M (Nat.add (Nat.add (Nat.add d f) h) j)) fun M' =>
  forceR (nmax N (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l)) fun N' => forceR (nmin O (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m)) fun O' =>
  forceR (nmax P (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n)) fun P' => forceR (nmin Q (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o)) fun Q' =>
  forceR (nmax R (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add c e) g) i) l) n) r)) fun R' => forceR (nmin S (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add d f) h) j) m) o) s)) fun S' =>
  forceR (nmax T (Nat.add e g)) fun T' => forceR (nmin U (Nat.add f h)) fun U' =>
  forceR (nmax V (Nat.add (Nat.add e g) i)) fun V' => forceR (nmin W (Nat.add (Nat.add f h) j)) fun W' =>
  forceR (nmax X (Nat.add (Nat.add (Nat.add e g) i) l)) fun X' => forceR (nmin Y (Nat.add (Nat.add (Nat.add f h) j) m)) fun Y' =>
  forceR (nmax Z (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n)) fun Z' => forceR (nmin aa (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o)) fun aa' =>
  forceR (nmax ab (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add e g) i) l) n) r)) fun ab' => forceR (nmin ac (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add f h) j) m) o) s)) fun ac' =>
  forceR (nmax ad (Nat.add g i)) fun ad' => forceR (nmin ae (Nat.add h j)) fun ae' =>
  forceR (nmax af (Nat.add (Nat.add g i) l)) fun af' => forceR (nmin ag (Nat.add (Nat.add h j) m)) fun ag' =>
  forceR (nmax ah (Nat.add (Nat.add (Nat.add g i) l) n)) fun ah' => forceR (nmin ai (Nat.add (Nat.add (Nat.add h j) m) o)) fun ai' =>
  forceR (nmax aj (Nat.add (Nat.add (Nat.add (Nat.add g i) l) n) r)) fun aj' => forceR (nmin al (Nat.add (Nat.add (Nat.add (Nat.add h j) m) o) s)) fun al' =>
  forceR (nmax am (Nat.add i l)) fun am' => forceR (nmin an (Nat.add j m)) fun an' =>
  forceR (nmax ao (Nat.add (Nat.add i l) n)) fun ao' => forceR (nmin ar (Nat.add (Nat.add j m) o)) fun ar' =>
  forceR (nmax au (Nat.add (Nat.add (Nat.add i l) n) r)) fun au' => forceR (nmin av (Nat.add (Nat.add (Nat.add j m) o) s)) fun av' =>
  forceR (nmax aw (Nat.add l n)) fun aw' => forceR (nmin ax (Nat.add m o)) fun ax' =>
  forceR (nmax ay (Nat.add (Nat.add l n) r)) fun ay' => forceR (nmin az (Nat.add (Nat.add m o) s)) fun az' =>
  forceR (nmax ba (Nat.add n r)) fun ba' => forceR (nmin bb (Nat.add o s)) fun bb' =>
  k a b c d e f g h i j l m n o r s t' u' v' w' x' y' z' A' B' C' D' E' F' G' H' I' J' K' L' M' N' O' P' Q' R' S' T' U' V' W' X' Y' Z' aa' ab' ac' ad' ae' af' ag' ah' ai' aj' al' am' an' ao' ar' au' av' aw' ax' ay' az' ba' bb' bc
theorem tm_ok {k : ST} (hk : CovK k) : CovK (tm k) := fun s h g hg => by
  have h' : U k (ofCl (matC PR (toCl s)) s.M) ≠ 0 := by simp only [U, tm, forceR_eq] at h; exact h
  exact ofCl_ok hk rfl rfl ((imap_length _ _ _).trans rfl) ((imap_length _ _ _).trans rfl) h' g
    (mat_gen hPR ⟨rfl, rfl, rfl, rfl⟩ hg).2
structure YA where
  (o P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ)
noncomputable def MulOK (s : St) (y : YA) : Prop :=
  MulOKg 8 PR (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7] y.Cp y.Cm
noncomputable def ystep (Ls As Bs : List ℕ) (qb w : ℕ) (ih : YA → YA) (y : YA) : YA :=
  forceT y.o fun o => Bool.rec (motive := fun _ => YA) ⟨(Nat.add o 1), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.Cp, y.Cm⟩
    (forceT (Nat.land (Nat.shiftRight w (Nat.add o 1)) 31) fun c => forceT (Nat.add o 6) fun o1 =>
     Bool.rec (motive := fun _ => YA) ⟨(Nat.add o1 (Nat.add qb 1)), y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7, y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7, y.Cp, y.Cm⟩
      (forceT (Nat.mul SIG (Nat.land (Nat.shiftRight w (Nat.add o1 1)) (Nat.sub (Nat.shiftLeft 1 qb) 1))) fun Y =>
       forceT (Nat.land (Nat.shiftRight w o1) 1) fun sd =>
       forceT (Bool.rec (motive := fun _ => ℕ) Y 0 (Nat.beq sd 1)) fun Ylo => forceT (Bool.rec (motive := fun _ => ℕ) 0 Y (Nat.beq sd 1)) fun Yhi =>
       forceT (pI PR c) fun i => forceT (pJ PR c) fun j => forceT (sumR Ls i (Nat.sub j i)) fun sl =>
       ih ⟨(Nat.add o1 (Nat.add qb 1)), (Nat.add y.P0 (Nat.mul Ylo (ind (inr 0 i j)))), (Nat.add y.P1 (Nat.mul Ylo (ind (inr 1 i j)))), (Nat.add y.P2 (Nat.mul Ylo (ind (inr 2 i j)))), (Nat.add y.P3 (Nat.mul Ylo (ind (inr 3 i j)))), (Nat.add y.P4 (Nat.mul Ylo (ind (inr 4 i j)))), (Nat.add y.P5 (Nat.mul Ylo (ind (inr 5 i j)))), (Nat.add y.P6 (Nat.mul Ylo (ind (inr 6 i j)))), (Nat.add y.P7 (Nat.mul Ylo (ind (inr 7 i j)))), (Nat.add y.S0 (Nat.mul Yhi (ind (inr 0 i j)))), (Nat.add y.S1 (Nat.mul Yhi (ind (inr 1 i j)))), (Nat.add y.S2 (Nat.mul Yhi (ind (inr 2 i j)))), (Nat.add y.S3 (Nat.mul Yhi (ind (inr 3 i j)))), (Nat.add y.S4 (Nat.mul Yhi (ind (inr 4 i j)))), (Nat.add y.S5 (Nat.mul Yhi (ind (inr 5 i j)))), (Nat.add y.S6 (Nat.mul Yhi (ind (inr 6 i j)))), (Nat.add y.S7 (Nat.mul Yhi (ind (inr 7 i j)))), (Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub sl (As.getD c 0)))) (Nat.mul Yhi (Nat.sub (Bs.getD c 0) sl))), (Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub (As.getD c 0) sl))) (Nat.mul Yhi (Nat.sub sl (Bs.getD c 0))))⟩)
      (Nat.blt c 28))
    (Nat.beq (Nat.land (Nat.shiftRight w o) 1) 1)
noncomputable def ydec (Ls As Bs : List ℕ) (qb w fuel : ℕ) : YA → YA :=
  Nat.rec (motive := fun _ => YA → YA) (fun y => y) (fun _ ih => ystep Ls As Bs qb w ih) fuel
theorem MulOK_zero (s : St) (o : ℕ) : MulOK s ⟨o, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := fun _ _ => by simp
theorem ystep_ok (s : St) (qb w : ℕ) {ih : YA → YA} (hih : ∀ y, MulOK s y → MulOK s (ih y)) (y : YA) (h : MulOK s y) :
    MulOK s (ystep (toCl s).L (toCl s).A (toCl s).B qb w ih y) := by
  unfold ystep
  simp only [forceT_eq]
  exact brec_dep (fun _ => h) fun _ => brec_dep (fun _ => h) fun hc => hih _ (mul_step hPR rfl rfl h (Nat.blt_eq.mp hc) _ _)
theorem ydec_ok (s : St) (qb w : ℕ) : ∀ (fuel : ℕ) (y : YA), MulOK s y → MulOK s (ydec (toCl s).L (toCl s).A (toCl s).B qb w fuel y)
  | 0, _, h => h
  | n + 1, y, h => ystep_ok s qb w (ydec_ok s qb w n) y h
noncomputable def mcheckP (goalN : ℕ) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (f : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 : ℕ) (P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.add (Nat.mul 335544320000000000 goalN) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mcK (tf f) false s.l0 k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mcK (tf f) false (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mcK (tf f) false s.l1 k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mcK (tf f) false (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mcK (tf f) false (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mcK (tf f) false s.l2 k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mcK (tf f) false (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mcK (tf f) false (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mcK (tf f) false s.l3 k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mcK (tf f) false (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mcK (tf f) false (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mcK (tf f) false s.l4 k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mcK (tf f) false (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mcK (tf f) false (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mcK (tf f) false (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mcK (tf f) false s.l5 k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mcK (tf f) false (Nat.add s.l5 s.l6) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mcK (tf f) false (Nat.add (Nat.add s.l5 s.l6) s.l7) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mcK (tf f) false s.l6 k67 m67 p67 r67))) (Nat.mul 12145025938708000000 (mcK (tf f) false s.l7 k78 m78 p78 r78))) Cp) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul (Nat.sub s.u0 s.l0) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mwT k01 m01))) (Nat.mul 8651269219434000000 (mwT k03 m03))) (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08)))) P0) (Nat.add (Nat.add (Nat.mul 1024000000000 28195867368000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mslK (tf f) k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08)))) S0)))) (Nat.mul (Nat.sub s.u1 s.l1) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mwT k03 m03))) (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 22223820732794000000 (mwT k12 m12))) (Nat.mul 21042948716829000000 (mwT k13 m13))) (Nat.mul 41416939206756000000 (mwT k14 m14))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18)))) P1) (Nat.add (Nat.add (Nat.mul 1024000000000 50516979727000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mslK (tf f) k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mslK (tf f) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18)))) S1)))) (Nat.mul (Nat.sub s.u2 s.l2) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mwT k03 m03))) (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 21042948716829000000 (mwT k13 m13))) (Nat.mul 41416939206756000000 (mwT k14 m14))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 31202320231433000000 (mwT k23 m23))) (Nat.mul 47970464688707000000 (mwT k24 m24))) (Nat.mul 49931791573808000000 (mwT k25 m25))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28)))) P2) (Nat.add (Nat.add (Nat.mul 1024000000000 69185101351000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 8651269219434000000 (mslK (tf f) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 21042948716829000000 (mslK (tf f) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mslK (tf f) k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mslK (tf f) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28)))) S2)))) (Nat.mul (Nat.sub s.u3 s.l3) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 17776096184552000000 (mwT k04 m04))) (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 41416939206756000000 (mwT k14 m14))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 47970464688707000000 (mwT k24 m24))) (Nat.mul 49931791573808000000 (mwT k25 m25))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 34428833097063000000 (mwT k34 m34))) (Nat.mul 61973173188925000000 (mwT k35 m35))) (Nat.mul 49931791573808000000 (mwT k36 m36))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38)))) P3) (Nat.add (Nat.add (Nat.mul 1024000000000 80158024056000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 17776096184552000000 (mslK (tf f) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 41416939206756000000 (mslK (tf f) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 47970464688707000000 (mslK (tf f) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mslK (tf f) k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mslK (tf f) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38)))) S3)))) (Nat.mul (Nat.sub s.u4 s.l4) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 36889575523970000000 (mwT k05 m05))) (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 46995446251313000000 (mwT k15 m15))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 49931791573808000000 (mwT k25 m25))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 61973173188925000000 (mwT k35 m35))) (Nat.mul 49931791573808000000 (mwT k36 m36))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 34428833097063000000 (mwT k45 m45))) (Nat.mul 47970464688707000000 (mwT k46 m46))) (Nat.mul 41416939206756000000 (mwT k47 m47))) (Nat.mul 17776096184552000000 (mwT k48 m48)))) P4) (Nat.add (Nat.add (Nat.mul 1024000000000 80158024056000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 36889575523970000000 (mslK (tf f) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 46995446251313000000 (mslK (tf f) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 49931791573808000000 (mslK (tf f) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 61973173188925000000 (mslK (tf f) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mslK (tf f) k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mslK (tf f) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48)))) S4)))) (Nat.mul (Nat.sub s.u5 s.l5) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 90239673332399000000 (mwT k06 m06))) (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 63110424476029000000 (mwT k16 m16))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 70456915128268000000 (mwT k26 m26))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 49931791573808000000 (mwT k36 m36))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 47970464688707000000 (mwT k46 m46))) (Nat.mul 41416939206756000000 (mwT k47 m47))) (Nat.mul 17776096184552000000 (mwT k48 m48))) (Nat.mul 31202320231433000000 (mwT k56 m56))) (Nat.mul 21042948716829000000 (mwT k57 m57))) (Nat.mul 8651269219434000000 (mwT k58 m58)))) P5) (Nat.add (Nat.add (Nat.mul 1024000000000 69185101351000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 90239673332399000000 (mslK (tf f) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 63110424476029000000 (mslK (tf f) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 70456915128268000000 (mslK (tf f) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 49931791573808000000 (mslK (tf f) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 47970464688707000000 (mslK (tf f) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mslK (tf f) k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mslK (tf f) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mslK (tf f) k58 m58 p58 r58)))) S5)))) (Nat.mul (Nat.sub s.u6 s.l6) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000000000000000 (mwT k07 m07))) (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 19520653335201000000 (mwT k17 m17))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 63110424476029000000 (mwT k27 m27))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 46995446251313000000 (mwT k37 m37))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 41416939206756000000 (mwT k47 m47))) (Nat.mul 17776096184552000000 (mwT k48 m48))) (Nat.mul 21042948716829000000 (mwT k57 m57))) (Nat.mul 8651269219434000000 (mwT k58 m58))) (Nat.mul 22223820732794000000 (mwT k67 m67)))) P6) (Nat.add (Nat.add (Nat.mul 1024000000000 50516979727000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 100000000000000000000 (mslK (tf f) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 19520653335201000000 (mslK (tf f) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 63110424476029000000 (mslK (tf f) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 46995446251313000000 (mslK (tf f) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 41416939206756000000 (mslK (tf f) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 21042948716829000000 (mslK (tf f) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mslK (tf f) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mslK (tf f) k67 m67 p67 r67)))) S6)))) (Nat.mul (Nat.sub s.u7 s.l7) (Nat.sub (Nat.add (Nat.mul 2000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000000000000000 (mwT k08 m08))) (Nat.mul 100000000000000000000 (mwT k18 m18))) (Nat.mul 90239673332399000000 (mwT k28 m28))) (Nat.mul 36889575523970000000 (mwT k38 m38))) (Nat.mul 17776096184552000000 (mwT k48 m48))) (Nat.mul 8651269219434000000 (mwT k58 m58))) (Nat.mul 12145025938708000000 (mwT k78 m78)))) P7) (Nat.add (Nat.add (Nat.mul 1024000000000 28195867368000000) (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 200000000000000000000 (mslK (tf f) k08 m08 p08 r08))) (Nat.mul 100000000000000000000 (mslK (tf f) k18 m18 p18 r18))) (Nat.mul 90239673332399000000 (mslK (tf f) k28 m28 p28 r28))) (Nat.mul 36889575523970000000 (mslK (tf f) k38 m38 p38 r38))) (Nat.mul 17776096184552000000 (mslK (tf f) k48 m48 p48 r48))) (Nat.mul 8651269219434000000 (mslK (tf f) k58 m58 p58 r58))) (Nat.mul 12145025938708000000 (mslK (tf f) k78 m78 p78 r78)))) S7))))))) (Nat.add (Nat.add (Nat.mul 10240000000000 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 28195867368000000 s.l0)) (Nat.mul 50516979727000000 s.l1)) (Nat.mul 69185101351000000 s.l2)) (Nat.mul 80158024056000000 s.l3)) (Nat.mul 80158024056000000 s.l4)) (Nat.mul 69185101351000000 s.l5)) (Nat.mul 50516979727000000 s.l6)) (Nat.mul 28195867368000000 s.l7))) (Nat.mul 32768 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mvKF top bk (tf f) s.l0 (uc s.l0 s.u0) k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mvKF top bk (tf f) (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (uc (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2))) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mvKF top bk (tf f) (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (uc (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3))) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mvKF top bk (tf f) (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (uc (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4))) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mvKF top bk (tf f) (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5))) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mvKF top bk (tf f) (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6))) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mvKF top bk (tf f) (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7))) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mvKF top bk (tf f) s.l1 (uc s.l1 s.u1) k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mvKF top bk (tf f) (nmax s.A13 (Nat.add s.l1 s.l2)) (uc (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2))) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mvKF top bk (tf f) (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (uc (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3))) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mvKF top bk (tf f) (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (uc (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4))) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mvKF top bk (tf f) (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (uc (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5))) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mvKF top bk (tf f) (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6))) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mvKF top bk (tf f) (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7))) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mvKF top bk (tf f) s.l2 (uc s.l2 s.u2) k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mvKF top bk (tf f) (nmax s.A24 (Nat.add s.l2 s.l3)) (uc (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3))) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mvKF top bk (tf f) (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (uc (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4))) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mvKF top bk (tf f) (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (uc (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5))) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mvKF top bk (tf f) (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (uc (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6))) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mvKF top bk (tf f) (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7))) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mvKF top bk (tf f) s.l3 (uc s.l3 s.u3) k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mvKF top bk (tf f) (nmax s.A35 (Nat.add s.l3 s.l4)) (uc (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4))) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mvKF top bk (tf f) (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (uc (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5))) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mvKF top bk (tf f) (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (uc (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6))) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mvKF top bk (tf f) (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (uc (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7))) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mvKF top bk (tf f) s.l4 (uc s.l4 s.u4) k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mvKF top bk (tf f) (nmax s.A46 (Nat.add s.l4 s.l5)) (uc (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5))) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mvKF top bk (tf f) (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (uc (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6))) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mvKF top bk (tf f) (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (uc (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7))) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mvKF top bk (tf f) s.l5 (uc s.l5 s.u5) k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mvKF top bk (tf f) (nmax s.A57 (Nat.add s.l5 s.l6)) (uc (nmax s.A57 (Nat.add s.l5 s.l6)) (nmin s.B57 (Nat.add s.u5 s.u6))) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mvKF top bk (tf f) (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (uc (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7))) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mvKF top bk (tf f) s.l6 (uc s.l6 s.u6) k67 m67 p67 r67))) (Nat.mul 12145025938708000000 (mvKF top bk (tf f) s.l7 (uc s.l7 s.u7) k78 m78 p78 r78))))) (Nat.mul 10 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add 0 (Nat.mul 12145025938708000000 (mcK (tf f) true s.l0 k01 m01 p01 r01))) (Nat.mul 8651269219434000000 (mcK (tf f) true (Nat.add (Nat.add s.l0 s.l1) s.l2) k03 m03 p03 r03))) (Nat.mul 17776096184552000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) k04 m04 p04 r04))) (Nat.mul 36889575523970000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) k05 m05 p05 r05))) (Nat.mul 90239673332399000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) k06 m06 p06 r06))) (Nat.mul 100000000000000000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) k07 m07 p07 r07))) (Nat.mul 200000000000000000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k08 m08 p08 r08))) (Nat.mul 22223820732794000000 (mcK (tf f) true s.l1 k12 m12 p12 r12))) (Nat.mul 21042948716829000000 (mcK (tf f) true (Nat.add s.l1 s.l2) k13 m13 p13 r13))) (Nat.mul 41416939206756000000 (mcK (tf f) true (Nat.add (Nat.add s.l1 s.l2) s.l3) k14 m14 p14 r14))) (Nat.mul 46995446251313000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) k15 m15 p15 r15))) (Nat.mul 63110424476029000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) k16 m16 p16 r16))) (Nat.mul 19520653335201000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) k17 m17 p17 r17))) (Nat.mul 100000000000000000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7) k18 m18 p18 r18))) (Nat.mul 31202320231433000000 (mcK (tf f) true s.l2 k23 m23 p23 r23))) (Nat.mul 47970464688707000000 (mcK (tf f) true (Nat.add s.l2 s.l3) k24 m24 p24 r24))) (Nat.mul 49931791573808000000 (mcK (tf f) true (Nat.add (Nat.add s.l2 s.l3) s.l4) k25 m25 p25 r25))) (Nat.mul 70456915128268000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) k26 m26 p26 r26))) (Nat.mul 63110424476029000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) k27 m27 p27 r27))) (Nat.mul 90239673332399000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7) k28 m28 p28 r28))) (Nat.mul 34428833097063000000 (mcK (tf f) true s.l3 k34 m34 p34 r34))) (Nat.mul 61973173188925000000 (mcK (tf f) true (Nat.add s.l3 s.l4) k35 m35 p35 r35))) (Nat.mul 49931791573808000000 (mcK (tf f) true (Nat.add (Nat.add s.l3 s.l4) s.l5) k36 m36 p36 r36))) (Nat.mul 46995446251313000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) k37 m37 p37 r37))) (Nat.mul 36889575523970000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7) k38 m38 p38 r38))) (Nat.mul 34428833097063000000 (mcK (tf f) true s.l4 k45 m45 p45 r45))) (Nat.mul 47970464688707000000 (mcK (tf f) true (Nat.add s.l4 s.l5) k46 m46 p46 r46))) (Nat.mul 41416939206756000000 (mcK (tf f) true (Nat.add (Nat.add s.l4 s.l5) s.l6) k47 m47 p47 r47))) (Nat.mul 17776096184552000000 (mcK (tf f) true (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7) k48 m48 p48 r48))) (Nat.mul 31202320231433000000 (mcK (tf f) true s.l5 k56 m56 p56 r56))) (Nat.mul 21042948716829000000 (mcK (tf f) true (Nat.add s.l5 s.l6) k57 m57 p57 r57))) (Nat.mul 8651269219434000000 (mcK (tf f) true (Nat.add (Nat.add s.l5 s.l6) s.l7) k58 m58 p58 r58))) (Nat.mul 22223820732794000000 (mcK (tf f) true s.l6 k67 m67 p67 r67))) (Nat.mul 12145025938708000000 (mcK (tf f) true s.l7 k78 m78 p78 r78))) Cm)))) (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (mokI f s.l7 s.u7 k78 m78 p78 r78) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l6 s.u6 k67 m67 p67 r67) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7)) k58 m58 p58 r58) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A57 (Nat.add s.l5 s.l6)) (nmin s.B57 (Nat.add s.u5 s.u6)) k57 m57 p57 r57) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l5 s.u5 k56 m56 p56 r56) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7)) k48 m48 p48 r48) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) k47 m47 p47 r47) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A46 (Nat.add s.l4 s.l5)) (nmin s.B46 (Nat.add s.u4 s.u5)) k46 m46 p46 r46) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l4 s.u4 k45 m45 p45 r45) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7)) k38 m38 p38 r38) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) k37 m37 p37 r37) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) k36 m36 p36 r36) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A35 (Nat.add s.l3 s.l4)) (nmin s.B35 (Nat.add s.u3 s.u4)) k35 m35 p35 r35) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l3 s.u3 k34 m34 p34 r34) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7)) k28 m28 p28 r28) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) k27 m27 p27 r27) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) k26 m26 p26 r26) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) k25 m25 p25 r25) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A24 (Nat.add s.l2 s.l3)) (nmin s.B24 (Nat.add s.u2 s.u3)) k24 m24 p24 r24) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l2 s.u2 k23 m23 p23 r23) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) k18 m18 p18 r18) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) k17 m17 p17 r17) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) k16 m16 p16 r16) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) k15 m15 p15 r15) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) k14 m14 p14 r14) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A13 (Nat.add s.l1 s.l2)) (nmin s.B13 (Nat.add s.u1 s.u2)) k13 m13 p13 r13) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l1 s.u1 k12 m12 p12 r12) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) k08 m08 p08 r08) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) k07 m07 p07 r07) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) k06 m06 p06 r06) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) k05 m05 p05 r05) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) k04 m04 p04 r04) (Bool.rec (motive := fun _ => Bool) false (mokI f (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) k03 m03 p03 r03) (Bool.rec (motive := fun _ => Bool) false (mokI f s.l0 s.u0 k01 m01 p01 r01) (true))))))))))))))))))))))))))))))))))) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l7 s.u7) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l6 s.u6) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l5 s.u5) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l4 s.u4) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l3 s.u3) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l2 s.u2) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l1 s.u1) (Bool.rec (motive := fun _ => Bool) false (Nat.ble s.l0 s.u0) (true))))))))))
theorem mcheckP_ok (goalN : ℕ) {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {f : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)} (s : St)
    (k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 : ℕ) (P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm : ℕ) (h : mcheckP goalN top bk tD bD f R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 P0 P1 P2 P3 P4 P5 P6 P7 S0 S1 S2 S3 S4 S5 S6 S7 Cp Cm = true) :
    mcheckGX (mokI f) top bk (tf f) 8 BS TS goalN (toCl s) [(k01, m01, p01, r01), (k03, m03, p03, r03), (k04, m04, p04, r04), (k05, m05, p05, r05), (k06, m06, p06, r06), (k07, m07, p07, r07), (k08, m08, p08, r08), (k12, m12, p12, r12), (k13, m13, p13, r13), (k14, m14, p14, r14), (k15, m15, p15, r15), (k16, m16, p16, r16), (k17, m17, p17, r17), (k18, m18, p18, r18), (k23, m23, p23, r23), (k24, m24, p24, r24), (k25, m25, p25, r25), (k26, m26, p26, r26), (k27, m27, p27, r27), (k28, m28, p28, r28), (k34, m34, p34, r34), (k35, m35, p35, r35), (k36, m36, p36, r36), (k37, m37, p37, r37), (k38, m38, p38, r38), (k45, m45, p45, r45), (k46, m46, p46, r46), (k47, m47, p47, r47), (k48, m48, p48, r48), (k56, m56, p56, r56), (k57, m57, p57, r57), (k58, m58, p58, r58), (k67, m67, p67, r67), (k78, m78, p78, r78)]
      [P0, P1, P2, P3, P4, P5, P6, P7] [S0, S1, S2, S3, S4, S5, S6, S7] Cp Cm = true := by
  simp only [mcheckP, mvK_eq, mcpK_eq, mcnK_eq, mslK_eq, mvKF_eq] at h; exact h
noncomputable def mleafP (goalN : ℕ) (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (w : ℕ) (s : St) : ℕ :=
  forceR (nmax s.A02 (Nat.add s.l0 s.l1)) fun L02 => forceR (nmin s.B02 (Nat.add s.u0 s.u1)) fun U02 =>
  forceR (nmax s.A03 (Nat.add (Nat.add s.l0 s.l1) s.l2)) fun L03 => forceR (nmin s.B03 (Nat.add (Nat.add s.u0 s.u1) s.u2)) fun U03 =>
  forceR (nmax s.A04 (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3)) fun L04 => forceR (nmin s.B04 (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3)) fun U04 =>
  forceR (nmax s.A05 (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4)) fun L05 => forceR (nmin s.B05 (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4)) fun U05 =>
  forceR (nmax s.A06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5)) fun L06 => forceR (nmin s.B06 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5)) fun U06 =>
  forceR (nmax s.A07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6)) fun L07 => forceR (nmin s.B07 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6)) fun U07 =>
  forceR (nmax s.A08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l0 s.l1) s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) fun L08 => forceR (nmin s.B08 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u0 s.u1) s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) fun U08 =>
  forceR (nmax s.A13 (Nat.add s.l1 s.l2)) fun L13 => forceR (nmin s.B13 (Nat.add s.u1 s.u2)) fun U13 =>
  forceR (nmax s.A14 (Nat.add (Nat.add s.l1 s.l2) s.l3)) fun L14 => forceR (nmin s.B14 (Nat.add (Nat.add s.u1 s.u2) s.u3)) fun U14 =>
  forceR (nmax s.A15 (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4)) fun L15 => forceR (nmin s.B15 (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4)) fun U15 =>
  forceR (nmax s.A16 (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5)) fun L16 => forceR (nmin s.B16 (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5)) fun U16 =>
  forceR (nmax s.A17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6)) fun L17 => forceR (nmin s.B17 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6)) fun U17 =>
  forceR (nmax s.A18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l1 s.l2) s.l3) s.l4) s.l5) s.l6) s.l7)) fun L18 => forceR (nmin s.B18 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u1 s.u2) s.u3) s.u4) s.u5) s.u6) s.u7)) fun U18 =>
  forceR (nmax s.A24 (Nat.add s.l2 s.l3)) fun L24 => forceR (nmin s.B24 (Nat.add s.u2 s.u3)) fun U24 =>
  forceR (nmax s.A25 (Nat.add (Nat.add s.l2 s.l3) s.l4)) fun L25 => forceR (nmin s.B25 (Nat.add (Nat.add s.u2 s.u3) s.u4)) fun U25 =>
  forceR (nmax s.A26 (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5)) fun L26 => forceR (nmin s.B26 (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5)) fun U26 =>
  forceR (nmax s.A27 (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6)) fun L27 => forceR (nmin s.B27 (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6)) fun U27 =>
  forceR (nmax s.A28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.l2 s.l3) s.l4) s.l5) s.l6) s.l7)) fun L28 => forceR (nmin s.B28 (Nat.add (Nat.add (Nat.add (Nat.add (Nat.add s.u2 s.u3) s.u4) s.u5) s.u6) s.u7)) fun U28 =>
  forceR (nmax s.A35 (Nat.add s.l3 s.l4)) fun L35 => forceR (nmin s.B35 (Nat.add s.u3 s.u4)) fun U35 =>
  forceR (nmax s.A36 (Nat.add (Nat.add s.l3 s.l4) s.l5)) fun L36 => forceR (nmin s.B36 (Nat.add (Nat.add s.u3 s.u4) s.u5)) fun U36 =>
  forceR (nmax s.A37 (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6)) fun L37 => forceR (nmin s.B37 (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6)) fun U37 =>
  forceR (nmax s.A38 (Nat.add (Nat.add (Nat.add (Nat.add s.l3 s.l4) s.l5) s.l6) s.l7)) fun L38 => forceR (nmin s.B38 (Nat.add (Nat.add (Nat.add (Nat.add s.u3 s.u4) s.u5) s.u6) s.u7)) fun U38 =>
  forceR (nmax s.A46 (Nat.add s.l4 s.l5)) fun L46 => forceR (nmin s.B46 (Nat.add s.u4 s.u5)) fun U46 =>
  forceR (nmax s.A47 (Nat.add (Nat.add s.l4 s.l5) s.l6)) fun L47 => forceR (nmin s.B47 (Nat.add (Nat.add s.u4 s.u5) s.u6)) fun U47 =>
  forceR (nmax s.A48 (Nat.add (Nat.add (Nat.add s.l4 s.l5) s.l6) s.l7)) fun L48 => forceR (nmin s.B48 (Nat.add (Nat.add (Nat.add s.u4 s.u5) s.u6) s.u7)) fun U48 =>
  forceR (nmax s.A57 (Nat.add s.l5 s.l6)) fun L57 => forceR (nmin s.B57 (Nat.add s.u5 s.u6)) fun U57 =>
  forceR (nmax s.A58 (Nat.add (Nat.add s.l5 s.l6) s.l7)) fun L58 => forceR (nmin s.B58 (Nat.add (Nat.add s.u5 s.u6) s.u7)) fun U58 =>
  forceR (nmax s.A68 (Nat.add s.l6 s.l7)) fun L68 => forceR (nmin s.B68 (Nat.add s.u6 s.u7)) fun U68 =>
  forceR 0 fun o0 =>
  dec4F 10 w o0 s.l0 s.u0 fun k01 m01 p01 r01 o1 =>
  dec4F 10 w o1 L03 U03 fun k03 m03 p03 r03 o2 =>
  dec4F 10 w o2 L04 U04 fun k04 m04 p04 r04 o3 =>
  dec4F 10 w o3 L05 U05 fun k05 m05 p05 r05 o4 =>
  dec4F 10 w o4 L06 U06 fun k06 m06 p06 r06 o5 =>
  dec4F 10 w o5 L07 U07 fun k07 m07 p07 r07 o6 =>
  dec4F 10 w o6 L08 U08 fun k08 m08 p08 r08 o7 =>
  dec4F 10 w o7 s.l1 s.u1 fun k12 m12 p12 r12 o8 =>
  dec4F 10 w o8 L13 U13 fun k13 m13 p13 r13 o9 =>
  dec4F 10 w o9 L14 U14 fun k14 m14 p14 r14 o10 =>
  dec4F 10 w o10 L15 U15 fun k15 m15 p15 r15 o11 =>
  dec4F 10 w o11 L16 U16 fun k16 m16 p16 r16 o12 =>
  dec4F 10 w o12 L17 U17 fun k17 m17 p17 r17 o13 =>
  dec4F 10 w o13 L18 U18 fun k18 m18 p18 r18 o14 =>
  dec4F 10 w o14 s.l2 s.u2 fun k23 m23 p23 r23 o15 =>
  dec4F 10 w o15 L24 U24 fun k24 m24 p24 r24 o16 =>
  dec4F 10 w o16 L25 U25 fun k25 m25 p25 r25 o17 =>
  dec4F 10 w o17 L26 U26 fun k26 m26 p26 r26 o18 =>
  dec4F 10 w o18 L27 U27 fun k27 m27 p27 r27 o19 =>
  dec4F 10 w o19 L28 U28 fun k28 m28 p28 r28 o20 =>
  dec4F 10 w o20 s.l3 s.u3 fun k34 m34 p34 r34 o21 =>
  dec4F 10 w o21 L35 U35 fun k35 m35 p35 r35 o22 =>
  dec4F 10 w o22 L36 U36 fun k36 m36 p36 r36 o23 =>
  dec4F 10 w o23 L37 U37 fun k37 m37 p37 r37 o24 =>
  dec4F 10 w o24 L38 U38 fun k38 m38 p38 r38 o25 =>
  dec4F 10 w o25 s.l4 s.u4 fun k45 m45 p45 r45 o26 =>
  dec4F 10 w o26 L46 U46 fun k46 m46 p46 r46 o27 =>
  dec4F 10 w o27 L47 U47 fun k47 m47 p47 r47 o28 =>
  dec4F 10 w o28 L48 U48 fun k48 m48 p48 r48 o29 =>
  dec4F 10 w o29 s.l5 s.u5 fun k56 m56 p56 r56 o30 =>
  dec4F 10 w o30 L57 U57 fun k57 m57 p57 r57 o31 =>
  dec4F 10 w o31 L58 U58 fun k58 m58 p58 r58 o32 =>
  dec4F 10 w o32 s.l6 s.u6 fun k67 m67 p67 r67 o33 =>
  dec4F 10 w o33 s.l7 s.u7 fun k78 m78 p78 r78 o34 =>
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o (mcheckP goalN top bk tD bD pb R s k01 m01 p01 r01 k03 m03 p03 r03 k04 m04 p04 r04 k05 m05 p05 r05 k06 m06 p06 r06 k07 m07 p07 r07 k08 m08 p08 r08 k12 m12 p12 r12 k13 m13 p13 r13 k14 m14 p14 r14 k15 m15 p15 r15 k16 m16 p16 r16 k17 m17 p17 r17 k18 m18 p18 r18 k23 m23 p23 r23 k24 m24 p24 r24 k25 m25 p25 r25 k26 m26 p26 r26 k27 m27 p27 r27 k28 m28 p28 r28 k34 m34 p34 r34 k35 m35 p35 r35 k36 m36 p36 r36 k37 m37 p37 r37 k38 m38 p38 r38 k45 m45 p45 r45 k46 m46 p46 r46 k47 m47 p47 r47 k48 m48 p48 r48 k56 m56 p56 r56 k57 m57 p57 r57 k58 m58 p58 r58 k67 m67 p67 r67 k78 m78 p78 r78 y.P0 y.P1 y.P2 y.P3 y.P4 y.P5 y.P6 y.P7 y.S0 y.S1 y.S2 y.S3 y.S4 y.S5 y.S6 y.S7 y.Cp y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 14 w 42 ⟨o34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
/- Eliminate forced decoder values without duplicating their expressions.
   This preserves the actual evaluator and every guard; it changes only the
   proof term used to establish the existing universal leaf theorem. -/
theorem zeroForge_forceR_cov {P : Prop} {a : ℕ} {k : ℕ → ℕ}
    (hk : ∀ x, k x ≠ 0 → P) (h : forceR a k ≠ 0) : P := by
  rw [forceR_eq] at h
  exact hk _ h

theorem mleafP_target_ok (goalN : ℕ) {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP goalN top bk tD bD pb R w s ≠ 0) : CovBy 8 PR (Pg goalN 8 BS TS) (toCl s) := by
  revert h
  unfold mleafP dec4F
  iterate 227 refine zeroForge_forceR_cov (fun _ => ?_)
  intro h
  exact mcheckGX_sound (f := tf pb) (mtermTI hlb hpt) hPR hTS (ydec_ok s 14 w 42 _ (MulOK_zero s _)) (mcheckP_ok goalN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (brec_ne h))
theorem mleafP_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ}
    {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x))
    (hR : rgOk R = true) (w : ℕ) (s : St)
    (h : mleafP (tinyTarget s) top bk tD bD pb R w s ≠ 0) : Covered (toCl s) := by
  intro g hg
  exact tiny_target_sound hg (mleafP_target_ok (tinyTarget s) hlb hD hpt hR w s h g hg)
noncomputable def fleaf (w : ℕ) (s : St) : ℕ :=
  (fun y : YA => Bool.rec (motive := fun _ => ℕ) 0 y.o
    (Nat.blt (Nat.add y.Cp (fsum (toCl s) [y.P0, y.P1, y.P2, y.P3, y.P4, y.P5, y.P6, y.P7] [y.S0, y.S1, y.S2, y.S3, y.S4, y.S5, y.S6, y.S7] 8)) y.Cm))
  (ydec (toCl s).L (toCl s).A (toCl s).B 14 w 42 ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩)
noncomputable def leafStep (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (pos w : ℕ) : ST :=
  fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M => Bool.rec (motive := fun _ => ℕ)
    (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP (tinyTarget ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩) top bk tD bD pb R (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩)
        (fleaf (Nat.shiftRight w 2) ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0))
    (Nat.add pos 1) (Nat.blt u7 l0)
theorem fleaf_ok (w : ℕ) (s : St) (h : fleaf w s ≠ 0) : Covered (toCl s) :=
  farkas_cov (ydec_ok s 14 w 42 _ (MulOK_zero s 0)) (brec_ne h)
theorem leafStep_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (pos w : ℕ) :
    CovK (leafStep top bk tD bD pb R pos w) := by
  intro s h
  have h' : Bool.rec (motive := fun _ => ℕ) (forceR (Bool.rec (motive := fun _ => ℕ) (mleafP (tinyTarget s) top bk tD bD pb R (Nat.shiftRight w 2) s)
      (fleaf (Nat.shiftRight w 2) s) (Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1)) fun n =>
      Bool.rec (motive := fun _ => ℕ) (Nat.add pos (Nat.add 2 n)) 0 (Nat.beq n 0)) (Nat.add pos 1) (Nat.blt s.u7 s.l0) ≠ 0 := h
  cases hs : Nat.blt s.u7 s.l0
  · rw [hs, forceR_eq] at h'
    cases hk : Nat.beq (Nat.land (Nat.shiftRight w 1) 1) 1
    · rw [hk] at h'; exact mleafP_ok hlb hD hpt hR _ s fun h0 => by rw [h0] at h'; exact h' rfl
    · rw [hk] at h'; exact fleaf_ok _ s fun h0 => by rw [h0] at h'; exact h' rfl
  · intro g hg
    left
    right
    have h1 : g 7 ≤ (s.u7 : ℝ) / SC := (hg.1 7 (by norm_num)).2
    have h2 : (s.l0 : ℝ) / SC ≤ g 0 := (hg.1 0 (by norm_num)).1
    have : (s.u7 : ℝ) / SC < (s.l0 : ℝ) / SC := div_lt_div_of_pos_right (by exact_mod_cast Nat.blt_eq.mp hs) SC_pos
    show g 7 < g 0
    linarith
noncomputable def WMASK : ℕ := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
noncomputable def rdw (f : ℕ → ℕ) (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (f (Nat.div pos 32768)) (Nat.mod pos 32768)) WMASK
noncomputable def node (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (ih : WF) (pos : ℕ) : ST :=
  Bool.rec (motive := fun _ => ST) (leafStep top bk tD bD pb R pos (bits pos))
    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) 7) 1) (Nat.add pos 8) (Nat.land (Nat.shiftRight (bits pos) 1) 63))
    (Nat.beq (Nat.land (bits pos) 1) 1)
noncomputable def walkC (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => node top bk tD bD pb R bits ih pos) fuel
noncomputable def walk (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ) (fuel : ℕ) : WF :=
  fun pos => tm (walkC top bk tD bD pb R bits fuel pos)
theorem walkC_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) :
    ∀ fuel, WalkOK (walkC top bk tD bD pb R bits fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => show CovK (node top bk tD bD pb R bits (walkC top bk tD bD pb R bits n) pos) from
      brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
      (splitAx_ok (walkC_ok hlb hD hpt hR bits n) _ _ _)
theorem walk_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) :
    ∀ fuel, WalkOK (walk top bk tD bD pb R bits fuel) :=
  fun fuel pos => tm_ok (walkC_ok hlb hD hpt hR bits fuel pos)
theorem covered_of_walk {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel e : ℕ) (s : St)
    (h : U (walk top bk tD bD pb R bits fuel 1) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walk_ok hlb hD hpt hR bits fuel 1 s (h ▸ he)
theorem covered_of_walkCP {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ) (fuel pos e : ℕ) (s : St)
    (h : U (walkC top bk tD bD pb R bits fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walkC_ok hlb hD hpt hR bits fuel pos s (h ▸ he)
noncomputable def kEqE (t : St) (e : ℕ) : ST := fun l0 u0 l1 u1 l2 u2 l3 u3 l4 u4 l5 u5 l6 u6 l7 u7 A02 B02 A03 B03 A04 B04 A05 B05 A06 B06 A07 B07 A08 B08 A13 B13 A14 B14 A15 B15 A16 B16 A17 B17 A18 B18 A24 B24 A25 B25 A26 B26 A27 B27 A28 B28 A35 B35 A36 B36 A37 B37 A38 B38 A46 B46 A47 B47 A48 B48 A57 B57 A58 B58 A68 B68 M => Bool.rec (motive := fun _ => ℕ) 0 e (stEq ⟨l0, u0, l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, A02, B02, A03, B03, A04, B04, A05, B05, A06, B06, A07, B07, A08, B08, A13, B13, A14, B14, A15, B15, A16, B16, A17, B17, A18, B18, A24, B24, A25, B25, A26, B26, A27, B27, A28, B28, A35, B35, A36, B36, A37, B37, A38, B38, A46, B46, A47, B47, A48, B48, A57, B57, A58, B58, A68, B68, M⟩ t)
theorem kEqE_ok {t : St} {e : ℕ} (h : Covered (toCl t)) : CovK (kEqE t e) := fun s hs => by
  have e' : U (kEqE t e) s = Bool.rec (motive := fun _ => ℕ) 0 e (stEq s t) := rfl
  rw [e'] at hs
  cases hb : stEq s t
  · rw [hb] at hs; exact absurd rfl hs
  · rw [St_eq hb]; exact h
noncomputable def cutAt (cuts : List (ℕ × St × ℕ)) (pos : ℕ) (k : ST) : ST :=
  List.rec (motive := fun _ => ST) k (fun c _ ih => Bool.rec (motive := fun _ => ST) ih (kEqE c.2.1 c.2.2) (Nat.beq c.1 pos)) cuts
noncomputable def CutsOk (cuts : List (ℕ × St × ℕ)) : Prop := ∀ c ∈ cuts, Covered (toCl c.2.1)
theorem cutsOk_nil : CutsOk [] := fun _ h => absurd h (by simp)
theorem cutsOk_cons {p e : ℕ} {t : St} {cs : List (ℕ × St × ℕ)} (h : Covered (toCl t)) (hs : CutsOk cs) :
    CutsOk ((p, t, e) :: cs) := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h
  · exact hs c hc
theorem cutAt_ok {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) (pos : ℕ) {k : ST} (hk : CovK k) : CovK (cutAt cuts pos k) := by
  induction cuts with
  | nil => exact hk
  | cons c cs ih =>
    show CovK (Bool.rec (motive := fun _ => ST) (cutAt cs pos k) (kEqE c.2.1 c.2.2) (Nat.beq c.1 pos))
    cases Nat.beq c.1 pos
    · exact ih (fun d hd => hc d (List.mem_cons_of_mem _ hd))
    · exact kEqE_ok (hc c (List.mem_cons.mpr (Or.inl rfl)))
noncomputable def walkCut (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ)
    (cuts : List (ℕ × St × ℕ)) (fuel : ℕ) : WF :=
  Nat.rec (motive := fun _ => WF) (fun _ => zK) (fun _ ih pos => cutAt cuts pos (node top bk tD bD pb R bits ih pos)) fuel
noncomputable def walkCutR (top : ℕ) (bk : ℕ → ℕ) (tD : ℕ) (bD : ℕ → ℕ) (pb : ℕ → ℕ) (R : ℕ × ℕ × List (List ℕ)) (bits : ℕ → ℕ)
    (cuts : List (ℕ × St × ℕ)) (fuel : ℕ) : WF :=
  fun pos => tm (walkCut top bk tD bD pb R bits cuts fuel pos)
theorem walkCut_ok {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ)
    {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) : ∀ fuel, WalkOK (walkCut top bk tD bD pb R bits cuts fuel)
  | 0 => fun _ => zK_ok
  | n + 1 => fun pos => cutAt_ok hc pos
      (show CovK (node top bk tD bD pb R bits (walkCut top bk tD bD pb R bits cuts n) pos) from
        brec_dep (fun _ => leafStep_ok hlb hD hpt hR pos _) fun _ =>
        (splitAx_ok (walkCut_ok hlb hD hpt hR bits hc n) _ _ _))
theorem covered_of_walkCutR {top : ℕ} {bk : ℕ → ℕ} {tD : ℕ} {bD : ℕ → ℕ} {pb : ℕ → ℕ} {R : ℕ × ℕ × List (List ℕ)}
    (hlb : LBSound top bk) (hD : LBSoundD tD bD) (hpt : ∀ x, PVI x (pb x)) (hR : rgOk R = true) (bits : ℕ → ℕ)
    {cuts : List (ℕ × St × ℕ)} (hc : CutsOk cuts) (fuel pos e : ℕ) (s : St)
    (h : U (walkCutR top bk tD bD pb R bits cuts fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  tm_ok (walkCut_ok hlb hD hpt hR bits hc fuel pos) s (h ▸ he)
noncomputable def ADJ : List ℕ := [0, 7, 14, 20, 25, 29, 32, 33]
theorem hADJ : ∀ r < 8, ADJ.getD r 0 < TS.length ∧ tI TS (ADJ.getD r 0) = r ∧ tJ TS (ADJ.getD r 0) = r + 1 := by decide
theorem cert_of (cov : List (List (ℕ × ℕ × Bool))) (Smax : ℕ → ℕ) (hS : ∀ r < 8, cN * SC ≤ BS.getD r 0 * Smax r)
    (hcov : ∀ r < 8, coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (Smax r) (cov.getD r []) = true)
    (hwin : ∀ r < 8, cN * 4 ≤ tA TS (ADJ.getD r 0)) (W : ℕ) (hW : 8 * KB ≤ W)
    (hrun : ∀ idx : ℕ → ℕ, (∀ r < 8, idx r < (badOf (cov.getD r [])).length) → Covered (rootCl 8 28 W cov idx)) :
    ∀ g : ℕ → ℝ, (∀ r < 8, 0 ≤ g r) → Pg cN 8 BS TS g :=
  root_cover hPR (fun r => ADJ.getD r 0) hADJ Smax hS cov hcov hwin W hW (fun idx hi g hg => tiny_forget (hrun idx hi g hg))
end AMW.Cert.PC9Tiny
end

noncomputable section
namespace AMW.Cert.PC9TinyData
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC9Tiny
set_option maxRecDepth 100000

-- Exact aliases of the already-proved current-kernel LB/jet tables.
noncomputable def TOP : ℕ := AMW.Cert.PC9QB6MData.TOP
noncomputable def BK : ℕ → ℕ := AMW.Cert.PC9QB6MData.BK
theorem lbS : Pyr.LBSound TOP BK := AMW.Cert.PC9QB6MData.lbS
noncomputable def TOPD : ℕ := AMW.Cert.PC9QB6MData.TOPD
noncomputable def BKD : ℕ → ℕ := AMW.Cert.PC9QB6MData.BKD
theorem lbD : LBSoundD TOPD BKD := AMW.Cert.PC9QB6MData.lbD
noncomputable def REG : ℕ × ℕ × List (List ℕ) := AMW.Cert.PC9QB6MData.REG
theorem hR : rgOk REG = true := AMW.Cert.PC9QB6MData.hR
noncomputable def PT : ℕ → ℕ := AMW.Cert.PC9QB6MData.PT
theorem ptS : ∀ x, PVI x (PT x) := AMW.Cert.PC9QB6MData.ptS

noncomputable def COV : List (List (ℕ × ℕ × Bool)) := [
  [(16384, 20480, true), (20480, 22528, true), (22528, 24576, true), (24576, 25600, true), (25600, 26112, true), (26112, 1040384, false)],
  [(16384, 20480, true), (20480, 24576, true), (24576, 26624, true), (26624, 27648, true), (27648, 28160, true), (28160, 28478, true), (28478, 28533, true), (28533, 28543, true), (28543, 28544, true), (28544, 28545, true), (28545, 39936, false), (39936, 51168, false), (51168, 581632, false)],
  [(16384, 24576, true), (24576, 26624, true), (26624, 28672, true), (28672, 29184, true), (29184, 45301, false), (45301, 45302, true), (45302, 45304, true), (45304, 45307, true), (45307, 45312, true), (45312, 45321, true), (45321, 45337, true), (45337, 45365, true), (45365, 45413, true), (45413, 45496, true), (45496, 45568, true), (45568, 45761, true), (45761, 46080, true), (46080, 46592, true), (46592, 47104, true), (47104, 48112, true), (48112, 48128, true), (48128, 49152, true), (49152, 50176, true), (50176, 50971, true), (50971, 51200, true), (51200, 51577, true), (51577, 51712, true), (51712, 51856, true), (51856, 51933, true), (51933, 51968, true), (51968, 51991, true), (51991, 52003, true), (52003, 52009, true), (52009, 52012, true), (52012, 52014, true), (52014, 52015, true), (52015, 52016, true), (52016, 425984, false)],
  [(16384, 24576, true), (24576, 28672, true), (28672, 29184, true), (29184, 29440, true), (29440, 29637, true), (29637, 29663, true), (29663, 29666, true), (29666, 44151, false), (44151, 44152, true), (44152, 44154, true), (44154, 44158, true), (44158, 44167, true), (44167, 44185, true), (44185, 44221, true), (44221, 44288, true), (44288, 44429, true), (44429, 44544, true), (44544, 44937, true), (44937, 45056, true), (45056, 45912, true), (45912, 46080, true), (46080, 47104, true), (47104, 49152, true), (49152, 51176, true), (51176, 51200, true), (51200, 52224, true), (52224, 52736, true), (52736, 53067, true), (53067, 53214, true), (53214, 53248, true), (53248, 376832, false)],
  [(16384, 24576, true), (24576, 28672, true), (28672, 29184, true), (29184, 29440, true), (29440, 29637, true), (29637, 29663, true), (29663, 29666, true), (29666, 44151, false), (44151, 44152, true), (44152, 44154, true), (44154, 44158, true), (44158, 44167, true), (44167, 44185, true), (44185, 44221, true), (44221, 44288, true), (44288, 44429, true), (44429, 44544, true), (44544, 44937, true), (44937, 45056, true), (45056, 45912, true), (45912, 46080, true), (46080, 47104, true), (47104, 49152, true), (49152, 51176, true), (51176, 51200, true), (51200, 52224, true), (52224, 52736, true), (52736, 53067, true), (53067, 53214, true), (53214, 53248, true), (53248, 376832, false)],
  [(16384, 24576, true), (24576, 26624, true), (26624, 28672, true), (28672, 29184, true), (29184, 45301, false), (45301, 45302, true), (45302, 45304, true), (45304, 45307, true), (45307, 45312, true), (45312, 45321, true), (45321, 45337, true), (45337, 45365, true), (45365, 45413, true), (45413, 45496, true), (45496, 45568, true), (45568, 45761, true), (45761, 46080, true), (46080, 46592, true), (46592, 47104, true), (47104, 48112, true), (48112, 48128, true), (48128, 49152, true), (49152, 50176, true), (50176, 50971, true), (50971, 51200, true), (51200, 51577, true), (51577, 51712, true), (51712, 51856, true), (51856, 51933, true), (51933, 51968, true), (51968, 51991, true), (51991, 52003, true), (52003, 52009, true), (52009, 52012, true), (52012, 52014, true), (52014, 52015, true), (52015, 52016, true), (52016, 425984, false)],
  [(16384, 20480, true), (20480, 24576, true), (24576, 26624, true), (26624, 27648, true), (27648, 28160, true), (28160, 28478, true), (28478, 28533, true), (28533, 28543, true), (28543, 28544, true), (28544, 28545, true), (28545, 581632, false)],
  [(16384, 20480, true), (20480, 22528, true), (22528, 24576, true), (24576, 25600, true), (25600, 26112, true), (26112, 1040384, false)]]
noncomputable def SMAX (r : ℕ) : ℕ := [1040384, 581632, 425984, 376832, 376832, 425984, 581632, 1040384].getD r 0
noncomputable def RC (i0 i1 i2 i3 i4 i5 i6 i7 : ℕ) : Cl := rootCl 8 28 1099511627776 COV (fun r => [i0, i1, i2, i3, i4, i5, i6, i7].getD r 0)
theorem rcOf {i0 i1 i2 i3 i4 i5 i6 i7 : ℕ} (wb : ℕ → ℕ) (e : ℕ) (h : U (walk TOP BK TOPD BKD PT REG wb 128 1) (ofCl (RC i0 i1 i2 i3 i4 i5 i6 i7) 0) = e)
    (he : e ≠ 0) : Covered (RC i0 i1 i2 i3 i4 i5 i6 i7) := by
  have h' := covered_of_walk lbS lbD ptS hR wb 128 e _ h he
  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h'
theorem rcOfC {i0 i1 i2 i3 i4 i5 i6 i7 : ℕ} (wb : ℕ → ℕ) (cuts : List (ℕ × St × ℕ)) (hc : CutsOk cuts) (e : ℕ)
    (h : U (walkCutR TOP BK TOPD BKD PT REG wb cuts 128 1) (ofCl (RC i0 i1 i2 i3 i4 i5 i6 i7) 0) = e) (he : e ≠ 0) : Covered (RC i0 i1 i2 i3 i4 i5 i6 i7) := by
  have h' := covered_of_walkCutR lbS lbD ptS hR wb hc 128 1 e _ h he
  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h'
noncomputable def WL0_0 : ℕ := zfNat64 26049 "Gcz4BgIBEMBFA5wlAHOEoBqBFAABMZAAAGAgHVkQAEKAYCAUBAzEmAssVANRep0EpCIww6AEDHSyAAAYCABCXAMBAHRJgDekwAb0mD_SMB0SYAAAAAMBAAwEAtIuVhJQXlCsBrJQUFScCKNRyXYqTgTku0E0iJDAAAMBAASGgAAAAAAAAAAAAEjIAAAAAAAAAAAAFgMFzyoDeJUA1A0kisCKNR+JQrAC6QGQgAADAQAMBAsBgueVAbxKgGoGkkVgRRqPxKFYAXSAyEAAAHGKgCYsAwEBUGALxUAtwqAUmnyoAqNSLhUAIbCAAAAZkqAJDQCgMAAogqCLhUTaKgCv_jYi0VACEugAAAGKKgYBgOeFw3AajKIC5WApkopAKjUcikAQl0UyBH6YjAAARBgAAlwgkqAJCwshQIyII3FwRl2ZQvAUyWUgFRqOZSEEEJd3IjGcRgAAAAJcGQKgISIHBlQRnBJUApJSAVGuZDrhJUT6G_ohAhLoAAAnCgAAlwXAqAJDQEZEAtCMmILlYCmSgLKFYBUajkEZIrCCCEukXwiMAAAGbJgdCgAKFysOgXRneBUApEpSi5WAV_+HDlBBcrACCRQAAUAcAs8qAJDQTREAEZlICn5BtwgqVgFSq2w6lIBhLvDkYAAAF0FRQDVOS4AIzKQFI1NaSKwCpElCuOVClCs_wFBhLpFGIjAACgGgFXlVXFwlAAkIVAKTOBUAVKJVIqGoGHUC8BZAA1BcDo6CgioHQoKuJQEZXIVKwFI1WSSKwCpRHIpAMJdIr4EYAAUAcRtGA4EIG2VBaDHyoIy7koXgKSUtSHgKjUc8NKgBCXRUiEAACIKAMwVP7JQXHKgzKNf_KgYikVGUKwShUanGyoAQl0BPDQAAAAS4T4VFlJUcmp8yheRmMykmIpkplyRWSUKjWcjLKFYAhMJFCIlH6Ll4AAA7S4N+VLETE0CWlC8CsZEcXKwYimShPJFYJQqNRy2koVgCEukUjoAFiJgdHTGnnambA3BUASGiBCapUH_RrvpUApAsFSsLIVGpx0qAFJdAAAAAfXCFyogQreVDxEKMykpopADFSsLIVGpx0qAFJdaIjFOjoAABPpUQIGBKF4pQ8hxkaxUrKaKZKGUoVhZCo1HLbShWAKS6RR6zEAAA40qC0TcjDyBBi0IuCMq+LlYCkcOUKwCo1HMprICkugokIrIBkYeB2dHQA9zARioUgYArysqCM2vKgFJKT_BUFQc8JKgBCXSRSEAACYGEMDVlw3A05SoB9lQD2yoBSadKgCo1K2lQAhLoAAAmBgBxlwMcqAKOKgJsFQGRScqKgAhX_xsVsKgBCXQAAFAFADRLgY5UASFhuCgLblQRn+JUBkUivCpWAEKjU2CVACEugAAAFcLgSZUJoUExaYXKwjJgi5WBkUgpACFRqOWPFSuOgIS6xpGAACtEwBXi4EkVK0JBMWlFysIyYIuVgZFIKQAhUa_6OmLFSsAQl1iiMBBAAVCQBSy4JcVAmJTyheEZWUXKwMin_pMFskVgBCo1nKZyhXLBqAQmEihYgoggAANEuBjlQBIaAW3KgjP8SoDIpFeFSsAIVGpsEqAEJdAAAAeUgGYuDWlTUkVBP+mDN0BcrCMg+LlYGRTJSzkisAIVGo5FNxAQl0it6RozAQAWpYzAC8XAZSoAADQKgBtRUAEKgo0mA1ERGEBMCRhD4SgAUAqRcFOKgTFJZQvCMuCLlYGRSCkAIVGs5TGUKznGQCEw1ORgACTkS6ZAyAgQQuBVFSOFQDFaxQvCMtALFYCkAcWKwAhUajkUgCEukFvSMAARwqAWKXBYCoMVNIoBKioBVhUApLJFQBUakXCoALoEkD9icFqPI4Ozo6UjYDHgroqKAGHa6ew2KVAtzWNADKFYPRSCkHoVGobD6UghJaYZlIwAADkGCcnMaenHRsAJiwBARFEGAZkisJaB4mTgQRyhMnAskEGsTJwOpdqs9ashPwAAACQ0AqDAKQHakisOmIw7UkVgWRMIwKQOpdCh58AAAALQgCQsEoUAC0kVhLQaFScCCMiJk4KSyQQHxMnA6l2qz1pCE_AAAAQoTUBwApAgGSKw9ojEAyRWBZIEjApA6l0KfnwAAOQ4AYCk7CwCkBopIrBiyMNFJFYFkFWkisDqXQ1OfBTQAAASEDAUAKQAxFScCQIEcY8TJw2lkgiDipOB1LsKFoIIAAsgIjQAEhAwFABbKFYAiCpOBFG7EycFpZIIg4qTgdS7NBaCCEGGIAABChI0HAIbJFYB1CZOBBIiEycCziJCJKFxrLVVYnoHGuhLgiJkBD5sAJCQ3BSnT4BSAGIqThM5AjiwSROGvaiyQSSgdS7VRRp5DAAAACDSejuipvpIrCWtfJE5USCCUNJZIIxMkThZOrgl62VZ6zRCfiEAASONp6BkSRWALomThtlYghaSROGkskEUETJws3Gs1UOaeQwAAmiQjI1R9PgA6SKwCAFScCCO9JE5DZuLJBJKFxrNVBCnkMAAKRMIyNU9BVJIrAT0TJw2ysQQShpLJBGXkicLNxrNVJVnkMP1owA2BYGTIx6egfskVgIiJk4EEEtcGILPhEIYmSJyiHUu1UNIhPxwDQAAa8PT0hYRGRJFYCCiZOBBAYkicCyQRqZInKJcayVR654_KoAcaFgdM4+dGQCvzBEDAA6Nm4ABCpOBFACFScIpZ_8hDwyRWB1LoVZPgAAKAwBckIDbVBEDA0M3FQApD_iMCkBiGGCoDaXQxcfAAAUBgNwwACNH6HTcGWkisBERMnCaQQShBLLOTyGDYJk4XGs1U_IhCWhgAAAeTQyh03ByhUnKKPfJE4TSCCUIJZZyeQwbBMn_glFxrNVPyIQAFwEYFICRihCEmhHTcHFkisAfxMnCaQQShBLM9KqEycLjWTKfrPIYABVAByJBsHB0Om4OfJFZRSDZInCaQQ2FQlCCWSCK+Jk5MTTWarPSCAS0IkMFwBBKDpuCaCpOUUiMTJwmkELEQJwg1WejYCZOTG41kqgAkJ+4xCEgu2MKpbs+CwhaagnAqTlFHjkicCCCUacgO0iLVeejEyROTE41kqg9js9FhA+ufE7MgAyKFkOSiaOwSGSKwOhPCZODUgglCCWTXnkMMoTJwuNZqp+RCP5IwDEQgAZhILQpISxnAMpIrAFwVJwII0kkTg5LJBBNEycLjWaqEE_4pHEAEwUDYHYUHg6bgMwqTlFBKE1ryE_FdECcIJVHoJT4ZlbaqURh5w_C8mWqipSBGDIrKzpiADlIACNAP1FQD8yRWBFH5kisCyihGBSFxrIR5PhLQwAABBC4ACNDGhQCkFoJgqThNJIRomTgWSCOlJFYHUqlEw4hCWhgAA5AU+ENwUAKQ8jRSRWHtkYF0VJwLINFJFYHUuhT8+AADcFAPCQh9CruCwMVSlCsHs57OSKwMkX_xdjMkVgWSKOZSB1KpRCZIT8AAPoUH4LrLgzDhGBwAdJFZMSSlNAgpTyShhNtNAakisDqWXxKVMEQRAAFEHgElFwDeKFIOGIFAlAmSKwahXipOUWmklCaaaaErJFYG0qlUO0PH+FYIiADWS4LgoAUn+zIkpTTmKQ3AqThhNutFI_8VAdSymdSAnpdAQYzYwBBJRcCsigvCgBSTEAEVJym9GUiShhNusFI_AVAdSynFSAIoAAKQLhuCg+BR+AmLaSKySklKLTQlRUnCaaaaCkDaVSsKwRweITSQIsHQNisrYzo4eNAbQqTk9E+EycpoFOJk5YSyBsCpOB1Ls0FoIM1BoAAHtxoCREycnoGEkTlNkshAAyROUAqsNVOUhElDzcS7VRWCE_AAIUZAMINGwa8TJyegXiBOU2eikSRAnJUPGGqz0eYTJw8nGslUOwhPwAYkXAC_iwAEmImtLA6G4iYDIxMAZcJgA30TAADkAAmwArBsbHtxoCTEycnoF8kTlNkwhAlLDVTlIRJQ83Eu1UdMhP6dMQAAnQAyrPbjQSX65FPRZZInvtNO0hDTyROWEsgLwmTh5uJdqorBCfgAEKMgAPqxCQ0blotfsTJ5DPQS32mz0UiLJE5YaqeBCfh_yROHm41mqz0tyE_KSAC7FgbcPQoyD6CZODtPgMRQnKbHhCBLSTCWQBMTJ56eTjWUhKwQQAAtFQoIZASmHT4b8QJ4dt1NGEgPxrxIjpJhquyD4Es9PJxrJVAeIT8pIAKgWBu7AdDE5GNAtomTl6z4EpTSCF6JEcNMNVQghAlFp5ONZ+wrA9AABOHAApYvRgQHwECSJ6dPQFAIE9RpoCUmmGqgeomTl08nGsgwVhoZ5DAABOHCCUiqDO09jYzo3SgIeUjYbTkJe"
noncomputable def WL0 (j : ℕ) : ℕ := (dpk j 0 WL0_0)
noncomputable def WD0 : ℕ → ℕ := rdw WL0
/- Each cursor theorem uses the original no-TM walkCut.  Coverage follows
from its existing soundness theorem; no finite or analytic guard is weakened. -/
theorem ready_cover_cursor (wb : ℕ → ℕ) (cuts : List (ℕ × St × ℕ)) (hc : CutsOk cuts)
    (fuel pos e : ℕ) (s : St)
    (h : U (walkCut TOP BK TOPD BKD PT REG wb cuts fuel pos) s = e) (he : e ≠ 0) : Covered (toCl s) :=
  walkCut_ok lbS lbD ptS hR wb hc fuel pos s (h ▸ he)

noncomputable def ready0_cuts0 : List (ℕ × St × ℕ) := []

theorem ready0_cuts0_ok : CutsOk ready0_cuts0 := cutsOk_nil

theorem ready0_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD0 ready0_cuts0 128 1) (ofCl (RC 0 0 0 0 0 0 0 0) 0) = 26053 := by decide +kernel
#print axioms ready0_parent_cursor

theorem rc0 : Covered (RC 0 0 0 0 0 0 0 0) :=
  rcOfC WD0 ready0_cuts0 ready0_cuts0_ok 26053 ready0_parent_cursor (by decide)
#print axioms rc0
noncomputable def WL1_0 : ℕ := zfNat64 33248 "CqSKxLPSKFisMk0epULFYlyRXWSSPUGFSeS2Wsk0eoMKpKcTLUaiQTtGU9CrRQBYGS8Gyk7QaenACQ0AgFAAcUolQBOMqAejUjwVACmgl7EIAAIulAAPECKmy4HoDCwFEALRUrAFLxSRWFtCYeykRpIrzQjBUaCCMwZkGWgGQLoAJppRSodA8FRDoCUgZ0KiZkisAeinCpWHzyao0EoIGkAAAkNBYgoBgOA0gdU6FSsDFJUKQB7PQulIFRoI81CBkrBnA_wZAyACuIBvNBiQsNjaAhMAJA9cVAGHioAemsCoCo__QiVJ8YRiAABNQp8RxGmMWAAyl8KlYApH2SKwYjUe2ELpSBMCoe0EVxtQTCUQAAsdAsU0ACiugJhyA5AcnZJgBLpMApBPpMB_9SC0x8B7kIBshMAENCHUgTjKJgAHUlCsAUyUKoPXoljNMhUnDTJajSeYGw9DoE0611rRcrA0AAjQnCz1CIAAAZQrPZJQPyKk4USKSR25IrAqJJNrIQBNA0hUABIaH5GgPof8UhSB1wqAIVJyug9HbkisCXnRJpJAc8hhQSKdSfZUBakI9TIaAagHSCFSsANgVJwB6SX36sFRJIoQ+dmVaKsE3rjkCkAFO0IQ8DkWAAm8VAGiioAenJioAc_8Jil58GUHIcgF6OmMqEFioivNTwXM0oFCcACEhUAQkKgP_HxIAqAqIIOPgLoExJ2VnZ0NHQGlAydUAwEE2hbsipnA8OVAgQUgE0FIBZKIQQAADAQA+E4BgIEwMBBAPMVAgR1BUALThRUASf_oRQ8+AAAMBAWDAT4BgIHIME1Ai4bKgGsphAVKwB7_4ubqVAVGgn40IAAAwEG4AxIbAbSKgDaRUH+VYendioJDUQemfAABSBgAJDQBVBsBUwqAKmFQA9LkFQSGog6M+AAAFIOpYTBs42A44VAHHCoP_Lw9PkFQSGog6M+EBBwAAKQUANQBSCXlauRwqd0VJwKo9HikisJDUaDLsyIJbRCAABuCpNIQBeMG4ApAqjYKijFScCqPZScoqThIajQWjmRBAACkNA2NzseAEhoBgKC6BsBq4qAOoFQVUegpCQ1FcqERtPgAAAA1AtYVKwigtDYSRWfgSCyPRi5IrCQ1GgneEIAAI4cABIyHkBqB6IqAAy0NjJFZ65eKo9KHkisJDUaCc+QgAAhBwAAjIVoaCABg3AL6SKwKoj4qTlJKo9F1FScGkhqNBGboEMAAIQcGIbOgBIaAYCgtQbAacKgDqBUBVHoKQkNRZyhEhT4AAAAeZAyFADUA05IrA3i1XZMVSUCqPRSigqThIajQb0mRBOVDQAAAGoBpyRWBrlquyYqkt9joKo9FKGCpODWQ1GgjEkp5DKrGwACEOBmpaBEhg3AihrJFZ_9WKoDCqS32OiaUR6KQ9FScLshqNBGKrzyGAACEKAGiXGpDwDUA05IrJenRZZMVSW+x0FSqPRS0wqThIajQZjQQAAThQCKHzsBiEntyM90kVhdqIFwmT32OiyUR6IKKk4XRrUaCDTPIYAAQgopzEnAYhYBqAKQSAtVyJlURyRWBVHojEkV1kTiQ1GgjwEKGEbE4AASoWAshg3D9SMG8kVgVRPFUlAoj0UkqKk9Yk4kNRoI+ZCfgbQBMJkcAAIcCsJBaQ2AxQVAH6CoCqPQupIrrEnEhIP+0IqCfAFUACAIBdEgVhIGGCQGHCoAzoVB_xWJpw4qrEnEhqINzPgNMxDIAAKQgHBIBqAHckVgCJCpOBVHoHQqT1gTiQ1Ggg+zx+BBKNFI6lwMi8yC5HT8FJGDcCKKMkVh1KoFomTh5KI9FIxipPWJOJMhqNBGJTzyGAAMgeABzhAOJYOQNAaMwIpaSRWHUqklDyUR7CwqJAVJ6vJxJkNRoPVDIggDUAAB2ErAdAwwwbgRWPkisOpVFVEycPJRHpJatJxJkNRIMjDKegFn_aUO1HgXGwGgXIKFqDhuAKQLNHip3RUnAqj0FNYk4myGo0HnJkVpGhgAAaCgNA36EDofAOgBSfdGi7u4qToVJwMI9MsXSmsScSGo0EaCgQwAAWhQAEgZZImCtRg3ASmSKz_TMBZipOGkqj0TAVJ6xJw9kNRoIj1AhgAAJKAxCqRXvkis9YzeVUK5JQ0lEetSKgVFSesScPZDUaCMVunkMABWx8AAQWZDJgGIQX0Iz3yRWFkqgKipOGkoj0RAVJ6wJw9kNRoLRzIghdAGgDRJMAxCqRXvkisD9KwNwqThppo9BCEyesScPZDUaCBSQn4RRyBGYqBuVk7EnMSmbAAMWA8WAGoBRSRWTSqqEKk8lHoUharj2UkgKk7Lly2SGo0EYoPPIYHQAAJkXRG4dwBqAlcoVhOxaGwkisshZHotEkVnUkNRoJXhCAAB6HACnQrATKY5A+hozAiq1JFYQYIKxJSiEaiPQDFUlMpVFtRIOIDZNChPAAJ0RAAcmumTndHQDUDghUAHlJFYaNUh6OTJFbUmYFtRoIUZiApAAFkhZcoTxyDPDBuBFPGSKwghJSiEaiwQ8dgWiZOZaCKaiQQJyRP_OhBUaCXIHgXnacABBeai5JyY_BkBg3Aij3JFYFUkpRCiPbxFQBCpOZSjIajQWrGTtTyGF0AABRWLm7HkMAxGjMB0ZIrAqgFipOFRHoMIqT2UkNRoIUE8f0E2yUAhhAnJsAVI4XnQ5AAK6TABXSYSi7GDOBaSYghUQIedAAAWCgNDxsDbY6hGxRD_xsAt0mAFukwAMFJgAAbHQAAUgoAlJcHJsIQKIbASyKgDORUBZHpwwqCQ1H_qEMJPgAApBQGgI1Wec0ZjEMDGwDtSRWBVlIBCpOBVHolQoXklkNRoIOVAhgABSCgB2oy8mjMIoTo0d1UCvkisiz0simSgVRz2QmPYMHz7JNISiPZSV88hgABbCg7Amxkl4Te5NgtBg3JIRUWkisshVFslNINKJFIMZNDJFZBZCTRyIwHFYAATwoAEKEAMKgAAAAAAAAAAADWEoADjCLLM1k78A8BZAAAABnBcB_wmB6xkAAC4KAE_ZiUpCUABCCQqTgPRXJIrrJRQ98dFEkJVC9x8AAFIKAAMIQHGKJBYxikDKAhMkVlEF8vElrP_g4okUY0bNyiHZDPaCIzPIf_l4qgAAOJD_9WkoN8aM4BQSRWAFBJFdm1YCKNhNHZtJDPQJqcPy7MQCe5MDsrJhdrC1NmTmYB6whFAHhozAd2SKwKpJRAooUK49BVFSc_4zSGo0ENGgQ5XEwAACnMIAkNB6AB7smAenuyYANMkwSEqg5w+AAAwQ8hjhQI4GUNwxXySh0kVlm2mrUK8lkpVvtNHoFYmTm2uyGekEYiEQn_bGIAACwADxAHcIGQFSsgP0PokMBiHqEZ75IrD_ysK0Kk4fSiPRrxUnDLIajQQz6BDOoAAskeQ7DIUcBHGjMBCZIrAJKH0oi+PHYnkkThlkNRJIwo4f_8diSJQ4l0iRYrJWdAIWEDfMhFAYRozmINrJFZB_E5FUkslwNRHqKyoaRUnDLIajQZiNRChgAAtDgBCQJyCAxAe+SKwKsrAFCpPVV4vRRLIpImT2EkNRIIAM4fnKQH4AEMNmYOgMrCAJDX8ExBBexg3AG+SKwBbhUn_srAWQlhUnLpIajQRHp5DAAAJUgTkEBiBFFUVJwH+oVxyJskTz0VimlkYITJy6SGokENscP7SFFBcxgvJ2dBRXMGZERQIogVwJMFQBJgqA_8fFACoAigpY+AAHeHCHUmc6CpF4KQA4tWRqSlQFkSRVJSsDwYR6PMKk4SGo0ESCgQwAAzhQGgazeAAlwD_zEGUfOTAAMSYrA8AAkJgAAaHQAALgoBfJcSCoSwiveOgygpByWeVlSzyRWVgeAJJHIllIQ0WhGaqcRgAAZhRGjrJkA5LLqJOe+SKwqlUjATJwolEe_sKgHFScKotqNBAEnkOVxMAAB6X0sZhOSy5YTm1kisf0rUwkoUaaPSSmUsmhKF9RoIPRCfsiahiFJECkCcfGOjVlzMWgpDkspNZeSKww6hXqJJaiUaaPQtRUnsJVFpNHoQQO5KxRAgSlkB+LssZhOT_Ks45ObWSKwihJQo00egxiZOstk1lmU1Ggk9ABLHo+3INAfx0B8uZgOQJqSSRWVEJKFHO6cCw8dg6iZOFUS1Egg6Dh+XU8ypbAHINioB84nWzIBzDbLNhOfgVJwq_8Vg3RUnKJRpo9G+kisglUWk0ejGUCGAAOQ+AGhxOsmQDmG2UmvwKk4VSqBSKk_6FIohMVp49FLHipOQSqLSaPReiFDmoJQFAExM4IDKVjXCJkA5LK4hOe6SKyk0EkoUSqPUGFTrSROGSqLaiQe7KU9AACaHAAHFjk1ZczCiOSyk11xUnMScPznK1OoyVFhMnFJRptujh+SUelUW1Eg_rMi9IT8HoAAavpLmZ_hSHJZaSrgqTqeUsAK1RCXkicUlGmj0FkUJx6VTdEi+okEHp_ByACqTYAFCj8PnZbSxmA5BHic8EkVmWFYJLKSjbVOHpJR6WZTUaCNAQn4RAomEAK40dnVLGYDkBQpIrAJKFEKkeOxxxMnHqIlYDxQnqJBD6Hzue0EShlPykwKzt2Bo9Y1ZGZLzaURyGWko0Kk5VajqUaioS_MSijTRyG8JFYVRKUR6AvQIYAA8Q4OymdJ78xlwNxZe0ZH0LuGQCACIAQARAAdYiAARYZAAA2BgE8FwfmwdjpuABO0qAul5ioDKPSdBUH2Q1GgrDNgAAG4MBoA4sjVi4DCGDcAUmVWKEDuCpOU2oj0LsSKwFtRoIjc8hgAA1BgChKwB++AN118IjMaSEDFjIDHxUH_kIFIHaaPQUhJajQQggAAuBgPAP6MT2ULwGM1IK6EZ7pIrjNNKpJQk00e1kKlzEisJMlqNBBankMAAFwMEsDStSYADl5MA9OXkwpoJhDShUElKoL3OgAAagwAFyZDmFQGkAmJQrAHpkisUknEC0PQNpQrCSz2glWkIbg0AAAU8yHDKF8loplnJBeskR0fkiuM00UahXkslFJJpo9okVCkJMlntBmKbkaGAE1G6XA6AjsyFgPyz1RWAGIFMSYApiTT0AFpxD56kHEz4AAIQMAbayLULKEsAA6cYqTgBhyRXPSKAiwoXnUjoHqT4AAIQMAPyzjIunwlAYQAAyaTT0BCXWKjqE5CLR0AAEIGABKIGGeiMPdWh8J08OgSWemEG0eOxJhUrwIPR6xY4fk9AACGDAF6MGv9CkBhA4qsAlIph0Ao5IrnpBByDiKF51IsdnIViQkCBFAAgDNl6MGvsykBhAUqsrtIph0ARxUnno5ByLuLFZ1IsdnI5BFIT84h_samIYAKCtGDWbJIpgYQkKrIpSKYAMQmTg5ByCILFZRIsdnI5Eqnjs8_9UgDbh4uJ0VFZcPCQsNqTM7BkGsYowfEYUJyijEKCMomTgCBiRGVSKDkU0SKxyRY7USCH1PIYAAWwYOyepqZ2pDS8LgVQDAQNAYBiC7ELNBMAeEJgAzCRAADUAAAwEEtLf0o2UgIeNlMaT25G"
noncomputable def WL1_1 : ℕ := zfNat64 23057 "fKTAAQ4BgIBQEAdQYCoB8BJagHwAb7OgCKTUugAAGAgAWpwDAQCIYAAAUMAAChgAAAAFQwAABgIAB5kASFgAAAAAAAAAAAAMBACaCgJBFQBIIqAHpOgqAqIJ8PgAADAQAEzIAAAAAAAAAAAABMWAAAAAAAAAAAAE4DAKoKAkEVAEgioD_h8ToKgKiCfD4AAAwEADAQnAYBVBQEgioAkEVAf8PidBUBUQT4fAAAAEzIEIGAMQUBFoqAMOFQA9NXFQFRoJKc+AAAMBAATFgGAghAwBiCgItFQBhwqAHpq4qAqNBJTnwAAAbAwnAYO6DQCwCpWAKZbkisACCQ9lJ9yRWBUaDMVwoEMAAGwMACFeBoGAFoJASkDoJUd0kVgD0RYVKwKjQT8aEAABoGAoAYFgUFpAZ8VKwBSxoqTgD2UonJFYB2o0GYpjQIYAAoAYACQcUAMGwKBDRUBF4qAMPFQA9NYFQFRoJKk+AAAAAowFwUBQCoCl5UAdFKvYCQD01cVAVGgk2T4AACIMAFwUBQCoCLhUAYcKgB6auKgKj_1CJTn0KBYAAADxcKQcBUg8hgLmKlYApZ4VJw_6ZD2UoFJFYQZTUaDMWzoEMAAKQcAVhUpzYBiAtHeUKwBSlgqThhiGdD0G+SKz_TcOajQRvaBDAABWFABwLgmChCAGJj4MxUrAFIpCqD0AhcbQqVhVlNRoMKDaggAAmCgNA9DkijwDELhFw8ShWAKWaFScJoPQUlYlIc1GgjSEKGAR4EgAg0eAYhNAuHiUKwBSwoqThNB6AtJFYURzUaCO6QoZOA4AAe1HmtjxJW_FjMGotFJQRaNUkVhkJk4TRyPRSloqThRGtRoIxWGeQ5qBSaS5U0dk6AaZIRQo9Y8AxCWjvKFYApXQVJwmg9AnkisH1m1RoJBZChgFVDiAd8KEIKDUPBH46AaOVAS4KgAAAQg1Ao1AAHqaLZAgHwWCYKnURABBAfgNSKlYIQUrWKk4zU6HI9EkkisBzUSKMSknkMOIV0mgI0FIcHgUjkBaLUoVgLRSGIqTgD0b0VJwKjQQoJ4_DTohWIphKI2CpODYqMipPTjpnLhQA0BAoAAbhcrAlJiyRWBBGpnC6UgWw2FNBKCAAKAGIuLAGAgTgwSoMgHglCsAUs2Kk4A9zGVCkJLUaCEqQoYAARAAkNAJgwOEMgGoFSsAUsSKk4A9lKLSRWElqNBmKT0CGAAAAbPgABCQqALyFQA9M4FQFR_+hEpz4uAUAAACs+RoShMDAABmKlYApeeSKweg9lJDyRWBUaDMVxoEMAAjQkToASGgH0koDLJUASkAem0CpWH_kao0E6chAAABhAQEkCUgQcKiZkisA1MQ9CElCsCLUaCL3QIZOCoAAFtGD73AAOBJAAiSKwBSTQqTkppgrD2UuTJFY5JrUaCMWznkMqjkALaMHwdna8ANnwCAUAB_cqA7qVEfJFYA9AKFSsCo0EGiiSx8AwAAASj4BAKAA7WVAIcNlX_ipWAPTvpUBUaCXKQh8AwAAXgAkuAKMIE4MAOnYpAmi0mBUnAykUWrGKk4UW9I0Oo0EYkFSAUAAA16ZTAQgDnJFYAtPEVJwq3eYiKMxJFYcSDUUaIksIKkAoAAAAKED5hEIQBXkisCiLR8FScLI1GzGRRa0gqTgRajQRiTc8hj4BgAC_GOB4BCA1HKSKwsgtIwVJw08QYiKMFJFYUR7UaCKBQIYAALgoAAOEG+NBwIiA7CVAANyhWGkIoZskVp2Ggi1GgnTkIAAWgpG1B4BCA1FIWcjJWci4EhMnDSYSKLRcFScKI9qNBGK2TyGjwKqqR04D_TEAAgyQuHgEIEpGyLwRouJmSKw0gQYiKGbJFYxCLUaCLxQIYAEZGoFdB4GFDiMAUgWcLndFSdvCMbQiiuyRWE9qNBCCT3wRsBXQeBsB0C6DiMBqSEkVlZBaN4qTgnm7eEUZSSKykIxRINRoIBdAhtQGv_KwAaQpgYEPsacAJDQCAUAH+nJsRUAPIKgBqQcKgBSCkz4AAIuvAHlUAgFAAbZSB40qciSKwB6J9KFYFRLI4hCh02EgAAAAoQcA+AAmwBIaAQCgGIEkoBMAAFiCYAcdAEUDTHQAAHoGEKhuEiBFQATGUgQfoFTAyRWAhHsxi6UgVGghaUIAANwkAWMqKAOAAmMpAg_QKmBkisbgbCEezGLpSBUaCH3QgABQBwBqSokwiACYhoKlYEEUqvJFZ_MeEI9OUXKxSBUaCNe3I1OhIAAMacvDUEkCAdAFIFNCp3BUnD2isPQ4JIrAw1Gghr0CH+1SAAagkALZCFISBIAF6yoBOJVKQTMbD0AsVKwKtRoJzpCAACkJAFrLhuEgyfUJirEiMGIEcoVlBIopQsVJwU1UeykkZIrCy1GgzFl6BHAADcJBiGjLw5GAOgCkCmhU7oqThZnEpD0OCSKwul2o0ERygQwAA3EQAWJt+mJwaEAdA7WVAJ1KgBlCsAeg3yhWCmGTXUaCdkQgBKAGDMmMigHQYSXCkBexUwQqTillYoj0iOSKyqF2o0ENwhPwCiDsB4FzdCJESBHAOhr8uFIFNCqSkUKI936VKGKk9NLpdqNBHBnkMAAfpkACubKQitQhBvoeAx6VABtipWAPT1RVTQqNBOVIUlAUgBhhE5pAjgC0YPhLRSAxoqkpFKpRHrzyoahUnkOnF37i1bqNBJ7JQKNBL4jwLzpTH04HJrgCQ0PIBUBNhMAJsJgAQSRAAKENgAAB_qkLCqghAAJWTB9AlZMFVD6JMCB2mpBORVBQAAGgZYuEcWpKHAKQmjDShWGUmI3SRWAGsj0vIVKwNpJmP_CLRqEAA5xCANMXIaSsMhaEklIXSYpPJFctDIAikXrY9JYXKxSBpJIxjqBUCOAAEIWAOiXCELQ0EXEisJoVcoVhlJiYckVgBLI9BKlCsLSSZiIeVoQE3_50H9kYAUBcA_4SKwO5lQZQbhsKQA3VWh6QkKlYWkkzEz6hEEDqiF0AyAUwuA0C0Di8JIKQunazKEpIrACWR6CkDKSRidfQqdDQVkmjuPs8FQLwMeAnIAQYjwSYA6RRTZcKSbTSmRUaAqTldB6M_JFYbazUaCHHPIY1ArsiVL_5sAA8KNVJFZMQ6RaPI0tBKSKymkFfZIrks5rtRHspMsVJy21mo0EYkdPIYCDIQhG4mUCbDESRWAdGYXAKDJeKRiUhSnjUiqSzmu1Eeg3ipOW2s1Ekj5zx+ATTrXW6lC8lQADxAIzIQyRCyFQckNh6AxAFr7SpAlm6isCByoCqGQYgAAQhYAP6MWqTAIQBSBVIqY0VJwwgxEjkisCivmS+TRyJYQn4AATxIKTbxxGKIqTk2WxkBaN0kVlWmj10xUnktpLo3FKePXfFUlLNpqtRIIxHQhP5KAE2hYAScsQ9hJgDINuLi2FSsAVOSK1NtX_l4Ho6wqTlUKjQR055DAAKINgB0KrIgPiUKk5NlsZAWjZJFdVpo9dEVJ5LaS6EJSnj3uhVJSzaarUSCMWmIT+SgE0AHeZkwRkPtFwpANAVSULoPQZBMneEtVzMCtUSSL5OH49AmnE26VErO2YDmrgCQ0RORB_AeAyAVAGQCoD_R8bUKgKiEhj4AAAWmrCuK4AkNHoJDIAABBEAAIIgAV8VAANEMgAAD48AgoxSBMD+BxHNQ6SVB0AUn9mIGovIaLnEMpNnp1xCI4HAAADNMi4SYA6AKaaHXCpwRUnlNdB6JVJFYcQ5MV8okGiBkAJGhkeDgAAzEqkisSz0ihYrDJNHqVCxWJckV1kkj1BhUnktlrJNHqDCqSnEy1GokE7RlPQq0UAWBkvBspO0GnpwAkNAI"
noncomputable def WL1s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL1_0) (dpk j 1 WL1_1)
noncomputable def WL1 (j : ℕ) : ℕ := (WL1s0_2 j)
noncomputable def WD1 : ℕ → ℕ := rdw WL1
noncomputable def ready1_cuts0 : List (ℕ × St × ℕ) := []

theorem ready1_cuts0_ok : CutsOk ready1_cuts0 := cutsOk_nil

noncomputable def ready1_0_state : St := ⟨26112, 378143, 28545, 39936, 29184, 45301, 29666, 44151, 29666, 44151, 52016, 168635, 28545, 187758, 26112, 378143, 54657, 406688, 83841, 435872, 113507, 465538, 143173, 495204, 195189, 547220, 223734, 575765, 249846, 953908, 57729, 85237, 87395, 115634, 117061, 145300, 169077, 285696, 197622, 385074, 223734, 575765, 58850, 87089, 88516, 116755, 140532, 257151, 169077, 356529, 195189, 547220, 59332, 87571, 111348, 227967, 139893, 313591, 166005, 518036, 81682, 198301, 110227, 269440, 136339, 488370, 80561, 239774, 106673, 458704, 54657, 406688, 0⟩

theorem ready1_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD1 ready1_cuts0 116 97) ready1_0_state = 53436 := by decide +kernel
#print axioms ready1_0_cursor

theorem ready1_0_covered : Covered (toCl ready1_0_state) :=
  ready_cover_cursor WD1 ready1_cuts0 ready1_cuts0_ok 116 97 53436 ready1_0_state ready1_0_cursor (by decide)
#print axioms ready1_0_covered

noncomputable def ready1_cuts1 : List (ℕ × St × ℕ) := (97, ready1_0_state, 53436) :: ready1_cuts0

theorem ready1_cuts1_ok : CutsOk ready1_cuts1 := cutsOk_cons ready1_0_covered ready1_cuts0_ok
#print axioms ready1_cuts1_ok

theorem ready1_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD1 ready1_cuts1 128 1) (ofCl (RC 0 0 0 0 0 1 0 0) 0) = 55830 := by decide +kernel
#print axioms ready1_parent_cursor

theorem rc1 : Covered (RC 0 0 0 0 0 1 0 0) :=
  rcOfC WD1 ready1_cuts1 ready1_cuts1_ok 55830 ready1_parent_cursor (by decide)
#print axioms rc1
noncomputable def WL2_0 : ℕ := zfNat64 33244 "MbAAhGAIkCQAA0AjxUAAFI+AACkFAASVhHZU8EfExROVAIMOgYlUlJFYTS8uHvCSoCO1UWgAANgoNwH6nBsFR2PhJpkERAAxuVEVAeikCOluYr5KBCAAUURALIKhSCk8HjsmInSheB0Yj0nJhqrHi5eRUGg9XyULwP8jxNENFU4ABRRMW4FSrkMjYICkwARkHlkxFYSDpyYAByB8AAB4OATeVSwNHbPH5MSHFxEY7qBSJKEEvRcrIrCZiPQCFysCW2EimARgABQCREgMROAJDRIB0ACEY_CJAAADQCmFQAXVaBIHwAAAgIqAJDRHp4_JiLQwsVSSOgYlUNcVKyKwmWj0yRcrAKqLQAADePAAVcASGhfjYDnkwARkDdkxFYSBcSYAAFR8AAAJvKr8Xjtnj8mJDi4iMd1ApElCCXouVkVhMxHoBC5WBLbCRTAIwABCCIBHRUiCslM8fkxgKXERjpRJKEETxcrIrCZiPUVFSv_4cEtsJFLWiSy3DwAAHxIFTKkjD4SmZAuUSAkoa3Kg7FYSD3g5UAQjphCCxEJhGAAaQMeBna57g6DLBUAEZD5BURWEh_4qAKyZoPhREwAAAWDIVEVAXZphLGePyYhEY7VBSJKEFJxcrIrCZiPSBFysBx0EtsJFAIjAAIEBN5UioZPH5MR_Fz3iKIx1SypTJKUGUkVhMxHrcyhWBLbCRafo3+jYJTSR7xBOIGJAeJ8R0jExAEjERAksNKXFQENHspiohg8BXR7SEAAKASAZmVhQZBsOH5Ma5FxEcREUxJKPT_5QrIqOSbPbUlCsEhITDRXEpQAAgxIA1RULIdAWoqAGIEEzoVfaOoqLWsKEf_59uQqAkNNooAAKASI8vAJGMFHKw3Mx8TFTxcRECSg_YoXkVhMtHpJCxWZQLCRWXIwAAoBIBVVmqBsNQuITAABUImksVAuITRUAKoHQAAHg4BJhVLyVHD0aO57McmFxEYyTZbJSenMLFclisJ9eXD0HxYrioCWwkVZiVHAAFAJASU2dSOjJ2Kk4LlwgGAjqByBoD+x8AHSGgAOQNAAAYJgAADAQE6GYMwYQhNg6AmpJRSKxYoqIqYQq0VAdQEcnwAAMwYDQPeXCkFAyHiop6PHZEQJBUrJLTQUkVKqezR2OQZkisDaMa7QSKB0PiDQAHgLgVFJB47IiSmKQlJaaCkipVEmaOxyJMkVgbRaTFav0EGCBHAACkFAAIMg5xcASFgVFIx47IiPgKlYpktNAMkisipVHPAjoUgbRjXczoRFAABUgl4uJISCo8mOiIiIShWSWmgpIrVRzlY6NsWKwNoxrocxCKqKdmAMoBtS4AkNAqOujoCUn_ybTKcCkitVHKpj7lxUBtmNdEkIQAAAIIALgILVK45IiCkkpNBSRV9yhXmr7TpfhUrAyi0uj60I4wUEGgx5VgAS1XIEDalwBIaBUddHQEpP_k2mU4FJFaqOVTH3LioDbMa6JIQgAABERcCopCPHZESUklpoKSKlUi5o79kdA1JFYG0ZxgvrtBIpbg6CgEAEIG5kEIlwB+aYQqKRDx2REfgVKyS00A2SKyKlUc8COhSBtGNdjsjEUABYy0Ak0uPR7DxVQ3HjsiJKSS00FJFSrNfwHQMyRWBpFpdoI+UCP0o+Jr_siAKpAnBkAsGQBOqVQSurMxNgPsFwBLYqIrVQpEVHENJ_9aExnw4CIAAAF6MGYLh+AyqPIjoABhUrJLTRhpQrIrVRyW4+lIGkY10a6hCXC4AApBcRcchUeBHRER45QrHMrSWmgpMMVKo5pOdMSKlcdDbMa6KJGCwEwAABZy4BR2UdASkKJKQR4qVkVquFTolIGkal0Z4hDgIgAAPMwVMXSoeOwe1FJB47IiSkktNASkisQxUqjkchXJFYG1IRszrtBMIjRxaAAsCRWAdouBUeGHRERzpQr_8nSWmgpIrVRyxQ+KwWKwNoxrogRCAACENEeOgBAyCtF46FRSMeOyIj4CpWSWmgpIqVRzso6FJlDaMa72FCA0gRwAAIBQBghchCVHCLUSwHjsiJKZbJaaEE6AqSK5LFSqORya0kVxUNsxUCuXyLRQlIdAUhEjJkpsw8dmzsVwyUFaYQXyqAYCJoKIGgCKAKUGgAUQNAAELIgAADARSgAkFCCKMNkSFisZElAlCyAzyRWV2qgKfTE1lrpZbOxWzpiEAAApjQAkjAqAvixWeeSgShZ_2jeYNhSV2qh6joEZIrLKZSzWQxCJDAACEJAASGgVAXxYrPPJQJQs_7RvMGwpK7VQ9R0CMkVllMpZrIehEhgAAAqFEShWElNBtJROypbIo1FJXSr_5GCsdC_JFYcbLVayF+QobCEYAAALJkCoC+LFYSQShGFS3RRqp0kVldqqFkYcrMKk5ZTKvBUt1kgkEGgAhQ2B2dBdFcABqh9BqZEANQBnxEADUyIACEhsAACIKA6HXMCFQSEAAPiEQASEADXRcAAAYCAQQdxsH4sVmAEoIoWaLcY6FJejau1UHMdCkstdLNZCYIkMAAAc48hljjIUhJCKFUijkUl6Nq7VchIyJjpEJIrLLXSzWQmCJDAAIUxAIMgPwYikJIjzh2zJIjhVIo5FJejau1WxCMIhJFZZa6gpYr1kIISQBThEDcDExq8hUCxFisJKIDYSn0SSxXoo1a6SKyu1UijkqRUnhNlMpVWotWyCQQAA3BQAklZVSIJAdAsVg5BKCGijUUg9qv4EYbx0i4kVi0wmVgipbrIQQAA3BRH1JTZgBJGF91w+g1MiAGoAz4iABqZEABD42AAAgDAYKgPwYikJJqDYShVIo1FKwR6u1WuiMKY6TOSKyy10s1mFCEQQAEsEwEooD8GIpCSwY2EoVSKNQikitYI9Xar_xGFfkisstdWwsV6zHJCIICQAAAkNJ6c4MhSEndBtJQqkUamJJFZXSrx5GFlkisOJdqrnFq2EEJrW0oAUgMosQn4B5KFY_pKJKFUh6MNRSV0qgvckVv6TKZxrtVrIuRCfhNADylCsR86ACAYVNAfg1FJWVWBaGkUAfClYI9XaqOWOhDkisstdKJJDyIkMAugADAjYBzhjkD6GekNhSSQSgSh_4+BSsEerpRA_pIrLLXddLVZCCAAcQA6CQs6A_LLGDcUhJBKFUeyeNhSsEerpJETHQpLKQSrWVroSgkSGAAKQBDgT4OplQACSxeAAjKFanh6uuyZgNGSKwPJWQ1SE_BaZS6AABJGPc1wCeSC0NXEwAAZNHgAzqPAAf7LgABpJQAPoD8yAZCkJI9c8iSwqqcRhyKSu1UG9kisstdKpZGzID+VyEabCz5eIoZQA7mQWp5DBf5QrEZJRRQql9zoUldKoKpJFYca7VayRRPIZlNPUGYCyioivQH4MRokisoo9Iv2jIqkUcqAKk4WRBqVci1+OpKc5sz2WulUsiAEB+GmwlEerkTjKFIBX1hn0B+DEFpIrCSPSKFUijlIhUnKNdqumkYcloKk5Za6VSyNmQH4zBqsJdIpNMpdjsSAjIASRgANcLDihbzoDLFQB1CYA6gVFdAFoAHHj4AAqgAfFi30B+f6NgTFisU8dAlCaAzSRWsMeLJZAUlhLJZrIcJEhgEZAAQGuFH4oD8BSANQsxURtpGwpWCPV2qj1joeZIrLLXSzWQySJDKiLQAE9BiDUkVgwEqONZKFV7SMNWYFSdYI8XSrpJGJKGmslUsi1zh+Fmo004mLWL4pJUblZONBdNcOhkfQamRADUAZ8RAA1MiAAhIbAAAQBgOh1zAhUEhAAD4hEAEhAA10XAAAQBgQfQH4FeLFYZAiymizUA6yRXIbaoZgzgKSy10rJc5CAAAgDABlGQTKA_BqKQzObhnTXkSXKSbRRybMkVyEmkkijlohUnCSTarWQCI0NqCJDAAPGbADKkjk4B9DBqKQFKJkcJoChJFYVJrtFCWApCSTQdKtjFVIkPeRsgQAAGoZDzoD8GopAUomRwmgKQqTU4KEsEbkisJJNFPq2O3SMQYLKRqA6g0dg7MjsfEgHSyBnV__I3NzoCoBvAqABSV0mhgkmtJXQL8HwAAEAYRkRlUnQRSTgL1FwAFdJoIRbaSugLgPgAADAQG_joI9ZFrK5NZwUNwIoAAAIQgAEh8AAQYLHYAAEAYCKW04f1WghzVKZPRaIesqw9WuWKwq2ZMpl2skUgjlbhkvVaxa7LWaDVQgg5AJBGzMmwBElAEhoAAAAAAAAAAADMA2B32QwCv_xGqqZBG1CALIAAAIQAQnCV4AADocADGyAkwySPf5KQ5EqGUQg3wLhCD2WhVGCZTKtZIvskKmnEOm9hstZoJCWKuEH+C0ABEABoLMI9CyJRRCDfAuEI5REfy0KgWTKZdrJFA_Jo7sNlrNBdexVwgqKXrqAAOiKes4f1WgjSTKYPRaIQeikKr8UJ6hl62VSKi8+SUnT5rYbKVaDVQYyA__4pW0NqxfBqEUmwD5FoqjOgPg1ipAAHJE4AR9Mpl2s7iTgRyaOziVkrJvpCKpdCOgAPkWXR6W+SiaJlMIPai4QhFluohYolZJoG5NHZYWC_ZazRaqmpGINROoTEAdEUegKlMph4wuEILhCIqZpSn3cXgFLVeihNbKaSqVUb+cPx6ebC9hOBjJQvJsVq4WTCtWVMSJLHugPwkneULYF0ugYFZKRLLtdAFNhMpR16uVUihqPIYAEHAoNa0HC6mNAmlkvMLAXosVgILJFZMhiAUgXQFIdTaVUVkeQwAAIAwCtkYLbXFIDNioDCJUFEKFFRPSyEOioLKJEXrZPQAAIAwHgumuCEaPoNTIgBqAM+IgAamRAAQkNgAAIAwBiWoPQajALFYlJI1Ho9LQqWwqnRJFYlrpZBrhUnkNlrvimKqhRkSGABBwKA6HXMCFQSEAAPiEQASEADXRcAABAGAAtdQFoyCMyzbR8AZixWAORyVQc4VJxKWaKCMyRWBBENdFLIkP_RcB9AAIeZAAa4RuwfAhgsVgcIyHI5KoLkKk4lLNFBdZIrAgiGuh2ESGBZ6AIMNHYOzY6AAe4AUjAAUIAUZAHyYAPPAAAAAAAAAAACJCQKPZAWK5BHIIQDhhUAXFJpSC0MRkxlAC8R8AABAGA4AlFTLIMBXEtpCoPAoQAAAACUACYgAAQBgF49QumyUUM+oQA9AGfEQANTIgAISGwAAEAYAAVmlSMu46CEicBa5WACUn+koEItMoAFCOgAADAQC2xtHyVHKmcPwNuoUwJI5KoLoVgTq0pJtFloHE4l3pCUQQggAEaEgOALReKyB1VxraQqAAADpSEAA1AAmIAAEAoAAMO3xIjj3OH4FEAczkFOKR2EynKaTpVOBPxw_MtlLO2EqqhBiodTCACK7k4fgpRQngDlaJ0F9lI7CZTlNJAZkeOzKFkqoUo4fzmcl0At5AnBedvSuTB4+1C6lFjTMLxYxCf4WJgCIqThOXhEisAcyUAHFkCcAmyrB1kIAACAMGZSZ3cqTzoVdrgGAoECwM2GgBiANGGgAZsNAAQIJgAADARTmNPS0oaAjseQ04CHhtK"
noncomputable def WL2_1 : ℕ := zfNat64 33245 "dQrgB5IjkEAUgNJFdJLoDkAqZPKNlIoWQM5w_otVop21Iy1E3xMnARAuBVakA8BAtgFPyoAL+qQFELpphC4MzE0ANgTAfHgGIaZQMgslWVq4BBAFgRJfKFf1i4whOR7J0+mnEkhGl62EG2lBKplLKdyYMgHEbnjBeVUSytTAph5PIJFAQvPKFdRKoDkmlUykUS6qWwbBw_NpVoOIlIy00ApInJ0pKQADTAAaIB9HAgDBSLgC2nAAA5ACaK3TgAqj+D4AAkBcRIKF4YSKjY2OlMqAaMoiQYCBMCkYhFMMoXwKAFZSA5B6D4qVgGEw0FLiNDAAC+DFrT0+HGgAwqAJDQAABYRAGpSoVsLB_o+82VAFdHZIQAAAAFaAQlwUiqAp0wRgwABdAQIXUmAQIhUmAAUsdAAAjBgDZHQCEuCMGAOwTAMYzFwAAsmAQJBAAAAAEYMHoL5PgjBgF+FDMAAKqGi5WPAFgsj1kJQvAmJhoKI0CGAACMGAQoVAsDE0ADGx0BJM4lQFX_60QgKgqCQTEuk0PgAADAMAykqCMGMIJUMgcimci7kiOSSan4qVhJLNZJJnCpWCUmJdHOuC4AAEYMRteWjoASChuBl1EQTfKgKLFy8AJoVKwLoInKFYHEyl0+chAAAAAqoAkNCqEQPEKgMelwBXAqAuhfAqA4n_1ojefAAACtkQIxKF4AtwULFNt8fCkCyTcDHRJyRWBpMNZFzIUMAADwUAPBRWyIFXlC8AWgRBSnj0cZIrCsk0cnxJFYWkw1kRchQxyQUAACtkQKvKF4AtAiClPHo4yRWFZJo5PiSKwtJhrIi5ChuQFgAAEEWgWNlTlC8AWgIxSnj0SZIrmwaOysk0cvpJFYxFJpMJZII0zyG6pCAD_xEP_ERJDSGDVRZQvAFoU0eiTJFYFkmjmABUn0ghCkytXXMZZIINTyGcoyAACkApBWMDzujR2Dsi5WAUcoXhTRNnQpAsmiToUhaTD+9YviMkKGMQCqARANO8NHYNoLlYBFyheFNBSBZAUgZQQMV+sjskJ+MQYh1TsxTJKiVHQgQT+ULwBaFNAvkisKykdOqCdClDBkWkw1kRchQwAAmjQCaNIEE_lC8AWhTQL5IrCspHTqgnQpC0mGsiLkKGIYMgAAAmXCaNIEGlFysAyRQvDSqcCkCyLXOhSBpzsxf_WL4QQuICTnz2AA2uIEGMlC8AWhTR6N0kVgWSaOXbFScehlfkxXyyQR6nkMsAsbRyf9OgaRo7AEBDwEEhBCCryheALQOlEejjJFYBlVLZNHKYSRWQm0mGs_8QhcJUdLwkAAE4AnmgHcsmyQNgv2VAAmMl4BKQLoTMKlYHEBTMXTwiEABPRSAZDBuUEwbgtguVgC0Kam4+djjJFZYSyTRyzQqTlFNJhrJiEIggPQICEQMgAHSD9VQBIaCrMgXQTAaEOgCUgEZAAmlRjoAAA6g2BipQvAFoU0FI49mrIyU6GuoUyqWmwl0bCgQ61IwAHEFINGYNwPkXKwBaFNSAfOxTg5GsJZJtmDpkydPKCZa6WQSJ5DCKVQoggFSmJME0xAeRcrKSMU+FoAmYps5LySK3NNwWSaORsJ0smjky10s8KRp6JoRiqE2ilEswJyHLfmDcCJFysDUxcvP9rRRDGkisstZpo5ppBottqpdOuiSxlI0MiAkAApAELHMG7DhxHOXUlC+g0mei0LNNXwfO3qFScsJZJo5D8nSygmWullQCNDnoT060WcuKIj5LwIKH2NOACy4AlNp0RC0HulC8AWhTSHHQpAsnejoJ5IrAMjBpMNZHcoEMUgDkNIAJBIoB6Ox0BbSheALQHoKQqt7U4j50UsoVhabCXRr6BDA2k5FIABIaCGHgveVAC0AceUKwrIBRJFYWkrI3w8hgYb4M1NKqFQMgA3uAFzQYMTTouJIAo6jqVH6jIloWoRgKpQrAugl8oVhbTKXQiaBDNpBCggH7kQ9ChOAgipWAwMoXgOxOhSFVB9ZIrJoYQsjvTh+bQ22WmjzyheDM6Kzo7N1I7KkoQwqgGAgFEDQBFAFKDQAKIGgAFkkQAABgIpQLzVAAaIbgYGgcAhSYC6AgQupMAgRCpMAApY6AACkDAJEOhuBgHrlQDEWgAgyop0VH_IIeiDKgAul00IAAL4MHoPaTiJBgByADBAjg9B6LRrRQvDDFg+d0nJFYExrpBbshQwAAvgwD9D4bgYAUgSQfIQGEfGXFOioKIxLkJATEkleEIAAKQMAA5CAJGQAEuDSFQAATMfAVRzBcBBBDhUBMSaAAAUgYAEKEGSKgCQkjQUAAJmPgKo5guAgghwqAmJNAAAABChB5CpGgoAAoofAYSWgQSq7ROwKVATEmj6IgAAjQkACFCE8lSNBQABWjxn+Q+Aw_3VuJFy8CCVT6Ik+UgTEmiEAAMIRAAhQhM5UASEkaCgAJKH1Ej4DCEeLl4EEq7STpSBMSaIQAAABChC5CpGgoAC1B9RA+Awm4SxeBBKu0k6UgTEm_+IgACC0RsbAzAjMDUgjwqG4GlUzAAJmPgKo5guDaQQYwVATEmpuNgAAATyVDcDSoZgAKIHwBuVMZLQ2kEqu4TvelQExJohAACNCQCeSoiQYyg3QuB2LySDIehpMIrUsXhtIJVMwmR5SBMSaIQAAX50AnkqG4G90zAHEqAuofBpKopYuXhtIJVMwmR5SBMSaIQAAGwsAzkqAtSw3AxlAAokfAHZUxktDaQSq7ZO9+VATEmiEDaALyIibmxmBsa+3LQAkNAFXlC8AWg9ZspTx6OMkVgtrJNHL7yRWBYPnbtGsw1kgkEAAAZXXA0DFkHMkQA1AHBEQAOZIgAHwGQAAGgYAlBgNpsSheALQJtnj4cZIrAsk0cvhJFYBTCYayQQPoEMAAEoMRoG7ZgAI0MoAAAjRmBKE4_yVA1LrXlodEVKwMIXSwCELqGAAAP2zDKCWx4jIG4yXklJpBa6SKya1mo_0OmRkisJptNNZH3IUMjgcAAAa9ma8WLIGOHEYEtP6kxNILiyRWDUsmsUK45T4VJwkmEylkghgPIZFAA14sTs7GgW9CAAjQihpYsXAQWMF4UUNOUKwHoZ9mdCkDiRS6CZQIYuoYAAE3D4LFlQAtAGgFSsNpdALJQrAw3SZi6LkQoaci4AADom4fBYkqAFoA0AqVm0hjaXQCuUKwMN1GYukH0CGAAG4WAxHoHQLlYAtByNWMmiePHY4yRWG0sk0cmyKk4UTCYazuxCIIAAMQosxNw+B2hcrAJEULwJogjoUhtLId06FIGEwl0Y8hQ06FwAAB6B0C5WALRszVjJonjx2Ka8mxtLJNwMdMnJFYUTCYayLgQoYACjCYHR_w+A6RcrAN4ULyojUTVMHQpDaWRU50KQomEw1kPAhQ5XBwAAArHD8JSBnT4WgTRyQckVhtLLrE4co8Kk4UTCXSyEQPIYxIYmmUmgc4cNgY0dBYsqAFoA0AqVhtLoBXKFYGG6SsXTZiEMSGAAAGZAAYkHoLoLlYAtG0NWMmiaPHYpDaWSbgY6ZSSKwomEw1kPIhQ5XDRgZKACbh8EpAfcWKwJrujoUhtBUqWwQWSKyKGEu1kUseQwuQwaTCGUS4GReZP5CxuDx2EpAjJ8OYoXgTRycckV2k2lkmjkCRUnJpRMJdrNHkIggASQXgHgNnHwNiEEellOMXKwBaBNcEcPxxkisHJZJo5Z4VJwkmEw1l+yEQaKADUDoCyj4GHlC8AWgTR6KSCOSz3hOwMdFHJFYDjIkmEu1kSQhQwDiAAKAOIQPgWKcOwBSFFAJkisHJN_odBLyhWBlGJdProRbi4Aancz4gQLBg_6Y+LKgYuVgC0Cano4fjjJFc5HJZJo5UkVJxiSTD+Jct1kgkGdSUBxCGgdKQGYJCELd+Tgs3qEgBqUWk+CRlakisCyWRzJ0kVhRMJxrOekIAqBDA6F0YyUJcCrIQhCzVkYNNOC4AYgDoipWA9CKfzoUgcSCXQ2SA_CKbQH9JEcGEchKQIMtLCTWoHjtXBUno0nB0bsZHFS2TZ5HDeSikomEulkeqcQH4WTaXZSDuRoYAVbJig+DY5UAr0sZgDpCpWWUbiyApAwhdCCUSjbQJdFQAyDJ7g+DlZUBLQounASSRWG0sgKskVhaTDWQF6BDIpZSE3AFEHQhCZGNQqooKlYUSCAQuXmEJo5fEVJ0VMWOwlUmkuOG8lOtZMJdREtVx6PZSVTb3RYvykJkcPypqbGZjwVTFAsHQF2KgEgFwBvwqAD0hcBhA_wfCqCgAKoMIHxZWCFysAWlID6gj0cZIrByWSaOV5FScIthAEwX6yQRUoEOnQkAAAIC1FgAIUHopMqei5WEGojknNNHqLyRWDksk0cp+Kk4RTKgBivlkgnxPIcjhIHIVBEZMAAJeBziwdqKEySg4ngLlYARAejICpOREsg98kVgYQsg9FUFA1P3PQAokZgqBtHD8JSA3woXg3ZOd8dCkIpVBmJIrKoRBhuAvVkHodSqWZyGkIE4i0VDNNHYI8KlYT1xBYrAmjloZIrCKVSaoo4byUs1kul2qhMjh+HUqln+p0GkIE4UzYzKwIATmsFJh6FdyoAWgD5SGgFSug9cOqyAkyhWSS22EugkUCGEQqgAACGJB4+LKWQuV1kBaBNQweO0skisCqTRyRwqTlFMJdLIIRAfgWS7_pOoKLChOABJiAA1RUyKAzLgA+RABUKgC3REAF5SIADMRkAALQdAtQWug95A+AFBUrAIoBKQUoqXxAR8zcoV1EMJXRLCFDII5Jo1ABJBg+pQwf0UJQVKwnrUCheVQmjl05IrAqk1Uh1Jf8qVFLpdqovY4fl0LJdOIJYgVkrgjM7OgAFGAGoQBIuAGFQAEWAYCAAAAAAAAAAAAwEABtCAAShlC8AFxgvAcgeSRXdYOAqORyxMkVgSS6RNYtkEmgAA2BgNjUOdJQhhVAMBB6FgUQNAEUAUoNAAogaAAWSRAAAGAilACRkASFilRIHelRPTRpMUkJSUkkg4j52doqVgFdJeoQAAABIaLnEgHeULyeghCZOUmci9CpWUkkzmcijJFZJaLPS7QSFI0MAAAeUgBIaLnEgHeULyeghCZOUmci9CpWUkkzmcijJFZJaLPS7QSFI0MAAAAkNFziQDvKF5PQQhMnKTORehUrKSSZzORRkisktFnpdoJCEaGAAACAEhoucSAd5QvJ6CEJk5SZyL0KlZSSTOZyKMkVklos9LtBIUjQwAAGxsA6FwBIaA1FGG0VAAAdYqCEgfYqAP8KQAAAAdC4AkNAamjERKgAA0uVBCT_yV4sqACiGSKgAAAMJcCYyEREqAABTxcrCEhJlPfjYAonmOmEFx342AAHR0ERFwDSiCYGcobKwGAjB_8aAFIZ0qCEjkReVACUojkAABMDBqBXioASFUYTTAPhKZkABJQ1iVEVhIPeAlQEdMIEBCABaAMwEynCDGwAIRgCJAkAANAI8VAABSPgAApBQAElYR2VPBHxMUTlQCDDoGJVJSRWE0vLh7wkqAjtVFoAADYKDcB+"
noncomputable def WL2_2 : ℕ := zfNat64 33248 "CFYIoj4+ds3KFYEUrp1NCAAc4TAAUihKD4KpFwDmBguABSKld9lYIpORSVUikkuwRQnxIUMCaAAN0fAGkoXgBUDGhMrIqV32Vv0IxFJyQEkVlVIpJLokVAhgxpk1gE0GQB+LAHLli8AXwobBaZc4diWU32Vp6RScnlJFYTSKSS6QRqoEMKofBSJY9ccRAdAeQweMXLwEoZAEqnCpXfZW+0pEEnJ7yRWF0NiA_KyMxCIIdQskkeusID5NioqZgAOuAbS0FQG4CIAkeVAhAhUVYhUgyhdK0IQAAMQoAxDMLIH0LgHIDiMAlIEUtofTIKleI1IIpXTgaEAAFkKA0CcIRUipTC6j4uADpFZyCILlZVBLDR6TEoViMTigimu0EFKBDAABMFAFEQgAx1QSd_pSnkEu1tLgA6RWcgiC5WAlho9JiUKw_ugNxTXaCCFAhgAAmCiPBeOG5VAdpQvADICqi5WRUrNK3FqBSMTkUmEIIXQWiFDA_oTARAHgDSGE6VgyEXAPAGj4BKQukUnIpxCpf0SiK4JKrpI0IRyNDDCAAAbw4VQTmULwAyVkkgXKyKlYWSKTlFJIrxSpEkikkukFPKBDN3EhMAYgNnhGjsoShXBRZQvAeBMHQBa0soVmkIJOU5kius_0SiCVkfyEQRBqtfIoQQagClM3qLnrKlsKpHSheApEJ_9YrgtgEVKwukUnLSyRXcSSRSTupetkEgldIpdIJFRQYNwPlwAazAAkIAkZBkIoAAseADNDABSB4ACsjwABei4AAwgH_DkaFlrKQNaKgAAYuVBtoM7EoWcVAQRKYQAPIISSIYAlSHDdayhXIIBcoXhBEoZMJVBaKTSo9UnkERScO1UFSeskkgkmsihPIc9CKE2ij2Wo8ADqSAw0dlUFnlC8JyFisMgSkUmkR6tSQRR07UoVJxlMQVSsk9CqeTaUSDNQZACw0EgAcKgFGjwAqAqG+NwC1CoArIp0+IIZN4KwAAgTIYi7IqsAtAjIGFC585QrKzQScnPJFZ_FOoIXQ0KBDCNJDLRYWH01B0PF5UTsQPnhAEjJ_5aBG5EAMQBURMABuCIAACRkAABAGLHDAkbUHUpgTz4ABuEQdAnvVyqogCkSRWfQDKFdOH4AAEQYAo1lHxNShCBAhMAGQDdBUACEACiRwOgABQBQAH7IYTKKDKF4AZ2CpAhgue0VKy6B_86KJxCCF0kCgQwAAIAwABbJZFZQysAABgcNgFEioByFiFI6hFP_rRQ8+AAAgDAK3WhBlmRycMQAc7AABA0mAB3yUA1AiAdAABuCgE71Il3ZJIZlYAAAAAKkoQAFtjIAAEQcAAHaEhHQgyzJBOLILhCgAAAQTAAGCIAAaWdAAAnDgAPswAJSAZpQAAAAAAAAAAAAhNlMSdF8+A3ocBlg6AAAFpJACqQOOgAAThwAOIMAjFfK4gP_EMwv0qTgDEA8CRHKNlKaBwTKZulKecQihZBoIUMmi0Asgc8vX6LHD8CFlScESHQxAIJ1VCmZQKam1MnnEHoY9Qrg9MJdoIXQmRgvJMdBwBCXAEyoAlPAAAAAAAAAAAChta25BrXMYtMLwjBvgQYkkWlUHI7yp7pQrsv9E4gk5PonTzqVR7NayZdEjkEACDgkBYmehYeC4pTZh47Ng3AwmToEXmwFmEgCZioAFKFQBWRZZ8AAFIGIklJwDeXDcDAARSFQAALDKgcMxAx0qAC6KcQgAApAwAEhIiQZmQ0FDi4AMgT6LpSEmsi0BzOH4pA2ldMOoQAANcCSBBoDIlQHjhoAlI4pKAes1KFYG0_euYzNaEAABAGAAkNFNDQUOLgAyBPoulISayLQHM4fikDaV0w6hAAAKqDRKfXFwAZG9IQLVMFysJJZATHzsUgbSu9JQqCXAuAAACy1FMDQLULgAyBIQulISQcScPwmlCsHZNxXSgk0Aki_R4HQAk1ABiFQE9hoAXAVE9AY4VAFZFlnwAAQgoYqUq8IQNRrlC8AMgKaLpSEkD6nD8UhaT+zFfRChebQgABMjwKKHkKGDVK5QvAYhkIILTMFytPasSSqTkVZIrB6aUoKxdILfEKGBBAEYLEyAlEZhnChA1FmULwAyDUfsXFILlYGSSPoPnYpBqYSrXSCtpChgADdDg2ZElkEGqfyheDGioMgC0YxcrNPIEoE0HzsU1kNJXT9aEAArQiAAIFAEmSylHkMUjVIZQvAIxgrDJZIILQ4Fys0kkqk5MKSK1urQ9spVLpBXchQwAugPsJRB0CGDVP5QvCrRkGQBaBQuVmkkhOT5kisDSF0HKgQyaAdf+MU6SolZ2zE00JCg0WjkV8ZBkky0FpSC5WXaKWQtB87FISbTZNarpy0KggABHCgPj40ADepOIaCMp64XABkCbxdKQklkdWcPxTbQ0hhA2hapQgD_yEeCPgAG9TKg0EZSMksXgAY0ZhkIO8kYWieLlYSSyTkyJIrto9NNNLpBc+gQwAkz0jQ4jBUtYuVnUFDZKQslC8DiGisMlW6SF9U+FsprpJJ7OU1kissj02hdIJJUCGAEE8IfABQGpVKgLChslPsC4AM9yQgFpji5WUSSAAj52KSyG0rrFEKgmkAgjUGpypGwobJSTEoXgNQyA5Fpgi5WEBWAczkfZIrLIBdDDIT86k0CT_c+bkSIwdFSkVxcUdKRkIkGYgNEpAATsfD0uktKF4E0Hr3ShWAbTDQS8I0MAAL4MRJOADeYbgYACpMACYiAAFkxTIuAAAApHwAAUgYAPpcNwMTZCP_lRMDoACiEFYZUC0AkJUFZC6ICQgAApAwGmoAiQgCQ0NYNEpV+XAAAhouVgA9WSUKwAw0EZiNDAAACmFwBIaBKZBlxGZMm1BJaRQmxcrJDRaKPUPlCsJCWEigsSo4AAGICjrgeBqCEQNRaAAf4WL7nC5WB5FinD8UgFdIJ50CGAAB4GAN6hA8DOULgUtgOgCqAWVAlC8DyD2IpUAITDJpGoIAAHgYNQBChA8DAD1KgCSAb9KgDex9KQuAfFdNGoQAAHgYAuyEDwMAtLAbAAAAsmAm_+IgLIwAADY6AAA8DCGXgAFeARlwAGiB4GAAgdAUQAF6TG9yIAX5MAAAAAeBgIBMwLAuB4GIoCKRHYAAH4KiQgIcKgCsg_z4AADwMBoG5KgC9EDwMpQ0ZhdWAXEZ+gBBLQYsoLlZISUj2UgFhItJUYAADwMABJGDZlwCzB4uA_4TEtQwlEpJCSRIZw_DAVKwJolroeVCAAA8FAHMLgCQkAuuQLgHIExLQ9iVYMIpCSQeykCbNwmMIQ1CAAADzFwCz0gyIyCUlqIEolODCKQkkHuICpWBNEqGmK_QWhoQABOioAuJcB3kgGGsBcBPQmJaD8yoqg1ISSDrSoCaV0GwhBBAABE5cAs9IMiMglJahpKJTg4ikJJB7iAqVgTRKhRiv_9QmhoQBQBR58DczMgSsXHAhQyqGUdMImTBmRkEpLSmJUclJISSMSQnD8UgTZKYSKhxKjgABRDgdBRZdAgWekGRGQSktRAlEpnylSEkg9PKUK7KE0SoUYr__UJC6EAABgGKkCD6waQufQFdFwApAIjlRIW2JQI5KgJoTR1HQAABgGACu3ArTIlVgdANmIAAABRMSEAGoTQGTEEIYgAAMAwHgXZGCkF56MZiYSSmDMKxlwR0JSWkkag+LlZISSMR6OAqVgTZKYaC3hGhgAAfBgF_F+oIxFZGLrvC4AdBArqotCUk0QkkAKcP0rFSsIlJEphdgjAAAHgYMyk7qbMlQzGdACQ0PoTAp0qAGoBv0qOOrwPwPpSBNK6VKQgAAToT0TArcqAGoAdR6Un_F4MLHyyShWBJK6bpQgAAIAwLDkwKSilC8OiHQ1CaRCIj8pK7MJKJyKQ4k0ro70KggAQcCgAAmQ_iuCEPHkwAAcZJg_0fB48mAA00dAAAQBg7I6WYTA0EqAsoBa8qPOMQGfyoCiV0tQhAAKKIg7Q6dyTB1wuAMoAwyoQhUrDCE5MGUKw400ro40KggAEKNgB44floKk5KWJlC+Wk0imUJpKU8FSsML90SXNZyykkVi040mmhDWL5BIITUCGY8TIqEh4eAEhoS0iAAHoAowqCqdA+BXxUBRAKsfAAAECa4AkNBCC4UieAAHGSYP9HwePJgANNHQAAELEVoCY8WZVUBqDNnAAJFSsMITlk5QrAoldO0oQABGhYJqJFaCCZOTE_6pXAsmUJomAuVuiKlc1rpJ_ebTlppIrGJxJpJFasXyCQQ7IhaAAmwkcKJiYmcVq4fOOhqE0EMpFeMF+ik5A2SKw4kkLsGkKgxWFgAALRKNGMmbx1SuA5GpSQ7xEfAwVK_IMxdopOVvkisgm2khd_ohWWQoapBoAAMykLAA+WWjJiUjjKF4DkahNDGjiMCxUrK7RScl_JFZBONJC7+5ChIhQ+xF09AAG6kH7VwRBwhCSgAB4MmCnR8ElD_SkB2A6AAX4RAAXMgAHioAVzUAL1KizDZiAVcVFEAujFkIk2GPgC8gCnaisCYLvFwBlAuUVBKKlYhLoTkhZIrIP8HIkhdGFIUMCwTABBCkA6I3TGwziRWaSS9UoXgK4WL4BKQmiklrNShWfyciaFE2ehAASQVgJoRyBP_xulLri5WBFMpSRkBUrMsVKzSXaKNZy3MkV4XTKdpJMqE6skEgl+VIANoA2YpxQkGjVwAEWCIKEII8Jk4ARCQgFAVJwqj0JKBRAXkcPwAACm7METrgCQsEQUNQEQiOwDKAHPJgANITAAHUOgAAEaDi2ljMLKxC5WBFMpSQUmWKlYXaKTl2pIrLSSdrJ1ZIKFTyGS2EgAHJ6yxmFlEhcrAakEpI7woXjDKFYXaKTldJIrLSSdCJ1ZAEhEEUDMUSCE0ZacPwUFUtiKMl89LINC5WE1EJg3IM9pIxFIpJJdoo1cYdO0hFScs2kSqJLJtZns9CiQSKTR6tQ+dgAF6iCSxnJSyTguVhEGpBNpNBSRkoVhhpJOUAFSc4nEknuRpdZILYkJ+E0gkUmj09Bw_F2iqmPAiCgpFwBoKgAAcgAhI2YUVABNDqHwAAkjoCQIgozRkCFSoA2gHCKpSFUCBnD8zJQrAkldM6oQfQAAGBwwkBfBRQBQlBSsQuVgUSSDwRKZd8cNoeLlYYaSLZyLMkVhxJJFLpBbEhQykzEUmEAGCVwIAwhCSgAB4MmCrTQ+CSgUQNMHRVQBMhMBLNmAA1wTSmKAKGoCIRHYBtA_8XFaKgggRYKgAGkHwAAUiYADlcCANkpWCiAG0D_RFF8qP_KwGgCoCiF0wCfFVAEyEwAoa4AFFAgDF8KgLUnAf+agDKZUARkACiJfNHwAALC4L8IhZljMLJVClSUcBChgSkUldZmjE5IamTw2kkrICJCflVopVMtRO8TJwDEgItC5VK4BBAFMpDCDAzomylPFJbBKC6G2Qn5VaKGU0GTCeqAMl6oUqqnHUK4AeSI5BAFIDSRXSS6A5AKmTyjZSKFkDOcP6LVaKdtSMtRN8TJwEQLgVWpAPAQLYBT8qAC_qkBRC6a"
noncomputable def WL2_3 : ℕ := zfNat64 24171 "EkYBEVAAAAAAAAAAAAAYCAAAAAAAcHAAAAABgIAADg4AAAAAAAAAAMBAAwEAAAAAAA4OAAAAAAB5cASFgAAAAAAAAAAAADy4AkLAAAAAAAAAAAAAQlwBMqAYCAAAAAAAAAAAAwEACEuIkGAD6XAACkNqXAFFJFclesXLwAmpDEqOAAIkGAALfAGC4bgYOgBo2AAAABE5UCBAarjQgAA3AwAgKobgYBfRUB+AyAFhFQAL6KgOoDPT4AANwMUtfSwMeFfjYBgIBKAwDyIASQUAc4QgAHoAgQSDEAAAYCAosRAAQoBgIBKAwHioASQUAQGOgAcr+OgAEI5AAAMBFWAAAAAAAAAAAAAAODgBJBwABgWAABwcAABAaAAAMBANwJAGgqAEMFACZioAFKFQBWRZZ8AAG4GAAkFA2BwBoKgCFBQAkAqABNhUAVkU6fAAAAB1oBaVAAAAAAAAAAAABsDgA0bA2IiADfpUAfGPpSAV0gohAAAQBgAl1QDwUAEDoAD+j0AACoMgABXHQAAEAYAkicDYHATw6AOgH_yIAApRUAK8Xgqp8AABAGDcBsDggmVAD0LSPOKlYUl859Co+lIU0rpnNCAAAgDFvS0orGhsCAExoAAgOAAABEMAACA4AAAAAAL4MGwOCCZUAZQ4fhaR5hUrCkz2zJ1KQppXTOaEAAFvS0saGg3AwAGjYAANKlR5IWHIPfDlQBXSCSEAAFIGAiQbSg8ABRAAnRcrAHIrD0R5QrAKCcGH_6F_lCAAC+DAAlTiJBgyAGjYAAEOFyslEJAPSOlCsAMP_0L9KEAAF8GC8IkGfMJAGEoXgH0OH4WkCmUKwpM9nINyRWFNoJdIJJEKGAAF8GLevAFBURIMaUWADRsAACHC5WAD2mBUrAUhh_6hcJQgAAvgwALEIAQfESDAAYNgAAQ0XKwAe02KlYAYf_oX6UIAAL4MACgqG4GDUHABo2AADSpUAD3w5UApK6NoQgAH+CQAFSoAGLESDAuDgC8ZAAAhouVgA9WSUKwFIYaCfRGhn+SIAAALFQBIaAwDgA0bAAAsMqABQBUApC6NaQgAAAER8CILABo2AADSpUAD3xJUAV0ewhKkFgAAAnDgA0bAAAhwuVg8xCB7TIqVgBhoPm0JUgsAAAI8qAsDgG4ZU5FgAyfPHhBxcrAEy0es9KFYMQMNBXegRwACOBwAjitIBKexMA3DIAAEOFysATLR6s8oV_kCgDDQWhoEdUgsAAAHMqBCEgG8ZAAAhwuVgAwEFy0erPKFYUQMNBaGgRziCwAAHgEIqAAYNgAAQ4XKwAoPVllCt4B8AYaDkNCCENSELgAA8UlJfXgBsuATCRlDw_kYAMGwAAbfKgAe_dKgmgYSeqESQugAAGy4oBZdQ0SUYJcAACHC5WAD1Z5QrCaBhoJ+EaGA9ABDAKBUBkEoUGj6AGjYAAFhlRiBeAY6VABdFiIRZCaAAUQsuoeBqDYuXhJq8fAD0OEXKwggOKh6PRXlCsMJBELrmOg0EAzED0AAAEhAM8ZBPKgAJIaVKjhEw1AIPfllQIEro8hCAAHIZABRKiiFu0EQNXJFwAAIcLlZGQD7YqHqzyhWCBDDQXSoEcPwHwAGNehk4D+KkaEg2BwITMgAAKEXKwAeilKFYHuRYw0EMCNDBAmUyjynruAAPaCzhQpBwbA4AIHQAAAAERCCIVBfpmCyNBSALIAJAEEIOCAHAlwuADoAlUkXKwBjn84fikArvAEIgh7JmC6UUbkisBCDggBwAARAihXC5WCvCYuj1HZQrACGMV8oIAXSiuMmIkBB3wVhwAAzIAAESFysAaQfOxSCBDDQShI0Ma8NC31SsUSCJ4mABCXAdCooBYADBsAAAai5WABB6hsoVgBhNUoQAULv_E6iRsAH0qBgOAHMZAASQLIXK5hDwAQo5w_FIBXbIIVBACi0uk1yBo7ADenAwFBsKgAwbAAA60qACtpUAF0vshABQuh+DIA0RUjQcOUeADRsAtAJob4uVkdAJPZSAFmlRs4tCAChZIfmwbmJOM14rMjo7NytiGhEg2ChYDyFwEmegEkohcrCxjEGLOH4pA4ld2mhUEAAL4MAMsqG4GNwJA0g2AJoAPEqAAZxUBphJdBknwA0AAQMBEgwFmC4yQVBXCpWAGiKlYEknJbyRWBNJpdIJQ0CGAAF8GAbgYqQsBiCoCWZUAR9KgAg0VATQulmkIAB_gkA3Ax6hoMvFwBejJWASkCSEAPnbOShWBNK6dpQgAMVEQAEhoJoWAsBUBDkqAInlQAPwKg_8nBdKwIQAAAbA0F8C4BdxUrAJSBJJyAUoVgTcQJxdjehLeQocWAYAAEljg0G2i4CUgAECpWBJJyykoVgTSunwUI0AlABUhoAEKFWikBZguAK4VKwABBcrAkk5GKSKwJpNLpBKGgQwAA3DQAAjIGvXgIBQCoCYJcAQtKhaAPQKgCf_TgumlEIwhMAAB4ABDQxFwFmi4ArhUrAAEFysCSTkYpIrAmk0ukFhqBD_EdAA3MiAGpAhC2jiIBHlC8AUgCkeRUrDSSScoVJFYE1kScXZ5IRBAugpDcHkMGROwiDFBcAuoqVgEpDSSScikCbMhOLsd0JMiFDLIVAAAcIRBcguAJgVKwB5xUrAkn_zooJIrAmiol62EEshUSQonUwy5KiVlbGPATAdS5MgYcRhI8qAloBv0qDE6UPQPpSFNK6VwQiaB1AAKRQ2rIUNgD8oXgSUB1xU3koVgE5LCSKwJJWSCZ5DMIQf5txRD7jiMlx0dHZOVJyUAYCFFDASI+D_y1CQAGxEAALCIAAExkAAFIGIkJAB5cASGgAHCoAgg0AIgKgASQVAH_VoTqfAAAACS4AkNADIlQHjhoAlIT6Wges5KFZgTSV0vqhAAAAYS4NhaGgmIuADIAOQuVgWRvx87FJgTTD5iMPmUKggAEKMgAnFz4IYPCaJcD_DRmGQIoxH4XKwLIso+dikwJpMNdIIvEKGwQaKCApwaBkAclwAEaE0ihMHA2wuADIBKQLIHM4fs5KFYGkrpYlCAACaRAKhLgmc0ggAeKgCEDQAiIqABJRUHQKyJ3Pi6HQAgg7Ojs6A5WYDfXBF6YbgYAARRMHQBzEYqKSBx4qAP+Nxwk+AACkDAABrgCQkNwMQxSAKZUAdgaAN2lQAPf3lQBXR7iEAAAARMgflIAplQB2BoA3aVAH_j795UAV0e4hAAAQBgAJIwjShXDBhcDxDIMgC1DhcrDKWScgJJFZ_JqNpXa_IVBAAg4FAgpIVKYUe5Fwf6MgyALTMFysMpZJyUskVi+QjSbcmKxdIKakKGABBwKA9ZOAqxUD3ioMgB2ir+iMAH6KiiABZT4AACAMH2pE8okkASZLGyWLwchyKGYZJIC0jhcr6UtBVns5NSSKzCZTaVS6QREoEMACDgUR5TZlIyh04NwMTQ+AKBsAAQS7JUqAB6IAqVgFdKqoQAAXwYAmh0AULiJBgAJFx0ZCBKAHXNlC8C6D1mhcrBKBhzgjUEAAL4MGsSESDAJWMgloAEmLlZRRq8ZeHoXyhWCkJJYmK_QaCAAF8GAN0XDcDGUCM+jYMoAFHm5UAWR7jEqAENhGMlAAAUgYjS0AM1xEgyDHjuD02hcAA5BDhcrBqWQetlKFYLSaGGgo0RoYAAXwYAAosRIMI8+C7RcAswYLgEpAik5TuUKwotnUqukJQqCBUAAAJDQRh8CnSoAMgFISoM4IwXbKgopXSsSEAACWwUI0+C7BcBTIUNgEpAik5ZuUKwotn0qunu0IdEVAAJbAz5z4P1FwAVAJwTGCKlYEUnIpAihdOGhLkQoYXQA54sDYFSeQwImWLwE4DBcHM5kspREiQxyRSclRJFZTaLSS6QQfoEMABi4cAAVGrpmATyVAf_GgCgZUgTVSMFtyojNFK6XYQgAANhQHgRB8C0SoAxwobAJTfhWCKI+PnbNyhWBFK6dTQgAHOEwAFIoSg+CqRcA5gYLgAUipXfZWCKTkUlVIpJLsEUJ8SFDAmgADdHwBp"
noncomputable def WL2s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL2_0) (dpk j 1 WL2_1)
noncomputable def WL2s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL2_2) (dpk j 3 WL2_3)
noncomputable def WL2s0_4 (j : ℕ) : ℕ := dsel j 2 (WL2s0_2 j) (WL2s2_4 j)
noncomputable def WL2 (j : ℕ) : ℕ := (WL2s0_4 j)
noncomputable def WD2 : ℕ → ℕ := rdw WL2
noncomputable def ready2_cuts0 : List (ℕ × St × ℕ) := []

theorem ready2_cuts0_ok : CutsOk ready2_cuts0 := cutsOk_nil

noncomputable def ready2_0_state : St := ⟨26112, 276711, 28545, 39936, 29184, 45301, 29666, 44151, 53248, 103645, 29184, 45301, 28545, 115869, 26112, 285696, 54657, 316647, 83841, 355436, 113507, 385102, 166755, 467751, 195939, 496935, 224484, 562407, 250596, 751794, 57729, 78725, 87395, 108391, 140643, 191040, 169827, 220224, 198372, 285696, 224484, 571392, 58850, 79846, 112098, 162495, 141282, 191679, 169827, 257151, 195939, 542847, 82914, 133311, 112098, 162495, 140643, 227967, 166755, 513663, 82432, 132829, 110977, 198301, 137089, 483997, 57729, 145053, 83841, 430749, 54657, 401565, 0⟩

theorem ready2_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD2 ready2_cuts0 115 105) ready2_0_state = 53592 := by decide +kernel
#print axioms ready2_0_cursor

theorem ready2_0_covered : Covered (toCl ready2_0_state) :=
  ready_cover_cursor WD2 ready2_cuts0 ready2_cuts0_ok 115 105 53592 ready2_0_state ready2_0_cursor (by decide)
#print axioms ready2_0_covered

noncomputable def ready2_cuts1 : List (ℕ × St × ℕ) := (105, ready2_0_state, 53592) :: ready2_cuts0

theorem ready2_cuts1_ok : CutsOk ready2_cuts1 := cutsOk_cons ready2_0_covered ready2_cuts0_ok
#print axioms ready2_cuts1_ok

noncomputable def ready2_1_state : St := ⟨26112, 276711, 28545, 39936, 29184, 45301, 29666, 44151, 66532, 152861, 29184, 45301, 28545, 89920, 26112, 285696, 54657, 316647, 83841, 355436, 113507, 385102, 201035, 516967, 246336, 546151, 274881, 636071, 300993, 751794, 57729, 78725, 87395, 108391, 174923, 240256, 220224, 269440, 248769, 359360, 274881, 645056, 58850, 79846, 134987, 211711, 180288, 240895, 208833, 330815, 234945, 616511, 96198, 182527, 141499, 211711, 170044, 301631, 196156, 587327, 111833, 182045, 140378, 271965, 166490, 557661, 57729, 135221, 83841, 420917, 54657, 375616, 0⟩

theorem ready2_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD2 ready2_cuts1 115 64017) ready2_1_state = 105540 := by decide +kernel
#print axioms ready2_1_cursor

theorem ready2_1_covered : Covered (toCl ready2_1_state) :=
  ready_cover_cursor WD2 ready2_cuts1 ready2_cuts1_ok 115 64017 105540 ready2_1_state ready2_1_cursor (by decide)
#print axioms ready2_1_covered

noncomputable def ready2_cuts2 : List (ℕ × St × ℕ) := (64017, ready2_1_state, 105540) :: ready2_cuts1

theorem ready2_cuts2_ok : CutsOk ready2_cuts2 := cutsOk_cons ready2_1_covered ready2_cuts1_ok
#print axioms ready2_cuts2_ok

theorem ready2_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD2 ready2_cuts2 128 1) (ofCl (RC 0 0 0 0 1 0 0 0) 0) = 122485 := by decide +kernel
#print axioms ready2_parent_cursor

theorem rc2 : Covered (RC 0 0 0 0 1 0 0 0) :=
  rcOfC WD2 ready2_cuts2 ready2_cuts2_ok 122485 ready2_parent_cursor (by decide)
#print axioms rc2
noncomputable def WL3_0 : ℕ := zfNat64 33248 "DRGhzkKpFAKoRYqVgE0eosLlYBhrtBNwjQwAIOBRagBIyDx1zLAsAVAi9YMgCIBUAEoCoACZB8AABEGAPHXAEhplgWAKgResGQBjgqADZhUAf7Wjih8AAAHQrgCQUFwdlQWAKgRRiAf3KgAbOUKwFqMxdC7ID8AAAOhXBcFZUFgCoEU2BkvAATlCsD_ykGhJFYBlActWwegAHyPgEjV4OBW_BYFIVPzKxFYyWMwKs9QOSKwCiOZKAZSqNc+a8fOwCkz0i44jBUVHakIkGA4LAARWrFwFVkyFKQ0lNPgfOxSAV2gkuRoYAEHAoAZ60NwMBwWC9jMAADrCoNJGR_hUAVkU8fAAARBgLiy0A9HQ3AwHBIMXHwVUCakwyoNJVR7RMqAK6VVQgAAIgwAfj4NvXAEgoiQYugSggTgTEAFIBZXadGvJFYC2olkLmcPwAAALh8HkriJBi6fkPIYlAevLMG4BFPWSKwCyORrFScBaUSzPTaHzsAIJJz8fAAFPg21cBwEiJBi6BJiBOBMQANJQrALIYckVh1guqJZB6ACEjIAwD4LPXESDF0IIlAevZMG4BFT6SKwCyOR8FScBaUSyG4OnYWSjUaTPU8mDcGRUVA49cASCiJBqKD_jZmH_laYgAxyRWBtZaE6kisCyUSyHxOH4AAAcyuIkGooRQwGzMK8LFeYgEVypIrBAlnPR1JQLJRLI94+dgBBJOfj4A8NcB4EiJBiKDZTBuBJmIAtgqThy+CLM5EEVJwKpRLIls4fgElCIAAG+Cf1xEgzDUSWEUbhszAqgCNmYBFbqSKwQMXFiurA6koFkolknIXTrVaTPWEGDcGRUVLwAGhAEhoDwqAAvqbAF_SoNIYTbJUBUS6UKQgAAAXyEAFMidChOABVMIdNwINJlIaQwl0PnaUyhWMSS1Gu0F0iFDAADyJE6Ah0IyQqAD+is_o6bgEpvwVGkMK8Th+zcoVhJajXThKEcaEgAAC+Qj2CoACq0o6bgQUfpUpDSGF9Zw_FISWo12guiQoefl4AAHTMBfIQAkaJ2KE4AFUwx03Ag0mUhpDCXY+dpVKFYSWo12guiQofvDIAAmQAkLIQHAuKgAJIAlamASJKg0mFmIpWVABdHlIQAAAUdCAECyTh2mCoAP4KzATR2FJJSG0gl3SB87N4VKwkpFrpwdCCyAAFg8B7nwAMyIiJgAJL9Dx2BSUJFysNIWRyhAqVjEKaXaCJZChiAhoAADUIQA4yKqHi4XaMgKoYjpuBhJSBlMM5VKUKxyUGol2gkEAA+R0F4AORgXyEToUJwAKpgjpuBBpMpLJpDCXI+dpVKFYSWo12gtfQIYACDx4AXqEABEj0ioACq0o6bgQUfpUpDSGF9pw_FO81IktRrtBcohQwACGDwZgeVCAEGQFuSdNKgAL6mwBgkqDSPTCbnKhiUWo10+2eQwwIGmC4mZkCElQGBUAAVuodACnyoNIWReZUAQRqHEQiGBQAABJj4AAPdlHQFJe8XKw2hZGpLi5WAJKJdoIgESWQwKAACUDSoQBIyRULmGQFWagYaSJAqVhhpsvl2cr8KlYEGol0kiFDIIr5mALaCkAuIQBcWQpFgAH9HTcASMVKwLphnJNShWgweCDUa6ZnQgigRQ2gG4Qq0NsSiwAD+jpuASkDaYYiHzNShWFFqJdAxnkMHGeQwAyg2A14EJPgAI0BgVAASTlHD8AgAXKyiaQsjnWJUBTSyYXQgABMFQCKkIAnJACihsAOsKz+jpuFhBLFSsDaYVunD+UhQajXQvCFDLcJFkAAvA5KEZyUKwANErP6Om4f9RiUhpHphnM6yhWFFqJdFsnkMtw0YECBRcTMyAvUICHNWUZM06FCcACqYI6bgQaTKQ0hhLkfO0plCsJLUa7QXNIUMPIAAExQruFjaFQADojR2AOgKlYBhnYfCkCol0Z4eQxSOSKUE4qfA2BgEwAEkwyhPAUgZipWGkLs5B+SKwkpRLpBLYhQ1YEQAAAb0InYqAAXiaOwCUlzJjaQS7OWclCsAi103mhAACgFgBtGYkNT0C4APPQV0AA+kxNCCAeyYYgMYZsYBRiIAACsIyPLluVpUABZWOaOwDzZUBBLv_j5dBUrAotdLOoQFwiACqDMpjwsPATSEBNmhjChOABVXgcNwCSgAsV_MdjSGEhx87FJ5JLUa6QVSoEMAoJ_5CAOshMYhPx9FCcACqgQ0dgElARYrCIO8YK49FI5Co10HaBDd0eQ5SAE3CIKR2dqZudqQ0tPQKuzE2bobgYAIhUQEHIMQ4y0soAAjRmAGIWgfCEAABEGAHcvAEjIAkLAKdowEgxY_4ZAjQwbllLoDDNHYTELpbdCAAABErwBIyG5HgooG0xYGIACNGZZS6cRZmFHTcJiV0wqhAACyLgAYrwBIyAaxRMI8BFAJoNFwYgMSy1k9mzDwOm4IZiF3f6FQT+EEAABIV4AkZAIdowDrRYATYYNyygLTNHYf_MgunpkIJJNAkUdA2NjYEjXgCQvOY8GccRlhIpASKSYaLgxqIRMsZllrMtss1BDMR5i9boIokKGAAAD9XoVFhCWH9SNHBziMSoaLkpKoaUsZllLMtMs1BDMQIq1foLSEKGJUZgAygDuXghCigD8Gi5KfxKwdcsZ1TLrKWZaZZqCGYldoLA0CGasKgD9DMAOheCEKKAPwaLkpB0oVwwZYzLKWZaZZqCGYhxFq_QWkIUMrwV_UWAGI0R4m4GbFIB6XgFM1hgEdweCigHiGi5KQGJZSyeZZiIHTcEMxK7Y9CoJ_B+AAAiy89IUbkeAigBSGi5LQUCWMyy1mW3HZpqCGYhdIAIUMpuoVoAsg2ARF4FoLZiFCEsNFAOsNFyUi4UK4MSylmW2U1h03BDMSu0FOSNDAUkhCIQiZOAVBePICEIIMQo4G3hYlJRIrljMLpZDKNQMzELLqEJ+iA_CyVTlz0UUG5sAAV4e_hAEjJPcaAegABQ4uACxRkAABg6AABKHAE3Xn0Uo8E1RqJLAmoMQR6WMwylmk__YpcGzcEMxGtZIKl0CGABGQ+AAUxAwV4BOLAkDwFbRJYA1JSAxC6WSSo5mfUaOwMzEalk5ehAEdAACDEEXXgHF0YAagAPyxmF3+y0vpKFYHDcJiNSyGuPIYWSqBelGBubAbq8CUPAV9ElgDUlIH3LGYXSySf6Mxrjhv_ZmDMxGpZaShUEABPIkR4DzXgVJkEI5prDEqP78SAaimUlERiWM4yXSySTKTY4bgZmI1LNBLglQwAE8iRHxIJRwg0tn_yUHQHoAAVCLgAuIZAALcOgAAShwB9F4GFiuISmtCSo4A1KMp1IpDtixmWS6WSS6hmGpxDMxGpZIEhPyCAAI8qANEvAEZrUVCuEoeArqJLAGpKQNkWMyyXSySRERw3OIZmI1LI7VAhgEggAAjheABFwMLFcJA8BW0SWANSjKQe8YLyyXSySQanEMzEalkaoeQz+ZcBNHRFwNzsSASMIL6ZyUXCCJi0kkA1wsSkohEDBuF0shtM4aOzqGZiFmggHQgAE8iQDucJejIf4wfAcgABkMuADKZkRQAIYdAAAlDgERLySnjsQ_1OqawxKjgCiPG8plJRHWFjMgl0sklEjMNSKGZiNSyIhCfkEAAZBsAjBeps8dhTSSA7I8bkpAYpCMixmQS6WSS+ZmGpFDPnzIa1EgofQIYAAbh4Bva8FBmjUYQ8BJAUAaPyUg1QwXkEulkkibjBuRQyFRFLID8IoA344bg7OxJSH1ICHjpThgBIaMXHgI0dNwBWGjM_+rAKQwlkqcfCkJyD0wyhAAAP0NO7HgEIdNwBWFjMKoCkMJVnKFjp2j0kVgpnIPSClxChgAEkACJc_Ak88cRgSw6bhXQOFjMKoCkMJVnIBTh2j0kVgpnIPSC31Ahm5ToA_gzAAgkmoDkYDwCKOm4ABDRmAapKg08AXg8+VBOSglAEIIaDkBr4ShePBNQCNFjMFuoUwDCSKwu1H7Z0OVGkisFM5JzPpCIJJZqTmeynKgVmYEAA7wAsyFVljwG+Om4BbjRmFkJSGmsh9D4FxUrPJOSglrUJSA0AAASneFOkzXZEBJACqguoqDCA9cMVH6CoYg9oKllJSA0AABa_UeBoh03AIpF9SAUhHRi6VV5J0PskVkkUzmwj0UygQwAD7EwAEhcjjpH48DRjpuARRFqsApDCWaq8k6J2SKwnNhHp61CAAAOWsER8BqBdIoiVMpkykI3ZIrCzUaqOU7FScxyUKZzYZrPVbHkMMqKl4GpBIINgAqyURsjwEhNHYCqkSeAdQKgwlkn0fCkJzYR6ZdQi6AEPwYgZsjKQ1EeAQx03AGJVQFIYSyBkPnYpI4FU5B6ZfQlIDQAAAA94CEZHFjwCGOm4AxKqH6ioGmGMCpbJyKQUzkHorUK1aEpAaAADMPCTkSWxoiPhNQrpHCxmFEBUkisulmozkctLJFZpFM5B6QX2IUPwTEAAAI2j6kAmd5pkwPB7k2A_wZAF0yoMoGqSown_zoIJbRCictAAbQAhCzKw8cRlNFkdNy6wBXMYxCqUQUhhKs5nKXSRWcZKjimcg9IJ7kKHTSYhIZSpQgNlx4BqBZFcWMwAUhZBhx0ikkVgl_+cOwckKj5+QY1NG+sk5sihE0DyCI+A1AslWLGZTQVGSKwBS1X94pTkcviKk_MloSzkHIoZCfhtEqsXyc0GmgfNwIDo3i4WL4tAALJNqoSfaFRJLJVg8xTmNZIrlodnJNaDrpCAACELAEM5xQWtUFwWEAAK1FRJLJVC9RVLSck1JrIQAAQhYJYXLZjCI+BpAsl0Y2mUya4JGhtnJFZJLNRJI5kstDs5os1BWhP30ID8w0Uos9op2Fy2AAbeAZixcLF9vBAfKSaQD4LF8m1UDnkisk00JM5dCSK5aHZzRZrQSVJEMAD1Y8AA4uWUiEB8BPsGsNJZLoE0UIVJ9UJVNADJU5CcVJ5aHZzRZqEgOH9o0ieWSjPZqEUGxUJCwET3kmB4PNGwH+DIAaIVH_04BxRUE5JqPoQhPFwAAAnN4AMNEIANDYAKhkAAfJgAAqTADxkoCz_oiAEyLQAgIUX5g+bsQHwGoArixmftVgFJBpoLKPnYByRXHQ7OSai1kiHEQD6EiHgBoGQGaWR0Hg9EbADEAwsVFNA1MVAdCag1DyHBTKWSclUEieAjIEds44fCbxszAsyQMF4ABMkVlEAOGSKyqBNQSJw_JJhqpORcKRPCmbHYGpj4EdD50_ACSMMJrmDDIABFScBNxMjAJdkwAUHJgAKNHQAAEQYABZkPQrljjJmElD_58mwmRgA5SRWACkyRWAA2RAdgAARBgIO1yFFSATBmElNLJQ9TYTIwA1xUnACSgFVAFnDsAACIMBHiuaceGJNTTFScJM9WGQJwJoxZOSK_jIQA1UkTz0Coh7jpuABBwKCkpMw1bXBaioBgJAgJQNSDwBCYeAB_g8ABlYyAAAiDFOT2JPYhN+qAYCBMDALQPNFQAx8aAB2Q8ABBIqAAAiDFKSio6G0sfAkIWT14aAh5G"
noncomputable def WL3_1 : ℕ := zfNat64 33248 "CADjVESDADUB3J8AKWZFysOIL0PnYpDAldIJ7UCGABBwKAGohBWqoiQYKhUg2AmgApJoXKwAZ5w_FIfjggujskJ+ABBwKA0NjQBChBRjoiQYAL5UAKQBS+YuVgX2espKF4BYaCGxChgAQaCgAHoQBIaAA_GgN_nwBhMqAtJvMqA_+vF0s4hAAAAD0IAKZAAejQE9AUIrU3RlCsC0zkwJIrGIV0ukF5CFDAADyJAAERgAOhoAegdSVqaFSsq8sKg0zkUgVku4WQifIUMAAEIUGQDwZP7GS3CIACxw_AFYlCsByaZytkkV3iWgrJdILhUCGAAIkKAAOQgAlUJY0AAOOPIYBZFaUlNDSAQ+dikCs1266ES5ChgNQAAByECGqhLGgAsDxsAcgDQipWU0NIFcoVgWUuizkJ+H_m4sgjgWAAehCWNAQuMgB6AbBKimhpPdlQHlVqum2kIP8NwF3DIAB6GDQ8B400bgFSQH4BVcsVKymhpnIpArJd_ugQygIUMJTJwEpAGLAB6GDg8BPMiAMkcPwBhZQrKaGmcqBJFYS2s1nniEQQKoC7CYGRkBjbOpna01AdFUASGgHwYBCBIwuAN+lQA1g+lIBXTZyEAAABIqgCQ0AaUdGUxYigFkIMXKwtI8E4fikMCV0grkQoYAABYASRgnNUA+DANQN4jK9FDYBKQDQZ0zkoVgBdCCAADYWAIfV0ihBFBgBkbNwJIZAgQVH8KlYBORSGBptZA+nkMAALIcGYDqqkpJoljwHxNG4EkMgCk_hUrDiE5GySKz5zFgabWRhIRBAABKFAEJqgqxID4mjcCSGQBSfwqVh_5uJyPEkVhgabWSNIRBisJAAAFKqgHk3ZScCcOAagqRGV2KGwCUgDjj5m5QrAM4L18IISQAAEnVOInQQEgGoUlXYobAHRFSsAnIpD88EIWXrYHk8hgxKoBhSxmDc6BZaothIDUKSGQBSYQqV_iJgJyHUkVhgcRp1ZI5nkMAAEQUB8aBJ6oBMGlIF80biEJIZxYXBZFK9ipWKQ2jmcuFJFYYGm1kgl8Qn4TAaA6CUBSBMKooBImg8A1CkhkAUsEKlYBOSEkisMDiFOrIys8hgBBJ_HwBL6oAmNAEiwDUAnIyuRQ2ASkAzWdKPKFYAXQghBAOgUA6B0aoIg4K4cABKQCbmcqANwvCZCpWAHEAMhPwABKLQFQqoAkHAiFAEUAAGojQAMcGgAIqFQAAAgSqCBCy6IsBpCkqJKGYAvAqVgE5FJPA4CsggTyGH0yh8w+LoAOqp8j6gAkAvGzWFJGIAtYMVKz+ZMbScs9JFYCcDTayQXhIT8LtpCKJsQI5NqkB1VQBIKCIOCuHBURmAGIBGAqACYRUAf8UioJ8AAECEhcDGgVWqAJDQDwSAYBgGoCtxQ2Ab9KgAjR9KQCugwzyGAC0ABKVQ3CVfC4BqFJDIHaipc5QrLaE5TOSKwwJWRkCE_Askmkj2Xg0ASCqAHCwAagBxGlq7FDbcCYBVRUrAHvnQpAC6FCQn4E0pIwQeACBVHmZdUHgGoUlSQ0XABSCkA5HTtLJIrPjCwVkbYhPwok0k0kepmOH4NzcyAEjIAeXCpJIB_wyD_yNFQCB5MAETSYAChJ0AAHQZAMtkEaqgeAoBqAr8UNgGZSoAOolX+HIAugXTyGAUkKKPAC7sgF9Vzh0OQ58bABkAioVABLQqAKyUxPgAAhDwHgAduANGQSGqGIyAGoCtxQ2ASkAbYfTMKlYAXQLJ5DAKSFFHgpAiVUBtGgiOhdBQDUBXIobAJSAM6PplFSsmgF0GmeQy6AOQAgABLt4PHY6gQWA1AhqRH4YNFwBSH0oVkECcsvJFZNBKBptZEoIT8ogUmehNJFYOlJSKitnHgASqBIGCKDB_M2AigEALCVAEkJsVABdIJIQAAEQYiQGhVAPgwB0KSTEsZgApAqL_jp2a8kVhgbLWQVqBDoOVAAABbRgRVUA6DAHQpJKyxmACkCovmOnZryRWIT88FZayPuQn4GEBLSBHAAkjBAqoBGQP_mQBlEqAcArFzCoALpx5CLoGwAACAVqoB8GAOhSW_ljMAFOSKwNtRHMiSRWGBspZINSzyGThGDjXRqTKGgBAowI6qAfBgDoUlvJYzABSBUd_HRryRWDT8sFZSyIEPn45DjXQBqULwdmQAzj4wNfOHgYj_GD4UlOpYzuIApvp_hqqI5bySK7iYUDZW9rFsgkEAARIcAA_jACKpRvcJAHQpKWyxmACk+_gLio+8OjXkisCy1k3GgQwNpZBvSlTAHFjBF6oNWNAThwRkKiJTKjJeAOqKlaBCogpMIGkunEUICCAIQBAG1UCnCg5SJ6GQ4IyANoyXgG_SoAqg4PpSAaa6BqQoZtAPoAAdxgAVX7yluoSAOhSSYljMAFJ9FpUZtHS8SRWBZayAJPIZHSiHEwtcKF4KzoFIRhFFU+Rw3ioGcHj4UkY5YzABSbQqM5NeSK7CYGylkcicP3LCwAAHhqLcMJgHQIoZSxmAClpzdn_kaOwo6SOjXkisamHIIy1kashQxSATTIDEWcDGgQGqAeTSNHD8D4MBExg+BFF+WMwAA5IrA0lEcwYKk4IEylkgmmQn4eQAACBVDcPXKCgjIEV_JYzAE5kisDppKI5YUVJyCoEylmerUPn4SbKTR6EmPHYAEy+PDoXQILCMgRWIljMAbiUKwCiBdJFc9Ay1kEshPziBhKf8WYgen_joHRudM50BIGAB4gkRVYlwFXAp9KQKaAI+dikAMO80L0aEAABEGAH0tAMBBbou8gzAAAg4qADojQqAACkfAAARBgLiy0dAbxMVMVB18+AqgAz0oXgE9lIB022HNSNONCAAAiDAEjJgCY0KmVBPQE6qV6dDQT0SyULwFpPRjFysA6bbCRSKAAADWJhLCoORnwVUAFglC8AHspAOm2w+ARqUoWfl4AAToAh5gZ2EADOgGAi6CPEoAAAD_x8AIRgAAQlwAAEQoA9BMRIUrw8bgNE8fgUQNI9G2TPJKF4bQKj0AxUrCyHSwkVvSMABBoSC0B07QQk6AJDQMycCvjoCKAAANf+HwGDYAACRkAAAH3JhLFIJ6BRFKuAPf_Ey6yheAtho9WIXKwDpYSKdhGK4HAABaA8iYAdNHJLFIJ6BQlKuAPRdZQvAWg9AUXKwDptsJFNegRxJDZ_AAAkhOSA8SZMpgPQKIHAj4eWULwAeykAodNthU8jQ0aoEcHIAmg2BudAaxMDEnByE+CqgAsEoXgA9lLljIDptsPgEalKEAACIOAEcTjoXGGWgg8fBVQAmKVE0Ae1vKiCBtroTRCK8HAAAADMgaRMSqKVgL4hPzLIaqAPRWZQvJoLQehOLlZBA6bbCRTaoEcigAGMWJ0PALZkBGJhBAggmhIpgAekoXgA9SsXKwFNGMohtrtB1EjAAAiDgPAtBM3Rg3uInAx44fgUQAYKULySAPe+lRVA6ba7_1CYOhAAE6NgDck0_GjMiShPAlx47AogD0YKULyTHQHpgi5WVf+AwdNtdoLiESWNQA26PE6AkhMKJEqZSAehVQMIHwfsoXgA9VIXKwDbXaCydCAkgIEAa5MKJEOBODAR8FVACYZUAf+Pq2lQBtroQpCAAABAOYsKJFvhGAOB8BNAC2pUAD3QpUFUNtdF7oQNQHIYpeADqTABBvqiIxS8CRzoP9qwAGFKgAKwVFUDaXQsp8QZKH9UoACSE6HE1AE6eA9AICsAHGyoAHspjoG2ukFkImyUKSc2SgdG4EBjymPDQEdDwKCnESDHoNgkoDWBB03ApK_i5WAYZyoUkVgXEukFjCFDAAg4FAVMTA7EyAmoBKQ_4fcyXMbLzpm5QrAW3EugTEKGAABEGAAmNCgkwNSNmYFUagaQYpQrAegeXrc5RaSKwFtxLpBWagQwAAAApkJcTAz8yAmoBKQ_0fPkXMbBzpnJQrJILTjXT4qEAAG4eAACZAEhISwmBR5kBNQCUhkw+MJ0j5m5QrqoLTjXTu6EAAAABMhLCYFmmQE1AHRFSsB6V5cx2VOhTVQWnEunY0IDxKQAAAEyCIIgrWZAFVMG4A6AqVgF1w50KaqDE4l0MOgQwLoDJyYGZkpABIaAKLMG4E1AeDZnBalCsB6XZyrckVgLTiXSC+FAhnqDoA7mvACADzIACLAoPAKLMG4E1AezZnBalCsB6XZyrckVgLTiXSC+NAhn9VYAAUjoSgTqMgIXmwA+AqLoBDYqOoFZHgnwAAQg4AK9m1hUnxaAAo8pUK4HEz2VABEoqAUhdJcnwAARQ4HCOp4KQeZYM4C9TBuf3QgFIEms5pOhQkisCbZayCcQoYABCiYHEOpbKQDQZsYCzzBuUEBSBJrJwTh2J8kVgJJtlrIGJChidm4ABI5GCgmUwMIHsTlSmDcCMKMKQJJZHLKyRWAkm2WsoCQiCTkAaabA2NhcaDRFwMtMG4BkTRuBlBSA9Ls5ZWSKzCC04kbWL5BqwhQwAAhBwHoODQlBFhszAImYNwAUiHGom1mcvjJFYC04i6XrZBR6gQwXklAB0QcGhCAaDZmA08wbhZQUjrHDfTayeU4drVJFYVRbcayQT+IUMrof+bi6ACBkjwTEBx5g3ABSAMUinWbunRryRWAtONZD0IUMhg8UkBepEDFCzZCI+AxAXAbMwAAZQrDuqVWY1nRryRWAtuNZAUnkMslJAymRA6MgAYyCkPgcoZATUETNwL8oVgPS7_s6GWSKzCC04l0FMjQweGwAGUVIA6FnjWqCA+zBuANQdA1ApAel0nx07cmSKwFtxrP_kLciFDDCGGmz34SUA8AYZwB0WEIWAAEZAOuOm4Ag4qVgGGcwrKFYCk410q2hBx_8bAaRCQIyj0OdmQDNjZmACklGTD2sy7OjXkisBbcayEHQydAFYvhhBeiFDFSCELAOSMgJqE7m4GGUKwHpd_ydCkA4l04OhAABRIgEIWmIvAHcDYq1EophHqlCsByYWPpSElK6XjQgAAokQCELDgSgdoxAc_NgDWJUAYT1JUBNC6WaQgAAAeYuDg0E5sINSiWMwblFDSwZ6KKSOkmstZOHbzSRWQUMSdLNNZIJBAIj0gjGsCkDCMSPkymAkFzGAFw2ZgApALIdzo15IrAm2WsgakB+GUglkkgV0ieBUkCckgXQJiBoRGFIBZHAdPZJFYTSTndlLIwc4fkUTChnIJZJKBEKkg7NwIXGwM3AxsfN1I6H25GegUyuOAFgv4dARRqAUiKgAswVAFZLnHwAAEQYAr1cASGjgBYL+HQEUagFIioALMFQBWS5x8AAAJDrgCQUFwdeAWBHRw3AijUD1o1PwqAD1hUAVkHoAAAk6uC4Kv0LAd44bgRRqBGZSAa3OnhkisArIPU4fgAHyPgFh14OBRMBguA1CqRRqH8laMrdKFYE1i6ckCKk4AWQkB87AKTPSLjiMFRUdqQMhlAIK4iQYygsf0Roc5CqRQCqEWKlYBNHqLC5WAYa7QTcI0MACDgUWoASMg8dcywLAFQIvWDIAiAVABKAqAAmQfAAARBgD"
noncomputable def WL3_2 : ℕ := zfNat64 33247 "BBQrIwQTYAALg0AV6LlYANM8fykALpFpChAxALlFQAh8eEgBIaBILgAX4ZAUDgAvhcrAB6T0oVgBh_yhebQgAAAzBcDVCp4QI4QzYAAHYkAJxKF5BAnttyqggFUBKhFUOgADs6AAhYDwuAAC8HAEpAB6IEoVgAz1zGffQizEwOQ8_4YlylQAAV4A0LAgmwAANA6UBEB8EqAP_H0dCpWAV02OhAB5ENlQAKhYYzIIJsAcRYgHYcASkAHogShWAHJXMZ99CADyYV7lROgBkuCIOIgVAWQAAAgVADEAAHC8H+Pgo_9UgF4IwAdy4Jw4AWhNAuECWMwB0RUrAqNcToUgUUuibkKGEn_ykHk9ylBaAjkoCJLBEHH0KgKoAATQACskwABhTo_4pAB2EIAB5cE4cfAuCqgGCLGYAZwqVgE5OWUKwAuhnUCGEkoqpTjyUkAdZcEQcxE2AKaQOoAS9KgD_x9WcqALpdCBIQAcQ56MBJqAjy8GhIVRkABkWhbwqGog4uVgZCchXJFYS06hkXSCQQk00PPaGK+EtIlgXFjc3Kyo7UhobOgGquG4GQIEkCK5MAUzKgAveVAf6Tq6aIQgAAIgwAkToBXXESDIELMmQAAKkLlZaT7ysPXtFSswIYa7QSVIUMACDgUAD+uAJDRAgBRCIPx4MLPh4GEXKy0gts4fikwIV0gjEQoYAAALqvr4uuY7B1ouAFIBSMqAC7ZUAV0zkhAAAiDgAx1ydDx_n72VyVhaAdEoBqj4CRUrDLHSckvJFZgQKRaz_JCIIAAJgoABBkBrrh9CWgHRKAKo+ScVKwyyEnJuSRWHdgqgl3yiEAlAhgABZCgC7VwQkVcGYAAOgCGiYAEkEwACWzYAACAMAC0qC4mDyzAAAiKgB6RUABUACaHqOgABQBQAS7JYZ2CoSsAJQBLRUTQBRCl_JWAA8p8AARoKAAwlAAboA6XAAMHQAAAAAGLgAAAAAwEAgZYvvU6e7HKQLQpUOKxaUQJKDyhWWbDKScrqUJ5lPIFGJZIozTyGATUcePEqJgBIyAHFwBMqAEUQAAAAAAAAAAAoQBcVABiYQh4WDkAAACVCoAFBKQAURRBsAAKAKAu1AZ1nA9WegLIDaCRWAb9KgBwR9UQCuifkKGAABAGA8PBQupqY8AWlQDAQeWYAAAAEEwH_lYACBycAAAoAoiQBCXADBIAAAAAAAAAAABoDrOgHdcCYMgQU6qWwogAJYLlZaQHrZyhWYEAtdoJgUCGAAhAKFgBtriBAigMgPIYAKQ5QXG2cmvJFYA9ekvWwAyFDjuTAAABJrkFAgRQmETMgPIYAKTujULTaWk4dmvJFcQFIB6AVYvlBAAI0PAAEG_WJkCB2EiOMCUhKoA8hgApsILTaTA6dvjJFZtAe1kgqYQoZhAAKlRMeQIKZRJYURCM08hgApCWmk9h07fGSKx8qwUGskH+SFDOIATjHidnS0jHa2LALdcASGhWj4AP_CwmBIA36VAGRD6UgFdKBIQAABKKEAAVE0JABAi5WGUD+nD8Uh9X8zAwmK_QaCAAC4OAB3XCEHEsPgMIAAYT7FQAMeKgD_q0NlPgAAIgwAe65Oh5ciEAtCJQs2ZKjgDoCpWARZyAMoVgUkuhNkKGAACYKAAfZALK5pJYfB_guA0OjAF1SoAimqyoCk10tIhAABZCgAFVwuECdnCNDB6LQCoZkqOUTxxcXRSGUIs5amSKzqfTLST5L1sggPQIYAEHAoqam1AGVcIocrdCAAKhEGgAXRcrI_MwENOH4pAK6QaCAAvoiAdlCAAKhEGgAgRcrDKB_zh+KQ+6OZgZTFfoNBoOPAAAOyPQgCYhUJo0AtDlFys_6xeIRgKh87FIeQLpBII_li_qJCAq0kKxszAAHXAhgoQRI_KBHAwg9DreSRWADeLlYZRLIweM4fikPplK6+5Ch0EGoJAADYOLGgRwMJv4yEKLSBOASkMpFJyf0kVh9AukGdZ5DIzLFOmh1MLBi5WSoAtrg2DjMI0MKKnlSmAhkoAxPkXKwyhOSckisPplJpdIJfzyGFH+KcBjgeIsbHRWLjx0B_bREgxok4AOoD8WCaTRGpQvAqg9VcVKw+43BhoJJkaGABBwKAA9tAAU4bgYa6cAABcWDqABDKHqi6Un6l4CiTjQgABQBQegLQuG4GYMpABGQQiwTEuuVBpAe2DKgmgXQtyEQ0FgADc9jQA2VAEhYCkmAAAsJAGpyoA_8fedKgCujgkIAAAWMqACPosBYSABjFysAHoIyhWf2JgMPAUKggAH4AgCcKgAL+LAWEgAyhcrAB7owqVgBhoPh0IP3JQAABIaAMCwAAa4sBYSACqFysAHo0yhWNoJgMNB+ChABNAAQEHh4AtKgVyYAACwkAanKgD_x950qAK6OAQgAAP8BhOFQAMPFgLCQASguVgA9DKUKwAw__Qv0oQAAABArYomLGVAA2kWAsJABEC5WAD0E5QrP8EwGGg__QgAD7JQAFSoAkNDNlQAbuGgLCQAQAuVn+y4B6KQSgYaCMpGhgAAAEq4AmNAeGQAAFhIAQQVEtARYVAFZEInwVQCfgsB4CHh4AEMgBJUNoVAA0zWLAWEgCUgA9mUVKwAwm5UI_0rAB9AAOVAEhoZsqAAaIobAsJABAi5WS0CenD8UglAw0GggA5AjmwAgI2DOlQJ5KhiKSo5UIQCgFyuUBdLQJOcPxSCUHWMV+g0EAAd4sAEQqHWPgAA2FQAfouVxBNHYdAep5KFYAYaCn5GhgAEaDgGUElQMAOH7Dj4EoxAcgfC5WS0YlgOpyBMkVglDoxLpBf6gQwAAZhwAG0YxHyVA0M4fhogmGIAKIuVlWWjkAEfOxSZRLIZjXfQIUJEKGAARoOI+lOwMNOAA4MfAH_yofgECQHswCpWB_pOrpplCAAAiDABVKmEdycBmWgAANKlRJl4EgPfElQBXRfyEAADYKACcVFuK1cKohFauMQBjGYSHYLlYCQHpxyhW542ZgGGgpmRoYACEgoWB4WA9WZBQgZAAHwcRgEQH4BFK4XKywN0tlpORSVRKEQuwqQjwIUMAAJIUBHxeAJIws2uDKVT_xkAAAGRCYANwFQBBD_x0AABEGAE4zAhUZRd0ZAAFkAlICZaOLOH7NyhWfEJhLVZOroHJChgABRCgDLMwA8r+44flWMF4TEBCWSiBFEEXKyrLZaRZygEkVw_PhKEQHoxdILCEKGABBwKDMAJowA4uAGFQAESADBwAAAAAAAAAAABJqMCMrgylUI_+MgAAkLQAAgiAAAAVMdAAARBgPD4kPApJMJQVAw5ozgADkO0XKx+AUtloDM8fykEolLCphGc2hAAARBgrQuYUbATA6dgHRyD0IcFSsnogSxWTkUg5CJVLqP0I2iFDAASmGIgTUmGwTkAcgAzipWGxSnrky4nKgShWf+OmGCTkFS3XSggBBKAHwAQStJsAbBpIQaOwDo5B6CRyhWKZ6KScqNJFdykYc_iCiiXSCWlAhgBBJOfj4KQAQVAlA6ti5LRsA1AlIBKSey0DYfOzalCs_4dCEs106qhAG0ejH6AcAA4qrQupcbDQHIcgHRyD0DQjDhKFZPQnJLyRWDkC6EEIopNtJnpXDZmS4qK0aGSgLHjBkCptTkRAABuMgA5hMAB8iYA_0zAFV4AAIQcApFw3k4ELGQBVAN+lQCQ4YfSkArpBRCAABKHABVKwcNp+qwAFZCErQSJ8pAST1YJw_USUKwP9nDeu0FAiNDAAg4JESCUjIVvVBuDDoAAPxkAAIJgACyAAGF4tA0AAAPYyOWWGQN2NgP+GQbCOgGhcrJbLQeiLKFYJRKWGg4BQgAAhBwUkoeCabMUyqDBEAxAABXBEACgiIABuxsAAEIOACX3BICvzUrQB1+lKAAIoD0RjvFyseh0B7KRqBYVcoTX0IAAFwcAAEuBQlW4LwBoC4BpRUAD4KhyAECKhiAAReAAAIQcAAxqAQlQHFwIkIAAMhEAPMKgAKgASQ8h0AAEIOAIe1AFKZJz4FjMABKQCTxVMQChCkOQP+MRJE+AACEHAIF7gadn_aNahCAAEoAlUmABEiUYQATMdAABCDgAASogjZug5UpjEdomSwEIpADZlCsmuoOH4TktyZTKv_DoC6KWQoYLXUguhlAAG1Aiir4zBvTRiOuSJ4CEUj0Ba+8oVk0chOX7JlMqi0Hoh1i_RSCBw8jgBRoiB2Bi0UFDQdN1ACyotEpiBaUAaSwSIPABv0qAB7KQCuj8EIAAIQcIoFNKgoLgaEQfaGgAAsjcAABUmACSAAAQg4iaUJKRmzMwAbXAoDC_JgZIhAIEAGEVEtAGIVAAB5PgAAIgwCZDoFAYThUBhjoAsgCmFZUACVCpUAFEh8hAACgCiJAAxUAIGgrCoFPjwA3EJ+AOiKlYFpnIpP0ExXa6etQiCAAAAVGBQKgOWPAF8Qn4AvAqVmELTORPlCs_QTFdrp8NCKxFwAAALKh8SoJfjwA9AHRFSvKSN+suLTvc6FIFdLoCRChgpAB1kQNzoAOKgCQ0JUVA8MeAnoA6IqVktLT4U6FIJSul07uhAAAHQAgVJ0THMKgt2PABCOH4AnkoVktDTORdkisEpXS6UEWg3AFZAYIqC4I8AEY4fgCdShWS0NM5XiSK_oJQlK6XSCg9AhjcGhKAHqYgBAGE0AKggRioDUjwHTT4AlJJC0uwPplFSsihXa6f_QgAMgNQAATItlSVAO4ePgGTgHD8tpcAKZLLQ0k2Onb1SRWCULtZINWkKHjpKAAmhmAA+4GTZAGyoAkJsNRioI6EVKkcPwAUn7S4NI5NeSKwSiRVq_WRQKBDAAAHgDmycV0FQR0MZDS+jh+ACkloaXHHTtm5IrBKV2s2QQgCoEMFJ+mYugbRHzIAEK+LLnalCsI6AZegcPzCAU8kVxyct9BLKOY2kisiiUrNZ_whDfQIYABmzIsykdEaDg0mQGuIgCLnwAxkqABZxUAF0eQhABtAAIAsD6CmJDipFQCUIIPQEOKwmi5WAuKl5aR6KQShRKNBJ2gRwAqRldBg3AEDwBSNBzJjYJaBwjYUR47AJSBaf+HzNyhWAVSiP1QgsikCvxsDYUAcKcmAqgVbPgDKJUSUtJzkqAC6VYQgA6iJioAQwsUAcA1KIATpEiMekRGoKSSy0LS5nEacO32kisEoOayQV0oEMIjNTqYZ8FxFgC4qcYMgDoBlaBw_ABSPwCGoaWSHSoSRWDErNZE4IT8NI9DqXUSID8AAOMAUKmODIA6AZWQcPwAUn9DYNKbTo15IrArNZEKnkM0mkeh1G2HkMAihWMxNdYuAOgEqOH4BKQH+tQzkoVjkK6XR0SE_MppA6gCDh+DtnNys3NmdaRzpOT04bNgFuqG4GAVSZAT0A36VAF5D6UgFdKeIQAAEQYAWVURIMeoOBcZg3AnoApVUXKwAPB87FIYErt3EIggAQcCgA41REgwA1AdyfAClmRcrDiC9D52KQwJXSCe1AhgAQcCgBqIQVqqIkGCoVINgJoAKSaFysAGecPxSH44"
noncomputable def WL3_3 : ℕ := zfNat64 21566 "ClAEjIAYVAByYAcLAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABs+AJCQAAAAAAAAAAAAB5kATLgAAAAAAAAAAAAMBAsBgAFbBwARwuABX5UAA1eyhAAAGAgMOGwDAQCgIAhBQAbAoAIIAd+QgBAgcmoAAAwEBIQiAAhQDAQCIYBtBwAbAoAwUdAAN_0dAAGRyAAAYCKsAYCARDANoOAFaFABKC5WAD3zhUrADD_9C_ShAAAAEQwDaDgBWhQBv0qAPkH0pAK6VVQgAA3AwALioiQYF4MAABUKAD_FysAHqgyhWAGGgnARoYAAiQYCJBgBxhwCtg4AJUXKwAe+cKlYAYaD+lCAAESDAATGgBIYA_BwAAIUOAAAcNAAAIIgAAAEKEASCkaCgAehwBAg4AP0VAAh4qAP9rQps+AAAAKnQBIKCIGBMFAOMaAADM5UAf+PuplQAdro3JCAAAAJBQNAwANBIARg0AaZKhywsA98aVAFdHtIQAAAXAwfQ4BKAzggNmbkoFoDC5WVGikFoR87FIAYaCEhGhgAzgYCIYgCg6AJBQhAwCIYBtCQABAAAornPgNGwAAFzYAAIkAQoQBIKBQGAB6HAG8LgDfpUASeRH0pAK6ULQgAAAA6EEIMAE0SA8oZAD0GBcrC6ElDpw_FIAYaCEhGhgZAoACIYgSgyIx4ABCfEsZgBmCpWWkKM5AGUKwYSlFdT+hYJQgfsHAAACD4AkFAjCwAAIC4AzqVAZT+h92MqTgHAV0c4hAAAKb0AA3wA4uAJBQByhcAuwuAN+lQHUtkfSlOQcBXRuCEAAAprwCZXBEDVmEg64TAdGLgDfpUWUu_8SgGH0pCyldLhIQAFyBIAL1cASGlZhIOuEwHRi4A36VFlLv_EoBh9KQspXS4SEAACdAaexLS2xAEIsAOigUBgABWBQXg4A3SVAA9_WVAFdHrIQAAATgwAB8A4CocAbrKgAe_rKgCuj2EIGFHQAAC4mFIGAEYLAABv0qAETHz+UgCkwk9UIAA4bMApAwAHPg4ABiFysAUicPQ8lCsAMOf0KggBFJCswCkDAFmFgDeGDcAweVAVk3aVAf4Tq6UuQgADhswW0YAtEgiBgAAMQcAJAKgATYVAFZFOnwA05OAA2BgAACgcAb9KgDrx9KQCukVEIG2GQTQSI8AB8qIkGXUBAAFQAlIAFc4fikArqXUIQSFDASjQHiaQcVFwDcDAduKgE4EQBKQDJh8zkoVgFdBsIUMBKVSaK2KgXGRkVgQAUXADRYJgYAAC8HAB_C5WAD1PZQrJi3AuDDQTdI0MIIAAAhLhLBgAALwcAJSLlYAPZWFSsG2FwYaDtlCAKvKQAAhLhnBgAALwcABCLlYAPTIlCsG2FwYTvqEAV2mqNIgVmwAeXADCoAkNAAAMQcAanKgD_x950qAK6OCQgAAAQBjzBwOLIgBaAAELlYAPZgFSsMDNwYTb6EAAGsKAAKZBsBwCyGgJOGwAOYuVgA9+8VKxiA9MPb0KggAB5EgDYSqVAew1cTGSEIlpUThxdKQs_8Ghbh87FIYQe12gimQoYAAJgoAAADMqAEDFRLhCARYVIYIgP_rQps+AABMFAaBsJF6JgWwPAfmNgD_pUAD1pZQrAIphNuoQAAJgoAB5cYYlAKQmiMFIAQ0VBBASEVIYIgC6LlPgAATBRFxoAiLjAGiYDwAAxDR2ALRmFysAHo+ShX_hiAemGgieRoYAAGgoAYNcCgsAUQJ0EQATYmAAphMAATQ2AABsFADKLiCIhCHFE4BK3RKAFrjC5WAD2UlEP8GxhoKPUCOAADYKAsPAChUayPByYqAloBKT_xdJSPZw_ZqUKwBpXS+aEYgGAAAihYQgjQqVgHYwlC8APMVKwWyUnJiSRWBUGj0ukFj6BD_YfAARYwbgAhLgBhUDwighEgAAExEAC8HgAHQRAAEMMgADaAQsPBwSEJSI+QIYNwHpHDcBaLQeFysFoDB5OD0UgVBolMNBmAjQwDjFQ6xw_AEAb1wMkSCISRMJAAHLKgAmBUC0MgN0mAGgAYQIIAQAAlQRB12iIJSEwB2UgDOShWC0JyTMkVhlIOKI5l62EEJSaSiRQVljMGZeVHScnqQBCXAiDAACsDgA4whKgByOaRlQH8GIuj1UIAANYUBIAFMg2A4KzEwFoC4AlIBFCmcP2blCsYgV0oShAAB5EgBtkwbCQAAqg4AkOtSouohAJHumyoAroUpCAABMFAAOLgBpUDbJgAAASHS5UACR7ncqAK6C2QjEAwAABHCYIgSAogKYWrCLASFZRcrABI9TcVKwAwgHQI5FUgNAAADuJgCQ0EYJB9pSAXAsASE+RcrABI9lIAYX9IzM0IAAAD4XAAioJeTQidAFEAAkOlSoAE_+Ps6lQBXQWiEYT+RUA206B0dHScDYSAWhbCjpiEDUDfCUgsoVgVmcgXJFYBtLsVUKggAAmCgANlwRxEABT42AKslQFZMNlQH+m4ukrEIrgUAAACQuC0SDsPGwABqBlhKWaUKwKzORqkisehcS6QUCIUMHoAC0SJ0CIHgzAJAdCNgCUgVm2Z0zkoVh_gONtdPxoRiAYAABSFruEQC0DCYVUHhqAA3KFYLSszkzZIrD+wcbS6BgQoYABCjIAEQcQYknwkRgegMJgHRqAYxKFILQ6AJWtiWOnbZyRWBUGm2skFzaBDALMtAAnDq_kQBEA6yA2ZgApJSJSy846NeSKwXOFHGsiUUCGAeaKURHiXlR0nJ6OpLQkAIFwAAAsHAGpyoAHvnSoKSV0cAhGEBgAACcOwICDGgAA36VAA9lIUkro_BCAABOHAAiLgnDsCAA31GABqFysAHqripWFJpJhMQoQAAJw4AERcALKgiDgAAAAHFQBJADNTkWRD58AACIOAkARFwTh2BAAjaXAEpApJFTh+zkoVhSSDXSeqEAACcOC2JHQAWhAEC4AkNAAAAAAAAAAAANAApkCMXAAqgiC8HABfi5WAD3YhUrGIBh_+hebQgAA8iQAgmwAAXg4A1OVC6CoB750qAK6PYQjEAwAAAEy4AHphYmhcABUC5WB0B6MkoVgSiLjDQTaI0MxAMAAAppcEyiYAogLkQH7AC5WB0ENnD8UgG2ukEMiFDMQDAAAGuOgDZcASGgPzYAAAHKgyYAP+fABYRL50AAAAbLgQTYADXp8Ab9KgLSho+lIFdrpVJCMQDAAFaa0ZiABxcBZmgAClCYHocAG+LlY5AHoXipWNQDCZ5QgAMEMQALTJeDIH5sAACwOACgFysAHonShWAGGg_VQgAejSkIFJSKgANeAPiwAyKDYeCCbABFA9BQBukqAB7+kqAK6PWQgAAAqy4Cvkx_weHVhwAX4uVgA9J6UKwAw0EaCNDR4NAAA2AFS4AkNAXGwAb4MgvDQAd4uVgA9ReUKwAw0EwSNDAAABwFwNILYM6AAKQhBeGgCapUAD2wZUAVkL2hF0KgADoAbLgCQ0AAAAAAAAAAAAAEGgYQUKyMEE2AAC4NAFei5WADTPH8pAC6RaQoQMQC5RUAIfHhIASGgSC4AF+GQFA4AL4XKwAek9KFYAYf8oX"
noncomputable def WL3s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL3_0) (dpk j 1 WL3_1)
noncomputable def WL3s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL3_2) (dpk j 3 WL3_3)
noncomputable def WL3s0_4 (j : ℕ) : ℕ := dsel j 2 (WL3s0_2 j) (WL3s2_4 j)
noncomputable def WL3 (j : ℕ) : ℕ := (WL3s0_4 j)
noncomputable def WD3 : ℕ → ℕ := rdw WL3
noncomputable def ready3_cuts0 : List (ℕ × St × ℕ) := []

theorem ready3_cuts0_ok : CutsOk ready3_cuts0 := cutsOk_nil

noncomputable def ready3_0_state : St := ⟨26112, 166402, 28545, 39936, 29184, 45301, 29666, 44151, 53248, 124374, 52016, 123142, 28545, 121600, 26112, 285696, 54657, 194947, 83841, 224131, 113507, 253797, 166755, 378171, 246336, 430187, 274881, 496835, 300993, 673274, 57729, 78725, 87395, 108391, 140643, 211769, 220224, 263785, 248769, 341824, 274881, 627520, 58850, 79846, 112098, 183224, 180288, 235240, 208833, 301888, 234945, 587584, 82914, 154040, 141499, 206056, 170044, 272704, 196156, 558400, 111833, 176390, 140378, 243038, 166490, 528734, 80561, 189790, 106673, 475486, 54657, 407296, 0⟩

theorem ready3_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD3 ready3_cuts0 111 355) ready3_0_state = 62540 := by decide +kernel
#print axioms ready3_0_cursor

theorem ready3_0_covered : Covered (toCl ready3_0_state) :=
  ready_cover_cursor WD3 ready3_cuts0 ready3_cuts0_ok 111 355 62540 ready3_0_state ready3_0_cursor (by decide)
#print axioms ready3_0_covered

noncomputable def ready3_cuts1 : List (ℕ × St × ℕ) := (355, ready3_0_state, 62540) :: ready3_cuts0

theorem ready3_cuts1_ok : CutsOk ready3_cuts1 := cutsOk_cons ready3_0_covered ready3_cuts0_ok
#print axioms ready3_cuts1_ok

noncomputable def ready3_1_state : St := ⟨26112, 166402, 28545, 39936, 29184, 45301, 29666, 44151, 53248, 195501, 52016, 194269, 28545, 97680, 26112, 285696, 54657, 194947, 83841, 224131, 113507, 253797, 166755, 402703, 289897, 454719, 318442, 483264, 344554, 673274, 57729, 78725, 87395, 108391, 140643, 282896, 263785, 334912, 292330, 368320, 318442, 647162, 58850, 79846, 112098, 254351, 223849, 306367, 252394, 339775, 278506, 618617, 82914, 225167, 185060, 277183, 213605, 310591, 239717, 589433, 155394, 247517, 183939, 280925, 210051, 559767, 80561, 227677, 106673, 506519, 54657, 383376, 0⟩

theorem ready3_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD3 ready3_cuts1 110 66525) ready3_1_state = 111418 := by decide +kernel
#print axioms ready3_1_cursor

theorem ready3_1_covered : Covered (toCl ready3_1_state) :=
  ready_cover_cursor WD3 ready3_cuts1 ready3_cuts1_ok 110 66525 111418 ready3_1_state ready3_1_cursor (by decide)
#print axioms ready3_1_covered

noncomputable def ready3_cuts2 : List (ℕ × St × ℕ) := (66525, ready3_1_state, 111418) :: ready3_cuts1

theorem ready3_cuts2_ok : CutsOk ready3_cuts2 := cutsOk_cons ready3_1_covered ready3_cuts1_ok
#print axioms ready3_cuts2_ok

theorem ready3_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD3 ready3_cuts2 128 1) (ofCl (RC 0 0 0 0 1 1 0 0) 0) = 119884 := by decide +kernel
#print axioms ready3_parent_cursor

theorem rc3 : Covered (RC 0 0 0 0 1 1 0 0) :=
  rcOfC WD3 ready3_cuts2 ready3_cuts2_ok 119884 ready3_parent_cursor (by decide)
#print axioms rc3
noncomputable def WL4_0 : ℕ := zfNat64 33239 "Sqo2QoMFwABnQRkAFkCyDsyYshhASqdAAAuCgF5CH0XByBOAQgEULIF0FHkxPFoMIBZToAAFwUAADxIlzZDFVA6bBaEgnoHkD4AAAAYHAAbuLgAAXCQA9qpakJfg8FDE4D0SkAFUCyTQLIYQKYHwAALhIDkkrwhEBkFKmYaiTSjWQ3SkDMWK5pCqVR+ahTFphMJZIpJ5WhEUAAARkBJiySgYcRk0JSoUwBMFeok0HSZTAolUmCxXMM9KpVLLmVCmUJMtmEwlkyCZTopBBIAAIwmSw6DmQiZTKpoFKeTWrKE8J8KRRKphCqVSqUSaGEogH4+fl023HWiqBoyBOTY6C1YCEhYPH2ZWJUBZFoMQ6zwuVlyk4kj0YgSSa4ZAjymASkGEy1mYtyQoYAALgoDUEpD4+BvwgVvAAUYBShAATYBgIwgksiATMRAADiIAAAADBMAAAYCAAChADD4BCXAMBAAAAAAAAAAAAYCA2_Jx0lAGWEDVLiJBlADwASUaZcEZACM_ONkbFwABUAgABSBgAA7wJHCAYCEaPALoiAE6PAAAHkBR8AAC42AACkDALTOhuBggFQBJJgIdHwB_5CABKgI+AACCdAABSBgrBtaENwMPQMYdNwkogDYBIUYLmwBJEmmUwCa0Ga4zQgAAvgwWgm0+AJCQ3AzKlIELGwAEWSgQ0koUA2AD_5sjc+AAAAJIwm0+L+UgQsbAARZKBDSShQDYAJqmc+AAAgDAJtPgCQ0X8pAhY2AAiyUCGklCgGwAf_NkbnwAAAq0+AJCQpByAFS2TkCSmeLgiyWc5vLiGklHoaDYAJrxRGAAAFgH8VCSAFS2TkCSmYLgiyX_Z1mEuIaSUehsNgAmr6UIAACAUAro_BwSUQqWych+kqkp+y4IslnNzS4hpJR6JY2ACalISI4RsbgABnR8AmggQCnmKQIWNgAIslAAJJQoBsAE1m2fBFNIBhAL0fA1BJbRWJyAI2AAiyUMcVABJLcg+AAmoOlJXRMFUAYgCC+T8HBJbSpbJyACHLgiyUMcVABJLIQ+AAmrAkaGAGOjkKMmQMzJmMztnMmNOG0D4pfXDcDE0ANGwAH7CIAAgE2NgAIBNAACkDFOAL8IiQYD0JQvDD2gqlIBayRR6Rk0llKipbT4VKwItNKJ5jZnQQAApAwAEhoIScpXJFYzhSpzEtZIrKCWSLMSimmsxHRndlCslJFptBFeYN6CAAAAevhfpcAwEBQAigCCYAANJsI6AYfALQKGLQAABgIBB5cASGgacPkblCsKvMDYUiCTIug1ISbSyK7KF4EWaiEagAAAAtWEQlwNOHyNyhWFXmBsKSTi8yLoNSEm0siuyheBFmohGoAArRGAKgXK7kQPRSFWYikmNZO8jD+Nmf4DaEtCaN5ZBTFysCLNRDNSKH_TYBB48DI6BjC4AkHUURASkKsDDYF5QrAulMzBuQk2lkqWVARZqIVWmwAAApBB5cJ2RA9G2UKwq8wNhSTF0qxfBqQk2lkV6ULzvFQRZqIZqAFISAFoBPC4EEiPtEiB6CMkVsPRirMUTlCsmNZorEDZmQk0lkF0XK4SEWaiGakUByhcAtAOQXAkAfO6KlYVeYGwpP_mUM1i+DUhJtLIr0oX_MLgizUQjUBCQkAAfHgk5CAUBlkwRQ7JMAAGkggDD4CKASs6lcVAAAILLlYyI4sfCkKrlDYUhRrIdw2Zg5NtVH6FysCLNRDMSVxUAAGIyqQRqhAGL2CpWE2ep7KFZHS7OpKGoG0kg+yheBFmohGqgEKG4wiAAAQKXxuNVKIglIVS4myGShWFkJiF028PVi+JUBFmohChzUQQAsgFbLgl_xEEpCqyU2JuUKzKWQSAbM_oPxdNtVLilQEWaiEAABkGxHgUEuCWSQCERUe+Th5xVawyAXkbBZANUVB_xGAAMgCBAPSXAARIW0kVg9FIVf+mQpFJZrIPo2ZlQLi7aX0qlsfgXKwIs1EMlAABMGQNgAHCGKlwB6_wqVhVZ4bCkLNZlq2DEMJpLI2wuVgRRqIRKOMIj_0FYSicNLiZmQCajBwS+pg7hZED0BZIrCrMQ0kiv_6InLJZA6GjMMJpLJTIuVoEIs1EIlHHEQAACli5BkJ_4+COSKwq3xMhSFksgxPgsazCaa3LFMakXKxKEWaiESmeNnGEQAABjS4xQiCUg9jsbaeKgsgOQwm0AS0SNKgIs1FoOMIgAAPswBlxBKS5fQiBOhUrBpVBSFlWi8LmNGYYTaRTD5UOQch0Eo44iAABSgndiAc2ID6XAcxYE9aEVKwcjUqhYrCsgxISBJs1lklIxCLNaHEXZDaT6FGSCAADCi_XEY4pED0UhVEeYNwvkismNZBqQk2lkaqULwIs1EM1HIjU2EgDhjR2DYMe4gVBEq5kMgxuVACkABAbDU5AxAAMQAAAIREAI_iCtFwUhEBUPpSFXjxsKQLoNSLCTSUSsZUBBkoRGrUUIAAIQ8B4IqMjkyZEf+PhtlCuUlXSxsKSYq9WL4NSEm0sinSheBFmohmoHFIAAjQ0ApkuAJet_zIp6PShkismlWYimizGs_1Rn+GzOawm0lkQoXK5SEWaiGawySgAINCwUlOCOjoudk4VgTJwDWUK5EBRVN6ZCkqoDEsLDmjODKCpWHEo1U8YbUEQYRAAABJiBWJk4IDJFYUZiCUkVlVqtBGJYTKWXioxpyhWHEo1WkzEjSFDABIQBF5GAj0kTgeEkVyGBijGcyFJVUJLVBGJYTKWehowpDiUarSZildAhhVAG+EQNjYACQ0CsTJwFiSKwozEUlVLtoQxLCZSyAtKFYcSjVa8pV6zBvQQAADs3MyrFhME4mTgK8kVhRmIpKqXXQhiWEylkyiMVcoVhxKNV+elAENmdBCkDwAAXkTJwCiSKwowlMhSVUpWhDEsJl_8tH0ipWSYSOJRqo6g2Z0EnIBjUyAB8kTgJMkVhRBSf5Vgr6EjMsZlhMoJqKlctOJRqosw2oJOQDGpkLiJd4o1PjpzhUnCjMTbkisqtVoIxLCZSyLZGjmnKFf8GI4lGq0mYujQIZOQBUBszA8pGwAYZBKJdQHTyyRWNSqMRSFUq2xQhiWEkjRnKoKTKcSaSRvHD8arGQobxToAAFKPATSPeZEAYmTxkFMtqKBDYUhZIVoQxOpdstRJSHWolWHiM0kyEkhQ6IswAGUE4NmcPSBODkdBUnoNNGKdSRWFUq0E+JYzMthyAwZyqRRSQTiTSqSRiI9AhxQbpiAAKSI5ZqkgzqCxYTCUGJkisU2mV2JGQpCr_hWoIxLCZSrUhGFIcSaVSS7o0ZhVQIZNY6AAEoLjJFY3FMrwGMhSFU6WhDEsJlKoKSTCRxJpFHRGzGkKGF0igOQYLYBKF0OoLFScpoxGKSKwqlBGJYTKVSKKXIlxxJpFJIxTCeQwukWWgTZgtgmhVIE4NsKk5TRibckVhVKtBNKWM+wLwFWK+YSqRRSG0mkUkjEoZ5DC6RZaTePgbMFsACTE6UTAs0kVgxGIpKSclQhiV0ylUFIcSaRa9LxgDZ4iFDC6RQHJMFsDw8pAAtfFhNE42B3BcFUkQVAESjYDSCNioBqAB_ZKAABAQBdxI+EwFBSHQagiLFYVSrbFCGJYTS0hUvkUUhxJpVJI1fkhQ40E05AAFuCYCiPyRWHQajALFYVSrQRiWE2DJrKpFFIcSaVSTEIwbkGYsCVgAgg69ofK7IE85D0FSeg00Yr9JFYVSrQVtljOo2EwlUiikqm0mlUkjFSp5DJr_EekIAQgfO39kCf8J0to6byWg00YugKk4VSrQVfGS+o10wlUio1JFZVNpNIpJGJpD5_TS6k1Ajy0HtVAALLDobRONg5cZBVJEFQBEo2A0gjYqAagAf2SgAAQEM0JghgVAPaKgAalhaU1BDAqAmgJ3Pj+yMATKOgAvsRexMnAUgRHRFSsAOKcPysmkPslQVOtRAwahBFAJoHQHx8eAnOIDbXG8EwW6KgaFQCoAmphLP9WIHWFRhKiAic+AAHIdACfMglBy9QqTjkVCtPGITyRWNSqVaCuo2XwmwmUqnERhSHEmk0cgENGdBCLMTykQbNOgzCcKk4uCZHPSSkmmr2MmrFSculUoLujJfZa7YSqRS4kis6m0mlUGIuzyGEWY_dIg4edFSgoIRtpgQBgVjwAxIgLsEwAPQAnmRAAY2NgAAANEcz+TAeQqVhVBobCkNwtAMQwmkP_lQdajVRdxtj1CN4LFkAoAAy4ASEgQBm0LmMBSFUFIMyXhyBY3LCaXZLwVosVhxJof+NsyoQAAAjQOBAGNEZLwRumTyolLyhWATEsNp8EvHVyoOtRpoKBQgQgEFJLQZAFokOZjgGAgNEwAC2x4AJIAN+IgAFyFQAAAgcSRoKP8dOwAIJEwkyUEZIrCrUSaow6bldsNhDglCsOtJLNRGo4kaGAENpdjuqDoAQZBXDcFAE6LGYD2i4Dqh8OQogE6JFYAA9AABmVAACvkB1cCANqouAagRYIgAAAagAaqKgAADAQAcK4ADJAgDLeRg28ZAZIKgCih_JiAAmgYOPgomkB_pUA_fOENgwIAxNB0hQvCqF5JE4CBKIB2RaA4gEU3yEf4UjSaSaABCK4bgreSMCYCxmDkACihRApYnATQL3HwWEBCRMANkWVwangRAwY0Zg1AVKlMDIUUHpZAASpTDadTKdXWv_IQEk0hlu8HAELFmUKsIEQFRDFjMGoHRMpgZHI9ooPSySWwGRREptOplLfK1sggSTSUf+M2Jg4AGdkDGFk8iIGCGjMGoCZUpgZCig9LIIoUK4bTqZQrchEkJJpBAwcAP8WtQ23ARAMQagKFSmBk2kfUUHpZABGRRDadTKUpWiDBQkmkOlBwO1NSABFYAGpAB0IAKbADiIAmLAAAAAAAAAAAA5wiSclRwMYdNwmh2E6eTUnNFKjYWqJQ1c8pTw4lGohPQu2GklbmYjhUrBOi4imbzoCLKRPJUsGkdFBooVa6A8k6eHWogNXPIYZS7_1eCUhNZMqVAjk5CgykcyVLGWmxQaKVEuh_T6mhxqICCkJ+GS6WayDPShWToAS1gI0SWCCFa2UkpoBfObA9opUa6VPNiiHGm0kEvIT88mUylEaA1ByLlYKo5UCOBVBGpEsYOmUwB6RQogMs2TwpT1ZoEdrzcTQB6aSTVRZowCknQDHZOsN0SWAlV62E0QApTwE8nRFhNRAD6oUz_DkUQGfIT8umUylEEJFysJwSo4rUCOCjla2UkrYpTwFknQAkCPQQAo1UgcnABwPn81IpVADGSKyPqQKQ5XiUGBAu2pAAAkyWAGsVICgCUHYkILthMIcdKgLCzuLmwAWpAAkoAMhADioAeLABA4AAAAAAAAAAAVYSFTJYEAZVyE7BRRszAK8SKwJiQQCtSMw5QlgABGNm4AAlBuTBYcNmZcABVxfWOBAGBePAEImAuwTAVCPhaAB4SBOABPYqAAjoLjY3L4JPOn9eYmIXOqgGAgNAwN4GgHEDQAOQAbwNAAPTIgAADARS0tKGgI7H04CHhtK"
noncomputable def WL4_1 : ℕ := zfNat64 33248 "DKkRWTobcZQgAA3BwAEmIVI6DJpUAEguVgUSUgXZgKRKQtplE6G2c0IAiAAACYhTDoE1FysGn+SYCBcrAokpCs00T4VKwtthp6pSkNqCAAYQ2AUg6BCBcrBpJZScImKaFQ6lIVmmnSPlDlCsDaYajMaLIUMJ6AdQeBkZApB0Cai5WElAgXKwKJKQrNNFifIMKlYW2w1EIhszoNjkYAANYGhyDUihcrCSykCyplMeuKLlYVmmz0xxUrA22GozFiqBDrE7AAAw4fg6AEhIohZdB0CaC5WH_SYBxcrAokpCs00T8VKwtth4KpSkNqCAAAUAsuY6CUgHUmysVKwpp7jqUgWaaPZ_lCsDaYSgqQQQQJpBWBkvJkZGcGpACRkHAVBn8qA4aVB_pSI0lC8C6GMSoLaZQrehAAYsPgAJGQcBUDJC5WAKguVgUSUhWaaSkLb_FgzvTUk7G3G0ICKAtZiAAUZBxFQRB4FysJLKQpvfj6UhWaaYc+FIG0w1GYkEPepRNB9REDMCAEjIOAqBdRcrAlIFEAsXKwLtNJSFtKawZxRxtmdCAAgsXApACwsEQUARYuVhJQ0FysCiPXUlC8EkrF+mz2UgltthqMxLwhQyk65TgBiDIBurgC1C5X9AaGMlO0XKwKI9HIVmmpmVKbPCpWBtsJtTMaOyCAAC0OAEahEiHAEZSCULRw3fCUKwpo8UoXhURqGALlYG0qz06htQQAARBwBKi4AQLFAHAHZSTFShozXMVKwegLQSl2PykSkLaWSLug2n6hBhAAAphcUAcCQOykAIXMxi9wqVg9EcpTx6LQSlzWL5RvyfSkLaXSKNU5oEcAuKFsAAJAXFAHAHWBFSsFoxLQVKwegksoXglLIGsKlYG0skW5RtQQLIDkiYGZsxPwAOZACHkMErFysCzk0pAokpBzWaaLNKFZBLbYSxqXBjaggDImAJoACDIKxAfgKgqVhJUTFSsJNNHqDi5WDks02evLKFZBLptsNRmKr0CGBVAMoYNwZbsSh6BTC5WH+yZGhUrCmkpl4nFZ+OnDGyhWYQ2mFRKlMaCAMiYAmgzdCQh6A5ipWElSgVKwpo9PgXK6TJU2LNN_+fHtKFZVQUvG0w1GYkECqAZQwbgASMiljyGAUi5WElJYVKwpuxj6Ug5rNNRsfCkLptMNRmKz0CGBVAMoYNypGVTUgAaqBbSwNqCCIKIIOgKgGsFQBW4uAB0BUBtAugfAAGEACQkEQVupKBVxcrCSykBlKU8lIOSrTRmJQrA0mHXqlFA2oIAAAIC8FgiCgDVFysAERUrCTTSUhJN0tWwRUVKwum2wjPDaggTSqCFgoBLFUAVlgnCjWGwXqJgBKADQKb_oqOSEwAEzzYCyAacmACBpBwgYIgocgYYqVgjY2lIAARYrhWQS+VBbTkMwB_Qgw0WYhNQAEGQeh2kqAAkXKwASStTCsg2UoVkEtO+GICCIIcN5ZrIaoLhBw2EceOwWIVKwJSF4U4gl2VqYFkFSfCkDKYQXshPySbSzWSwLULQCYKwAOXLQM5lQF2yo0pXTgLISS6ApC2gcqQjAllbq0GoC4DzuyIagQ8oVgGMmFIE0gn4VqYgjYLJNnpNShXOQy10DKIT+qmEs1k_2zBlKF5d1MmDzYzNk83U046LkoEEqhuBg2BwSkOTG2GyoAMoCBOJPSoACcaEAAFIGAQcdESDZpJieyaLgkpzzRuAFSqQUQIRIAbMwAmvrEYAAL4MAcA6IkGjoGXLgkpzTRuEECpVBSIEIieNmYATVxKJHAAC+DAaDhPZaADpwCFCAGFQDAQHxjoAegAAAAABw2AACkDAOhThuBgd0ZHyOgMM8CoAegBhKpFQAxCorY+AACkDB6AvMIT+VDcDAkMIVSoFsxceVAaQghDayQBKgJjRQiqNSAAC+DACMLgfxUAliVAV_+ZdJKgNI9U8hgDSyOnKkGBQSkGhEAACkDACfQgf5UASEhuBgAFIWQqDDjULXPgBpsl4AJj_46AAAAE8hBqCoAkJDcDAKTKgUzGzpUBpNNIQA0uiCSoCYjkIgAAANVCDdFREgwfoGhaClN5g3LsXKwNNGFoggDS6LoLgJiOQiAADNNgBzoQagqIkGAMi0FKZTBuywuVghNIeloggDS7+xKlkXATEchECHzMAACfQhFRUNwMAlcqBTMXElC8DSaSQgBpdEClQExHIRAgv7jIGFHwMjIzMk5+BqSoAkFDcDQlRgPyVAObKgNJ_8+DbHWZLRNMqAmI5CIAAAJfKgCIkNwNkRKB+ZUEx2aVAaSehtjpdJplR_YuJiOQivJSAAAGnlREgw_EqODkWk1c+YN0HFysMJpKs9DbHS6UUWli8FpMRyETwplMABWgsAAHCDQFQ3A02koCIlQD0SoDKCOQH4bQyWS45UAMRyEQ9YtAAAAzOEJiQ3AzokYAGFmQxSYAD_0FFQABiDsDm7LQABhAUQVDcDf+SgleVBMeulQ1pmMoPQ2hkuleyoAYjkIlQUgSgkB6SUDMCAgMrYgENCDClQC0eG4G_6FBpAy6ZQrKgMoQQBpZFJlQAxHIRAAApAxGm5aAEhoiEyAvRcrCSh0LlYFEeuRKF4F08ClPnspC22Gog6NmdBAAADc4QqwWCg6j4uVgxkspEDTe4qU5Asm1fCtTXGSKwtJh+KpTGggAAhBgA_cwAKqBoGAmsZB5HklQA84sZh9GoTJKgNP_EIIsIQAAGgYABpcASGgRXJJUHk1yVAUQWgXUWJxksqECbSyEwUIAAAAYXAiq0C5WHmSkyLlYFEFoVk7CZHD9FSsQJtLJ942oLlj4AAAAS8ApQgGhewy0EVeCULw8ibC5WBRBaABF62+hOJSLUCbSyYiNqCAABAKAB_hYgbQEirAC5WHmSnaLlYB3TKYLSaVkirQQpSIQ2lmovUNmdBAABaHAeAFF4H_xZahcrDzJRaFysCjmg+FoVkmkEVBUrA2lmozENiFDp0VAAADALgAIvxDMA9IuVh5kppC5WCZFKeC0GlZIo8coVg0NpZMotDWggAAaCgpqSmdsQJ9bBeS4HgYChxcqCWkaLlYRQLofTqCPiheBtLIHQAADwMWIGrLgAI0D_6Fg82DiEpLGYWPUiWgWR6SzKgOJBV4LALqGAAARqXJliQSZqHHDzM7ssZgUSWgWR6S1KgOI9_8HHzNhyx8AAAtsuuMqFIJEwizUOJliIZLwqI3YyXgWSCJHKF4HEghEagJQsZrQfgOhSACny4PxZBQsTHWJUeahxsLxyxmFRJaBZHplcqA4j0I_8Nk1oQDEBApkTY7O36GCA14ATXAD6IAkNCaESC4DKRcC2mlBKLWRnC9KQym2wmZkL_6EAAAIMXuaFiaF0C4JKYkoXgtppQSi1n1qd_teCcVKwym2wmtkKggACRFgCOV4BrXCaHWC4JKVMoXktKP9j4ghJrNNrrsipWGU2mEILOEKGcYmAAAUCvAOK5vx4mhdQuCSi0ltNCCEmskxTv7r0pDKbROsGMnAhOKQoY9ACTB0DoJvXgL1cAGlgDUUNwkTQHeVADhKgWhQSi1kPPlR_pmNoE2kIAoIdQE2LwAGuAYUQ3CRNCExcBXIuBaEOOqCUUsn_l6UhlNphC0iFDCaSQKMJRAzcDHzoASGhRAyRUrCyO0KlYU1ER1KQpKVTLNNFUfCkNJtMP+VKYkYQoYAAB0FEOqlQPBgtnQyoAFpUf9rF8NYlQG3PLEEyUIAAKQsJiUQbSUKyqyUs5QrONJ1NHrHi5WUks02eqcKlYZTbYajMT_IUMAAFwUR5zhMUQkwVKwsyUUhTaJH0pGGqUss003x8MkoVhpNphqMxQshQwAHOEwAow7nCYog2koVhZkoBCpWFNhEfPOLlYBtInlmkhryhWGk2lFXStTGtBAAGIc4TFEFnFSsB4xU2ckwpAmj2UlJLJN7afCk5s0ZzCYSjuEyIITZzbQWEQHyXAAYdzhMUQ+eVASVDGSkHkJwVEoXlJLoCE4lIGEqlIjbVaEBxAABAEC8ABRgTNUGVjgAAUUeAL3GwAGoIgAEiGwHUAygB0EucJiiCii5WBJUMYsQqVgTRWhcrKSWSaIRKFYGGwrSUhrQQBjRQBk5wmKIGZJFZN1QxyUUgTRKHjtMxcrKSVSaPTZkisMphLpRGM9MUIyBNNdB0GS8mRcBGpjYDslCsMOdjYUgAiyheXQyVQlIQTCWZ7+0yoIAALgoAEBkGoCkMIxFIdPRJ0ajpvBcrKKWf9JxpYqVgSUowlkvB5DmNBAABcFADbRjUYChPK6+8oVhhkrcipWAyUiaPRaE0sk3p59KQaYTDYSiw42ZkEAAFwUFJmKohP46ABSRWACVqcwT4UgTUSnD+W2kk1Um47QhSUdvMRlMNRmJaUCGAA5wmBCIlAAcZAfVFUlBaEgGIAAAADEADNJUAAC4SACXVDodCeMgADOgDIP_IR_5CAsgsEmAwgHPOgAAXCQAFKocjoThcHIE4BCATQugXQUeTAYQCynQAALhIAtTECXth1JhEDelKmVEo1EmhVXYsV6yZS6YTj_6CFM9MJhLJbgwb0EAAFwkBJHwnB4FnJwE7FIAGoFlPJsAGEsgVkofAAAuEhAE+3MRAmdMpgD9SJ4EEAmlUghHk6WUQ6ln_iEbxPgAAYiQG3N4Jpj_wrAFUDoycAJuTgAKWfAAAaKgAAXCQAN+IO3jBaFUk4CbycAGUagE8k7_5UAA5zoAAFwkAIYWPE8hg2LGYKNTKYWaaAlQph55CrJlsM9luGEIKJRDDUabfBKoIAElCeECOeQsVg9fUmUybUSasxMpgPSyZbCORaPSqJZMpkkql0mk0ivnPIYZSzCtSCSf5Ijk2AQQaCUCHKQTGmUwPytTppRALNhsI5lozDyGEtWKNNDDUa7p0tUagiGKgH0CyECOrgoXg0pMplRJqkEymA9LJlsItFI9KpLkymSSqBBctk0mkVuB8_GWpEmelUbwuZxaCY3HgBeqAqLgfEpAOUUgD_rkkJWByD4lIDaAmE+AABiJEeEbb4kj4LAsE9UIC2aMAE0AJ6oQAALjYAAFwkF8aDgoAMQgBxkADLgBBUAEGgAgkAAAAAAAAAAAIdBCQu1AQoD4CzaUqAOjELlYgBOJIMQJIeDKgMJlN+G1BAABcFAbZgMDigSaBcShWeJUqHHwpABVlC8q1EAS5XCUlUMJRmr8jb8qEAAC4KMEBBsQohBAqVl1U6xf_+TTyKlYU1nZ1NY6TSzTaaKZqaTSYTTfo2LygQwAAYhQBIjP9g4C6xdPajP5WAWUKwAWlRKoPDR2axKgOJFAh6EAAC4KAN2jFo+iBfOSTBwqVlWokEeJQrAmysPhaGHPqZRGpKQCYTCVRyPWiMGcAAFwUFIFNxghCNBUA80mAPrHxhAIDkw9AAmZ0AAC4KAHDjDjKqXkJuAsBTCZOAJQAaAAUwmTgYQJyAAC4KACjjAEqqNkKDBcAAZ0EZABZAsg7MmLIYQEqnQAALgoBeQh9FwcgTgEIBFCyBdBR5MTxaDCAWU6AABcFAAA8S"
noncomputable def WL4_2 : ℕ := zfNat64 33248 "CcKg4jVCoAJIAAAB1UZ8AAG4KAAXhC+lC8EdlCsOpJ7eVAfkShyBho3gC0lYigAWNCAAkgbAOyULwBySKxqcR4IkuUgEkcm3_DsGlEr_qsRQygTbmoRgCoAAC2yheANyRWHH8CVKQCSOcIMwBJ36rEUAJO40Ik00AhcPA7Ag4_eAs4Q_OVgEYABKOQAkgAJpGAABcbAAAGAgPJ7SheBnkymIdo5nFxSJLlIA1HJ9OqnliuEmqhZNoE2TJZ9UCPK4yAAB1Y4XKz_acNBOnmk4qSRJcpAOEYNxyHh2OoEkNitXspZMrkFopNBNoAZDFgdkwsPBTGzAS_EukXAMQ6tcWq9lQAGkJwrAGEK40ZwCSfCBhoAAAPSMFoxKJISRWQTqSQBFysBrSENQJoCDKF58o2NtZB6y5GhgABrCgpAkbEFpYJWUkVKw6klD5QvvotARS6bQBeZQvJoAPbroQAAEAYAbeOnZNgkqAUgdOKgAQJRKICksh5AVqfAAARBg4+VO0LlYGtJFZ5OKckSXKQKSZTiAOrKF5ZJ5NQD3PKEAANU2AfCpWCIuV12muXJFZ1OKfEiPKQ_0ZEkym2mgTW9FyssjUy+iWgehKRodFAAjwsToCD4NmgoM7gzYC+zhuBl5lQSIKg4k8yoAPoAWQAIKOzYKiEAAFIGAGGXDcDAASJi8DsAfJgAmh9AGKdAB1_8HB6XgAApAwD24ASGgPyheFFxZQrDqST_FysmIePLgAa6WLycyWYk1FegRwAAACQ0B+ULwouJKFYdSSf4uVkxDx5cADXSxeTmSzEmor0COAABSAWa4HgbhJ0EpDqipInniLlYAAgQjkXAANaqoQAAHgYACRkFkKjBjIExlQAJw7i7SoByABEahRSoAJqrBSAAA8FAHSKj2zIJtlQdSTg8qCcykMcNARmoB0qACatQVgAAIAwBsyoAkNLrGwF_Kg6i7yoByKQAiNQMJUAE1hopAAACHyoAkNMyGwQ5Kg6kmpZUA5FIIUIjX9xEGEqACa5IUgAABD5UNEYNwqjCLlYdSaqwuVgORSH+IYIjUQlxLgAmr2FKfTpCAAAADvB+irGiqh5kB5yoOIpcqCcgARmoSsqACapAVhKADGioHR0dqakvA1SEASMgNgUuilwdf_q2dSoAAHoAVUYgTTZriEAAB4KATehAAjYBVlofaruUqBiyMAUFJZAnAKqNRGhtVdCQMHAAAAN3hrSE_8VBVRsZLw6lk2hcrAii0UgPRL8oCPwXRAHiqjEIjV+aBDAAAwDAElQgjJkABGuqPg4IpdHLgydarr8qAAB7_omAKqMQJ5sAAAaBgADbwqFCAEG5ZKwCtC4unUgGVABFQegCEqoxAlm0MT4AADwMFNTU1IAJRg3hcIMRB_0uDrVZSIKWg9QfCEqmEGqlQVUYglAAAPBQCDy5YUiCaKssXh1qoKi5WFkDeHzsKphDphcdw2KqMQiJQAAKoUAaguAAkXOLw6iIIClwdSSZUARnOgq_+YgcWVBVRiCUOUEQAAKgLl1CJAnKa3ksXh1f6qV5SFkkk5PqcPy7XSDJWpli8clVGoNEv1CoAAHYcAIeBG5fECNNgiCb0ouXh1KspF5KlsJzSSrXQFopKqNUMCQ8ShtMi3CQAACYy6a0CPsUiCaIssXh1KoMipW71SAIsVwnNJqtdAWikqo1holFYXTkACKDROjoCJ4gmRcY0RBLQ63eVgKFSsAzkff4aiqYQauVD0qoxBKAAAYBgFQFxunD+kBEd8Tv_Fy8knEqlcKlYthUthOZaVa6AthJVRqERKJ0yAABGDBSgmdnYkoWkXLwHiUKw6klARUrhsFAIceGoBBaugKFKF4E0Brb1CAAByJAAJYntC4FNlCscnXvSVKQBSjw1P8LwCwyoKSAjNCAAOIJAAJYityheFFbpIrFpxPUiS5SEkOcRHxqF2ihBeAXKw202kg1QcjQwADCHQAEmIAkLBaHgUh9kisbM6cyTKQKZjiMahd_ajBOsoXhtptJBqqpGhgAAAEmIKMoXgkskVhxKQiS5SAHRqFkMXISFi5WFJAatjQIYbS6AJMkVk2NwN2DpK4AkHBsFYUJg+uTAdBJgAAeh7kmCogTkAAAAkHxYXC0BSB8cO+mEpWRUrADKF2ASUFpyoKiA1tahAAAKQcAIiSCz0oXhRNGSKzacWbJEeU6eMiSMRCNQuu1RJYNXzlC8NtNpINVXI0M6qdAABV5QvCinkkVhxXciS5SfSSiHY4jGoXaKEF7JQvDbTaSDVVyNDSwNAABNxkveWULymptJFYcV1IkuUnHEr+xlHRrRS7RQgpoLldJttJpINSnI0NyA8AAFJmAA9k9sXAzkoVh14QlSkAGpXQFOlUREXJ0sA+qFYZGAAagDUg6SuAJBwUhyaiRWH1yYDoJMAAD0PckwVECcgAABlN4JRXAEhpX5GADaJf_HQB_JaAA4RMAAfY6AAAAJpQA8uAJDQAAAAAAAAAAAAA6kAEQgA50AQKgCQ0AAAAAAAAAAADA84Pg2epB1L6lQAZT4zEAt06CmgIoQv_IxoYqALojyCAxsKFp0HAVUcAMhgtCaKQPTpvPQiSyqFSsAQjUrtFApxcrDb_9KnlEGoZkaGZImLIB+hcxgARFgAIcGwcYQ0ZhRS6SKw6kk+hcrADo5C6g1GBW5QvDaAVOlgNWgoEcAAAGEHDcHGEa0_CWPnYdSSfQuVgB0chdIejArcoXhtppJBq3tAjgRAJCDY2BAhIbg6aiH0YJAoTDiPXLlC8A8BENQu0EGAFysONNAavjQI4AQ4kWihLy46Cya4ElJCkFCkAfFScDCZIrAA_4nD0AfFScKiBi04fgAf2TgBvCxrYdI4iHKmjcBC2c7C4MsZgFJC6BZaBoJUBpATWhAdSCAAUgXBwWTGGEwgo3MG5bTC0ksZlVBj31EllZKpNWZFysNplrP8kqapwRoYHUgxWMhUnQA3vBQK4ALLAMBVcSgA2iUegH_EIAEokwACqzoAATxMAAHeFIKo6VBfJSDiVyKgAglVAAqIBWMJ8f6agB+BUKflS_i5WFFyChPDiRXqlCsLI9FpFC7RQigRUK4baSeBAjhJbagQw02UCCzAuVgCYYgYyheB9kymHEkgqLlYHcioghksgaXUK45KSBJmAhQw02UBXJQvA9CIXKy6bBQnk0wnEigXKFYWR6KSOIkMEShXLNFCLURNLFc20kghRUSWQSqYbKBBA4SKwAe8SR5UFcFKEnEvaVABRGsMQCGFIKiAiBCNJxABrFQBB0YlUoXhUYadSDJW_SoAooYQIdKwU0DuaERbSAC+Ml4OoOCAChpXhguSIqVi0mk2am0ij7KFZVB6KSCcVSL1coz6OiKCBWpk000kggRUSWQQw2UogpDyULwO2ZSChc2CEFA5LgTcVBSJKABSAABMmADvIwAABmIgHAStcKQVDUqCjxUHEsqVAH7mYAFcFQVEB1SEUOfgAIEHBWdcKQUKQZYVJwGSkisAAHoMsKk4VEB5B87CiAI+HgAxgwpBRlSheA_yRWHF5iRHlIAtMoWftoksGgFysNtNsEpA1QMjQyMgHUAM6HCkFLELlYURMFScOJJAIXKwsgYQq0UF1lC8NtRJOdEoakTQI4DAWNgMSbLQTAnyheApDinpIjykDIhURQsgAyLlYGvSp4DUYqBDMAdFEg20prUSBOBipQuVhRcCSKz2ThvIsDCpWFlCZw_FJBCzRQag0LlYaaSTbtn0xIIZFamUSDbTDTV8EyMHQHkL3YHC0HgWK2EkisNpJFgiQwdyMDUijUskkJS4BGNtNsIPScI0MJLWQyKQAA6MDbF_VGpaC0UmrWjWMpIjtgQoYTTlR0RSyVSSCPi5WHGmmUHpxkaGElrILQDwG1XEwlwJCJgE7kwAOQASETAAKKOjFF2BAAAAcsfQXKwHuUKw6pySpSAeImHMtAKelQpADiqFCTaXQPLJwYgcPxTPSahoqTiUxzZ3IoeSRWE5t8SKyKOSyAxNwVK6aaaSSZ7MQzIT8omUumUo00BydLI8EPcQAKWORSHrCoYk5BwCpWAZ3TgAOsVAAHzPg4gCdEoA46OW_bLioiPJFYlOpFGIVKwumKi4ilRJIM7KF4caT_lOJiuRCfh5LptKa6pOlgeggM2AEkYqbLLBGQVAIgIjjwARQAqARAATyLgACSTYFAGhTiheApDJ1B0kRyoFSuihxAyIptLIBTC5WTSmgNeLoQUSCbQYgkIh4UeLkSKwaGSK6KbQoxUrAEo5OIAxPAXKyyMURgB3nkMEEB3LNFA7uRE7ZlIIQUqoyA2BcHVHCMAQSKAAEkmAAB+dAABCIgHlwcbmRfBpx0BSZREgwtA7KFeUh1JpsC5WAKZCEWkRkDyTIAyTSTNS4IwAAUgYtSc_P78AQoQSWqG4GAPSTAFLJgAygIE4ivJgAE3nQAAUgYA9J0NwMACUqA4KbGCBYCpVAQIRY+bABNV+IQAAUgYBwQGfDcDAxAWPkNBFQAAB7ORaAYfAABBOgAApAwCDioiQZcwsBhC4PzkwtAmgjzR2E1rJyouAmNBmKrlIAAKQMAe0qG4GAygDRyoCaGHNHYRZGmtZHblQExoMxQcpAABSBgNAEJcDtKgCQkNwMAALzKgAchNfBrQ_IqAmNBR2ZAAAABIyAHlwP4qAABLyoAjgdACwubgk4qAmNBRaZAAAbgoAB5cD_KgCQ0AAF5lQAOQmvg1ofkVATGgo7MgAAAAeXBySoAX4uD_pN_ouCkgezR2E1rILQJjQZik9OLIFAAAH8KkDLkzGwL5LgkorSheBND_GjsJqXQWgTGgzHx6UIEACsbABTLg9pUKQsAANDKgJoVI0dhNSyOzKgJjQZiiBSDKFUECAiIqzIi16bAV8uCSi0EvJ0sFqaOwmpdBaBMaDMfKpQdA42fDFOScAa4qAJjf_k140IBfFwSUWgTQPxo7AWl00QXDUJjQRizhSAAAPgZsCLlwDgqBJzZRGQAAvEqAByOQW_eWhzRUBMaCECWgFIAAAouEZFWhE39jYIOlwSUk5QvAmjFDR2AtLoLQJjQRiypO_2PABAiMbAzOjs7UjIDoKgCQkNwMTxuABhUAvMqAByAt9QtDmioCY0EAAABCpUASEhuBj6ABnAuAmgIjR2TCShaWRiJUBMaCMXWKQAAAkoqIkGC4+bwzyXBJUSlC8JoBESeKwOG4SRaXQWhhJjQRjhhOAAVsZAGEKgScsNwNrRuAAXmVARQcgLfxLRAUqAmNB_4ZDmUgGIAAn8qG4GKw+bwAM2FwEUA4aOz+yULSyQNKgJjQRisBSB6AQHNGwMzYzMk9OXloRIMuwiA+BcrCSykCiGaLlYCgXrdNhCfSkLbYaiEQ2Z0EB5QcAAAGqAJDQSA8EnyoCt5UAESMF4F0MalQW0yhCpCAAAAJGQqR0D1i5WAKouVgUSUgAxet00lIW0ypEVk6G3GUIAANwcABJiFSOgyaVABILlYFElIF2YCkSkLaZROhtnNCAIgAAAmIUw6BNRcrBp_kmAgXKw"
noncomputable def WL4_3 : ℕ := zfNat64 33243 "FMaElYfCoJTHk+CAgkDOB8GT4RAiYuXgVX_lC8AAJplLNSDYBKQRiGVrKQEWCgAtyUdm70J7LQDQqAYCA0xt_g6AHoAAAAo+AABUvAABSBgAQrxEgwAtBBKhXXmULwP_FwZAsgn8oXgbZuLwNb1oQAAXwYBuBrDJQdALgw1GoJUAHEGgACaVAAAuQgKHBwAAEmJQxKDgRcGH_6lUMqAFdDQACDKgAA2IQAAEAYACQ0oYlALQw1G_5UAeUHgAJSVBxpuAMChAAAAEhoohInghUoXhhqK7C5WA+AuDIf6WgJ2ULwNoDWeqEAAAAORjqEyWF1bZQvDDUUYFysAWhkqhZuQjDFQJQvKSbS6SRqlxGhgADdHgdDHNHdJB_ZQvmMfWGokkLlYAtDIFkcsZL0_lC8whtLoNSxI0MAAF4UADoyKISJ4ZEXlC8YmGorkLlYHqi7_Q4bCsgY0oXoENpVBqiFAjgAAiCgAoWQkgo0qAKIVAQ6Hg6WQBbRUbQAP+fAACgCgElGHAlAUkqAM+VAAhDSSsAAAVUohAACgCgAy2QAGqSpCWMvAAPcNpQABC4QgAQJOAAKYfAAAQBgB46DgrA+5OAggAAAD5KAABibAACgCgG8pQPiyA4VZUBX+EYOVKwAAB_BaIIFE0hlIoadPgAApBQABAsGAgXQIkRwKtFLrHFCukRWpgFkYl0uEtA9qpxDaBrkyXAVAjhFAAAAdUNwgXIoFUglk_ihXfcrUwCqMZ8LwA9HkrVzSOG8NoEmgl04gCbxomxc1H1VyJLApqpXNJdOooV6iALQyU9SiyC2qnENpdDVJks7yNDAAg4FAeEhYLH1KDZzqCL34NwMqIyDAhcCkqn_KgNpRAAEGVAACNQgAAvgxDgLcqG4GIIZABZ1SNqVAEUcgWQEobATT_TFNRBKQAAUgYNQAkNEAGDcHooSheCmosOLlYTXjRNFQoM1GsFysKCSR6NSVI0MAAAAKXAEhoALQceoV0+FysAZMMFwIIVjKgk0Ein_jbLqEAAAEaLgCQ0AyCttouDjUbKlQAANQHmVALQiObNgAAD8AClwAWg4lQrp8LlYAywYL32Mgggu0oXn5kqgkUGquEaGABBwaAJkXA6IpC0Mp7VCu6IuVgBeQyBrJSOBcAYiBaEQal3QgAAdixfgH2ybjBcCmo3RKgAMgQQSuVBQeVIwHfQkeHQlALHMwAgJkuXQBaClw6hXT4XKwAowobmIQQOGULxrbaCRQa0jQkbHQAAAHy4C6NhibAC0FKFFamnwuVgDuhQ2BBBSJQvCgkUGuF0K6jX_ikAAeBPS5vjiGBgIuBT_9SkKVADDBoABrlQRKCAMpCKIAQGQgAnbwiEkPpKLQzBXxqFdUhcrFIAZHJQQn+VSWRigkUGudUIBB0AARxojwJkXAAZsDC4DARcCmoyFKgBhA0AA1yottBAGUhGEagB2lCuAR7iBPlziiIWAoBMAWomAAAAFHwDkAFC8AACImABvxUOfBJRaORS4dQrqyLlYBbwaAggAUoXhQSKDWE6Fhwsjk0ArWbAeAoICyLnyLGYSUWgpcOoV1qFysADIEECslC8ttBOqgRwao3QI8dAA+RYzB0dGymdABIaWGQgN+ULwU1EvxcrCYIwAGGC4VSCDrC5WGmgkUGq9kaGAAAIIMrKF4KaiWguVgCUKhVIIL4qRQXKw00Eig1DwjQztasAG6FgdAzq9zRMIQmUXAVXPlRFQFIORvJwMFKgKICn0IAAFwUHOEymkieDcyheGWojALlYAGQ9CsQQo+VBQQGtw0IABzhMAH0S5wmf4lAbwuP+LwVsqAAEdHQBnKgmoGxNgDiANQ5wmdMkTwcMXKwYjJfKMpAw8TBUKpBBPhcrDTQSKDUkCNDD7x8AUQZACQlzhM+5Ing3coXmQlzOUZSACAGC4VSCEVShef4aqCRQar4RoYAAHOEzqk6WBNC5WGEoueKlYAlCoEUFJGC5WGckaGA1LWgQyonEygm4wXkzMgJ+Bo14IQtoXAVRHlC8ip84qEoOSSCdi5Xxo2KpRKITUUI0MAAFwUFZCoJidLBhxcrDCUTyFSsASxUKtBHDFSSC5WGmgkkGoREaGXQAM0SKwdCpEoP4FwZajfMqAKoDxZP_GwD5KgoICKUIrEfAAAHRHgY6JoJRKF4ZaiQAuVgA5Bw2EkghPcqCgkUGuIUIrAfAAGYCcCvYJEYnkyWDsC5WF3ZClKQAow4bOIQQVqVFUoIA3UIANIRQfooTkke0tC0LlZBLJRfCUKwIoECcM2WqkEGMp_srGWgkUKeYNxNoEMKs1oIPVNChsdYJgDJ0sFrFyssNRlIAwoaLrNbichdEqLJNQGuhUID+SEAAIqBj5IdBoSCEB_iYA6xEABkADvkQACTjYAD_zcAT8XISSCtyhfyJCstRCcXKwAI4obAc3ayjQQUeULyiVaDRSa7uRgDoA6iheAMzZgMES74qPoKfKF81LtRF4XKwASMAVCqQQaQXKw00Eip4Qhql5Gh1DOjSAdGoADkamIa70jAsguVhlKKRipWABUAH4lQUUCzqEGU2gTYLgBvMRYyZLBdRcrDLUSUFysASh0AmJRi5WRQggNRiIT84nE2oYYgqpFKF5OpST1EllZGkXKzqWSiSMoV2SNh6NRKFQo0GaowKE53i5XPTLQSTOZieU8hlW4m2w1GckjKF4gzM2AiRiUAtDLvlSv6VAAdLoAYEqD7aEAdpCAABcFAHGMgEDBNSwi4OIl8qCSAEX+iEBdSoKCOSaj2UgAAXBQHh5+BNbJRcopAQQeAI6PAElAArBEAATguAABcFAI+XuSLo6AEnVICZURUB+FCeczkB0JUVQAPAhAAAxCgFNMQ6GWmb2RcGkqg1KF4HtyYQyUsgEeLlZJ8Q1UUKDQQAAXBQBsVTGXgAyj02SRPABCABbioPtoQBZD4AAFwUAp5KAA2QPquWoq_8jBIpSAAAP8K0JCEpMYQWgOjOgAAXBQKoVNySgXMrAKwKgCUhaM2ALpQQCsPz4AAFwUARtxCqELlICihUAFJKgACcnAABQPgAAXCQABuJWztAIC4HTYAkgdGQgAAABR0AAAAAuEgAA6QNiuMdDwXIT70YFFKQCNSYA_8TAA5psxh_06AEoAAMRIAAHiAbjQKL0jE4IdqxxMI+cqAMGmRFCSB8VIKCAhl4Lp5AAaQIJf7gDjMCsEkEmgAAsJgAXRMAAJkoAADB0LQAACEBxJoktMKJLBLipTCqURYFysB6yMJSqEkCqYSguiQgsoARoZJAaAAyZSkSxsokuozkq2Uq01URUrB6SSKJaiUVASNMQEKVMu8sXh7SaCVTiIT8y1l3TNnOpTZSC47PxoAU5geOgAHJQkRGAAI4VAADFCAABYbAAAuEjDjwEFtQvBvw8pD4+BJx0AF5w3AxAjIAxFQAAcQAILAi4AGtrDIAACkDAHythuBhumQGoLgKIhSoAANIIxKgFpRPs1RapAABfBgrhyU9DEe8NwMB0BCAHoAAB9h4Bh8AAC42AACkDAA0KgAAAAAAAAAAAGhPZeAaFQDARFCwSMBPZKAAAAEIwAAHGoAAAwEBPZmG4GIoSoPgGqhjoAAZsPAAw+AABsdAABSBg_DQADzEeFobgYGxUA5A5sdAADNh4AGHwAAAAFIGAKYvAEhpKQugINmYFk_ZIrAAAa+VB0Ll4ATUIyVHAAADCrwBJGEEMguzECqxkmABaftMhvMQALKF4HEBrUNCAABEFAGXX+UOgLrWDJmBVWuTAPAOhaAEkyoyhxD_xtotCAAAiDAJuXopXL5CyheQS7MQLI7yRWSGmjkWkxMJNHqLyheDljDpzLoNV0I0MAACAMB4ISXgAJkQY1EkuC7MQqqHyYAci0mJhIQHy1yheDk4l0GrHEaGAABUGASEv2sVAXfkmQFUiJMAORyXSCH_EqYZUaRYzkA1uChAAAaBipqbMAAsQFJeBDlwAEWBoGAsvyMgowrAAUQegAiNgCSTUN58AABoGAcAHLwVFCagGD3jBfUKXBUxWAAABqABRCebGvPgAAWhQAAl4KyhBWGQXeYmQFVLpMACQB4AaonKgjIUf+G2WUIAACYMACBeDgISixcF1FxszGIWQgkisAIoQUGuWS7sZMRmElGapWRoYAAGAYACy8HFQl7LmzFwXSOGzMCyP8kVgBFCCg1yyXAE+6NBRmqKkaGAACIGKkpjwVUvPwHP2LguzECybEkVhNCKWSe0kAQgPxaDGW89NgarTQI4AAPwoA3C8AIFzEC7MQKrGSYALIQQHIhIPKgPBRkMuAHihAlAABWy__plEAuC7MQLJvSRWE0IpZCCi5OlhBFoIAoYy2akEakbQI4B9AmAA6C8ASFgF12hkzAqvDJj+ycBZCCFjkbjRcToKJaA1hOhBphIAApReMVqFwXZiBVUSTDp0oIpZB6H4Dh+SUoXi+ChiANRrI0MKNZAFoNzI2Am1eXESP4XBdmIVVRZME0IpZPWnkOq6UEEWykYy0BqjtAjsEHgAAHgiReAJDQHRkF2YgVWMkwTQLIQQ_8jcYLjvhlLQGsx0IAAJ2dALTEKXXj0C4LsxNIWQVkisJoRSyEEx6RPGJBFsZGMtmpBGqO0CPp5qCz+pIpgAAmYhba8dWULwuzE0hZGmSKxzaRPKJFLIPaSMR6IkoXxkYy2aj0aqORoYOZyFEpORA2CeF5zWjeDIuCzMSyFVepMARSyUZ6GwEB2asoXkUYi0Bq3tAjgRgNgAGdr7KwguC0uZyzMSyFk8ZMEkIpZJs9BiORPlC8ijEWjOEIaoiRodJByA2MiBsDCrwCyzYyCDSsH8lINYLRdIIApyoAANiEAAKISA8B+MQZZfLZxFwWZiBZQWSK_fkxJCKWQgk1vRkQQhlC8GItGpBGpZUCOAAEcOAauvE8pT3ZFysklmYjELIfSRXNSSEUshmerYTJYxIIIyheBkWgtGodUCOAAC4OAcYvJJwC4klmYikKpxyYxC8AWSyNTwRcNRClC9Akkgn_E4akMRoYAAGAoKUEzwZ0ZqTsxAaC8HdtguBgLLsTBuBZAIVAAEUygHQuXgNWhJFc2zVxicAAC4GKsnHb3DBuBsfFwKQKlZdST4cqABqAelICvlQW0A26EAZ8CgEvg7FhcBgipWHUk9PKgD_RsABXyoOWNwB0UIAACIMC9BcBtipWXUkk2LlYANQHMnA5sqA2h_4+nmhFwBgAAeRLiA6kKS6kkmxcrAII1AmgfEoXgDBu14vXge1_QnIHwAAGIUSheU0FZIrDiSR0FyukikWkEak1JIRUUlC8sjVjzRnLoPUII0MVTlvAooSUWB0ASoxQZYvkpRH2SK5ydSSK4uVgeWQhqaQmgdEoXgbS6D1myNDAAg4HAE+QhubNYtp8xFUy5IrMp1JIkC5XrJmAei00hJAW1WEmkmg9IcjQwAAghQAWcIfEZ2h0DnCoOI1QqACSAAAAdVGfAABuCgAF4QvpQvBHZQrDqSe3lQH5EocgYaN4AtJWIoAFjQgAJIGwDslC8Acki"
noncomputable def WL4_4 : ℕ := zfNat64 33238 "ODgAAAAAAAAAAAeXAEhYAAAAAAAAAAAAA8uAJCwAAAAAAAAAAAAAqkANQgBxcANKgAxMABFgGAgAAAAAAAAAAAMBAAhLiJBgGplwSU2pcApAAopIrBCFy8AJqQpKjgACJBgAQlxEgwBzi4JKcouABaEwAUJ7FwIEJrXxGAAESDAAhLhuBgECFQB4ioArIZAZQQIVAAAAAbgYpa+lgY8AAAAAAAAAAAAAAcHAAUEgASQcAADg4AACA0AAAYCAACrAAU4BAVADxYAGJAAAAAAAAAAAAAJIwBBCAANIgAJEQACAOAABpEAAC42AADcDAASFgDAYATEwALCYAFcJAACYmAAAwdAAA0gBAHQLgkpyi41IRAG0SAC3xcAE19UjAAI2DgAQoQBMSAAAAAAAAAAAAAIKgC4kcUdAA4iAAsRAAPBYAAHEQAAAAAAsx0CQ2AAAAAEpUAAyTYAigEHQwQrBmQALDuLA2S0PLj+5dJT6lxtYiAABFxcvACahMSo4E8B4Av42PgQAkJAbhQBPKgBdFwAwAqABRJUAH9jZxKEAAABuFAwMqAK+VASYGhqADAyoP7JwEPUIDiA2QmJkABZQADVJMSYuNTEQNQAD_lQfyKgGqvUIAAUQ0WoCgEoLl4SXp5cUAIgaYUJwIkUD3lC8KiSQavvQI4AAoA4JZkBE4QAEZUFEBiVABBAB4pUAf4UhLCEAABQGABIVI5DwSkKPFjbfpUAAAAlKgOIDLNgAAABofKGmwSkKPEjbfpUAAAAABFNhBIQAAQg4AdRUeQPBHAqCaTbKgIJXguAUgjYqACagAAQg4L4EABVR5A8G1yoJp30qAKBFjMDKFmSoDaaQb0hAAAaBilP7EbsaUNgQAmNACAQP7Lgkqky4AFqFAAiYuXgBNQpJUcAAAANBgB8VABIKgAVgkAAPipKAsAAJz4AABSQaUNACh8RIM7YoTgosuCSm3LgAAcgHguXgRQms90SOAAF8GAbgZ8w0HbSoBjn0qABSCJm4EqlQFkA9yEAAF8GAAudAMBAAsIgCRHwB_wiAGISI+AAA8XAABSBgHAnJ8NwMtgWBxBsElAJyAfRD+Y6AMoRFNkaoQAAXwYLQiQZ7wkARFk0FysJKpIuVgWSCMQNpVM+gRy0FSsCyTSCIcwb0EAAL4MF9eANCoA0GA4JdQACJKT0uAAAA9Fy8AJrpdGAABmDAAiKgCQ0cOLAo0uCSm5LgAAAPhcvACaoESo4AAAAReARFQBIaABONgogNTYAAABKVAAMM2AAAAERUASGgADeUlXkwKC4AAARSVAB_42X2hAAAAIioAkNGFDwH4Kj_iUHYKgAAADhUAAwTYAAA_v40APlxIhQBkC4JKbUuD8BUAA6DhSS4LgYgTXTCMAAJEKAAkZADy4AOVACuFwf7JixFwAABHIuAcgNV9oQAAkRIAAqsAORgCZUAOFgAAAAAAAAAAAAEkYAYXAByoB4EuAqlRKF4AABIYuBiOQmuikYAAEQUHoAGVgBiMAPLgCZUAAAAAAAAAAAAAaXAByoB4EuAqlRKF4AaOfgAOhcvCqOQmvQ0YAAKIUHoDvLgA5VyJsABo2AKaAEkCgGdKgSDkOrmwAAG4KDMzKS8AHlwAcqAJDQAAcpMCguAAAETlQC0P+Gy+UIAAAAeXAByoAkNACuFwf7JixFwAABHIuAWgNV9oQAAAAwuADlQBIaAKLLgkpty4AAADwXLwwi0JqghKjgAAOjoACTgB5cARKgCQ0AAAAAAAAAAAAAYXAByoBdouAqlRKF4AABIYuDCLQmukUbOSMAAHo6A5T4kRIOYIUqzIJKQw2AAKoEGQhcAFWaoLQI4AAkRIBuEjUiwLYLgWiui4ADpnxWA2AXAANXsoQAAbhIAAe8NwkADI2BaAZNgD6iUf2NiSAAB4TYaZ8AAG4SAc_ABB8BgPAAOkmBQXAAB5BEpUAH9jZw6FY5aAAEHBoGg4jC2ZcS2StnLgDKAeQOYXLwAmriUSOABBwaAE4fAYDwE6NgkoXi4AkgHk_IhIcLgAGri0KVykAAAI8+AAlzJFQzBoAHnQAAAHkAHnQABHzoagAZIqB0HnacF0HEYd_LgkptS4P+KxFDXjMFUN6WLwLITUdqBHsctAAAAMUbAxH0GwBFAAZ2VBxJSAayPQrHLQAAAZy4A_i5xpUDmU6qLgAABE5UBRD_xsvlCsctAAB_GgbCwS2OlelC8BicEoXgZQNhCAHWi4CyE1P+gRwAAbCwAZS4BBQuVkxGLUyheACEAMNmsNLFwFXQSUTXPiNK5SAAD8AGFwA_ZcElaMZAVbKBQMpVPslwYQJr0VGlMpAAEOAKEoBGXMgVB_o2AqTAABFAAGaTAADdOv9GwAGQKgBpl22ljMN6k0tCSm1LgCKAhZw1gsEsXoULITVKaJHGqFAG2ljMvx2dCKGUSuPgEJcKQcAPQAD_ykB_xGAegAAAAUg4AfRUjQkeQGwXBJSxFwNxeiqZAFkGzEhAXH_GYCagABGhIAri8A1KhSDiaCKj4BGR8AAAAMPgAAWLwAAUg4DQCdlAATIG2XA0HACOJj_x8DsJgAD_wcAhD4AAzC8AABoOAGoVO5IwETKiskBC4DfDEADQJSVAANSxy0AAAAouBpFRiRSki+Ll5WZLoUuCY10AGzGa2XLgAmpv0o2y1bVMWKwGIAAJLgbpUIoUxO_2XBZkukS4BivhgvgA0YlMS4AJqSsUkKAMeMgbAOxcDmKssLiKBCyoLI_QuA3oxAA0CTlQAf6NgagAywuB2dpz8vNa8dAAtcGwKgXBsCJOTglMlIyXBV+CXAFEEgxIuECCUkzUq6cAABYGAAEfAEjIAeXADCoAKHAAAAAAAAAAAAAQrwBI+ARFQAAAAAAAAAAADY0BALwNgwBkcZUElAPRIxZPmJwBEyoAAR6EAABsGAAuhADJ0C4JKNYuDiCQFLBgcPQIrFx7xSAmvdEYAADYMA4DYMh8kVhJH+SKw00EVBcrHxJ0sEoVKaSRyJRylC8tphpo9GrtUCOAABsGAGAYUjp0iWlsoVhpIqfC5WH0IKASS6oAuACrNfuowAAGAYh78ARFQBIWAAAAAAAAAAAAFvXgTBUDYNFQMiCLgUUrUwACGgUCilQAS9NgAADwMHoAdPgeBuNnx_9KnwVKw0kVNBcrAAAI5FwH0Bq3dCAAA8DAI4KghBjjkispJni5WGmipYLlYNSKTQjopJI5OKXARmKzVcilPAABCDBffmJ_T047ggCFeIrLQ3AwA5A5ofAADNh4AGHwAAAAFIGAAkLBKDE1IgdKWMwLJ8SheAABI0qDoXLwAmoRkqOAAAASGhNSIHSljMCyfEoXgAASNKg6Fy8AJqEZKjgAAAGy4iQoCWgNpUtv+LlYEuiaagVQISULwe20JqTlAjgABCCgA5rwJAwE_y4NpVeGVA9CYERJCiAUsqAAEehAAAQBgAJDQb6EHfy4Cy94uVgE1BgCsHai4DaA1j6hAAAFqHI+RoYHoLl5VSqkQuVgCWahZWqoVwinBKF5aTaWSar6RoYAAtQ4nb8nAC2UCwMTEeBx5cBVdKVATWWgUQAIoQRNg5IQAAEgYtQIgpPxEEtAQCxXRQXKwAUhOQtOVBQd6pR_w21KhAAQYDgEYIglsfAIWcsV0bFysAlITkLPlQUHSaUf+NtMoQAAGwoC6kYJaCzliuiAuVgBHCxWE5BipQvCgkkGrUkaGSQOAAAAkxC7IQS0oivFiuyAuVgAuzBuE5BTJQvjpQQGuAUIAADYUAhETMEICElQBQioAdcZAAB_4+AKrqPgAAMBQAfUbKyoDuZcWR6VVWFysA6ANANQTwrBQRyDn0IAADAUADLGMomIIKBKgF8FQAAQQGvrTgGIAAABgKAADtABU4ASfAEjIAeLAAAAAAAAAAAAoFCAjyXAhHIlQAXTSQQG2qRRG4oQAAABgKANyMuZCAIRcvAqnmLlYAJJIhhSQeMrVwoM9BrygCAoQ8ACDCURQYwXLyrLQVS_FysAatcQH4UUAlqlcqlBnoNUKE9ALSPAyAgALaABpwAw+AAmQB8uAAiwDAQAAAAAAAAAAAGAiHDQ8EkiAUgUQBJROTYAMIQCTgU6pBNQAAADAURoODGJnOIQS0E2LFdEBcrAB0FisJqFVGEzFBJJZT6BQh4ADvyYggxguXlWWgqoELlYA1FITUDgZMfVK5lKCSSy4EJ6AWkeBkBA7MFQakAJ8wPBQf7BpaA2lS2oYuVgDHiheEGcgdcoXgxHopBq7RGhgAQcDjDYsOjdFwS0BALFdFRcrAADFisJyDayoKD7BKBrKEAADFh0bguCWgs5YrogLlYARwsVhOQruVBQSSf+NsvoQFCHgAYqOqdGQIELl4FVHhcrAw0bCkJyDGC5WVGgkkGofkaGE9ALSPAyAgCFWAB6JgBIEwAAAMImAagDOOgAAMBQJ0tAE+Ll5VCqcYuVgFP+IURkyWBFB4hcrIiVSqDVAyNDAAg4HACUYgDJlfjJjAloIWiKltMhcrACaCGcg3EoXgJnpFBq6RGhgAQaDgCRMdXMQH+S4kJZZYXKwAklUcIlBm8qNJWQHPOUIAADAUFMbDgMQyYS+GXVFolqBHLGFiulIuVgAtBDOQGeULwGoZ_IDDUJKBHAAg4HAAOXgAO0ABMgBxUASGgAAAAAAAAAAAAAl4AmnAAjIAYXAAiIAiNAAAAAAAAAAABWlUtjECKbZSXZGhgHBC4Wt8XqTOR7PTEnj801Gg0EIIEEaGABBoOANmbhCpT9LgPAXLwKqdnLeAAR0A4k9Ev8hIJSFclCAAAwFAASElk0pYzAhhcvNw3BVOO2cwH2qxRCmg4U8f2koNZCCQJGhgAAjYtVz6GS8H9Fy82hVe+2cwKqUQ8aUUQEaePwFN2uo0GshBD4jQwDfCMAd4sV1mGC8Fhli8CrbQCqTQJpBpqHoUHPS0E2QH8nkKGVQgmEJCDwKzJWExMLU4IAGMpHLgJaDXlS2iAuVgCFixWYRbOQqaVGH_xFQSSDXAaEAABgKA8BasSUxkAUi5f+6CCqvouVikDRGjsekEkj0KKei5WSabRSaDUViFDAAg4HAANTgEJUAAAAAAAAAAABRQb8XL4jNQVetlQAG4oX1EAjAfGEIIEF0IAADYUAgQ3ApafUbMwbQXLw60rSkAJ6R0Ask9Ev7RIJSFf9CAAA2FAHKkTw+C7akBBAArikAAajoAAKR8AABgKAqZxIoGSCoC3SEAEcSgABYXAAAuNgAAMBQAQkFOerbKUg4yXAyZWKoAGCYgsgoQ+JJQSSNpWIIAAMQBA_XL5NJihEsXrnYMY_lQr1EDoTaaUQmlpUqcPyCT2og9MeeQ6iRaaZRyNX_zYkBMjJUZnQMnpDaCVC4EoYFOANsvG0AAfHQAAJD4ygkAAXIAmXgo1lnqcUQMcVH+iYK+lABNABMpsAAq06AAAwFBTGhJWHwqCUx5PggIJAzgfBk+EQImLl4FV_5QvAACaZSzUg2ASkEYhlaykBFgoALclHZu9Cey0A0KgGA"
noncomputable def WL4_5 : ℕ := zfNat64 896 "CKEALKgAxMANFgAokAAAAAAAAAAAABgIAAAAAABwcAAAAAGAgAAAAAAAODgAAAAAwEADAQADg4AAAAAAAAAAAHlwBIWAAAAAAAAAAAAAPLgCQsAAAAAAAAAAAAAKpADUIAcXADSoAMTAARYBgIAAAA"
noncomputable def WL4s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL4_1) (dpk j 2 WL4_2)
noncomputable def WL4s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL4_0) (WL4s1_3 j)
noncomputable def WL4s4_6 (j : ℕ) : ℕ := dsel j 5 (dpk j 4 WL4_4) (dpk j 5 WL4_5)
noncomputable def WL4s3_6 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL4_3) (WL4s4_6 j)
noncomputable def WL4s0_6 (j : ℕ) : ℕ := dsel j 3 (WL4s0_3 j) (WL4s3_6 j)
noncomputable def WL4 (j : ℕ) : ℕ := (WL4s0_6 j)
noncomputable def WD4 : ℕ → ℕ := rdw WL4
noncomputable def ready4_cuts0 : List (ℕ × St × ℕ) := []

theorem ready4_cuts0_ok : CutsOk ready4_cuts0 := cutsOk_nil

noncomputable def ready4_0_state : St := ⟨26112, 276711, 28545, 39936, 29184, 45301, 53248, 103645, 29666, 44151, 29184, 45301, 28545, 109383, 26112, 285696, 54657, 316647, 83841, 361948, 137089, 438085, 168587, 467751, 213888, 496935, 242433, 573870, 268545, 751794, 57729, 85237, 110977, 161374, 142475, 191040, 187776, 220224, 216321, 297159, 242433, 582855, 82432, 132829, 112098, 162495, 147840, 191679, 176385, 257223, 202497, 542919, 82914, 133311, 112098, 162495, 140643, 228039, 166755, 513735, 58850, 89452, 87395, 174791, 113507, 460487, 57729, 145125, 83841, 430821, 54657, 395079, 0⟩

theorem ready4_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD4 ready4_cuts0 115 323) ready4_0_state = 56093 := by decide +kernel
#print axioms ready4_0_cursor

theorem ready4_0_covered : Covered (toCl ready4_0_state) :=
  ready_cover_cursor WD4 ready4_cuts0 ready4_cuts0_ok 115 323 56093 ready4_0_state ready4_0_cursor (by decide)
#print axioms ready4_0_covered

noncomputable def ready4_cuts1 : List (ℕ × St × ℕ) := (323, ready4_0_state, 56093) :: ready4_cuts0

theorem ready4_cuts1_ok : CutsOk ready4_cuts1 := cutsOk_cons ready4_0_covered ready4_cuts0_ok
#print axioms ready4_cuts1_ok

noncomputable def ready4_1_state : St := ⟨26112, 276711, 28545, 39936, 29184, 45301, 53248, 152861, 29666, 44151, 29184, 45301, 28545, 96286, 26112, 285696, 54657, 316647, 83841, 361948, 156884, 487301, 201035, 516967, 246336, 546151, 274881, 642437, 300993, 751794, 57729, 85237, 130772, 210590, 174923, 240256, 220224, 269440, 248769, 365726, 274881, 651422, 90836, 182045, 134987, 211711, 180288, 240895, 208833, 337181, 234945, 622877, 89686, 182527, 134987, 211711, 163532, 307997, 189644, 593693, 58850, 89452, 87395, 155136, 113507, 440832, 57729, 125470, 83841, 411166, 54657, 381982, 0⟩

theorem ready4_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD4 ready4_cuts1 116 72326) ready4_1_state = 131132 := by decide +kernel
#print axioms ready4_1_cursor

theorem ready4_1_covered : Covered (toCl ready4_1_state) :=
  ready_cover_cursor WD4 ready4_cuts1 ready4_cuts1_ok 116 72326 131132 ready4_1_state ready4_1_cursor (by decide)
#print axioms ready4_1_covered

noncomputable def ready4_cuts2 : List (ℕ × St × ℕ) := (72326, ready4_1_state, 131132) :: ready4_cuts1

theorem ready4_cuts2_ok : CutsOk ready4_cuts2 := cutsOk_cons ready4_1_covered ready4_cuts1_ok
#print axioms ready4_cuts2_ok

noncomputable def ready4_2_state : St := ⟨26112, 276711, 28545, 39936, 29184, 45301, 53248, 251741, 29666, 44151, 29184, 45301, 28545, 146383, 26112, 285696, 54657, 316647, 83841, 361948, 137089, 586181, 166755, 615847, 195939, 645031, 224484, 710759, 250596, 751794, 57729, 85237, 110977, 309470, 140643, 339136, 169827, 368320, 198372, 434048, 224484, 719744, 82432, 280925, 112098, 310591, 141282, 339775, 169827, 405503, 195939, 691199, 82914, 281407, 112098, 310591, 140643, 376319, 166755, 662015, 58850, 89452, 87395, 235835, 113507, 521531, 57729, 191684, 83841, 477380, 54657, 432079, 0⟩

theorem ready4_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD4 ready4_cuts2 119 73) ready4_2_state = 157323 := by decide +kernel
#print axioms ready4_2_cursor

theorem ready4_2_covered : Covered (toCl ready4_2_state) :=
  ready_cover_cursor WD4 ready4_cuts2 ready4_cuts2_ok 119 73 157323 ready4_2_state ready4_2_cursor (by decide)
#print axioms ready4_2_covered

noncomputable def ready4_cuts3 : List (ℕ × St × ℕ) := (73, ready4_2_state, 157323) :: ready4_cuts2

theorem ready4_cuts3_ok : CutsOk ready4_cuts3 := cutsOk_cons ready4_2_covered ready4_cuts2_ok
#print axioms ready4_cuts3_ok

theorem ready4_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD4 ready4_cuts3 128 1) (ofCl (RC 0 0 0 1 0 0 0 0) 0) = 164746 := by decide +kernel
#print axioms ready4_parent_cursor

theorem rc4 : Covered (RC 0 0 0 1 0 0 0 0) :=
  rcOfC WD4 ready4_cuts3 ready4_cuts3_ok 164746 ready4_parent_cursor (by decide)
#print axioms rc4
noncomputable def WL5_0 : ℕ := zfNat64 33247 "Bko5H0DSEkQoBuzoCKdT6AbBEFpNC+jQwCBWSkks_+ct4eaKoKG2ursLiOlm1mmuoDXrZZIMlTFDA6TRZzOaa7s8frNQI85HNFNidPxyQSKtFGhlGo2WeykWj39KRLqMYVKuIUOxL2IM6MwABAKab+Uggn_06mRQgj0LqD0S+YNgroGqcOR9DzTUG0A+BCwAXitTAiDUpodAqFSqpJavoABVAEdAUu06gxdPYfYuLQdT7CQOJBQysVyqWQgk0uJ5DKJdLI9LNRtL5DhfOZ6mA0Zgb9kzh6jE7GddP4HEJk4UyzZUAZcCF0DrttmKpYTSFm6lRANHvQDhD3mJlmUUoWwKIEUXQEAPidgCKO+WgA6BX2oAAWjMIYCAkprwkbHFdy7gbQwojWhKhQMDLWZmtG__y9XQqmFO55DMJhLpRMNRXGzawuhZAeg6AI7cz1uXctpM2zecTbccCW02m202UypeaL5lLptzp+ZTKYbCYajEtiz0kUiiTSLOQrCRYbqYTcsV+0mEwkLaN+BptBpplsqej5_JZiTaShU6fjkO_1KF89INRBy1Z5LBbciBMUykkpFbtYACZZG2DODdy7mm2iCbt9pNtxwNhsJpH0zZ7LVSrWSbSRwnT8qlEsz0g1GynnAlEqlXgrBfBU1bwbCatMWLEmd2BQjkG0Y43VwDKDxGxgBhNMhLwABaABdQjABNcJbliPQvOtwLBZM4FpADaAHb04ACygAAEG2BPoHtcN4cTAltBtNnc2hlDSYWOpkPVy53LplLplLNMnLGGWmT0bQOIHosN1YXYNMOwcQ2gB1DKG0+gtGEMpdQQ3BxAAPoAgISrg7QXdP4LebuYZQDKNDADrYTSRGZOZ1PJpNppNJ1L6FUroHSPo4CueN11A6hlG+oksA9k7febjCGU8E3GkALiFUAySjAGEuYOx9DuzsAgQJrPx1tpxANoxaziHE4nUPIVUoMwFFAkAJnwA4yAAlwAUaAGiwAAAAAAAAAAABQAClAEj4AeZABRoAaLAAAAAAAAAAAAHAAAjj4AAjMQAAgYgAAInQvCoAACx5eY5AfSOikFUAPoUQsn0HoCjUQPJTVSLwBvj6OB4KFgCJkAPTIAEiEABGZgAA8ZAAAGLheDQAABg8KBh4WJ8AwqAegKJUgC+aMG1UYFslQV0AxiEAAKI+A0LCbwBIaYHWgFIF4kIACKZAACYmAAAwdAAAf3oaFhM4AkNAIlwC0B+JsAdKLgAAAADBwAAW4OIvgCQ0AiXBMQFHmwB1EyACiBMAABg6AAAvAZcJpRuzARkIBXowGhC4Ce8XRiZEQBVIuACavpQgADBExHgA8yACDQA4WAAAAAAAAAAAEOAGzIAMNADBYAAAAAAAAAAARcbFx4bDhYJTsgldcASGh14ocHTSIB4xEACUAG_EQAELDIAAKkHgHIkAmSIAXBcADTLgAp4XQUAGri0J7hUAAABMaAHCwAeDEABQiAAAAIEwAAAAEIyAH9Zh4RASTCUnTykmIuXgEGmgBBV6ULwIIpQ9mp70COLSyAJRLE4AuLIIAWBDTEBEQuAoN0lIAFLlQATVzqELQAdmXACY5gENlZacBlMIaYUkDlwFB94rAFBg8XABNQW_0TgBqZYnA9DhwI1ZAQZZFeUJB7AuAU4VAHdC4AFoFQADDT4WnEAABb2QAABQVAAdC4AAOFQAALYgLwA4gyAsbAiFmqBEyVGP5JxVBFaFHx2XAAAWkOBcvACajjQI4tLIAlEsTgC3shi0YDiKwBUi4AgwjA1AhSVABR_6bVzQhaADsy4AO42zqcVQqgUUzxsAABNJqPSVABR4CbAtADDJcB9WBK7IAiNIssT4J7JwC1CoAjyVAAw4qAAY8fC04_2XgAGwIuzAB0oFvZAiDSGIKKqIuANsRACqBcAE1cyhC0AHZlwAZ2YAPZsoRBpDEFFqcXAFkxSEAPRIhcAE1KYjC0AHZlwaxoCosnaYgAXJwAKCoAAAA4VAAH+i4AGiGQAMLNhBsPBl4iqVwk0XRpYvAoM4lSmAUGrRcAE1NwjC2egERS4h8OLAYEDvzQr1QWAWgLuJgCZBMADMiYAB0B0EQAimLCY5cUESAARQXACdy4AGnlRFAP_G0rUKIn0AFaJAWCMZoV_iZB_9KAWARAF7yYAHSEwAEJDoIgB2gaDuCodg0Bmk4AkZUAAAD8Kv9EwAD_PgifQAUA0ABIWEQWABMbAAkIgAOyUAAJiYAADB0AAAExmkXNKEBVJy1VGhsfLF4BBNumUwCRSELRKATX_CMCKeJ4pGIAABJoKRJCkVApLgkGlAGQIgCkSUACDiYABJh0AAdQC8ixaKSCVYKoFFB0VAUEAPRoQAG7zY1C0ABmhGAEAHjRVKEYuTiqTmgi0Agm3TKYAF5CFolAJqrNAjh_0SAmkPABORgCSGqhORKtijB_8+4wXAUEogH_ELjRcAE1fShAABuNgA9jQhiEBv0YCkRcBQeAKQZEoDDSoAJqdtCAANEfBmAArIAINNMYP5cIQbFRgLlFwB+ZSLIBUsqMoBNbuoQAAFICO6gKU0FNDjlbxsFHzoAAAAAGHwAAKGIigAMEyAHSJQIkR1bIUMKKHyToWgCBQiiOQBQZQvnIf_Qga7xQiKEhnoxYqBcdAFw0ACFgPCIAPn0cAhpQvAKaBVDbJUJQq0U4ObUECiPQQcNAFaF0UTZEFBAYyULwBiSZL6mdDmqhKRyFmiiozBuqpChkUNI9BwRUDsyAB0YAmZACBYAWJAAAAAAAAAAACLjxuZjYeNA61kBLrgJk0ADlhWggkH_0oBYBEAXvJgAdITAAQkOgAP7JxUxYAHmhvIhNiQP8YgBnHwALQByAAVjNkeIQABhhYFAJk5OhIDCA6wuXgCERhiAVR9ZQvACanPQI4hACuBkADOaVciJgJAYQA1lQAQAyAAM5UKxeAAJiEAPQADGhyNEwbBIDCEPlIAbQjFkOgBCCsLgAMzU9C0AdQLoAgIASMgOxIGtnD8Bq+EoXgUGWgSSqBgKlYFJno1JcjQwKJhqpzcyADwNQqRIREgM4WQwDElC8AFpZAokpMoFnsydJ826yhAVkmgFIAX1gAM0KxBwOIqAiwf8IE4FLyoAFYlRwAA4VABNTAlkIoPcOgERzfzERNAATgRAAtABnBMAA6g6AAL0LAEWmwkIgBaAVgiAI1FwAHCJgAD7HQAEJC4I4JkZFFs1Fpx4yWsXK2JlC8ik5notoIRSVplOeikglEpM9KKcPz+nj821kqmGq2kExkvA0NE50EVWQCWuIZiCwEEBlhMAe+LgAbsTAAPuOgABQDRUghEQahIAB6LM6AHKlwBVEqFQAAUD4AAFwsCNEwNRIACWgEni4AojsC5WBdFKHs1cIjQwchhBUQ0HsWLlrKhMWQKoUjRq8FwAAB8guEoBNVPoEf+p0AErh4DKE4FXJwB2SoAbunAAaYqEoAG9Pj_y8AF2GgXwjEGTLYPpRgOuFwFdT6igAEUoXkEAmtu0IAAADOLWAlFUJID7z4AJ6fB_RgAc99Lv+AQBNSTIwfTCA7heAAmNAOfX2TgdmjAP5LgDM6MADla5QvACasTQI4CQDkCcAIYyAkCV5I1JAkgRILgDwiUAQCOJUAH+ja3aEMRSAYyXgdAnYkkyNDGkdOwooG0i4AMQlR1cLF8AuaVG0gof8Ns4oRFFIABSNgBMaWnRgNSgQwIBFysAnoDmUp4AcKlYFWgusNpiQQQm2mgXhKlgiqJHFwhPwenBPH4A9C5WA9GrvTh_QQmjGYh1KFZBntZoI1GIazh+aSydazTZiVpKjk7MgARGAHFwAkqAJDQAAAAAAAAAAAjYEAHmQBIaAAAAAAAAAAAEOAEDIAGNADxYAAAAAAAAAAARYCHw4Ils_uIiaHGUoBOREAVHJgAZ4TAAOqOgAAbCRUgUDwNB4BFpQCUD4D_yEAAD4mAABsdAAA2EgAIpQAI6AHmQAIaAICwAAAAAAAAAAAEaJgckQODVgEMKwS0AAqgXABNeIIx6w6AANTUKcIgl8pAIxKgCD6cAB+CoABTiEIf+LwBbcqACcuDgKsFFXWWLwCCbVMpgG_0IWgBNcOIw4i6mgClyoAQDQZ_arPXLgXi3BRQFHwFBNYvCECgn+gIAmodl4YxUAAANj4ARaUAEImABaJQAA+JgAAbHQAANiII_Si_oEegu7TKdVJzRcglwS2gqgUK4BQTaFy8LqE1oUlGmiICh0kkpAU1CNvJxVJzRNCji0CgnzTKYTkWuhC0BqE1CugR0DpxtAAAAQ1EKZTtwlUGoqrVLZOaLPsuAoJVAKD98uACaiSSjSbQCAPVQrgD6RhPVgAwKwDRi4DQqEVQAVMXABMXSoEeIgAbROlgGPExKRl6HQAACyYAAwlD0AAAC9LUJABKTEAFMWsRGhhCPIYE0BjZQvJIBPFCWPRiAoQuVgBMYBI0MMgdA76lAyZjoCMxoDUh8OGxceAAaoADTD95YAFHFEdBkB6BEAmAJMWCYALlEwAGoDoAAegArrhFUsBgVNAWAwgKkIgD6BcADfiYAB_B0AAJQABmQZCWByyQFBQ9CkgLCIgAcgA6YmAAhMdAAd2JgAEmQiqWAYKygNBSQLJFQAH7koDChUABYw+AAEoCKpYBylKAX8TAHTFIAGhEwADsjoAASgJ3rgCQ0gkbB91KAaQTABRAByhMABBI6AAAAXDW6BwsIyFDF6n09JiNW8lC8pIDc4d0UKNFAjBUrCzUZyNZiWdAhh5MNJosxpIDLCYIHL_8lW_OgmoAAAAAABLNgPLXhHLA1EBi6BDAemvCO5f_koEKsAAA4qAB7HjsAMOkwADlD534RywIAPQHSAySlpCfj2ktxOH5RMJPUCPKTzfTCSSCV0mlFnR87FpoDR2YajZSTHRWoEcIjRvQNdnMhCyCSqxCflJVKcPwqjJjIspP9qxFnJaUCPPSqFGcgzJFY5rpZtK2lamD1fjNjNc6ezTXS7baKCd_RzoDjsgV0v+Sl1xCD4x8A3wuVlJAilVACwVKwy1UGsxBciQziGmmgvxKAICjAUZYwg+CRh8A2sqAIaIwAMaKgAO9IQdvP_moAigBIMwUFj+ID8Ho9AYvpKF9JCjBsRRzVQGq+yhWGUqzkazFYSE_Ft5NNNA3yNHDMdqQAmZAAAAAAAAAAACHACZkAAAAAAAAAAAIuBjQeNiwGbHQTLZMZEQFUBWhEAEUAHKEwAEEDoAANwkAmWyIYICwGkBWhEADEAHKEwAEEDoAANwkAOdZEOIBIAwK0sDNpUAfoKjj_VeAvMVAAZOQgAABIdkNKD3+IqdDQEUABBEAARJgAAAAMMRNADli8AIUBXhkFkQgNmVgAlpFwyV4aMzSRQpLByRXfT_DEAF4+dgABuIgAA7wbOyIe_DwctSgNAlQANQG7MRfgqvoAd8QgAADaIkYdCzSRa7ZzigrACLlYAxGGSKzjXSezEU30OjdXSbQRi5s8f3Gu1k0g_NElkCfi4DFx5TUw8bFwIfHxsOFwM7N1MaOx4zDhcCGgIe"
noncomputable def WL5_1 : ℕ := zfNat64 33240 "uEhdnQAA1ioA4gXAANwqAAGYfAJABlHwBcJGKQgYQrAIqLgAABp5UAA1lehAJADMIwBGBID1CAji8E9KeVADkABqE8qNIPAE1J4pAAGdVKYBO14FWLOKJwNQI6ASYOtoHwAKpKjSDwIQGrt0IASf2UgAH0LAOTowcSqLQonBDaqCEACwi40g8CEBqcVCAEgQaUg_GQECNCqD0IHJI0cmI5U6WLweg448ZmkWgHBKF4OR6A1VgjQwY0Eah_xKADujE+IQd_RgMzFwAGI8ZgBDkqD_R8DJDagjkY0EATaBHB0DVg56I2sEIHEn0MLIh0oXgAtJw5AAUQAKiCUgY0EDEykAj9eSY9pwGY+A_4NAACosRwobgCqpUUQA3OhDUY0EABKBHAAQlBoQ4ANDPWgR7Onwf+QI5_puCclQATobgAX5UAADUYyUDSE1WDcUCOUE8hhBfSeQ6KaRzZQvJINRaLTCMQei0NhcrJo5HrTUymPZ6608hjUWzkujk0p8RoYLn8mZjYBwmjuUIItFJi8Q6fs8Ll4GZDYelkA3AXIEAmr2kaGAkAcwASo4A6hNzCraaEf+RuDoxMZ7rwuJoDUekEDp142o8XABNQADyikAKsaIUQg+GjAeGLiaALSCAOjKF4DyUJ4DXLqEBkskUGQowMmYAK6g7wfNiFpE+CegDDKgB4h9SQAZpUTQAC6IQiAkFWAO0vAGJr1j4EKsAAA4qAP9EC8AF7k3_E4AG4nRdEIA+Y+D_kKHPZyro0dj0mlVFKE8UoXgPZSLaSALQiFysmikKt+T6YtvPIZdDIxroRVuI0MP5cdnQAcZACyoAINAEBYAAAAAAAAAAARcPFjcaAxoOFwIKllgxEgwCRMBKBVMqAAIMHwaALUHu5lQADtkJ+AAvYaLg2NgBIaAwEgQoxAD2PgAWgf4OgfB8AABQ2AAAAJDQGAkCFGIBgRMAEQCWhdCYAADB0AAAAEMgAg0AMIaWUgolC8BSCUYQCqL7KF5NCij0ahbQI4pQmAAB3OgjiQGEKoKSUSheB_5KLoBVGvlC+ShRR6NR7oEf778AADoAoMmVQgDCDRFIBJYvANolKZXMYEUqjyi5WfQos9GorUCOCQAe4lA6Jg35KrAOQBjlC8AB6uXwK2jFUIoXKzSDb0aejU6CNDLIAbJRgAMo6SaUuACcjVJgAFoVUVgJoAR82AAA6GwGgEwXQI6AZUfAZmLp6BNkowi0IpVGqlC8AHo1VShXUAMtLwAOxo5DZCY0CCTh+ALQBKTFflpRSqIELlf7wYCejWTKFdRqJQAGzMAHDQAwSKtKAAESlQBShiA_8pCCCoAA9mwTQAL0xAXUwIODwBCNAARIqWYAATidfguAIoxAJNUEb3RcAKQaqZQgEI5CSkCWgXCQbBIG5MQA2j4AFoA5BvHwAAQToAAFwkAN8POVujwBRLGYHMi4AGIBn1CuYBKjoGwS0Gsn0LAikPoAAs0IBFN6YbAXiPgIglQAu4sZhU4hVJrlQxAohkVCMIt_khADEDUA4obPUFUxAamULwpL7z4WjW2hRILNyhWNazhJSnlEgzEaKBDVYyYx7MWdsmuwz0YliLgPQ0ABIIuAKCGR5ioCqJVKglUpAADQgLIJABFg8AjiQADwic1AuAA9GR5h4CKJjKgJCDU1KEE6FgyAKQBLZ0A5Eg_qrBRZulwBFTzCQFEymzLgAszXACMAUgoQgAdpiARmrBPWjlwAmhEfgTEsrnKF5shIAijUiaBH_8hAdAwgAhVswAFaDoABhHygBYHzlQEgqA0n_0IACI5AAECHCRVswC524I6RQ+AAA_2rCgAoAShLNkwLQf+GgLaQJXFgAQ6AJGQGAkESmIAZx8AC0Acg0j4AAKp0H+j4AOwsAEGSdhiAMIATSheAGwLGYBVFYFyt_wcFFBq_lAjh_1CLoLUHE4AXQ4DASBvz8AAABtQ+CkFRwAoAvSbAAhAGgASMg0xEASEgMBIAiJQDeCoCTyUAC0AA_6bIwWgAAAAJkASGgLhIBgJQARioAEkdAACsmAAA2dAAAALRIA6HFEZE2YgAFelQAOQJ6U3KgIruFiGUIQB_g6AAFNHpyMHQAJMFwAOQJ6dzKgIrYRr29C7kRADkVerADEEwGNiSjQAQHLtDFwAOQEs9CJFysCK2EarCRoYtAHIvFWB0bAIAkCrDiELgCqGSWy0BzQRyHQSz2WSkrYuVgRWwjVD6BHAByMXVK4HwNCAyhKeToPokEJAQqzKF4fdMiWhPSqGqKlYD2uv3TKcNDZnQQkhpMM5ABTCRCFwEJAQmLKF4AegwXhPSqGsKlfxBIHpZKIDTJvQQCiWc_nQB8uLieJy5GYBiApEoXgAGDBeFBHJKQ8scS4TLSxmzMqCFDCabZ7SRvxYzAAkNEJMwEePGYB4yheARiLGYA5OKlQEkMFm1BP1JxtnoPyLgNUaGwzZwKobMwGXlC8AFoE5JSLQhstJcbM3cIUMKqLWjfPQdYZLwdCQIE5lAYg8YuUiULwIILYHIxKI+HP_kIcxUrIIOYTLZitdAhnUNs9pIOs0bg6OgBjOAJGQocGE+FgGIERSoAooEMjoAAmpmFILJtHv9iojIfAJAJhpB4ByAAAWYaAMgAAhj5AS0E3vD1_0WCAiEAH0yOQFCwCoMH4CHyheADEAgjYRjUFSu0g5HpNHpIUCGFU2z2kmUUBkvAlFwPHyiOUqljN2iBHJatEoXk0IL6kCOMabRRMp5DIopKpJmrVTR2TR7PRqWTLPaSaSGGS8qQDEnIDGyhePQBiMQWSEQa5IzBipWJTeiRBHpNHp4kJ+Ek2z2kmkEhkvA+jExsAJNQAEyIJ0wFwkAqC4BzRMBIpKIIAbLJgAJyAAEIiCMGxiAyJH_j4AloCmEYYgFVWCMscoX0gDgopNSyJEcI1LwARczAloAGGgB0kZC0AGZOAHwfAAtAHIPo+AAA6df+TgAAEMFQAcaehWAFAuZwIN5y4Ak+sMgAHFzuky0AEs1t4pE06KbAAAIRoAmHpgrAFEMEoTwyheFRDjGC8ppRKoJ4qVhNLI9Jq4VAjk0DppAcgABagPA0CCRPAk1EKDAEoXhUQ6BgvJNpxRKoI4qVhNAktS56TV26BHMIpJJtAkkuSgruqAJjQIikECDYBfREADUAFgEQADzDYAAKUtBAHhPJwCASgBsHwALQP8HQNw+AABcbAAAuEgAco6SaBoxhFX+rBRUIli8AijEagTXzI0v6BcRQCa4kRgAAvjwCvCYQDBvdRWC0isBBUYAIKkjKmgGZ5HxKQArNSiEaj4AAAF3AApoCkJ_sdccVg1srAG7KF4AMaaAmEiGSkB6PSjJ829KhAxAAEaMG5VB6yZTAe8XKwEiIkMYrIQJZRSCRValCsahFHJNmKcTyHaJiMJxmtBBiTIEGElYMG7JliuCjlauFFZ+UL_ypwD0DBvTQikkFMXK5SEUelGanJQI4GUCWgDRhCSmAJCRRGQnk4A0JwDmiYCRSUQQA2WTAATkAACMzLQUiYGg8Ai0oBKB8B_5CAAB8TAAA2OgAAXCQAOMrQUoSpcACuUYQhUAAAANAFCmwHloI1HwAGqks+KgDWrBRZnlwFBE8oVwyBQQpFy8GjUCapwRJYRqPgAhw0HcuAGjNttWCivqLgAACQhcw4OAJqwdCCNR8AADIMy2nzsGED3qMNUqAoIASXQgnlQNAJqMhaCNh8AEOHzsWB_zoFFJF1qQEEAAABSgQLEHFBAJZtOU+C6aQJCEwAbhqUj52AycgTgPALlYAPU4dhVTSUaKlYWEuk3_5kW1Ahn2cm2mgksWCfCpOHhWpgIQCbFysCSUVpHTsHZw_CqaSiKZqRa6XUdJkuYkyQn5hrp1poNnKF4OgEWSCR+NQP8IgFblQAQQAYeVB_8+AaUhfSPhybQFAlQHloABMgKckgvXLgAAHFQABkq_8TAB_oSCSAP4+HIdQCYkwGjIyAubIBnXGMDRIP7KFsIphIuAPCFwAOJKpKAFA0IAAwhMN8nRAxKihekqOE5f6XAAADTyxfJQCai5QI4AAhSRWAnCyJaKG2DoBYBEAbKRgAWiRAAOANgAAnCwCEkCcI6oQG9i5eU0INNKSDeEJE5QvQpVQmqMUCOQIWAAAEBZDAkQCxQI4ElC4AyApE1pISbKiY0kBrQFCFIAfwJgBDpSBOAMz6GAQ0oXlNGbIVNKiA7ouViWslUJqO5Chyks1kB_Q4nJ0xBOHWRAAU4LgP_oXHlIAGMlQlAJrF1CAAMITAASGgAKDYAAAVFwAAGBgAADBwAAE6G4W6sE0BF58HoqAtWfAAAATUDy1+oyHoAPQBACQ0BKMRQk9dRiYz0iJQvANkdP6KADlGJYvAJjNXZJEcOoBBBCAAWjAnRZxA3CVENGC8J8LQFNHT+igA5FoATVzaFZ4iACKA6AVEYJGhAApoAHLAAYJRmanAZk4CPJ8AAK0YAHIAAwhGBrRQP1owAjUZJNCCikxQwdArKF8hCFR1RSCgJlKF5EZCA1ZGgQw6VSaA64sVhmNjoViRiQVkfOgRwi0UmJ7z6WjkDGnyfUaGBEByM8sX_ogDY1HIPRAgAGEJipTk4aBDCgkxCNlC_NTNTQdOgR7bTaSDai5WRZTS0yJiNSsoEcIJFAAPbCIQfbRgGMlR_o6DpKMDRg9hUBhpUJQAD2hBxACqAIIHKz0sp5DA2aMB1wukw1EEntFLIpBISeLhiATUFo5CIAKjhmAAXG8Q6RKdB_NCAABqJ9DAwhMgqIoUUGeHx_xSAGlDwA6A4EUJ_9RCBgR8_AxsrACcT6HOpiqoPS5JURS2k0J+oQtHIRAAHm0w0mQNjYBAHQE70YAAQdMwAsUTAAZWOgAAKcPn6FAe+ARhrQW1K1MFItoI9rots+ZT2YikgkUslGggJOHb6TyGLW5KE8om0YuhD0Bja0LmqgAdEKRUC5mADxkAAA9ACJhMABCQ2AACcVAKCxBg9CAcinAFFAqjmYyMEUACuHwAAhjoIVB7l3Axx87Bia0yKIAhS7UQag9k6eRS6XSKQRR55DCiTTSBsUR+EKW1y7k5HohGo5DgrU_3oRJIJlZ+6dyriVQrj0u2FNClPoJdLNRKtFSEhPxaTSa3hu3lBHoDgq8htcu5NHo9po1MIcN0WK1MIo9WMhQx6YSjTSSRQVkisqlEkkkiiFC9KPgBID8emUGsNDx2ABtOAAmQBIaAAAAAAAAAAAA+lbcu4D0Go1b8pUzzw0EJKo5H4gMxaEiNHZVLJdIJBCavH_wh8QYRHxlAeg+3EITTUlGkMTuoUyihlupVotBLJdFSmEs4dlUslU0lWinXcu90j4g+IPjCA9B9uoNVdO4TRp6hXAql06lWi5NQh6BVLJVCaIX0PXfwSlUdAKxdAejVDscR+7gZRCC5TAAsJVKoTTGLzd2LWVSq0EDyihSKpZroD0AARaAyjZKOR9A0hJEKAbs6AinU+gGwRBaTQvo0MAgVkpJLP_nLeHmiqChtrq7C4jpZtZprqA162WSDJUxQwOk0W"
noncomputable def WL5_2 : ℕ := zfNat64 33247 "BgAAPNQABdABKVNaMQamVgP8FwA7skVm2GgGIvIuVgSmew8NqCaMZjaBbQMkWMICUVKYTaCyEoXgTU5hUnooDElNFCUz13xszQCgQwFTJjNtFptJEW0bwpIwHDVBiJOIYgKoAAhRepgBZEhlQAD_0IEnIwAAQcSDEScQxAZFuCimGKgKqAAH4+ACajoWgIoE1EINQCrJBcJOIYgROlAAAAEEAYfAAEOOgCoBLyoABZ8AELgBpUAEFgBokBgUAAAAAAAAAAAAA8WAAdKFYClHpQvAClKU8+QcBEgiWC5WAGRiNVPI0MAaKf+Hx2w2AEBjADhYBUQqAFiULwAgClPCMkE22VABk_0bOzQg6A0UgKBCAAgVAaRZLDBuA9YyUKwFJgSheAU0P+CRB6khQzkFysAMjEathQI8BAaKR6TYNgdswAiVJ4lApOG4CeJFYCJyheAMASJ5mI2CCSkAMg1G0hQw2iGY0U7adAB5KqQHhiC0SgKX0lC8AUgkTyhhsEEBQXKz+pUBkYjUayFDIphEMxooo84dg6NgC4qBXEwYiRKC4AAAAAKhoCoAO3mwAAFIyAsAJ3VgL_FwAE9MpgEEpAXK+NEw9AyDWdaEAVALCZAbDloyAxYySj5HRhBrZQvAQuULwCSllSK2cx6Skiw5IGokU7xszI4hQwAMqpQAAgkGBE4piAThUADIiABTEwAAoIgAARGQAAAAYSGkmcQxAOwoXgC0AYYUJwNIVPKgPJRIpWtCAAAZgQ8BjhwYiRhB0zZrAEqULwBIxQnA4_2PgGxcrA+lEijUzyFDItLxZAAAGjQwgTQ0dgLuLlYA5FIWmkj_OHZWShWOObOYnXj+XSbMZ6OTCbTbYZy6EcPgIogXMILINHYDlJhcrAHIpC00kgJw7KyUKzaCleP5dJsxnplnjuG022GcmTHD4Oi4KmjgMCgBVFQCKh4A_8jAAr4iAAaIZAAC0lxklByUNMaByJAYQAeaO31lwG6jqugAi4uXgBNQmJUf85l9oiAAAoRIP_MQU+OkwFwBrleAC+BcAE1_gjE8IiSAB1EgbAfZ8ByJBYI6Aei_LgB6aQMIOSElwFUJr7dGsgXAAB6Apj4DkSD9bUFRQiXATWk5UBdA6JcAE1+ajWOLgAA1AdRMByJA_BWrgAGUANoMMLgJJ1JqRFGscXAAAAfDgORICyESEr85cACFvA0BVDGlC8DCbSarVQI4B9D_wcHinQpxIKqE+EowBcvAGqCBxGAURy+koXgXaXNG8qzWg_jMgwm2ukE1Q4jAfLgA8KpbAkm2Ll4AIQ_6zFGsB0Y0oXhXTbVZq5tAj2OLrZFQAhImAGjHXloIrmUKOE5diXADGuh9RqAAZQvAwgNTSoEexxcAAAgpeARJQBIaSEKaA0o+AAAANEQAAEjIAAA0AHLwBK6MATouAP_rwAC9KgeYxADjQieEQAAHfjh8LJBCeOGsq_3LhbS0DGug9Mv9j4A6WLwLoTUdqBHscXAAF+fgJ4+LUwbr6WikryTgnJ0S4Dm5o3AMILrLgKoTV_SNHAAjITAEnPgYU0U+vUgBkpAAAKSPgwgAAEs2ckhBVABCDqPAKR+RTEeBmBhCcE5LwXADUAwgaAuACa02RkzEC8UgAlAEADZQDZGAJDTCVMuB4CkAADUBoYQPEbAAApPgAADTULANxnY6UAEkwbgWKLgAAQ4bKbbdInwmcoXnEqoDXiSMFQAYAdABPGgNgsk70XgB8ZAAzKgAfA8EU2gZkqMoVQo2bAtKoB5YuAEABzf8JwLE6OAxB9yMPkoXgAVIpZtIOKLlZpEfKlMBq5NAjgZQATtTlOJUcJiBLEYWgIRJgqFV9LUCzi5WZQwgNSRIUMLNxFytAPSZqQCgjnP2w4AABxUAAoFgyHEAAADZ0RANgAI2vrwBKHIIbGnTgU8jAAzJgATgcAAJCYAADB0DQKIAAlBJeR6I60ACjzosxcAHyGgAUWVAANXFoRFAMgAuI+LKVWL4ekkV00D8oUtIGGQREnoDnSheLSaYQGoPkKGSSzcQDwjh8mQCEL3krA7Eg_8xBYJSTAXABpxYAKqFwATXiyMLbiAAdyXFpEjjhEYQFxlwEPzIcgAxP+WLxaBMZqnlAjhUAJxjwAsJq8yotIkf8FjCAd0qAPYVCkAFAlQADfUIAB4psDoNB0AlHYxAAsLgArYLACPyoAP_Gz2UIAAUQ8A4CR51tMrZLQAQePmkBHpcAWw0dj0KkEBqO4uXikAmpoEqP05GnIAADrRtiOkGlwYSdgACcgAFvOgAAgnQAANhoDYcPAFwk0o8uZaCqh91GkoXADzV4AKfFwADVxaERQugAI6LF0EYbVEFJU0KPksuAGImmK+AKQWgBNWrI0Mkh1VopAMIePgyAQhfl1SuJdaCqgRdpFwG1DYQgBVQuACa8WRhbcQAABUjUIdFMciejGbgAD_psAEAIGdAABBOgAAbDQHmsXhgEMWyNUtr2FiemPLgAWjUAOgJIgDFFy8WgE1CQlRxbcQAACRzJkZMwnohS4BaxkMQRwrUwKkECj7cuFIBNTEJUcizkAAyPAfhjoB8xgGQn_xdSQeAABiXABTBoDSA0i5eA1CasPRg_U5AB0AAIqAFCS8EwtRoAAQrwBi4AAyAIpKgJI1BqpFCA2gAAx4Byxs3KmTKlsAAExcBNAsiwCkJsFwATXiCMEtC4AAGljwcnGuIgAAHFQAC8SCKKQGvNwAAAAhRoB4BaxgAQsC4VAAFhiBMXfKCgAFiwAR8LjaATVeiMPRyAaKJgBABCMAnJgBYsYA0JYeD_zEAAAABBQFoEs2AUtAAAQEgAwowCRUBhDbClRIuAA6APQI5QvgoU1wyENWuI0Ml8dAAEYBhRh0CYEOK1cCLLsuAggBMQkBcvgpL5KCasrQI4AEYiYAHiMA2FqhHgyFQIUWq4UWZpcFQAAAlFy+CgE1QaiRwkgAlAGLKQ0DPYwBIXdIeJoaAJgEbEwB3IOABMxMAABg6AAAAmGXGl00mYAACZUHz0YBYJBRQHWVH0AiabGfiYAADwAUjANSZiBoyqcBljoAAAACCgVQMJsHICoAAAwowRisAlCRWBbwuAI6FR_ilCmyhfBQsINVQI0MAAnREAGFGAWCxxrED5CoC65cAR0KjSRTZQvgoGX_KcNVTI0MJIBoQmAEjKQBGZABRf+lobpcAABMqAAWCQfsTgGIVH0Aa+bAOQCSKkAD9GAIJgVQTANZLgoolgQNgUQTaWLwKATUV6BHrLhjoAEoAjkYBQLDEFQAAKC4ALANBlmoT4LgKATU06BHLpZAZMvAOlIaXgA4WK4uVyZEgLuSJ6iBeyxf99mqIBE2lWmhtx5TpQvLoxAGo40COUkAmoABAsKJEAEciABiVAA7RYpUlAAlKgAAZIQUQAAAFjBSRZszh2pharg+0irP_EomCXGkkht8WQM5AsUXD0AmoAAEZctgHSFtjOHYPCoBODMAJi408iSgEDOQEmFw9AJrHlOAAAEsXwNgQGPswds5mzASq855sAfsiDqKYLgAJREfIyA1UoXgxJ6DUSCNDIppMoCHCpOAGJHnxGDoJFPIYXls5nli4AithlIAWSheD35acA1JsjQw2mUALREjAPETARpYxbiNB9o+AAA1RBABLiougFdTYC6TQPyEwAzgcljYzowfAehqGrmILKF4AHQAZ+VWSZgD_RtJVCDSVQMoABMaAAAAAAAAAAABExg3JeeQwAIu9gvi0WgMKMl4dsJFGoNSrFyssgZQeujQIYxMpdBTTMLQAA4wAGWKoyO2dB_56DSUQAMMVAAG4qAAC2fAACaKgBFa6rGRgToGFPQChFIA_MVAAAGUDr0z4AASZ8ANjGCY0wO+X_4yd0dBftyA1wnAAAMQbSQCyFKToAD_hUAAKGIVPIYB7dPYaTjasADU0gD6lauWQAk7FQhjc5qAJiDKsGcjZ5DAxj13MJpDHK1ceyfC0agOOm9hoI9CClVQrlkmlkuhJVOgQx6USaSQFjNnFoHgdPOAJDQCRkEZGoBBSEACUAANIQAAEzIAADcHBQkLjZMjswQ3N8APReGg32dALqJgAIgA6cmAAiGdAAfsED5On4PAdksFwkTwSAogDaHgAigARAiAAJ4ZAAIiHgCjSwGBUVzICiAR4eAA6ABaCIAA0xkAAuQeADPXAYFCgFgh0pAB2HgBpQ8AAkCIAAUBkAAADeDlnLmRDwFEBRJcAf3Li7icBswuCrQQmo0UCOGkmnkAAUYcXgPT0qJJxaHilwALSmgFvLF4UaCE1HygRziZSaeT7ZkGpOA8rYypoPAUQEjli8BORcrEIVT1Z8LTfFysMK7FYqhHTBuQQ2mm4mEipgSpYH_DwGwWKYCbSxeAy0oXiEppPRagYuVhNKpVBqKVAhnEDSxnMtxsJFKEnSwPlwH4HpwRUoHgKIEU4JcAC0ADTli8slU2yEE1OqgRzKZaKeQGMnAFKm_0QjVCwFEAkQ8AB0AC2EQABqjIABdx8GtlC8oIwfAogC0BS_8qKWQIxyA0_wXLKLlZRAogyjZmQQmNG8wkU4hFGKiSwCm3yNFwHB4GpRAukFKF4AHQAWogLlYFjlYGrDkaGBcQi+CTgvD5cdgY0HARK8ABlgP8UAR+hAAGvD4igtAotrKgAKuoUrj40mkCnJEDYI0CgTyGGUI+WLwCCTT5asE4D4cpQvLCANUiI0OVx8cbSAVEgTh+iOLYTEgdshPwG6li8AekWugDl8ZQvNvq2IAagZQIZ5NqLmrOA8QmRk6AzK4LhLKJ8ErT4BXhUACEAF6FQADAj4NoAACeDnyMkYI0cKKVm6B9csuAOglxTQNMFxUQJr_5GDLKT6AwE4ANIcKMlRx6CcRo5WR7zEuABaU0AuZYvCiBNRhoEc6mWUn0+6ZH8TiPACQ00YlB4pGA4UXAAhABjxcrA3srA1f4hQwu0E6hF32lAWoWRo4DuRoYU5OhaBk0qEIAF8LlZIV4KiCNMG5BOJtrJxCKSlElk6ADjIAKNADhYAAAAAAAAAAAAIsauUmAPOhAJdKgCSgAqcqAsstA7VCCaNbqDNkoD4+XAigeqhEDc+hgq5IjgHELgC4BcADGSosgH_jaLqEbS6JT6AAN5iIVRgqKjANOLgCUlQdDoA74uVj0AjcdUEumks20rPU0oAdXEBTmk5BxKBHOIZpKgAOgBDMqLof8Wgv6hGELaERkoA65XKyUdBCfgAHbKgAUgAhEqIofuSgWuhG0whk4g3BKjhRSdLZshQwcqeQziBXSheBVFIdqoBLCheWguVl0NtRJifE8hmkukm2_1XiKolElhKDkZIGzYKBUH_jYBe48ABUAHREQAEWDIACm5sTMfgy47AgXCQUBoEJowBHC4Ac8XAAIMqAAEahAAAAIRYAAAAAAAAAAAAC0WQiTgxknBOUpGwAZ46hgACAu40TEECagLR6Bv5SALhIXZ0AANYqAOIFwADcKgABmHwCQAZR8AXCRikIGEKwCKi4AAAaeVAANZXoQCQAzCMARgSA9QgI4vBP"
noncomputable def WL5_3 : ℕ := zfNat64 33247 "BwHQ2k1acpE8IgAAAA4QP0qMSSgAFMlQB2s2DCGSyR9KgDqYQQiETwiAACMANlQD2aSTgIQAACyYAAyVAAAAAeWpCYZJDwAAWUrDAoZkkGSEisCOpcV2cifCxmGEMgrAuXgdAmoARElgBAZ+ZAyOgA9CAGFQBIaAAAAAAAAAAAAeg8Gw+AfJUAT46ABaB_46AALRmxyz4AADoUAA2atImUIhAL5EngC0AJ2WMwyhVGFFysEgJwDWNqFQQAIIAAcIOoRLwRAlOgFkhAPYKgJRJQAMQACap2WguxUAAt0TNwRoYEUILWDo+5QvCyDVjpuGEolFF6dKQok2mmlJRszoIVnIRSyMUBoksANc0ewwQgzsiTwI1lQA_M0dgFEzmVAE00myUI8gvAA9B0ATCy8EQAAA4qDQNQJWOg2gD+KgCgDkASfyKwAFIGhASQdzhMuhGhgQQHIZSheeoWgb2WMwwtMUq5VDiFysKJNooNThoEcHohOoAc4TPzQgIoDXi5WAOw+FosBeCjZ8+lIFdmgnTEghVLt5BqI4fJcbAQFShAEhoVBaAOgACOkoAwjUE4fAAAUNgAACy2NjQBhhE9jwDwPIYTQrpUCkAICYQA+gKM2A2hZ8IgAAGinQFo8ADD4B+x8AITiACGjxsB9Can3Ps+EQAADgFfCBcJgAjjRfNEFwAQQgNhBhFSsD6VSiNUbI0PPhEAAAfcqYSHjiMHL6jIKNFUSULwUi9k6mOVJHRATCSRaB9IoxmpjFIAAO4cAfIr2daOSOIwejEmlGirVKF4KRSidTHIQEwkkMpYvA+kUYzXnydnoiAAI8_LTEAYTRqhUSBjpIrAX+ULwLMxHMXK2vIT8so5JTVRETp7pM9GqvEKGF0AKoAXZoDcSAUgBbKF4FKWhYZQvHoaRyH4LlZZDqSR6NT4IUMMhimIAegAgxgANXpjVaQFyTACGKgAaZUGTCAFsmAACCdAAEcPgB8L7dGwDAioQITUqBCH_kImwkBlRUHUnYA3yEAARw+ABgLLSfZyHgHoaR+BcrAH8lC8hNYmL_hMeLKgOo5BruVCDiPQAEFO4wfCclpCMFysWKYNwFJskaGCayJStDQ7ipXPQicRzKSlGzOghh_kzAKSQI4N35iZgIJiOgnlUASFl2IgkJwF0AAAKKADD4LCA0k6AAAHEgT1UFSkisJovYuVlCWoDNmjsOJlspRBkVKwwnU5S9bpMxoJRADOhsAC8WXYiRwrB24qAM2ULwAchtJIyYzKPCKlYSTaVRppE8a0EMoAHQBrQAGNAJhYZoqCyRUBmwuAAElC8K7_g6HuFysaltJI9Gs+EaGFGOgXZSgAri1nHkc3BUApAC2ULwMytXxYZQvABCtfHJAMoXkNtpJHo1WqgRwyUY6BSQdDQDLXCQZZMQGICKh4AvAVAAr4iAAaIZAABUANK8ACqj0HgM9FRYRQZUAebMgAk2VBdQKEIQWbCB_suAGsYPgw4+dlpEXFysAlIO5WL4lAOFSs_uNHEcymYsjQIfvEqqmEB05YzATEdA+qoADNHoXBUGgMIAAAEkAGHwf6agGOnQAAmi4DVMAwfAVx87CyEWKlYFoE4a3yNgD_5aKK5SxmKSaFTaSRrMWAnkMKJdJoOfLGYWzt_GgBIaAwEgdIVAFxKgBvBcABRioP_OwBokIAAAF4dduTGUB_pE8AWgBTyheBNBcxcrA2xHR5cNSCPUTKdNAUQlRw5wmMoLvJFYCYi5WAEEDLeWuLylShWBtMoElCvMTWnkMeYmUybUQLslRwtAHUsNIHNJFYBKSheAL5KF4aTCGtSoPJ1JJmQ2_+hSqMgugMgRgBHLwAUgfaLgQhAI6bgFPE0Zw+GVAdSTSZQG1BloZBdAOMjAApFnJR4B6BmbOYyYuVgCoC5WAUuiEC4VKyEmmaiUagiRocrjI_qmSwKSH5iDZV4ThLAAoFQAMSoAGoBQeUjC6KlYAE9UgjGkASAcPwZXQjh8qo9DanpSpqULlYFUlIBSyIS6CxgipWDE2zUSzFh6BDrwlGk0zkoKzEaOH43NgMCNgJKDaMIADXEDSYAkNCAECcCaAAABtoODhFQATUsgAAA4sOKhYKg9M8ULwmieC5WB2xCAGWMxAhZIpkyhWHUy20NCxfmNBAAUYXAD3wgVB6Z4oXhNEbFysD8yEF8sZiBCyRRNlCsOJlto0li_MaCT4eCmgs8yAMPhA4wNziIOQgXBlxQvA36VADwyxmAEpAy20CmoQNAagLQAJIw3DCGkCaArYeAOuIwADsBgAAGBwAAAUHCaoUJj4Kk4PRSE3y50AwuVlxCCegyXiBNpVIq1yRWHEy20siOMmZBIJpMNNoogAqTgbNjoGcwoHEgqBmiheAHIuVgBrDJef4ggsjqipWBltoJVQgugAAIBwwgVB6rAsVhNBZFys7O5BBLSWMxAnECSpbIopDqZbaWZiz1AhjUOH9dLoGixYGwEBJYwGTCIQqBmiheVITgORcrAJaNUCFkFIGW2l03Bto9CAAFkPBnRmJiBg5olTcHB_omAVoTAGmioAGxkwAD8ToygAGQAKTf6DiNIQkBhAPaVAEoC796UAIlKgAD7IRpABL5EAATuAoCSiR4iAKqUACwmAA1FQAAmJgAAMHX_kYMoAAFASO5Yp3bKiegwVq4UWaZcAAAB2Ll4GEJrpNGA0eRwylEBEKxAiCfQRElAD8JgA4JMABDCYAAext1ZaAAsg8ASRCPTMpwUWGKwAAAeQBTRkAUAlG1L0Iog5AmaZAIvJ6UMrJIQIJSJ4AFEAJpJA05V9ROA6k1SkpFkUjkDwBUARgWexMjnPQgWYrUz+p0O_KF4UQYqWMwmkUsj9CpWBRtpdc2YN6CTQSgABTQ6fjL2CEBVCyNWLlYAMQihJJSFZNtsl6Wht79CUItHkkgAQIWMwDoEMFnIEcGohAuVmBlIkkFh5YzKKVUiikKJRNpZA2Hz8um0FSA_OppnoBipOC83RmIK6wgCQkYuXBAg2ARYPAA1ABYBEAABIyAACxjRkFTSQEwcBJAXwRAGaSYAFfEQADRDIAC7Q8DMXAjsbDxYDESBYFAUQAB3x0ABaouAAavZQgAA5iQAoD4BQKAsgAAbFKeAAZYuACa8QRvdFQAAA6D5wR4sYsH+FoAAmcpAFkAAKgmzzUIegAcEeB01AxEnEMQFEAAFQZAB7hYAAAoHwAAbhIAAhMK4lQhiAogK7Lg_cVFAyoAMjUVZQvACakXFS0AAyxIAsFMGIk4hiA_xsA_MqAB6ADmioAB+Z8AAG4SCMtAEBODQsIESA0gAAAAHQuXgixKLpNdIowAAcxIQaFhAiQFEKbZUuAA6ATRdpQvAMqzlSeNWnI0MABWiEAAcaA5EgY8VAVaLgAxxIfA_8nCNSheAaQa3XQiCFJAGgsEqCyBRIEFFB8DBhcAB0AvCcLvKF5lAAjRnBr39CDKUkCACxOoNCwgRIADVJcATA2DoBNFplC8Ayk0at2RoYHyUoAyRYuRgXCQJg4AAbR8AC0Acg3j4AAExkAAG4SAA2jBsJQADri5eAjRGhjEAqh9SheBRSa+yRnhExwgWAAN+TjXCN_9OAaQXLwKCMRqBVCUjKxKF4FFBqENAjs6IicgC7GiZAGGoyUBzIuA8UjDEa7cGgkgtAoINR_oEcKAkAANRIjQAgjH8nAHMTgOZFwDlkYYmEShVEUlC8Cig18sjHLjIACxABiMABGnOYgDkJwDrC5eAXJGhjG4gVRFJQvAooNQVoEcAAhhUAPpGBVzRRswB1E4DmRcAxRGGIBVKRlQADWgi0CqGPk4HZ0AWiYMGy3hoKSJwFZi4AwAZAFUoWVf6XgAauzQgMIBFAAUJEIXAL1UKYHty4CgjGsgVXQIyxShfs5WCik1NKiRwHoAB5PZo7o+NATQIKGyxeZiQhrQTqljMyjkQlUT4XK_LL1snNFBq3dAjgZQEWFy8B4BYEgORIP5LQG3C4DzyNMW8LQFU8sXAUUGp_0ICyBjYqAEAJowBs+BmhwCAcAAAABqgaAGHwABeF4ACKgCKDgORIDaBLQHJXkaGMc7rQlgmJpgkZrZQvAHoNRnoEcigI1i+RkAXAORIACCMUoXgNQWt4WgeEoVxSBUrArpNmKP0CGCEFi__96Ms5QKQJyXGZkgITIpGg3IPANTKgAYmEByPFKh6ENAvKETgFgAANNjB0xbtD4VI8AAAgiAANFwAAADtF4AAQgCAgAWWc0iTiNAHQBhlC8AUaWM8jMQT03OVFEIaDW1KESRjHQANrIE9hxoksTB0BCJcoXgNSW7EXgnIWwqVlEIbLZiipChnqaN5RAA6Ds2ALT4WnTAAaIQiIFgsAA5omACCAEhyYACYh0AAG4SCMEsiEONAAdX6FwBeAyAQiUn2VAR0ajWmaEAAHMSIszsy2HjQFnfBiJA0CgKoDVGJUAF0Cwi8R9KgAA1IQAAbhIQcFgaBQADZSxeAVIIxAJuPkp_5QvAIo9Gpz0COAAHMSAAAAAAAAAAAAXp7X16DgspBgzgDEgTgABJAUMTAuwuXgBNY8I0cAAOYkAYiTimIPGswCxi4AqoHvDo8EXAANXtoQAAcxIATJUGIk4piD_x8AAX+bgAAB6GezYDy0AAG4SD0AeFYOCzimIAHDI0MGJcAAANZEFwDkJrDNGAUgBfEirtQExAv01iAZJQvCc9nLgAEn6FYogeMoXkkLIzYwGq1UCOJQADWGExBwWUgwZw_UXAOdTlwEEI4GCwpoFLKF4FUBqe9AjgDw8jgAAgCqagweMIC0OIHWuS4Ad0CDwKIGnKF4GUBqrtAjgngiApJOgE8OGQYgJYkTwIrFwAvYEHh_5SCPJUBlAa0JQrHHwLQAARgcRYsYQfwkTwKolwAvIEHgUQJKULwMoDU96BHNOQloWgAOoOCzimIBaA5Q4XLwA6CQMApTwO0XKwMJRBrIJChgWTTIpiKtPyYlxkBinQYiTiGICWKVcAAAB79xyJDFwEkJqq1AjgABzEhBwWaQyYwqoDySlYlC8AHIUaKaexKUpP9qRBKpNJcbMymIUMAAOYkVoAHGgJGDOBFCckbLgII5AnEjH_li_OMsXgQQmpN0COQQAA9cenIOdQI4TkuRcANQALO4i4B6E1nKgRwoOnMAHrjwBQJACnPgABUB0AAGgqAACkfAAAoEgNnQA4VBcJOIYgQwtAAApAFIDOPgAAAADocWoWAPKoMRJxDEBhAR2VAEgioAE_lQBVBVCEAALI2AFtVBiJOIYgnwpAAAAEEAPwLwE02R4hAACyNgGOYgwurBXVGFoAOosZp4GgIkEReULwAyDWCaEBJArifAAEEueFjCBVAu6FHfMXKwNLIQtuIrARINBUoXKwAyMRqJtAjgSQOQnwZlsWAPKoMRJxDEBhAYOVAHoCoAgkRyoAq_7RiXaEAAFIaAO2TBppIFQ4BvSEAAAAACEYAADzUAAXQASlTWjEGplYD_BcAO7JFZthoBiLyLlYEpnsPDagmjGY2gW0DJFjCAlFSmE2gshKF4E1OYV"
noncomputable def WL5_4 : ℕ := zfNat64 33242 "CdRIGwGBMTElpVSAGhMUAsDQOBjRMAAAAACj4AAFS8AAKAWAbg4KAUEIBoAAABfiUAMPgAAoHwAAbg4A7CgMgxZQaDIAmSheBRZiAgZetkkuBcrAps9Gq4UCOAADEKC2jAGiUAwEBAGAIQkAAAAAEhIAABwsAABAKAUhIyAcA_B4AIRMAT0AAfEwAANjoAAKQkARBwIQoBVDQAQiYAnoAA+JgAAbHQAA8h4EsDg2BwBmGgAhEwBPQAB8TAAA2OgAAXCQMETCcDgUoLAEcLgCegBb4uACa+qRgAAYiQCERDgIgUoLABuKgCegAGgqAACgfAAAxEgCYeBMLAABCJgCegAD4mAABodAAAuEgCYeBMLA3BiACETAE9AAHxMAADQ6AABcJAjRMRQeB9qpXCi4vLgAAC4BcAE1cSiRwAIOCwCiRABiVgqgaC4BcNBeQAV+VAB_42eyhAAAxEgRom2sPBUQw8kTi0li8AvIAXALgAmvrEYAAGIkH4PFxcbHx4CG2oHysg0AYgI8IgDrRcACECIABahsAAAPA2EhqEfkYAIRMACRGgACSTAABBOgAAbCQBsHDEAAjhcAD3FgAV+VAANXsoQAAcxIvQA4vDQLABHIgigaC4AVYLABewuAAawJQiCAAaBYAA80HgsQQFYVABhLgAWIs7YeAJuFwATXiCMQTzB8AADAUQQbgTAQCLgAKhUHi96kESyoAP9G1R0IDiAXYWBkLwWIILWJgGrF31UIDVQsTSog88qAAavZQgAA5iQZn4ACshM80AFoB_B4ArITAAoIiAAX4ZAAB0AIU0amEAdkCcAp5cAbTMgogMALl4ATUKqBHIGMnOggLRIgNABcsjQsPQdeRAIWKgC+xcACPCoABM58CX_7sAxI6BsCo4RvBQExAjsVBdDnxcG0CJBUAAFI+AADcJBiGMLGEFRKwAwyoAOsXAAM0qAAGAhf+RgAGMLASwsYQW2jBOTnlwAABIQuAWhNb5I0qkY_chABqFgLAsFjCH7iYCthcAYILgLIULKgNIf2NrXoTmEIIIAEoNwkYQOmQJwGplQALQZ8tA8MqA0gOaQgPICchYGQACNAB8EQA2j4AFoH+joG8fAAAmMgAABzEjCBdAQyd2QuAS0jDEAySRa5QvAHoNRXoEcAAOYkAWS+G4SAHICBCYAg0bAAi4mAABcbAABuEgA_nw3CRhAKgHhKgCQRkGGFgeiFyoDjMQHQhAABuEgLAdRUOYkYQfcVAcyLgIpAkYYjxkIUlUHuULwAmoAAHMSC8vBzEjCBAShWE1dCULwLJMkKWgaSiFuKlYHkAiVLno1McjQwcoZAABmJGEBSA9soXgEtAtDJrWsqUyUgcSSUINtEoSpBIOIElBYGaUtAOs0GYkYQA+QJwCZlwBjsytoAs4uXnEAmo9UCOBVAYh+TKYUYLGEJhEiMBZpUAa8LgKoMpKoKF0Bc6EFQAEmTBSCF8YZAAMWKwHMEwAhEkVoEAkGTAAA_OgAA3CRZjsbHw8XAiCTIOANJAnAZ6VAGkCIomUB1ZUBlAS4hBZACCAF+aH1EgKIFji4AeMSKwAsiVAEk_obUEKIXSyV8GgGEEJEQApiYANmPAAMkmAAGydFZACwCwoKHRIH_kCcCpJcAKABg4AEdKF4SQBq1hGhwWslEA9QobAazNLNCwDEBWQ8AAANsIgAILGQAHWh4HQDIdAiZoToSD_CkAAAB_wyAGHwABbDYJoBHAeFBQKJB8paAFoEgEJFBgvAJo28oXgH_joauvQI8FLIAagWAHZNCeBwFEAlhEALmKgAIgRAAFuNgAF3CwOlqgoFEg_8jAn06iQXACBAAT5QvAAa39QoKWaSAgwWAMNNEgDQR0OgDmEQAdQAOqRAAH7MgAFKkQOggdKAQlQEwcAFjIBCyMARkAAFjwAAAABoSAcCglaCHUSAohOTolwB6FiuHINgygE40ZgRQmrHlICKAAIWDVQTXiQEED8hcANiKE4F0MwlQWkBr09CCz+ZeA08rAE0mmJRICoIT8Cm5UACUzerAXzKgtIH5UL67MABJJ0CNiSqAH_C4A2bAB9yYCSBvSoCSBrTY9gZU0LIPuIgCgCSauQWCK1RGhhNIN9S4KaBQKgJIapLgJMpJqGSMiSFkIekR8PwPWdoIgRIC6ABK5KAByABRBOZtGpCAogOqLgBOh6CIESBDTJjAUCULwAegZVwOm8lIF0ok2WRt11CAogAWjKggSxQg2gkYDKgAARcrBGC8TTn5UFpMIV8QgLJ5B9RcKCTcSAgklD6FysAFIHzWL73E6XOXVFSsDTXabMUbnkMKyeQgsmsey0vxcBJQsHjQAkNCPJYyAOBYhIjAkqVAVGKhCAGxyoADvSEAAFQbi4EEVTRsgcBpCRGBWYqACsCiMALyFX+GIANDnwAAVB03wiIsHAUQDTFwA7kWABhJUAA1iOhEUAB1iQAEZq3h4wgADIKgAnpUAAjSYAASJ1_ZGAAQQkADib+4mLsJAUQCNFQAb8qAAkxUAARo+IoADkADBNnREL4SDhCMAAAATQA+sbASzYLCERQAGMLBvhEOMSDgiMBpAuAEwlC8AiiGC5WBVSSNfioX+EYABpiwRgBtaA5EgAATFwAMwuABRJUAH+jZxKF7xCAAACMSCKAGbRgCT5kACLi5eAE1CYlR_eIQAAe3oDGw4SzuEgKIEl_hcAP+IgmLQBG8qNIANcmoQRQogZkWB0A6TZvDiNPocDIyBOBGEuAIqAAtACas3QI4ADFng4jABVNmURGED5kQCAC4AkCLAAzkqAD_xtI1CAAFCJAAVXgA80GaJLHE5AA9AXlwA3waNgAjAuXgBNQkJUeKlUYgAAmF4ADLK4RBedgA4giSoAI0TIz9gsAmkqAAYGhBdKqDVSYGwAJNKoCUI5EBURhjBcAZOFgAFoATVeaBHGN7mIpIGJFgABTSVLFcAyIUuAXO3MA2XAAgRQ2ADFi5eAE1d2iRxiVQB_QsYYADXjjRJYRxYAMIDEuABLihsAGUFy8AJq0NEjjEKoAzzBuAAhev9CAj+TBhH+FwA0UQLgBN0qCugNd8oX8E4YK6ewBaTIAKmsGRgAjkR_piADyacYQAv0XABNSKAAbQmAAfNlojMMFgMI5BuGWFwGejb_iEAFOC4ABq4lCIoCEAANAuViMhIWAwhlOwxXULh9CkDUegBaQuAnJNfDIwlCOgUASWYiwGEMJOkuAmJVjpuADE7JQvDCTkGqckaGBxetj6bNZpqJFB5kCcmxcAHza+I2HVYCqW3IyNzQuAzkbf8QgAp4XAANXFoQ9ByACfaUrRYrhUSybQNo0Ms5YvP5rQMwPG4SaSBWyheBVAauGRoYUTSAH8gTgyALl5HD4EZcAAAYiABwEQAAsIgAATGQAAAR9e5xKx8VBz5iDTOQBpho7HoAUcLgAmuxkYGIAGNWIENi4eBDwAqLZIddKHg7whBxIzFwAAM4IiORcAA1cWhfSJjCAAduTDFGD4GRanocSqLQCaARXeEiMkiILl4Ab4wXzUjqBHDaXftlwdSHgbAE9N25Mg0cRlVLgeOy01HsJcAAYSiAdC5ebuZiiE1acjRzjRkAAAz0LtyY+48Fk8iRHDiVfzlwUUD9y8QQ5mXARQmp50COcaMgAAAEZAHSYH0YPgxJAjhpCDlC8_0zAFS2lUEDlC8ekkigNRkoEcrEfAAAGAX_g6AqMHwQwgRw0hCSheABUNpVBupQv9MxEUigNamoQlABmx0AIonuMuPqMHwJ4iQw0hCSheABUtoDdShf_hiCKA1R4jQw6mUAOCRHJsAozUeHD8a4wfAviBHDSC1KF4AJgcLltKoMPKF5+BKIoDVMKBHC6QQAAEhMCFFu2OneDwFkQI4aQWgB4BwuHEqgjUoXgRQGsW0L5BMaSqAAyOlNiSgCKmBPC8IH2Eh4DPnkMNoTsoXn4UYBSEEkgUUoXhBrKBCCvNAjiUAqH7jYO1JhajB8JDHz8NIZsoXgD3LhAnKySQPgXKww1m8hBQEhQw2mkogewwbk2AHqZzQeA8J5DDiE7KF4AKQAPCULz+SlWUCEHeKETwSOIEQDgXABYFiAQn4dKyMhCfk04lVeZQvAClFCcJJXRYZQvCiAJWtoGykFniNDEpxAiCJC4HQEjI7+_Afy+upMJcSCSgQXLj+g0H2JEYdBaA5QgXKwmlWgi7jR2QRAm0snmsioJFYA8+YIWHM0Re5KgLJ_x2GwFwAaUWACoBcAA1cahCBIIAK6kyNCI+GGgh5GilC8donSx7KXbDBcLJJnotD8XKyy1WokE8Zg3IIebSca6RT5jiMlz+bAIU0St_EgfwQJwAyli8ACIVQ28PP1KF4ADVNCFDDqbQD1CxcnY0BDiGIB_EQA2D4AFoH+DoG4fAAAmMgAAXBwAFbP8Cb3DEAA6wuXgIyRoYxAKofUoXhvIsZ0UmvhUYkgxAAADzXAE0SGIOcEwCgyheBREvGS8CyVQ5xcrAy0UGqiUCOAxAAlAAMkvBEYQvyRAJTKF4ArQyXgFUCAXKwLtFBqEBGhmBmo2gAyEC4MloAPQgCQslxsAEQiAIcfAAtA_4dBED4AACRkAAABZmgG4n_R89lSBCTEAmkqALlGQBVFalQAAMEIKgJAAALi8HHxNFoDCEKFIMJQvAR0jDECaVRdJQvAooNfNIwlOIAAyA_EIA6LX4hP5SFQHfXNQVEvpYvAeiPQI4xC6LSqRRaBRSatVRI4lMIAAaAwUIA6LacgP1kMWcGpw1S2FFHeULwCKMRAwkekUNZYvA8ebE1IolMIAEWWgAGWAoDgcMxADWPgAWgf0OgbR8AACgyAABULBRhNkBaDFShXAJKULwCFJYzP8JwVQhBcrAAa6vQg4z2qlEzINAAX5qKJlLKxHTSBzAuABiAwNQrj4i5WARQazHQgABQDQBNUIAPLAJoJRCJmRUAAxEqAOwGQfoLiqN3KgCKEYkIOJpA5MuYwBAix0DyPS4LBtwFEdxUAAYT_qkG4KgA+mbAPQB5B8AIbhi8ESJk4DCAIwiADmFwACyJgABPGx_0iABsFQBRELtyaARUABRTeWLwGYI0MYgLSqRTClC8Cig1eMjQyQ_sQgJUGQGjZaA9DoKZLHQPbOTghclAAAADEAYfAAGuMgACyAOlDAomXExBBKYtVwootAnIgDBeBMR6sUoXgH_DYal8RoZJOJBqIXRgLmMLRdiIF6cAUk4AHhUAARQAZFQAAUD4AAIRcAEIWOgegc1ABRS3FQFBAAA4VAB982AejkB5h8AE9CBXCXak1ZCrBJatgtos3y4CggoUK4BQZaAE1I6iSyQnEJq1w4bgDeQl2Ij1MwVSqBd4uAYKhFEAaHti4JSE_DagkhLo9AWpYzBkbhwEFLoS8EWZS4LaBBYcfAAADwj4AAIJ0AACgWA2LmwHAVApyZ5pIngPQohnC4rs5AMIZAxhcB0NpNWnKRPCIAAAAOED9KjEkoABTJUAdrNgwhkskfSoA6mEEIhE8IgAAjADZUA9mkk4CEAAAsmAAMlQ"
noncomputable def WL5_5 : ℕ := zfNat64 33248 "CiLgCkxkAVSUJUDyCYP+GzF0IAAGIkFoASMgxAqZAnATqXAAMzBmFNBYZYvCshNRkoEcABWh0ABIyAHCQAAAQTAAFioAAP5GwAGl4CiArsqAEAJGQYhHEiAi4XAE2i4AI+lQVkBrmtCA2gAQEC4MksPFgIASMgGwoAqDwALCYA+4xAACYmAAAwdAAD0HgAFGQDIUAmx4BfBcBrFGKoAU+LgqADVxqEAAYMiAN8TAEhoBgKATA8Apg+AB6ACjD4AB1y8AAAPDgAsyADkwDIUAAAAHnioDrAsABJNgfoQABdiIACRkA2FAXYqAd+VAHmDYAukQSoC4gfBCAAHkPFHRgCk6AJGQBISAbCgKIfAAAAHEAYfB_s2AEadAAAAEjIAWJANhQJ7IgBIlC8AZWcOwpoimrOUZSFZrNJGpskKGBBAAtAYh0ASMgRMkA2FA5s+AAAAOIAw+D_5sAbU6AA_wZAASMgGwoDukQEIyoABYeOwDSXjKgrNZpI8hCAALsRBbMkoASMgGwoCKAdwuAJ5FjMA_shNvKF4accgojVgCNDAABiJAAH2gCRkA2FAAAkLgABfh8CJSoAP7GziUIAAGIkABIyAbCgABPEwAXU2CegL0mAAA6dAAAuEgvvQAmNAMhQAAMS4AC8LBDUoVgNIuXgBNQpJUcAAAAkNANhQIUYgBdFwAADMCpE5UAH_DZxaEAAABOJgCY0AyFAYQYOmUy7lwAAAGUh6Ll4CBJqndElgAAAExoBkKAtS8A_MqABqAXSPpUB+R2BGiEAAFGWgBIaAYCgCclAAFrEoAAExMAABQ2AAAAJjQDIUBVAig5KF4LHWL9hFwnSwCa3JCFoATUKSVHAAABEFQBMaAZCgA+3B_9GACSyUAAApD1psBpeAAAHtYsAJDQDYUBhATAXAEiQYAG2lQbsegGs2UIAAAAOZAMhQGEBMBcASJBgAbaVHU3o9B_42myhAACiKgdACJkAyFAYQpp3y4Bj6xfAJyWX2Fy8ehY3DuE1HSgRwABgiwBwzoAkZAMBQIUYgFQHwASQAUofAAAOLgAARCQDgAsyAZCgP8xAcyLgK2nwtApolkoXn0KCDWCKEAATw+AAmNAqA4ACBAMhQIAYgAAABiGtKgAxWbAADMiZGAIAPGgAIsFaZCkMIxF2plMl5QvAHpoyheBTR64coXj0KCDUT6BHApoBpFgAJjQAwhphSICULwOmHwtApomsoXgUEGoGUCOf6aimgA8WAAkNDcDQGEDlBcAf0LgKaO_KgKCCF0It07AB1CIGxsXAA40AyFB_5iCxSkLsoXgVfPhaBTRLpQvOoUEGoA0COAAGQqAB4ZAMhQH+YgODFwE5T6WgU0SyULwKCDWCKEBQAKSnA6OloOAETIBkKBWitXAiy7LgCSABagu5AfCGnYJr4xGAAGCLAASMhnmIKqBFycXAFok4AmnJi4ABq41CAAFELAASMgHTVYCL1YuAiszE0AmmuC4ABqz9CJUDw3CoAAAOZD6CwUEVgDOlQATQAOSVHUAE2oQWaioQGiz4ACRkCgEgAFFOiVAeiagAARlQADUFIIw1AcSYLwBACI0ByJAq1Qrg3lAji0KyJBipIBNDklC8ek1AarvQI4FUBiI8AAcyA5EgKoUxRuYFwBIZIngE0L2ULzqADVOqBHAqgQoKgdGRuNACZkCIKgGQoAPtwf_RgAkslAAAKQ9abAaXgAARCQD2sWOjoBtOgCRkA2FBOZCAAACQnEAHIBHNiXIQDUAC4kABIyAbCgTSRAF1KF4AOQFJtG8lIT2u02WRsNBChgdQBeHQAEjIBsKBpBMjAaaULwpOsk4chUTSUWYFSsLCXRwJ0uYkED7WSiFyNmYAEjIBsKA2ZEBuwuVgA2jx2AbTOpUFBrtNLloQGUAOJcAIzWgBIyC3MgXoTIwDvlC8CaMFHEYVkDJFysLLPQamUQoYH2mhF8WAAkZHsBwHuJkYE2yoAayOIw_0tBYkqCygYTQgynkC6IsDcySxYDG0sOFwM2AEhY9A4HAAAmLgALwkACPSoHkEQDVjKEAAAAJRgCQv+BEAsQiAMCVAH8iIP_KQGpKgroBlUIAACUAJCx6MAOBnBEAb0qAA1DiMrpRA95UAAEFCAACzAAsWDEKAcDAF0OACqVAApAAJpUAAD1CPmDQAAALFgxCgGAwVMGgAqlQAcIWAAJ5UAAD9COsDQAAABLgBBUALFgtCgFgwAAMS4AAADoXLwDoho2mqDEqOBkAAAEFQAsWC0KAWDAAAA9AGNlwTYuXhMRKTUMyVHAyAAADzoAWLBaFALBgX2jAAAAAHQuXhYQmpRkqOBkAAANFQBMWC0KAUDAAPFKgDip8AbSJJUARQNEhAAAWkdGAFhbtSYAJZEAIEuADYFwAFwLl5wIaAmpDEqOABUQAKCzBkQAMRYAAABhzkSGLgMgTXTSMABCdSAAcXAExY8h4AAVuVAA9BwBUaRh5UA7daAYCEAABaWgBYW7UmAMoRAIRLgDVBEH70yeDhyxecCGqyE1CKgRwAKiEoPACwsOYkAAAxLgALwsFPCIBpFy8AJr0VGPFmQAphWACLVAARoBALA0HAEoNgAAAP_KwAw+AAFCdASJiAAAJiwNCQANB4BxpUAY0NgATrmMgOVSaLgKIFaQgAALaWBpQuHAY9UgA8qEeFgAAJlQAA8KAAEpUBBAP5sIGDgAAAwDgBGHABcLgAUgAlcqAOh_g2Z+hEOhgAAAREwBIaAwDgAAAAAAUfAAAqXgAAAMA4KnDQAAAB8koAYfAAAdOiHQwAAAYBwVOGgFUlQBmY2A_8vC_yoAAGCEQ6GAAC0jAKILgAOxcAAAInKguAdCfDL_xsvlCIdDAAAAcKgeRIAnoGAuAGIrAARELgIITWzCMQ6GAAL8AoouAA7FwAAAicqC3R0J+Mv_Gy+UJOQcAAABEqBREgAaJ4_AYlwAAAHQuXgQQmqDEqOnQOAAL8JpmAcHAAAmLgAACORcAdBpGQ1XyhGehgAE0zACHgFwcABmCYALwbAAbwyGkXLwAmvy0bPwUAAABYqAuDgeobARTVFwAABIQuAohNb6I2fgoAAAVhUBcHAAFS1lQAAF8WgM5UAfQ3BsEOhgAAjACxUBgHB142ABSJLYgXAAAEhi4CiE1vkjEOhgAABWFQFwcAAVLWVAAAXxaAzlQB9DaGwQ6GAACOzPQA3dAGyoDAOAAABKAAAfyghCpsGJaIdDAAAAbKgMA4AByZUALELGYH_E4geVAFEDcIRDoYAAIy2jC4eNACJ0AjqgEQYP3twAAABxAGHwAAXzoh0MAAACYMGvjoB0ZUAHIPHYBpKnlQFZpIyBCQcDAABaAIgwT0B8m0si4APOMHwAKKULwONJBqxpGhmWBgAAAHkwBIaAAAAAAAAAAAAWAEhoBUGBUDEAAAAADD4BEg8AKl4AAAACVBTSYAkNAIAwAABEQADvHwACul4AAAeHAK50AmDB6hiBoykAAAEci4AEo1jahIOBgAAATBgnITFDpQvALCUURyBRtIm1I5hUrCa12msdMG9BQcDAAAASGgFQYAABBMAAYOgKo7AAXRGAAAAC60jAiCUAgDBy5WAAAAuhOkqA+yU_wbV3QiHQwAAAJgwSgVq4EWjBkAfmRpYMaZg5sXAcQmo7UCOQ6GAAABMGASStXCi1DLgD6AB1MEXLwAmoTEqOg4GAAAc1AYZUBWFABRSjlQAtVGzAABwqAsh+U2CHQwAABOSYCsKCZa8AAQHLgCKBIioCSE1CHQwAAALBwAJUK4IBRoYtACicQOCbu5KZunJpKF4VU0g9WIjQwAB6ACpisBYouACibgNsUKQUdKgqppP+H2VUIh0MAAAJMIQA1CuC50aGLQAogTQvKcmkoXnemaqmkHq1EaHn4KAAADGhAMDKwKRc5UALUUK4bf+KQItKgqptBnaEQ6GAAAZMUNgUQikEhZQvK7txKFpRDaWaT5NOemULyq1E02EeqARoefgoAAsT+xgaMlAxASitXCi9ELgBb65WACnhcAA1cWhEOhgAAAZCgqoJLRpKFwB+5WCigD8oXgSQGtCUIh0MB0A0gOiwZyulUDbokf75cAKRGqFcWgUU4pYv1YTAE1C2gRwpICn1i+EOjVYmIBRqlcKL2guAxAXFUKoGJi4AJr6xGAADgXAC1jF49WCi_BLgBbVQDa6NUIuMIBNbKIwZAAoRsB4CAfCYEY+AMycAASkAAAKpR82A8tEOhgAAdSTi8ikVQeAjQxaAFEB75xCE0lC8B6WQau7QI8KBIAAIx_5OKtKRfFamFFZiWLwMBFRVAAq5YvACaoNQI+gBaGjkCqA8AOSWP9OgeEnAFKJgAogAZkmAAOedEMhgAS6RA2MgANeAJDQGgB9uBzGgmAAhykAAJiYAADB0AAEaA6iYPYSAqhJnCjLALgBaAExM8XAF0motlIh0MAAAPwgXA_qhXCSKdCFoDHSooi0JINjKF+qiYpJpB6gJGhgFkORKQAbqYAkNAFBIBgSBQzMAAAAAAASz4DS8A9A_wDADRgDSSAp8+S0pBFB_lQAQpSAAHxUAACc+IdDf+MqSAA8ILAoFQrhJMXFwAUxQrgBDMqAAa39QiHQxdpIBsBoGxk_jYGNmQBhlAARoBAGADB6MV8qAFoBNAD_hMFlzYOSEQCGAALUHiwsAHIQFo6ALyQgAAA_4PHEA0bANQBznxDoYAAAFdCjbkQAoSheAMlOHYfHTnDsmslIVms0kajCQoZcAYAALQDcdAARoBO5CAAADDF0hOIBOQCWbFiQiAQwAAADsIPQVWRAR7KgAAR47CsqlaTWJUFZrtNLooSDgYAAAV6ExMvAAeWLgB7Bw_AGm0sWVAKS6TTLaEQ6GAAA1NGDhJMA28oXgEETR2W0s2UlIFku_aTg7G2f0JBwMAAWIAHkg3EoDjECcBMpQvAByBRUI0ZyUgYS6a5OlkuNmdBIVDAARQCUVQBIaAvMgJoA+h4ANUTAAToiAAH8VAAABsJQKzQI4f6OlXlC8AHIU1FDVnJSBZLpNJcbMx1IUOFAkAABYDMgBF5EAL0oXgBojx2EEY_5aN5KQItdpuUDZqCFDQcDAAEbG1oGwJidBoCSAHDF4A4gcWSKBQSoBaE1T0pCAhYAAKQEg44TALjKF4AMTiB1lLpZJSFZtr7l6WRtc9CEBCwAFGc4JWmEgRGQJwA7lC8AkvAISyl0FAFysNtdAavWRoYVQAeg2CHCY18aBEyVHAAu00AskUBfFx+AyFoTWLCln4KAAAnASJgDEgTgL7KF4XQijEspZLI1EaOPAqVhZrNtLp6TBvQc_BQABRgVEmGwGg5+lAAAFZ_sjAcIqAW4Emo21Yh0MAADqwkBNyBOAxYuVhdBT5YzDSWSyRS3FSsLNZOJda0bM6CnIOAAKMAAjRD+gSBEpAnADyULwAQllAEvBn8qCshyw2oIcTKAnUSBsBgTExJaVUgBoTFALA0DgY0TAAAAAAo+AABUvAACgFgG4OCgFBCAaAAAAX4lADD4AAKB8AAG4OA"
noncomputable def WL5_6 : ℕ := zfNat64 8314 "PAAAAAAAAAAAAAAAAAAAAAAAAAJiQDAQCgIAAGJcAJAIhQAGkLl4NQAgmo2EqOAAAAAAAAAAAAAAAAG4KAAwLAAcgoAAGAwAADA4AAAAAAAAAAAAAAAAAAAAAAAAAAAAQA4AAE8JAAAaGgAAGBwAAACEuAGiQAAAAAAAAAAAAOQoAABBMABeFgmsTAAAA_OgAA3AwFSGwLSIgCRlQAfweAAnZUFZAJ0hAABuBgAZYQA_BEAM8qAC1DwfQBtlQVkAnSEAAG4GBMoSC4RMAj0qAKEkQNQFBlQVkAnSEAAG4GDEGsYRyQkAtAdgRAH0ioAG1EQAAJjIAANwMGJiSksbDhcfGgBMaAAAEBYACUFAAAYGAAAIHAAAAEhoAEIKAAgLAATAoAADAwAABg4AAAAXAeADcVAA5BoAA0FQAAVz4AAEQMAC0qCYOAAAIFQAGIOAAAAA8tAAAmBgAFFQBIaAAADioAAsLAAB+JyAA8tAAAACioIRIYgAAmLgALw0ACPSoYhxAasZQhVhkABbEidBCDgPxlQDPyoA1uTAaQdaVAeQEXIQAAbgYpSWPKQAIjADzIAcLABRIABIKAAMLAAIAoAABAwAAAAAASMgB4sADEgAFgoALRcAAkCgASuVAB_w2Z+hAAAAEjIAkLBwOwAlDgA1lwAJYOAAoRcvACak6So4UEABkZACRkA4HAAAmLgALwkACPSoHkEQDVjKEAAPQAJGQDgcClCIAtJUAdwIg_cpAY0qCugFFQgNAFAASgAYyAGDQBQMCyiIAwpUACENeKQGtKgroBlUIAAegyAEjIA8GDKo0AOcuABDhwAI0Ll4ATUIyVHAABiFAASMgDgYDHCwAui4AFIAKJKgA_sbOJQgAAYhQAHSoBsGAABEXAAVBYAEclQB0P9GzE0IAAFoUABIyAIFQTQkAABEqAAqCwAAlKgIICHNgAAIQsABMyAEFQFwcAAA4qAAvCwAAcKgAD6bAOAIgAACZkAYFAAAAAH0IgBh8AABY6AAA0JAALMgBBUB+HAAAmLgAAAtFyJyoMkxD_hsxdCAACELAATMgCpUB+HAV5WAABCpQvAA8JYvAohFmpr0COABBoaCGjABZkAVKgPw4AEaNQMS4AAADwXLwyDEJqghKjgAQcGgLgY0PABRkGICCFgBdFwAcYWABRZUFQD_xs4tCAAMKRAASMgxAogKBoCqVAAlh4AAgFQAAKT4AAGIkABIyDEM6EwA5y4Ac0NGwARoXLwAmoRkqOAAhIWLgASMgAmCIAex8AC0D_B0D4PgAAJGQAALhIACRkGIAEoi4ApMZAFUlCVA8gmD_hsxdCAABiJBaAEjIMQKmQJwE6lwADMwZhTQWGWLwrITUZKBHAAVodAASMgBwk"
noncomputable def WL5s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL5_1) (dpk j 2 WL5_2)
noncomputable def WL5s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL5_0) (WL5s1_3 j)
noncomputable def WL5s3_5 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL5_3) (dpk j 4 WL5_4)
noncomputable def WL5s5_7 (j : ℕ) : ℕ := dsel j 6 (dpk j 5 WL5_5) (dpk j 6 WL5_6)
noncomputable def WL5s3_7 (j : ℕ) : ℕ := dsel j 5 (WL5s3_5 j) (WL5s5_7 j)
noncomputable def WL5s0_7 (j : ℕ) : ℕ := dsel j 3 (WL5s0_3 j) (WL5s3_7 j)
noncomputable def WL5 (j : ℕ) : ℕ := (WL5s0_7 j)
noncomputable def WD5 : ℕ → ℕ := rdw WL5
noncomputable def ready5_cuts0 : List (ℕ × St × ℕ) := []

theorem ready5_cuts0_ok : CutsOk ready5_cuts0 := cutsOk_nil

noncomputable def ready5_0_state : St := ⟨26112, 89920, 28545, 39936, 29184, 45301, 53248, 89920, 29666, 44151, 52016, 106240, 28545, 73728, 26112, 82304, 54657, 129856, 83841, 175157, 137089, 265077, 166755, 309228, 218771, 387007, 247316, 415552, 325642, 441664, 57729, 85237, 110977, 175157, 140643, 219308, 192659, 297087, 221204, 325632, 299530, 351744, 82432, 135221, 112098, 179372, 164114, 268542, 192659, 297087, 259594, 323199, 82914, 134071, 134930, 239358, 163475, 267903, 214293, 294015, 81682, 150391, 110227, 214655, 136339, 240767, 80561, 179968, 106673, 211101, 54657, 156032, 0⟩

theorem ready5_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD5 ready5_cuts0 103 2014) ready5_0_state = 42141 := by decide +kernel
#print axioms ready5_0_cursor

theorem ready5_0_covered : Covered (toCl ready5_0_state) :=
  ready_cover_cursor WD5 ready5_cuts0 ready5_cuts0_ok 103 2014 42141 ready5_0_state ready5_0_cursor (by decide)
#print axioms ready5_0_covered

noncomputable def ready5_cuts1 : List (ℕ × St × ℕ) := (2014, ready5_0_state, 42141) :: ready5_cuts0

theorem ready5_cuts1_ok : CutsOk ready5_cuts1 := cutsOk_cons ready5_0_covered ready5_cuts0_ok
#print axioms ready5_cuts1_ok

noncomputable def ready5_1_state : St := ⟨26112, 89920, 28545, 39936, 29184, 45301, 53248, 138496, 29666, 44151, 52016, 106240, 28545, 73728, 26112, 82304, 54657, 129856, 83841, 175157, 137089, 313653, 166755, 357804, 218771, 428607, 247316, 457152, 273428, 483264, 57729, 85237, 110977, 223733, 140643, 267884, 192659, 374124, 221204, 431040, 247316, 457152, 82432, 183797, 112098, 227948, 164114, 334188, 192659, 402495, 218771, 428607, 82914, 182647, 134930, 288887, 163475, 362615, 189587, 399423, 81682, 150391, 110227, 224119, 136339, 306423, 80561, 179968, 106673, 262272, 54657, 156032, 0⟩

theorem ready5_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD5 ready5_cuts1 106 177) ready5_1_state = 92934 := by decide +kernel
#print axioms ready5_1_cursor

theorem ready5_1_covered : Covered (toCl ready5_1_state) :=
  ready_cover_cursor WD5 ready5_cuts1 ready5_cuts1_ok 106 177 92934 ready5_1_state ready5_1_cursor (by decide)
#print axioms ready5_1_covered

noncomputable def ready5_cuts2 : List (ℕ × St × ℕ) := (177, ready5_1_state, 92934) :: ready5_cuts1

theorem ready5_cuts2_ok : CutsOk ready5_cuts2 := cutsOk_cons ready5_1_covered ready5_cuts1_ok
#print axioms ready5_cuts2_ok

noncomputable def ready5_2_state : St := ⟨26112, 138496, 28545, 39936, 29184, 45301, 53248, 138496, 29666, 44151, 52016, 145508, 28545, 106240, 82304, 138496, 54657, 178432, 83841, 223733, 137089, 290733, 166755, 320399, 218771, 372415, 247316, 400960, 329620, 483264, 57729, 85237, 110977, 223733, 140643, 267884, 192659, 346303, 221204, 374848, 303508, 457152, 82432, 183797, 112098, 227948, 164114, 317758, 192659, 346303, 274963, 428607, 82914, 182647, 134930, 288574, 163475, 317119, 245779, 399423, 81682, 189659, 110227, 263871, 192531, 346175, 80561, 234205, 162865, 316509, 110849, 244736, 0⟩

theorem ready5_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD5 ready5_cuts2 109 113103) ready5_2_state = 149782 := by decide +kernel
#print axioms ready5_2_cursor

theorem ready5_2_covered : Covered (toCl ready5_2_state) :=
  ready_cover_cursor WD5 ready5_cuts2 ready5_cuts2_ok 109 113103 149782 ready5_2_state ready5_2_cursor (by decide)
#print axioms ready5_2_covered

noncomputable def ready5_cuts3 : List (ℕ × St × ℕ) := (113103, ready5_2_state, 149782) :: ready5_cuts2

theorem ready5_cuts3_ok : CutsOk ready5_cuts3 := cutsOk_cons ready5_2_covered ready5_cuts2_ok
#print axioms ready5_cuts3_ok

noncomputable def ready5_3_state : St := ⟨26112, 138496, 28545, 39936, 29184, 45301, 53248, 220224, 29666, 44151, 52016, 145508, 28545, 171456, 26112, 235948, 54657, 178432, 83841, 223733, 137089, 346925, 166755, 376591, 218771, 428607, 247316, 457152, 273428, 483264, 57729, 85237, 110977, 305461, 140643, 349612, 192659, 402495, 221204, 431040, 247316, 457152, 82432, 265525, 112098, 309676, 164114, 373950, 192659, 402495, 218771, 428607, 82914, 264375, 134930, 344766, 163475, 373311, 189587, 399423, 81682, 189659, 110227, 320063, 136339, 346175, 80561, 290397, 106673, 316509, 54657, 264493, 0⟩

theorem ready5_3_cursor : U (walkCut TOP BK TOPD BKD PT REG WD5 ready5_cuts3 113 121) ready5_3_state = 163544 := by decide +kernel
#print axioms ready5_3_cursor

theorem ready5_3_covered : Covered (toCl ready5_3_state) :=
  ready_cover_cursor WD5 ready5_cuts3 ready5_cuts3_ok 113 121 163544 ready5_3_state ready5_3_cursor (by decide)
#print axioms ready5_3_covered

noncomputable def ready5_cuts4 : List (ℕ × St × ℕ) := (121, ready5_3_state, 163544) :: ready5_cuts3

theorem ready5_cuts4_ok : CutsOk ready5_cuts4 := cutsOk_cons ready5_3_covered ready5_cuts3_ok
#print axioms ready5_cuts4_ok

noncomputable def ready5_4_state : St := ⟨26112, 285696, 28545, 39936, 29184, 45301, 53248, 220224, 29666, 44151, 52016, 239000, 28545, 171456, 26112, 285696, 54657, 325632, 83841, 370933, 137089, 464857, 166755, 494523, 218771, 546539, 247316, 679263, 273428, 705375, 57729, 85237, 110977, 305461, 140643, 349612, 192659, 520427, 221204, 653151, 247316, 679263, 82432, 265525, 112098, 309676, 164114, 491882, 192659, 624606, 218771, 650718, 82914, 264375, 134930, 462698, 163475, 595422, 189587, 621534, 81682, 283151, 110227, 454607, 136339, 568286, 80561, 410456, 106673, 538620, 54657, 457152, 0⟩

theorem ready5_4_cursor : U (walkCut TOP BK TOPD BKD PT REG WD5 ready5_cuts4 118 81) ready5_4_state = 201502 := by decide +kernel
#print axioms ready5_4_cursor

theorem ready5_4_covered : Covered (toCl ready5_4_state) :=
  ready_cover_cursor WD5 ready5_cuts4 ready5_cuts4_ok 118 81 201502 ready5_4_state ready5_4_cursor (by decide)
#print axioms ready5_4_covered

noncomputable def ready5_cuts5 : List (ℕ × St × ℕ) := (81, ready5_4_state, 201502) :: ready5_cuts4

theorem ready5_cuts5_ok : CutsOk ready5_cuts5 := cutsOk_cons ready5_4_covered ready5_cuts4_ok
#print axioms ready5_cuts5_ok

theorem ready5_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD5 ready5_cuts5 128 1) (ofCl (RC 0 0 0 1 0 1 0 0) 0) = 205211 := by decide +kernel
#print axioms ready5_parent_cursor

theorem rc5 : Covered (RC 0 0 0 1 0 1 0 0) :=
  rcOfC WD5 ready5_cuts5 ready5_cuts5_ok 205211 ready5_parent_cursor (by decide)
#print axioms rc5
noncomputable def WL6_0 : ℕ := zfNat64 33248 "CAEiGAEhoiZevgpSyULwGrFScJtdJrVipOUk010WgXKyUlEog1aWgRwAAAexHHpsOBaBeZUBU4+AADCBoyoB6IHBpsAbAaABj023YvH_yoVJQvAK+SKwBYBw_KSaQOQXKwKJROI1JkjQwN0NAAQgAuXBgeLpikqQiULwGFFScJtdGFFScpJp_KvC5i5WBRKINWYoEckv1VYAB7BeCCJQvAkoBJTEqUaQJ8XKwqoAloYkbUEKJxNISlHgZGxVAEwXyUrTKF4CkipOE2uikipOUk010UEXKyY5UUSiDV4qBHS0fAAzcSBpQqtAw8qAFIAKQiI3Aw8qAogI4QhyADkRYHUeA+74J5WB2ZMAB_tKCSFZBXZMAADE2AADgJAD7vgnlYFdkwBJAAKz_tKHZkwAAMTYAAOAkBOR0AOyheAoZQngChlCeSUygmQuVlEFpBBraNCAADcJAGoCxKF4BNDiLQE0a1mygWQuViUqlE9i5jBqaJGhgABuEgpBdF8CEBAn8eAAD_x0ACfx4AAEJcAAAYCAXRfAhAQJ_HgP_HQAAAn8eAABCXAAAGAgV8yEkbAz0qAooBRT_qFaQe2VBSf8JwIRQjahcASUA+hErhk9o6BxZUARQACKXU6JwVOGVANQySFvykEah4ABXDIeJkDoyoDQSMAEUDSEfSoKqOschjCEAlABixGRUcNyUrfKF4AQkCOEUVsfEEpJpCUhSaybU5nkMwCFDJtoQlAMpAkI2AEm4ATJFUHQf4LgCKf+RgQqwRSkmkGHFysCiTQa4lQhAgAADcWkIwjqqQHZKVXlC8A_yJDCLVQzyJDKSaaqHaLlYFEmjEauWRof_A5AwkAJ1NWAmDcFpFysCegE9AygAIuVgUQgIbaaQoeSF462VwTMBOSRWTYzDxIAJQgCRkAKFgBAkAAAAAAAAAAAIcAWlwAAAAAAAAAAAiY8VomDFhMAKeTgBTycABUioBqAV8+AADcJAaBvLmMlItAlwoTwrpLhQn0EamGujOyhfuRGCiUQaq_QI4AAbhIG1VoJulQBSlCeSQClKE8inGyhKEqAogI7QgAA3CQZx4OEgiIiUoXiUrRKF4C+jx2E2wwBUgDCSQAeiVAzXVKcaAaAABrteJSLQCRkis_8nAy04flJNIDOLlYU2onESZo7oLCCYg9cWgJKADITJBWy8vBywuAH2SKwBeJw_KSaQPkXKwpocZryNCIIWQAHQDUZMKCFyuSlSpQvAdgVJwBYR47BiXQlID0kgCcN41VMhQ4KPVvLGsw0kVQQJwrNQr1kFAFysAAhUnAuulDky0mygKTaFksmn3hsnk8h1uOiicQGzjB8qRkHgAxlVhC4DdhUE1rrED0pNlDyxcBRDiMpQraFRJAP_kwAkIDwmmmjCsBMyIB9BMAPoJgAJmRAAGVNgABKA8E_XgzkXAFdJFZTQK6SKwk2kGQlC8KbUQajdQI6Xkp4xozAJKANMS4pUpggVLYMPKgBSACmii0GkKllQEkBrKVCLJFOIAADQSMw29svALQI4kisJueV4jiSKykmmujGi5WBJKINVEoEc+kE4gAHgiqFcsggAuVhNU9EycKzSRLSSTZSyNVwlCuki0skhVLY1mK2kJ+s5Ut1E62mkhVRxGAAEaRI2vitA6UoXgSUAkpSX5NWcJSBZCupg3d8hQ77QTMPHM0hIQPmRsBAtQkXBIrHstVwfSVAH7JFYAfskVh_hqB9JUVSmgKwQsCSTyAADj1gaecAFmgooOjY9_pWCd5MAOQAcgACsmAABIff2cg4gALGOIxgLVcBeFysGXGwlApIlpoZQaoFKFYKFSn7wyKoDVKCE_OJROJppJdC+SKwTmZ0djwEPHQaLzAMBbMagGIBhCoAMIVAAGgqAADYhAABuCgAAowMdCE6Xw0IuAYCgIMANgACogEX96UC2KgBKTUqgABuCgNQ4GNACQ0DGHAXUsXgLlJFYV0mrlJFYW2ujvi5WS2ulEGq2UCOAAAJfZh9dcA6pgGAh6BZR4D_5UAf_KgAb+PAARDLgAADAQCkDAIDKgKrFQBDIuA2g90qAP+LQoJCAACkDAKSXhSBnqKEsGoLi4PoLQQ2NUqiOSW10_qpD+LlZLaSUSyNVcIUMAAKQMRqGCQSIAkNARjQRAKgABID8LKAGmCykBYKgnMhQM1acrAAAC7iIACLBWHDRGD4NSKFysspVXWcOwsNRFoGkogVaxkS2cyFAzUiqZTBaAAkEgEgkQEGWCEKPSNBlEqAHoHfZgAwgb8qAa2KIkCNQONZAFoBxCIBALBCFADGD4NV0FysNIPQqmzABhqogguAaiFAjVqysFEAUGXACCQSIbgowI0GXSoAegABpA4RUE5jyRIGagOVgu0kCMxMDc3Ojyw8FLyoNIOQAcv2FhKaQJoXKwLoZ1I0_CNqCAAEkOAgkaCl5UGkA8eOwADx47OYRCU0hS8qAuhpHSIQAGLCYZ_MgJjB8KblQaQcgA5BLuZqDs5UBdDT9Q2_6hAAE8Thn8yWuMHwo5g3lJZQcl_j4pI5BKaQlJRS7UbLAY2Zn6QoZNQAVI0TYCAG2IpEYPg1DoXKySaQcgIvShKmjsAyU0hKYzRa6KNSso1MUhQwAIOBRU1IASGiQRg+f+NiKFysNIOQAcglNIESLlYMFGLoaRr81CAAAOgBJGAHoQAw2AAAMloAAAAAAQlwAABgIBAKEOElABipfrIuCirheIIISSD0BjSQyJEoX1gGgSLSCURq7FAhgABSCgAEjRxiE_CimDeUhJmrODkrJSRyVmqlJlJSaTUUFsmshpg3MYhQxKAAE1ljdniE_D9mDeUllAfmjsLJSQfmjsqpVCUlJpJRsp+zBuX5ChlMbgA_0TAcBIvcchPwtZg3lIaQchZKSOSqnAWK4SkpNJKJpLWYNyQIUMMoAJSBGaGj7IT8mLFShWWUKYdNwslJKYdNyqlUGMlCspNJ_kpWWYjBQIYwxs5l0AYgETEjoFjeIT8GrYyheGkJ4cPwshAA4fhVroOhKF4SSCHEahLQI4F0AWgCCGnkMmJ5CpWSbKJZNHYFJVWaOwqlUEmFSsbRESSSWWYuPQIZRTSAM0YRgALshsTyGXQNpSGkW8dNwBbx03CqAkwuVz0JoaQRiFD_whEE02EF+jwlJSD5+TF7BUrLL1hOmoWSkzUKtRMCoxcShWnU+JJJKNlmI1EJ+VaKaTKCjxxGDpSMzc7YxoL53gCSMA5MVAf8WgAMBsAAFx4AAEJcAAAYCACPjH8IT8GspDSDkIpuFKHILUpKlsJT_R2opJKJpGpHkaGAARoKAQRhxtikqDSBLNHYAEs0dg9AqeVCELoaTJKEAARoKCkAgmQgmfjYkxcr8wPF0J2aOwAcoWW_8WgIkXKwnIXRrtVCz4PAABQdNHz8mMJCpWWUPMdNz_SEUk8x03SknS5aVQcKUKzbRaSUbLMWCIUMPBsABFIGpAMBkj6sYs8hiXjZnKQ6XQpZo7CCUkcoWWj6XLYEeKlYJZyRS6NQDI0MJqAso6ABsZAIA4jRCfg9bcVKw6XQpZo7CCWlShyCn_i9TAIBcrBKNSCXRq0xEhgFECATYFyahxTyGCVXhcrHplCDVQLKzjpvVZaAcoqVlKgPdFqJZZihBChi0Kg_4fAANf3gg1kASD_6PqSpwFUAAGfIwADrHgACKlwAAABkKORAjz04tiQnbKCpWGkDEmSwglJcyaO6KKaiBSCpWZaKSaiaZigJEh_2ggAgAAH0IEeFB0iQ56D2QnZ0CpWGkJIFJHNFFNRCUmWikkmmk_RszPkiQy7rs2AAHRBBCcPw7O05NIVKywk0khBKTNaKKaiGLRgJlCsy0Uk3KTrDMXWnkMklGmhp3IhBkTcQl3HwTbKgKaAd0OqqKcyrwTbKgJIBWkIAAAOeHHquzyGJMQpSA2o6CCHpjqqiksgpIuVg5EodLo1AwgR7tJwAFkgQGViUWpBBTMBNFiiQmhKQAZTijUfkQgHIKa6EryoCSUuahMCEAWQAAbDRLiE_JimYqVkk0ijDpuEEpLFDpuCmogvoqVlFJNZNMxIJMbNnRtGJbYmBtPUMnD8mI4ShWGXz6dNQKTNRqLfxqFMzCjCmmkWkhlAOYMx1IT8zzlvJJNONNBSkCcHZeZACSMJwfAPoqAPsdAB9jo_8LAD6KgAA2IQAAoAoAsSMawhATC4C6AABY2AUgNCYNJ_YmC6HaQgAApBQHh8fGgA7GDH3QM4wfQp0QuDTrBOHoAOYaKQJIZCxWUUulhGr8kSGAARoKADxjA6FQBGy+yhebWQsmsHIBOQSuRXMYBcLlZli6jD0NI1+GhAAEaCgBp2R5JMEMCoAcgA5KiBDAqD9jEBCBCAAI0FAFERi3kw8DU5hQvDKWuOgCph0RUwkkSwULwelEtI1MUiQwABQBQHgBMyAAAaF4ADQjAAAAAAABgIAQbEBcMhvzyGCkDJeGUYg9poACQI41IJdCUlFpI9PmG1ZkIAAjQUARXGPvOgXCTAf+cgDkJ8IQBcJMAAEk6AAAcDACCsQAgyX5CIJJTtFysoIcRiBORrPf_KwFUKlYJZyfJUK451qgQwEwRAEEAgrEA2xgANsDik56RgDdFC8IIcRKAORqNS6AVCxWA1BYzFntR8QfvIwAABZWIAGZMnoQHCKF4QQ4iUAcjUa7gXj_i8BwsVgNQsj11h5DBoAXuPgdGZmPAAWMAOQgAJ8AEMgARcAIKgAJMARGgAIkAAAAAAAAAAAIcJjTMpAqLEJHs+gFgIXFQBlAKCAE_SZAgB4w+AAAMBAGMYgJ1EAg0QQYIZLwyjEHuNU4CCUaDWTvy0LoqVoELNJD_6EAARoKABixC2LJHw2B+BMAaQCagBDQmAAj+hAAAOBgCaqwx6iY+QghcVFBDiCEACERijReCgoEKIBkzieAAG4KAJsxAAbID5RDFnQBQfcJxxAD6SQCFxUgQAZMfAAEaCgAWsQAFaAAAAAAAAAAAACAGICDZA8oEMTcdFUoNdMIlMJDxmNpJGoEszh+gaqZQpJ9kSHPQA0YPA6NgAluAEMQBJCANnwAAAAAAAAAAACYULBw8ADcwAxiAC7wC1CAAAAAAAAAAAEOExtTig63iUwIgd8RAEkADoZAACwiAABMZAAAGAgDP8QAGzsdGAhgVAGUAEsbAAEsmAABGXAAAGAgIy0QlowSzoASjwAlEYAAAKoAFJU4AAJIUDlokt7B87AG5YvPphFpXc_pwUWgy2shDYqV1mi0memfjb_6EAARoKAAkjAG0IAAAAAAAAAAAAaZGBjm0CLWdEIattPh6gTCW2ekkCaRUogd8qhISf5MRJDpJ0sAALIUABDCptRJY9BsB87DKO+btet2IPBLRJNI5AGwVK6yU0NK4DagjEAkgAwJUdnpw_JIRzqclhR0rGkwgWaLYRiB60YU1kJJYZbmVRzyGUaDSTDYTF48Co7J2cWEw8bHoJnZiqDQ346EJcIBgKAYkDfx4D_5UAf_KgAb+PAAAhLgAADAQYk4aGwNSXkteAh5PEkIa"
noncomputable def WL6_1 : ℕ := zfNat64 33248 "CKERKF4ARScneRgOSVBWQBtoQVACXQkAICP6Qn5nRxGTmU1mitePgTFys_efEZHPFkCPNSCBjC5WXZbVSKDUmyNDBiAJRMgbAAJSoJKjAui4ACWhIIIgAAABghEmCgAAPqQB7jhPKCIHq3C5WUUeSULwGTD09JyRQZ+ULz7LayA1hKhJ+DgAAU2dSAFBONlIQg9X4XKyijMiheAsAenpOSKDHyheLnLqyA1oihS0mj0AAAkNBCGNOH4Wi5WUUX8WKwggZHJOSCIwMjKFyslpVIoNS1IUMDKUT9ZsG8YPgQopHEZ_U6EMXKyijdCxWAGRyCNOgCwFys8h47CqG0DYgm0il0C3xsBgBEDyyooozIoXgE9P8FwC0SoKyArVCnwlBdAR4VAeOjIBaxnWiIHqoC5WUUZkULwH2D09JyRQb2ULzr_EurIDV66EtomAAAH+jGuOSIHpoSheUUBkULygjF4Q4jIJOSKMfmHRVyheS2skUGrUEaGiguHoATQpCgNGbxiI+QZyiwqV02ihPixWYaIIQGRzaZ7PQYnWLlY9lpVJUgRwa0F2hcAA9LOzAByPjJFWIiB6w0oXgAEKF4FWh7wSE_PM5IoMNKF5LayA1tOhAAB5KgDbIwAOaCRwWKHQAuyoBUxcAKsQgAF2VAUAJ6VRyTQBrKEsHQAkNskZCrHEf8EKcsqLlYCXiheAHRzaZ6GpGBDBcrHstLIDU+yNDAAAo8sZsQIj5TkKcymmgvwsVgBkcmkA7hYzIkXKx6AFLMG5BNpBAPSGRO2Y7Ojsmik4LsrhuBuijwcyKgHWGjsAKi0AOAXbqKgAJ6AAG4GCcIkG3SRA9OGULwAKAFQDFIEcJp7jYCaB0GsURgABEgwDw4C+ohuBojEQPW1lQAAHUCAFKSoMALQU3tKEAAG4GAQMbDcDBPHgNMVAE0AnIEUJOGwPbWgBYHwAAbgYBwLmXESDEnHgeugLgAJjJaKFBmOZGZN5QvCiymqjVkaEAAIkGAAk1KjEQPYjlQDQyheAF3QI5OQMqlQVkKv_jb+KEAACIGAAkLAiDVGIgexHKgEulC8AEigRycgYhKgrIVRr6VCAAAVEIgexFKgErlC8AHWgRycgYzKgrJVf7G3v0JiQMAABrZAjB614uVgBeLlZQQOosRoZOSKEpJbWdyIxVGqgkKGqQaAAE6GtkCMHrXi5WAF4uVlBA6ipGhk5IoSkltZ3MjFUaqCQoapBoAAAMqMBmmgAcFAo8IgMCVAf4LgDkiMKQBrZUAFU3KhAn_SEAGUAEAn9CMcskTg9cIXKwAuFysoIHUUI0MnJFCUktKpFKoAzBuoJChv1JgACbSQOmEESMHq2i5WAKQDSEB0riNDJzURGCUktAIsVwqzFtKBDC6mEIO8CImZ0SeIkYPZPlC8CwJQvPyoQHXZoEcnJFAdhcrJbWQqjUHiFDOQHAAAAwFq0Vk8ESMHrpyheAkQuVlBA6_FAjk5IoDWLlZLayRSqNQ5IUMOIAHQo5GhiEZmcP1JFysCUgJCGD5zEaGXZyBKSaFUKs4DZhSFDAygC+XMZN2YAkxjWyBGD1rxcrAAYXKygkdL0jQw7OSKEpJbWado1VGoHEaGKwYPgBJSzs4EA0TTa0giBqZUBKQA5iNDHvMToClpUBRCqbDQgSMbAG0CykisVo4jJymguVgCk_6fAZK4jQwanUQn4BoKlYpkpVCrMRXoEMw0W9xcATSdKQDbJOTkQPWPFysCUlBA6cxGhk5IoSklpZx4jFUTpg3UEhQ1oEwxhIBhA1ssXg9a4XKwJSUEDodEaGTkildlJLS4plMilVcJg3IYhQ1tEwAAA3xYBvJD4xcITblC8CWgC_EaGTkmgV4uVktNIVfEG1BC8hGBGAZPwMh5jiMHqbC5WAKSfh8LQ6AhGhg1BbClelIJX_LQVZiOE8hy0wmEqkkE8nSybG5kAyI5C4wiRg9cEXKwAeFysoIxDtBPM5IpBDKuyklpZIpVUOYNwtoEOOgUmYppKF4AEhtrjL_xEP6PrilQEpADpIkaGcSCBpkqIJrBaKqYhQgAADLLGZNRxGGDSoAUgBUriNDxSxAH5yolCE_AKoQTbPV3KQAxJ2zHZ0dG0UnBOtcRINHQenEKlYUEPhqA5CrRkCOAORoBUrACqbkPn4AAiQYJ6uhQ6enA9WUNwMBoGCUxsHAIY0gAn_x8AASSYAAKR8AAG4GAPXlESDA9BgIcXAD0AEqqaOYAhWfGwALZqzFCAAESDAA8ygYtsNwMDEGAmZsAAR0D_hUAjioAMujTYAADcDAC42gCeUNwMCUGAAAI6AIuAWgBiAWIsNTmbG8QgAA3AwQgAk+IkGAb4ZBpA2ABqDwgrAmkDa+5cAE19YjAACJBgAHWwBiqG4GCeFAADEPgAyB_mCAbxsAYECYrAABuBgAVGxEgwTwoE2lwDWNhcB5DIdDAgvoyAAYl4RgABEgwQgDtaIkGCeFASI2ABIAZIof5giJzFnYuAC6A5QI4AAiQYAH6cH3PhuBgnhQGZNgFJ0kYD_Q0ABNAAgi8kIAANwMHtWB5j4E8KBCR0AAaf+LQAEfhIAAKR8AADYGAPMfDcFBPCgQkdAAGn_i0ABH4SAACkfAAAA3j4AmNAQhQAQOgADSAAIAEgAARHwAAAss+AJDQEoUDizYKCAaS7zc6ADMocAEhT8hAAADQD4CMKB_BszCguyNgNJhHIEVlpqwgeAEhK8lR3GCwAACvD5th4sosCmjRmG_0IAolmOZ0AFZbCQAEIdUCOLQANsPE6OjoCH29iS1d7ajt_Ax4AEMgBUegyoSxeAsckVgUrpNWOSKwttdHQFysK6UQasLQI4AABgIEaBgFAQMHKgP2FQB+wqD_rcDByoK6AXhCAAARoKAYOVAfuKgD9xUFtBg5UFdALshAABuBgEFkQLAwEaioDKh5DD_7MAGkAtFQTmQoGapGVgAA3AwKlDAMHKgP3FQAnA8dhbQ2WVBXS0jXvKEAAG4GAAkNACelQDXCoAP8dAAT0qD_q8ATxCAAAAJBQNBSlIYMgFwApAGKHjsLaCsC5WFdGcpWka85QgAAAaCjiDByoD9xUAJuPHYW0JHlQV0tIzJCAAB2FAASGgmIYEslQGMioAYUcPwsoPhKgIp_1qFgIQAAAchyQuAHiSKw_qvA1Dx2dvRrKCvC5WBFLSNUhI0MkgsAAAAeaNwmHIaOLgC6kisK6ACPHYwdGsuXV4SgXKwIpaRqkJGhh_JqAAG4ak0dBDMqAkCSKwCGpo7CyhocqAmlpPBoQHW2h7YmBkdHQGgoBh5UAKQBKh47DChBQvhtEqAKlp_0bfHQgAAdhRGxoASGgF1C4AUgCVDx2FtBJRcrCu6QUrSNfCoQAAHNJQF1i4DtRUAMsPHYW0NLlQV0tI15ehASQAOcQlKQwDdKF4BnipOAGQOm4G0JSBhrJprGZOBQIYHk2hFUWJkdAELMKmpiGTgAGkQH_jIA_8bAAwsiAAg6bAAA2CgALITRLwBAaqUsXgIJJFYF0mjLNHYGUmhUC5WfSq0W0jURSFDAAB2FCGAkTPa1oDZxcATckVhXQMh47BJNtoKELlYV0o2karbQI4AAOwoMQADXAFRli8Au5IrCug5+wrFtNkvCTi5WFdKNpGoukaGf2HgADwkA+0MHmi4Au5IrABz+BWLaBEi5WFdLSNU4IUMVgxF0AaxIrAA4DINAwK7LF4BJyRWBdB6Ikv7ysG0FkFysK6UbSNRtI0MAjp9ACViQCuGAAAGyYAModfuVj_SUBoD4BaUHagAD_RtKQBZhwCwCEAKQBKh47+4rBlBahcrAijW0znVaEAdB3y0AyJioqoUColC8BQhUnG4pATWYHTcuhtKLpwAipWcSumE0zFnqBDAunmqlLBoAGNcnBsAxEqQpVEAkisggLvNHYG0OIlQV0tKfDaghXT6EqhoDwE_xAHdlQCKEqOADk4htDZJUFdhazG2zxtQRqU08gQAaADcjANTFwD0ipOAPDNHYG0B_FysK7_xmtL8jYgiUrp9D4xkDuCLjdSC6MZVASEPAf+PgD_x8ACQh4AADBMAAAYCAXTjs4TANTIgAAIoANTIgAAYmwAANgoJIFyFBgpQvAK2kTwBYx03NpJhYxhKSyD0NMxSUhQwKIEvjYAAIsADEzwLgD7lC8AmihPAGxHTc4hhCUlkHpaZoG3wUIKiC0ABcjQCNpUAHhQngAeDx3wJyDCFFyoqg9AVghG0rJZABkyAsZoUEeFysA1aRPApKmjpubQsgj0oVlUHoaf9mSoTyGZSqUQI7EROio2CZaoGCIA8Q8Bq5GAByAB4h4ABJhcAADYKCUJD7MPJxUdj6EAJDQBaZUB2gqAO0FQf_bgWmVBXQCfIQAAAr4iCEGAsCVADgPnYWVUqkAaSiATmQoGa6AUgAAZgwABIsGIUAkksXgF3JFYV0HIWTSIheEnFysKyUbSNQuI0MIFFwADIEsvgYBhyJQL9JgAAW_+RgLIL9JgAAbHQAABgIEaCr6AtAOx8DBSngDRzR2FmshKT9iVMSjaW8mDcpyFDG+pwAAAtEgTBmOOwLjKgGxplMADWaOwrIcNKgmJRtOGjaggRAAAAsnXw8VRqBh5UBRlOAB6BZBh5UExANwhAAFSVgHMOPoOWklC8IM5JoOCOm9FUKaOxUyhXqoY1OlISZjTTTMXdoEMTQzYzDPZ6VSqB8zMgC6OBgGPIORilC8bggR5zTQHNFJSaOwqlkjy0SkJMxKNpRSYN0TIUMC7BQABgGKo1BTUqAJIAAZQTaWMwmPClIqm9EICyWQcuVAASMgnGoImlQCclKeAAGdOYFkKblQTEpM1EJkICyApUqBhCLAgWsoXgBQSJ4AbQUYoWwTIXKwmIaQlG1BJTLxZLIC0BemoCmlC8ABaZPAKzN2_u5cFkD3FysJiGkrRtQSbAxeLJZDjxcJmDxpB35QvAmokTwCqbQKJDdOk+UKyiTEm2WYpyQn8DG4ulksgvEoXg7Z1IOMy4IE0gAmcABygGAiSDsSYAkgBBUh5DAAJJMAAFI+AAAMBFzEgAJmFT1QPAwCSR4AYgA1ABJY8AAscuAABMFBKA8DAQTxBwAtAB6HvGIGHlQVEA1CEAACYKI0BPcwPgwC8yoBpeIGCaA5DZ7JrC7pUBVoptL9oQAAKwoABu8DYMBTIuAQ2YNwA1R47DSYQScXKz9TUPRSWerG1BKwDwAADQMALQPQlCsNmZFQQWaOwsoSkDSUQOM2MauRQIYJQACgUAlauB4GAlIAeDBeCkF+mjcAOilQAAHmDOAACYKCcnP0ObAzGEFIMBrEqD+iMMQwhNQ4gSkJIHgao5GzQUIAAGwMWNCOgUgxD1y+ClXpQvATwVJwm10TwVJykmmuibC5WSkolEGr5UCOAAQYEFgAV5gpBgBPCi4AUhXQUn1E4wgYMoXgpHolBq4dAjgDwCgBIhgBIaImXr4KUslC8BqxUnCbXSa1YqTlJNNdFoFyslJRKINWloEcAAAHsRx6bDgWgXmVAVOPgAAwga"
noncomputable def WL6_2 : ℕ := zfNat64 33245 "XR4tanFKROTACZkAPLgCYsBJZUCUqAAAABEpUAH+jZeqEAAAASMgKJcCUl4LgAMcqQAA0QuDiANURoQABOjYAYWUASMgTwkA4LAsI2AAAAAACagsVg_sTAWALgBAAXMAHSgCRkAJKgCQsAAAAAAAAAAAAAkZAaC4EpfCXAAU0wgAAk4HwXLwAmu70YAMIVCeRQz2ZA2MzYADMgJ5cAEFgSllZcACEFamUzCAE0CMXLwqgTVtqJLAkIAAPy4AgLAlKqy4AByaZTMIYQJoBIuXh0eu5dAmrhEqOAHQAUlIBTLnAKglIZi4AAm6cABNAbFy8KoE1l6jBEFraAAAAjIAeXAAhYCRSoEpUAAAACJyq2gA1XyhFtAAAZZcACF_6egR6VAlKgAAPnMQARcqOIBB02C2gAAA0WACh39HwSkDhUAAR2cgAD+BkAKDNgWKwAAB4AjRgAIsdR8CSSoEpUAAAACJyoABq41CLaAAMympnQAmZAlIHCoisVABA5yKIAA8KgAARHwAAQhoAARkCRLiHholNji4Jo97SXBUQAJououtoANSPoQAAQhoPwAEZAWS4EpRuXAAFHQjEz1gzgE2mnWLl9tKoE1QqiSxDDRnKIAAAIyAqFwJSzAuAAC6+piAP_p3ki62j0k4JqGNAjhaQENjwMgAIyAgFwJSo0uAAdopTzCKZQrgE2gg_KF9tKoE1a6iSwtyZLAAAARkCALgSkvBcABPxSBTKFcAoPci62gE1lQjAJIICWzYG4eHAV_MACypgLgGglwAdGfiKXQeiUCJXEuLIxAmuV0YLIABQuAACXAkohS4AAAA2B0B0Ll9slougTXG6MW0WgAAGgX689Aj8qBKVAAAF1CgInKjCADUl6FaJeAAAAaXAVhqUBoEklQJSoAAAAETlRxABqvlCDCAAHgAdKAGIQAMuAGFQBIaAAAAAAAAAAAADUQgDV8ZcABPevtQBPSBJcABCatCRo6kE4AAjQADhBgi51BHpUCUqAAACiATUq145AFJSYwIALRJgCJly5mwSlSxcAFVC6CUo20YgjkXASf3HxJQIFylk4AAD7ECMF2MFjMJShUuAAJrXF4EKE0FUXLwCTkJrEdGGv8AIAYwWMwdnSexqZsbKcPDAW7MCgNHQ2peNgAD+y8CyloAYJUAAGxCAAAoDAQhmMmYXYaFy8AAkl0AJI30sXhtz0pBNRpoEcAAMYcAxhwZjJmF2GhcvAAJJdACSN9LF4bc9KQTUaaBHAAEIAxGTMSmuWxaAACUKyADUoXn6G4sgNS0oEeiBsAACilYyZiUVy2LQAASgA1YrgA1KF4NsVgGqB0CPWJyAAYiUY1koyKyC0oXgAAhKiACTKF5dmDOADU6KBHsgvAACdKR0BzJQXqWBUKRgTAk4mAAAyAAk4mAAUsdAACEATAkMYdVQyCycEqAAALCARsqBCScEPDYAAhIAaRYECDDGHHQMgsoxKgAD9x0AAYcqAAaoLQgGoRCEgyAgAGWCNgwxh18DIrIzSheAARQ6AfoJh3BcAA1cWhBpIP5RoAGwMYyZlolq+LQCjRUACjhOFZAP+ULw2stAQYWoEcIIFtdEZAASGkcDILN3i4AALISOwiitAC0ACDQlCCaBbWDGQHoUJxiFkjZQvAAFIlAqj35hIrEalC8e2koj0Q2eQ6CoRk3k0+ApFtBOYMydnQARZrMFDIo1mtRcAAf+NgABaFQAg2dQhaycBbWLGQBQDNcBI9RkTazHwuAJSABhAqMXATQIKLUIoJ_pOLbXYyAIYNG1GX_kIsyULgAAB6AURLjKAF0+6EAm02C7PoaAEjNCuGQD9KgAD8Q0AATEmAAKqdAAGYKhO9KcGXAn0qAmmkAAAbCVcMagAdMhHEAGfFwuInf+Mgfq1MkqKKd7RgBKPQAarpKhBLmMALEoRt9itAAxAljZOGIxFamSVAGWJEYApNIAWRKjCATAQqCcX1L1sAI0WMxbROGJLZaFoDUegCWp6MAFkSpZi5jAMAIVBNtZAANFjMBwcPnSkLApRU2yJbLEQXFIgAAAAvKRAAZiMgAAPExUotTJzYEfygdDjYnj8fQvWwA9sNF0UgEUUmkfuXBFRGCa0UAAMYcAE7OGMOCkbMyugsLl4AAAG00k_y4LJBLpNXTJUcA6AFEOLc1AQ_DpycBqlQKgw4QoCAGTMACO2kA4x0TkZAZIoTVbCdLAAAqDBqa4c6AFAQAaNgAAAwihABo2AABMZAAAGAgG4GAUBABo2AAADCKEAGjYAAExkAAAAhXhuBgDplQGTgoAucVATQRmVAYQD6oQAAbgYAEK8NwMAF42AFoAGsWCPKECTyoABq9lCAADcDASAIT4AmNAAAAAAAAAAAAAYGABKVAAA9RoAAEpU1gKAAIbBQAANwNABCBB5UASQB3xMEiEYIllQVkBrTVCAADcDANwMBpAuAeyoLjjhMRkD8iEA9SheBZAa0tQgAA3AwegCFmG4GAjYXADUDLw9TQeAigbMoXgWQGtLUIAANwMAAFmAIFw3AwF4S4uI7AAGQCCLQPZQvK6VS2nkcejVBKBHAADcDAC7ZhuBhCAGUY6_AF4BoABxlQL0VgCNoQAAbgYvz8ADJQA8yAIFwA8SAAAAAAAAAAAAAHTgAJ8AHOgCRkATLgAAAAAAAAAAAAjS4bgoPnNRIyoAAAAARlQf2NgGObAADnCIAd5cNwVlZKDSSsqAAAAcgT8qAahKk2AAByHQBCC4bgokhpSoXAAEZB4AchfYuAag0msxkYBKAmQiBkZjxlDw6cCtJg1eXLEAA4AS0MiRFgIItCVlC8DQqlugg1Y2gRwAANgwABAoIQYwpMHdy4ARosEtDIBBFoMUoXgclUt0EGqe0COAA0ALqHgXUXAADKRg+AB4guAsgNaXoQAAFwYACQ0FsNATEqAAP_DwABMSoPlLQBjUIAAAJg6Pw8d8LpaAABkAggHsoXgbVUtgNS+oEcPvEwAAJEiEIOHIRAUAqAxArAAAAH9C4AmmwLFYAAEwcAih3Rh4MsFwAtADrUDx2F0igFguVgWfUIxtGq4EKGABBwSKEEIOHEJADEiAADnCwAAMSIAAGJsAACYOARQ5dQ8FPC4DWCMADOLlYEUFzlC8KzRQa4XQgABcmwAAUoAwFCKHBEGD4EdKF4GEigB2MBcrC6RQhgXKwy1mig1e2gRw_qRBhABFDuiDwJJKF4IFZMZFAjKPkB2f+XiCC_C5WBZIoNSVI0MCyAdYaJWZvb2THY8AAmQDAQGkERUAAHGFgAAzFQAATj4AAAwEAOAuAAlQLAwRAKRsAAAAlAbRUARRYdEBzYLZCQAAbGgBIaXNNgDQXLwAJItDIT1lp5DFIHkoXhBqpBBqpFAjgAAAiDL6NgZOVAeIMg_8ZAT2gjEemVAWSKCQkIAAJoUBi9Q2DAhcALQOnDwP0CWT0ig6MoXhWaKDXC6EAAJESARQ5y5o3BWJQvKaPTKFyspIxDtBJ6RRjCg2ecXKwg1miyUatwRoYABIcRxEADHDAyHQDrKgKeFwABJIpgNQoCVAUaKf4NrooSGA4FoRUA942D1xcAdUoXgB2gk9IoLOLlZzBCrNFBqXhGhocDgagdqOgZF1zYD7lC8B6xouVlJA6tBKhk9IoOwLlYQazRQarWRoaIA4ooAfhYmQdQSGVApJwGQBqhKJaAe8qCCaQEKoWfDIAAGX+zUH3i4AP5QvADtqkqGT0ig8ouVgVQGuiUIJoAhwiABdNtMQmoJJFwAqyheAEWrhdPSKB4SheBVf0lA1s2hC0_UbAAtKWmrWAxSheAhkoXgQNGD5BJ6QQQYXKz_CFUQGpTkKGtY2ntZqITNHgZA2GoEtlQAtAAgoEsPNIwSXKgKof8NqCoWejIAAALRmg1oZimlhKF4D1MZQvAYkmID5JJiRRiOWUlC8FpJooNSboEfPxkAAB4GRcvsoGZKF9hBfJQvA3qMHyCwlcxhBA0xcrNpUf_IwNRDI0MagBCo6Kkpjw0A0CWWD0oFIErlQH8C4AJIEUJJlQVkAqMDWdaEUQkgAAiEYNg2DYxcAdUoXgF2HqCBFBN5QvAshpw2oItDKA+gyCYSBOOQT+ULwG_lC8CMj1zTVnCtIQB4LldNKqA1G+gQyqWnkq0H_x4sxkdnZOPARBlTHwIcLgDtiw4BqJQAUklwRozAAyGRsIwAAUgohwcCXkQIgw4EYESFQH1C4AAHoEAKgHoVJVmwAABEGA_42DCxcAFQPTDzTjx2T0igHQuVhBrNFNo1bshQx0QwAAMuCjYNvFwAVAyEPNOPHYf8RgrSULwLIbZqG1BCaAIcIgAEgxgCxdjZuHTC4BT4gXLoB0wh47J6RQEkXKwglkim0asqQoYAD0AJhQ2mM0bgd0sXgI5EC5SQOjknsCkCOVGUhBLJFNpgDZm15ChyUCq3EQKZTADh3AnZoAUJnKRf+YgN8VAd2FgBtB0ABvioAA3R8AAYSdAFIUwS1Qw2DmRcAHQIZDy8Dx2T0igVIuVn9kKs0W0jUqSFDAKhxAABQ0aBsXIyC3RcACAoPgBYjx2T0igcwuVhWaLaRqCZChikCocQA8AqhUcjwBTR2AtArUOIwA7AA4fk9eUgRwFoXK56Fn_CNbRq65Chj0CocQB0UENgcuWL_4FQBUpIFkYPj+PHZPSCFGUhBLJFtLADZm4lAhl+MiilxoPeiIHHGD41B6cssXklAqAskYPjkBweOyDLccKQ+CpXNRyUJar0G0zEglWa0UuNBUKOIwdlZmTj52hAGdECIMyA2DwpcBKQAiA4k8hgVZKULwglUko1PkjQwAAIgxE0M6TiuCBDK4iQYCKEguABAiEhg+Af4OhPpQvACAPSiIUMAARIMA3AwTx4DwFQEcTYANIDkEwFQFUegbA+AADcDAC_LgCQsDAMEvj4dBUAAAAAFF_uVATTYE6sAAAFKLhSBgAQcP0+lQLfPgAAoJDs6MCVBRZSWTNgAAeQsAZ0uIkGV2PA9qoXBPTGFwfzMgCgzGcwCLgospJqLJSBqABCEgbGwAk1NwEQPbplRRR45QvAJ6TmDyMFCyoKyH+jamaEAACIGAAKDAiDc2IgeuKLlZRSFpQvAJ6TmmyMCKSheFZAaznQgD0wcAAEhpuAiB7gcqKKPHKF4BPSc2YRgoaVBWQGs6UIAAAIQv5w_CQVKyij0GBcrCCB0lhw_JyQQfmULyWlmiyEauURod+xoAAAE4cciERsfOwBFysovmD4VBcrCCB0DR0_E4RTkgg60oXktLJFBq9RGhyUCSAGFFjcQiSTh+AwuVlFsIfC0npWIcTjkmpBJiaYuVktKpNBrJxChyUJpxnpNN+QJyXnQAkZNwEQPcDlRRR45QvAJ6TmzCMFDSoKyA1nShAAH2OgAJGQQg9O4XKyijySheU5QgOz0nJFB_pQvJbWXYIwNWuoEcAA+SEAFmyHUvEQLDKiihESheAEUnJ3kYDklQVkAbaEFQAl0JACAj+kJ+Z0cRk5lNZorXj4ExcrP3nxGRzxZAjzUggYwuVl2W1U"
noncomputable def WL6_3 : ℕ := zfNat64 6972 "w+AQlQAEKAAAAAAAAAAAAAAAAAAAAAAAAACfALS4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMBBJBgDMZAAABm4GAOhcvACauJRI4AABgIAESUASGgBAICXlwAAAAI0Ll4ATUIyVHAAAAJDQAQEAZjIAAAByAdC5eA2NRUrCaimSo4AAGoAhZgWCgBHGwAAAAAeoGgCWbAsVgAALBQAE0oA+Xg0JACHLgAAAALcXLwWgTUhyVHAAg0JABLShFCjciQLzLgAAAAIO9LF4ATVxKJHAACKFAA2SgAVcEQUHZFoCBMAAAAAQiYAAHB0AACIKAA4lCOFB1laESXAABhAAY4XLwAmriUSOAAEcKAQgrxxED21RcAAdANgALVFwADV7KEAAEIKAAllCEFVAIgewGLgAAAUgQGLgAGr2UIAAIQUWqHh2oBArmJCkyFjMFMJS4AAMIBdA2xcvACanVQI4ABiQoAUSUCYME8WA4JUAAAAhB_pUAZAawxQgAAJgwX09OA0FGbKgEGVAAFsF4ABX5UAH_jZ7KEAABoKAACZAxi4ACLA0Ff3VgLQbAAE1vzkAE0F2VABqU2AAANBQGgI5KBR1wbBX2nYCREwAB_ZeAAJETAAE8OgAAbBQA8WYoAocgrI2AALXLwAAaCoAAKB8AAKAKA0ABgwbBxTVYBBlQABbBeAAUWVAANXFoQAfmDgEIIimqwCDKgAC2C8AAokqAD_Rs4lCABNg0BQ48JJarzUsy0AAkl0BrKlsJIwEsXldEbJxNXBI0cM3DwZJaGKACI4Ngp+asFVFhcAAG0C7h8E2i4AJrxBGABJ_AuCXACRkBAcxBUthVZEXAABdDMS0BsYuACannRI4AD0Zo8DBGTEFS2FW6JcAAF0G8LQGxi4AJqG1AjgAPRmjwACTItparzEs8tLgAAuhStUtgJ3LF9tyUvATUigBPRvjwACRPYh4BixXCrJAuAAE3HisMKIE4AWnEAGoy0COFhAagiYPVUKu0C4AAFRUJQAUhUyhf9JyABqTRGhhZNoUHNZETIACSg9GiaKwAFKgADaAE02iPyoBqH+jZxaEAAF0eLWpxSkTkwAmZADy4AmLASWVAlKgAAAARKVAB_o2XqhAAAAEjICiXAlJeC4ADHKkAANELg4gDVEaEA"
noncomputable def WL6s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL6_0) (dpk j 1 WL6_1)
noncomputable def WL6s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL6_2) (dpk j 3 WL6_3)
noncomputable def WL6s0_4 (j : ℕ) : ℕ := dsel j 2 (WL6s0_2 j) (WL6s2_4 j)
noncomputable def WL6 (j : ℕ) : ℕ := (WL6s0_4 j)
noncomputable def WD6 : ℕ → ℕ := rdw WL6
noncomputable def ready6_cuts0 : List (ℕ × St × ℕ) := []

theorem ready6_cuts0_ok : CutsOk ready6_cuts0 := cutsOk_nil

noncomputable def ready6_0_state : St := ⟨26112, 285696, 28545, 39936, 29184, 45301, 53248, 94495, 53248, 94495, 29184, 45301, 28545, 97600, 26112, 302334, 54657, 325632, 83841, 370933, 137089, 449311, 190337, 502559, 219521, 531743, 248066, 629343, 274178, 809984, 57729, 85237, 110977, 163615, 164225, 216863, 193409, 246047, 221954, 343647, 248066, 524288, 82432, 123679, 135680, 176927, 164864, 206111, 193409, 303711, 219521, 495743, 106496, 147743, 135680, 176927, 164225, 274527, 190337, 466559, 82432, 123679, 110977, 221279, 137089, 413311, 57729, 142901, 83841, 360063, 54657, 330879, 0⟩

theorem ready6_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD6 ready6_cuts0 115 105) ready6_0_state = 39886 := by decide +kernel
#print axioms ready6_0_cursor

theorem ready6_0_covered : Covered (toCl ready6_0_state) :=
  ready_cover_cursor WD6 ready6_cuts0 ready6_cuts0_ok 115 105 39886 ready6_0_state ready6_0_cursor (by decide)
#print axioms ready6_0_covered

noncomputable def ready6_cuts1 : List (ℕ × St × ℕ) := (105, ready6_0_state, 39886) :: ready6_cuts0

theorem ready6_cuts1_ok : CutsOk ready6_cuts1 := cutsOk_cons ready6_0_covered ready6_cuts0_ok
#print axioms ready6_cuts1_ok

noncomputable def ready6_1_state : St := ⟨26112, 533248, 28545, 39936, 29184, 45301, 53248, 135743, 53248, 135743, 29184, 45301, 28545, 304889, 26112, 285696, 54657, 573184, 83841, 618485, 137089, 726720, 215467, 779968, 260768, 809152, 289313, 1072793, 315425, 1358489, 57729, 85237, 110977, 193472, 189355, 246720, 234656, 275904, 263201, 539545, 289313, 825241, 82432, 164927, 160810, 218175, 206111, 247359, 234656, 511000, 260768, 796696, 115509, 188991, 160810, 218175, 189355, 481816, 215467, 767512, 82432, 164927, 110977, 428568, 137089, 714264, 57729, 350190, 83841, 635886, 54657, 590585, 0⟩

theorem ready6_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD6 ready6_cuts1 118 49213) ready6_1_state = 85296 := by decide +kernel
#print axioms ready6_1_cursor

theorem ready6_1_covered : Covered (toCl ready6_1_state) :=
  ready_cover_cursor WD6 ready6_cuts1 ready6_cuts1_ok 118 49213 85296 ready6_1_state ready6_1_cursor (by decide)
#print axioms ready6_1_covered

noncomputable def ready6_cuts2 : List (ℕ × St × ℕ) := (49213, ready6_1_state, 85296) :: ready6_cuts1

theorem ready6_cuts2_ok : CutsOk ready6_cuts2 := cutsOk_cons ready6_1_covered ready6_cuts1_ok
#print axioms ready6_cuts2_ok

theorem ready6_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD6 ready6_cuts2 128 1) (ofCl (RC 0 0 0 1 1 0 0 0) 0) = 105358 := by decide +kernel
#print axioms ready6_parent_cursor

theorem rc6 : Covered (RC 0 0 0 1 1 0 0 0) :=
  rcOfC WD6 ready6_cuts2 ready6_cuts2_ok 105358 ready6_parent_cursor (by decide)
#print axioms rc6
noncomputable def WL7_0 : ℕ := zfNat64 33242 "Ca1gSgAAVhwWmIGtL7iTi_FQABWaCAZZD+5KGAVCVC4AJLbAqAABWHAABxg1xfdScX4qAAMORVmggYciMsh_klU0gIXAUkktJCoAAFYcEdmBULIYWXwJVioAAMAtUZjRQcYtSYTOQtKXYEGoTVIidLAACKHFTOhpSAF6oNhocosDfDoCKxsAAAR0LgHoSRqvtCAAI0FAADXwD6qBGGgPCzAAAFcMiM_kagB50AYQAAAXBwPyOIw0Dxs200c0UCIEyOqgI1LGZVYigR5LKSUnEsz0MlkR5g3fugQwAAYhwA2S+BAQSdAQxIhvrwAYDZmYQloZYuVoEnsZMI18ehAAEaEgPRiA+joA7BAnAE_GjObhkCUWizC5WXQehEwjVcCFDAABcHAfGkYAKZgAaMAFLhX1MAD8PAC0AFoAC8KlZdABsR5DAABcHBGADG4AMjDp74AeXABaB8gqAPkFQAMJHgAAJlwAALg4rwAsZNYhAJ+HgC7DQdAM0aMwKoSUnFysQNdAQLGMaoaRoYtAABocANpDuZWADIPABUGv2GQA1CIEgkokJQvEoBZGvdUIAAUAcFIFAL8ALgEHjiMjJ08enpdKpAU4fi0010CtlC9CldCzJYdjwAAwQ4sTMdISUpmymplwTbXDcDAGyIE4EhAJCAGCioADIx8AACIGALwYnIkT3vJcAABUBWLFcAEpQvDjYQGpuUCOAAjQOAAkNARiQDeLgAA3gsAAokqAD_Rs4tCAAAoYaJyJH+z7vJcAABUBVLFcAEpQvDjYQGpuUCOAAH0OAPlXDcHLSEgFoHWCoALIAL0JgAGrHQAAQgoB9DiRiBcDjlC8rI7gmTgUZGpyF0qggcoXh1soDVA6BHAIwPARAFnEC4PV7lC8rNJAMTJwqkZnIqVYvlUmKcSheHWykhGqIUCOMQUNgAANsJB4ouA4UTACjDB2AE6SoAP9G3CUKsmUAnMNAPzSh6NcASGhJCtRsAAAACARYABLhEAABvzBfv+TAnooXgCUBywsq44ZlZAdkXKzbcbCA1DMjQ6yABGRAuACJKAJDQCg8AZioAAAAAKDwAADy4AAA8AEhq+EqGZMAtA7sTADwjB2Tf0rF8BKpQvMJ0diAa2NQgAAnY8NDwSxQ2zESBHRcrAEoAVWaYN3rpwA8UoXmEAbkbUE6mEsgDhFDZOjsmDcHFpFgfEbFRACswsABJdObAAhoeNAAAQgoh4cD5Vw3By0hIBaAAHWCoAF6EwADVjoAAIQUADXeBQkQ4ByBh4KuIwA5AALoA9yoPvJwOtNgAAGwUA_NKHf1wFAxJCtRsAAAACARYABLhEAAAwGA+yJhZIrJ6LQGo5CqKuHEYoDx2BDWL9RGtRlJcTLSTaA8wbuAQoYAAPQoAp9kADrjFAo8GVi4DiBMARGNgAQsTAAJWOgAAhBQAymPpS4B+5cBOg6CyCEchdKtgDYFsXKxjcbCTbSNVAIUMAAI4UB5V4wf7GTVnaiEAMsXnEIo5poB1Hx47JtZAlJhuKtGbHSTaVcwbn5QIYAARwowakNoQBPRDcHBNEgF2VASkDiA0AEVLkVAElCtnwAARwoiYmhDx0bAI+UNwMGwSATRMAdoqAAA_wjAAMfNiJHwAAIgYAGGURIMAGQqAABiRcRsQgLkli8D_iMSZqC9AjgAAiBghBKJMNwMAGQqAvSfAGG9J8RuQgP6GQABVAABKDBragHhmABVwlymG4GJc5AAC0AFp_peA0kVAAYiPgAARAwBlCIiQYCSIAiAfwsXwCSCRFYIpPcuDSATLoZNWTJwAAIgYBCBgJoB5UmAzMlDkUcrBVE7FysAym0ah6QoYVCEgDLCwAEhoB7koQBEAqMmAB6ADDyoC2jMbRpSEAAA2gwfCHiUIAiA8qTAZ4SgBHjsAqifC5WAZTaNSSIUMAAPocAAsWH0ObIVAMQJKADkgmsXxkysESLlZcTDZWXtG8au6QoYOQAAfQ62RUEtD_B0XQmTgAsTR2FkAVBcrDjXTLaRqPdAhh1mYzAfBNgAWrwKqKAYCBYZAAAOFgBOBsAA0CIAAZZcAAYQBFBw+h1qioBSAJQAchZBwrVMIkXKw4mEyhxaN41eKgQxIRQvhJTQBsCB5QJYGHAODYTBNIyAG0gRwCggBBEqALT_w2uWhATTLIUCAPodkgqBRxkvDThkJQBnpo7CyBKT_TcWE0qWPHYozyGWGqnWomkcRgvBMXFZsAqHwhhxGSTJQMfkwBJHJUSqRSYK1NaBcrGGNG80102jVOSFDAABqFEWD6HLtRg2qfACUACKaOzUa1_9gzghIuVhXTLabuG1BAAPsPAABjhuDiSF0egCUACGaOwhy9bdMzYwHYXKy4l0PDNjtI1LIhQy2gAC4ASGhXEYMBHwH1CYAHIzReMocVKgLpltOsDaggAAABxoSQgC9bHoTAQhKFkIo5KzYaichSAcXKy4l0FbBntI1XUhQzCAATpQJEqFElhPQAjECcAFWaOwqgCsLlYF2w2kag5QIZtIxmQA5AAKLCIPD6TJZSJmHoAlAAPHjsLplFutBIi5WGmsmE0jUcSNDMJ9AIADIAEGiaUSWA9AEoGdkYIpo7CqxxiABBcrDaBRet2G0jrMG5BMJ1LtRDCo8TYGIobIINCPnYCCCBOARV5mjumlqF4JSXSsmEtrRrmJBOoVlzGACNGDZOzs2ADEIBCXAAAAAAAAAAAAFcMwoS+BcKpsLA5AP_lQB2syD_RkDhyIAAFxsAAFIKA2NLw8dF6EFF8wAFGACnQDAR1CvCcAFoeAAtDwAAAAIS4AAEQMAMtCIkGh0ZAlnIERyYD+iFEcmCyDEnQXB9KaDWyaEAACUGA1DwyONAMOEClIhuBlcCwS6MG4Fxi4KJNAKNFA1pUAf+MpqTQAARAwAEhIDAOAEw8AJgeAG2F2pg4AReVAFVFFIQAAAgQcCbh4C3Q8ANQMF+rA4o10H2FysAqo1ZcgRwJgJAAEbhwPRHEYBCRg+fsVgpwXL9XBxVroKgLlYAVRqYBGhgYQAxhwMjICmLhCCgoBwe+IgGwDwQaqXmLGZJQ_6hKPKF4BVRqRRFAsASEEaCjGhwGDHEYHVR4AFoXbCBEi5WfubjiXtUK41GUhQwAJCU4CcLgRBYCEDiMCsA8EEmguDBeSX_KMUGIpQvAKrNSKxIWAAAIUtBsFZmLgA_U9BEHgcg7g4fklhoIKLlYBVRq5BAjgAAuCgDVlQhCRzioAKyCQyDxIQBiLiSw0EhlQBHZqAAD0HgDnFRLJUAFZBSZH+EIA2lxihaSw0DUlQBHZqIBWAABiJAGoKnei4GtHRLSzJo2CCAxQgTSUGmCy7NhcAR0agAALhIACRkGVKlzi4B7HQVUyxsEEHpGRJQaEiC4A_+OCxqAAAuEgC2FY3LWzDIIlHQFyDb9SMQQFIWMxjJQaGXi4GgAkagAALhIKampAb0AYswAXCCp3QbBQEkHREAZ00dgxCaklAlIBUXyGwUkCOAAC4KAI8XJ0VB65S4shACEIINKMF5JayCkSheBpktVGrFkI5kdAACkCPFwPWKXFkJsUMAhCCC0jBeSWshWkqA0_3JqqNWpIQAAyC4AhhcASEgZqUtCITYoYBCEEFpGC8ktZCtJUBp_uTVUatSQgAAAlJcConJPIbYoYCejiMIIS0ktfVYMNlQGUqv_DbJKEB1HIZmLiZmQAk3AHqoQYKDSR8AAAxJKXQT2TAaQDFHwAAIg4AAZkDWLgCdTvZIRKQohBAoBgvJKXQdgXKzKGmS00ak6QI4AAyC4ACRkAPLgANUF6kgDejYCACMARcKgARATAAF7LgADSAUcuUYqAopsPIchzOVB0lSmEGsgtJLWS3qE6QuVmUNMlpo1AEgRwHoCYjYAZmJA+pc8h_ZS6chAARHEYQQSwZL4RpE+S1kFQlC82htktVGqd0IAAEocAD4yAaFxKBClYHJ8ABBBjRcSUAeRUcQPyqwAAAlDgB7C7g0SWUEokEAQ44jnpBLIRcsXyWS1WYkF+BcrDIaZLVZqhhKjgNQOTDxMlNnU4Muhko6CisIIVVAMBC0BSB8wmAPmEwALAHgACVlwAABgIJS_B4zocA4xxGBrMeACCGC8MNhA+RcrPnMRtKiNYQIEcAAeg8EvmyCQ4DjjiMDzI8FtWgFoYbCBQC5WPTCbSojVmyJDOQVAAA+R03V2HAz8cRgB0OorWwQEULwq2EA7FysemE2lRAKYNy3IkMugAXAuVg6KSkAL1wJwKRoKISJBLQOzlQBssuK6YQfmVBaSUiT0IAMoKQJgEgdYVJwOcjwALSu1mZg7mVAbSiKhXGtBOQLf3MgAvqMPPl1LxIDRFScAFY4fMSrQIxKF4XbCAai5WG20lRGqbEKGUZiASnRgdAHQtLJs28SBZhUnAjpVJSAmBgvC7j9gzhKRycTaFkarQQoYBNQA6BFOYAkrBzSZK8qCsgAAksuCkgTAqAmlN1YA410DrqEABQaIaGgv+dAYpKgABJYvACm5VLSbzcFU76hGk2l0DYpsAxmju6g0CLTh2AKQOQJyOSheEhVLYABC5WMTLZTTUZiQTSYeNKwA7TRuDoF6sgCQU2+eGg_0dAS2JgCQhUACNCYABd50AAAPqaObAFBkA1rgCI0b4JBHAmAroRG0CaCJLgphsIeqLgwgQQpyEcQJKEkAdJkRULB+o2A6gTG0AHBY7gphKoN1KF4YS6TUImmQI5VLpNAIwuZwdDulC_cwlTQSBUnqoB38LUGeCIUmGqgYs6OMVKzjYbKE2YnXQIZVGoFtdQlRyTqbspFQPnFTyFLzEiakiJFYC_QQWVEJSFmsi7Th+cAqVhpNM9JsxXGeQwUi0EhhHoKgWOORoKKaHBIQHLDicjCtBQIoXhVsICiLlYWQJoxMwiQwAB6C4AKDkaCgWEisHkrF8C4g8VkMRFwYS6A7SheFkCaMbrIwAT_x0AAEwGRoKsELAxMsZgDkAIIdNyupQZgUYXKwtoVRr6lCJyBEIoADKuBHVQAEORoKPoZMQgBKAXQLgwgMGKgAFtIQAANSIAAVcDEEr8HnSIQCRLGYF+x4AdEXLww0UPolQGEKvtjaggBAiFUAACHX4PQmQgWCsXwA6AI5KF545aAAYXKwCo2kNgCoEMrJ1CJP5WEoMgASyIhPgLSWMwK+jwBLSugSrKhqYvXgqlP0Ioz0ACITADiF4OZNaoEIC3ljMD4ZEAfcLl4VQKalX4l4roVS_6EYQCIAPeaO1vIUMHToEcAOgWlJkGlC8KoDHipXQQCjMWzIT8wm2ohEKKASheTY6AUxoiCKg6EC5jJeB+4eABbJTC4VWB2RcrnpZMITRilRAjl2egRAARMANjiM055DCYgDZGD4ElcGULySAJWKlZNAKIx88hrOaN5NnIRP_KSayBODpSUxomLguiORoKJSHA10iCu50JQCiKQCc4kKlYWQJv_DKwZw_J6AEyHjYLjYDTwNSQmIOurgGAnQhwb8IgBCACEAGPjwADzS4AAEQMU9PTjsDAjseHxNKTxIbGg5C"
noncomputable def WL7_1 : ℕ := zfNat64 33247 "BCgAaB4ATpQvAycrTUAJrjShex4gTgGUavWRoYB_1GAIQC7tADi4FLJBUAoB_5GAzwfAADCoADCBEAAzNgTqwYEAJkZNQAeLAAhiwAZxYAGIAVLKr8EQFZGvm0IAec6ewfY8AAIYsQ4MgM4sAARLGYAVRKsIEQBZGvo0IAOoSMeACiXAAYoAEUWADSLAH6DIAGClWEiICskQUICIf+dhrx0DY3Ky9DFjs3NgA8yAJCwFBwAFgoAgQsAGiFgATCVAANWmoQAACkMgCKkHApQeAJ4NABPBoALVFwADV7KEAAZ8eAeUULRJEgPURAQKIgDwBUAG_C7_jMADWZaEAARoODDRYQIgXADDEURC8LAFXyIAOIFxlAJqZNAjgAEaDgB00QRCRlRICWEwBCiIA_4pAAoYqAAUcfAAEaDgAFHxQCxlRIABqCkiADPJQD0HMFwADV7KEAARoOAe9Af5EGwcbgOAjRYzADQULwMIAZQZUXASS+zUBykAARoOAAcXADeECcAWBEjAJ7_46DaDySheFdFdOHearcRoYAAIg4AA4uAKeIgK3EQAIZCfgbQtyVAB1muIUL3R0AAAEcuQcqAU8RAVqIgARiE_A2hbcqADr_82w+hAkACIlwOjpSIUTJ8EgdURAd8IgBWR8_C0hcUqAyhx_0bb7QgAARBwAEjJqASBcRAnAEJYQGLwPQwpPas4YZWdmULw4mUOI1RIjQwACNBwU05CXkM6AByIAkJBsHCEFgI8NACEFgAAAAPyHQSzYFisAAAAGIg2DiqjwBkGgB9DQAAAicqABz_42XyhA35SAACLEQHaSDYOJoPBwY2AGIAB+FKAMJUBJA0RsAYQFgjwMjIASGgnR4BCCQByBYAAAROVACaVjGNV8oQAAABkuAJDQjRMAAGoWAGxHTcAJr3yheFULKNWrI0MAAAeQgBEuRoeJgTAExAvCwAPQigHxUphHKF5_o6A4jVQqBHAAI0HCmxlGMeATYwfAYMNAA9CyAEcoX_qQgE_OQ1nyhAAAmDgAJDRNI8Grh4A7w0APaPj_S0BkwuAAauNQgAACZR4NTDwB3BoA7QfBZAFoBQ5yGsxUL3h0AAADgyHXHg_4PAKPGgAelbFoAI5QvCumGm4a03QgSABES4HR2pJwFWRACRoIgeAKosAKwWAMqIQAAlKgC0zU94hAAACGMgB5cCdIgAOx4AH40AP2RgAA4VAFpmobQAhc5ACQIiGGhfjQAAJBYAykhAACUqALT_82AgYVADyPgBACRkAPLgfJEAaoXAM6KgDKiEAAJSoAtM1AKoBlxoGZ0ADJwAxGAAmQA0uAClQAcmADDQAIWAAAAAAAAAAAAAtMgYhF4CcSgmAADELABBAAKfYyALTNV+J0sAAjQcB8eDgBsyAIiwmBMAAF4WACvHD8AKrdSheAW0av6Roe2gYcgAAAkyEwJgAQgXhYA4+fABLUqHJDwHH_Rtr1CXa_GUAAdACQ0CuNArYaAFKNAGED4AEmlQAbRNyEAAAASGgmx4BvDwBdBYA38fABOMqADj_Y24ChAAAAAS9p4ERAokeAxMZAD7Dx2AFVkBcryUrG0DaNTkI0MAAvI8ABkaAjCbSU0aAABUXABGjoqgApyr8ykApxuA2gBM0iIEABCwmBMACEBUXAG2D4AJrlRLioA4jXd6ETQAAAGmQAEuceJgEmPAHaMgA9xw_7oDAFV4JQvCCBtGrsEaHQxOMI9AAAGFwAIaAKxHgNAGQA8A8dgBVYQXKwggbRqaJGhk0GIF7S4GamPAB5cASGgAHCIAHhUAA2NgAAQPAAAAAAA4uAijQAf48AMguAB6VQEoKyvyheUQDiNceoRtB6AuEiIGZiQubACCEZo0TAmAAC8LAA9PtHD8MDKyvyheAG0ap+RoYAAURoAB3ECYCvEHoKjQf6HgJbFwBg4+ABJZUAG0TchG0qgAAAIKIceIIRAFo6AAAVxw_AkhVYyUL_7sRNA2jVziNDLIJwF0ALAAS8ABTgBZ8AeMgANEABFgBQUAAAAAAAAAAAADsZ1anEwJgAAvCwAPQaSQzIrK_KF4AbRqNtAj2aYgC6AHx4PkRAC0AvCwAsw4fgSQqsOLlYEpSA2jUXyNDAwkTwDaBA+h3HIgAumQAGKCXHgAAvCwBxI+D8yUCCSheAHEa+DQoiB_puIWGwOioALMgBRcA++TBRU_EyMDSDkPHYHEFpFysumUqltGpVkaGDREIAAAkZAXC4JQkoUU0RMjB6jVnByFtpoiFI9BcrDKVRgrRvGtBCwk0GLjwM15jO0M7QgBIyAMFwAMqAAAAAAAAAAAAAZLg8koAALwsPQBviwViRWAGULl5FKoE1BUlRwACIjiMB4zADpkAcJhCkYAqiwAAAAB0Ll_NoKYgTVBiVHhoAYaKgAJmQBQuBcTgAEMGwA4YSADERcTENoNYXoQABlSIAD5kAVLg8koABiRkAAAXdclxMS2kWarsRo_6w4AMKFQDgBMyAKFwdSUAAGIaAD7FjMAIJZSheTECaNRqoEcABzRUENGAGy4CxSAAC8LAAEhIAAOFQAB9NjOhsAAQIBCdAFIWAAAAAAS1DASzYFitoRGAAAEaXa0tVx5JQBZDIxUUQAmgIJIv+lxVCek1ZclR83IwAANQjA_TgAAUkwAEkAOxFHIuDcdAA1b6hGWFgAAABLwBIaAfOgA_wbAkJgAAEdEQGjYAAEx8AAAA4LgCY0I2hBaQqCySVxkwAABIQuAnpNb4IwAAH86HgH6cAACsmAAEoB4IkTlQAf8Nm6oRFBANAARHYjwA2XAByICxSAAAyNAAAAAASzYFitnpGAAAAyXB5JQAAXhYAKccPwAqttKF5_pWA2jV_KBH1IjAAAADMgBA0C8nAABgFgAegCdlZX5QvADiNUQI0MiiUDSAH0JDRwIBIhf+Rgkg0AAAA8geI5FwADVxaETY++8pAAAAhqAAmQBsWAsUjaAAAACuioROVAB_w2bChAAA6PgdHGGiXoQH5LgAAAP+ERIYuACagbQI5bnIAA6jQD+oRRFuFwAAAAhA6Fy__jUFXBYmoU0COHEAPIREeNgCIyBhQuVNQMU6AAAACQhcAHMzRuwdCAokVAAAi6gP5kCMhAMU6AAAABE5UAH_DZfKFEQAZQbA7igBdmE8SC4nA1AACLQ0ABaouAAavZQgAAojQAMEIURYRKUSeZgAAAOIAdi5eAFSagZQI4AAURoACRkXChB_wyZl2FY6KVABzjJeGknIXcoXhLZqDUhKBHAACiNANKhHsl7_hsAACGwhcBcZgHPkC4KJFwTUixYSgAAAumQMKECCjYAAhwRAAVSLgAmvEEaIgAyg2B2rALVMCMhROHgCgAAALQROVBRQSD_htKNCAACiNEWAEW4ACZAUKopNKAAAuh+xoCT_qCBBxcvAmpNUroEcGoAA8aADUVGQXG8QgAA_6XAUhYACAKkqABeRsAABRGgxAj5cutzTgAAALIsANQHqVALQbUbBtmzGACLyYAlpcA1m9NQi1KQAAAF8WAABKVALQD2bBtAD_TsAAGqACDZaLw3FoAAABgHAAAC0ADS9_4yAAriUAIeBDC5hDR2P5QlgAABtBoAahQAuAS_wNiaxERoiADKDYHSUlscMAGswA8uI0aAgfAAAH_SIAAEpUA9JIjM2AAAojQAHSZCBpMKEf3fi6AACEAB4hcASSaziRgAAojQBV8oAkZB1C4u5iAogAH_Q4ABVx8AAu5mAAA8LAWhgA3KAJGQH6cAAASEBKAZsqHGDwST_xsodCAACiNEfagFYyAKlwHqcAAosmAHYkwAHHKj6MQ0z0TWhEEbMYAH0ABZcAYlAfESAKMVJwKTJQKyOHKF5JIoaZ6NVqI0OQisFZJi0hMpgB+nAANnJgCRZMACNSoA0_vPhhqE4g6CsgEhKI+BAPBkspUEFOAAUOTADrSYADilQBpnomdCiIAGXMgAumQAQuDORgCoBSCpOAcJOlyUCsi2yheG0NM9Gr3kaHEQJoMZNHYNjpHRzs7GhsaAsWYADZcSPBWRZCwEKS4AM8NQBBECB_Y2CabAABHAoBZHgrIAAGrjIGcZF2IiyQxKgCqjXbaEAARoKBGh4J4cANA64ZACCDJeB_puJIlC8CwlXuhtQQACNBQC8PCDFu_JQAFjLGYHZl6WgGkcgXKw_MlE0qjUeyNDAAI0FAVw8EtjoD8yxmAC0qyccKTjaESLlYFGwxmUK41bEhQwACNBQSgOLJQAsoyACPFjNISUHkwiKSheH+kIclUa8vQgACNBRFhZaQgAGywcet+TB7ZCAMyQJwAxpIrMIApEoXnUCgjXMKEAARoKAADZYCOIxfkCcMKcEJ+E04oPF0qhTSoImEqgKrKF51Ls1Aat7QI4ABGgoBSHiCEwAALB4AjoWcNg2gINgAezUgqEAARoKAApvJ_FQZS2oR_0aAAI8WM0gJQPSgkFKF4ARRq81AjgAEaCghh78C0nQNeyeXxjQWFKgAAAAAubf0ggAcCfAABSCgAI2QAAACYLQf0bgAAAKB0AAKAKALMXchAfwBRkQAYZyFkQ4ya4yB5cuQIVwXiagABGgoMQAFzAETIAaVABCYAkLAAAAAAAAAAAACvF0bPoMRKUGWugTUw0n3CMR5qzzUyhLTV5cgQAINRDpwABGgojbWtG5Doso0InZqaMAJgYgNROJEXBeABabQCaqpQI49AA3Y0ABeaz46F+MH6iZSaFm1qkK0gTh_JAjgCBKCCBaC5eAE1KYkRwAEIADAHAw6IuMH6jZTOpk8LoJkgThBGoFEmkEB8Fy8865jKpNCauURo49AADeTZCI0BJAkGRAAlpmAEYlR5ABUqFQQAIkXAcoDGD9RMqUk6WVUBmQJwkjkMRLQHRSDxLF_pGTWAUFVyNDoID0m448TMgHABt80yEHfmYhiUAAASQBy5cABBlqhAAaUuGRXyYmfzoHM0dkhGD9NLNoQAEEai0LNNHpVBAuMNLF9pLNNEpNUuoEcegAbsaAADdDShAHrSgACbESBSUfWYpCBZKgABHoQAAohorZ0LkwANzAEUYAoXADSoAENAAAAAAAAAAAAAD8wCXOABGUoJROkoAAAwgSQAM50NQBspsHIEgAANNw8NwwCd3ABcYCdZAHipxDR2VQAAvCwAJoWD9SUEsC4Cg9CakUAAjQUAAjZDQfA8KgAAvCwABISP6NwAAAGE6AABWHAASRgZJcMQVAAOQnNJEKli8jJFdgTTlRxcvACawKSgAAVhwAEkYR4iDRBUBM4mAADJFA55UAAGxCAABWHAASRgLxcAOykZA2AAAAyRQmxuLgAajUyKEAACsOACfLhYCoAAAJctAGf9IwGjKgAuwbDBEYAAAJyMADMgUJcK8VAAABLloIz+ZGAYpUACvjYAoAHmNgdnYkHvwAkjAvi4V4qAAqUTA5CLUomAyBpAjlUcWWLwAmtYEoAAFYcFpiBrS+4k4vxUAAVmggGWQ_uShgFQlQuACS2wKgAAVhwAAcYNcX3UnF+KgADDkVZoIGHI"
noncomputable def WL7_2 : ℕ := zfNat64 7998 "w+AQlQAEKAAAAAAAAAAAAAwEAoCANwMAGwGABCAFwC4AJr6xGAAAMBAAAAAAAAAAAAABgIANwMAGwGAIzCwAK_KgA_8bPZQgAADAQAAAAAAAAAAAAAFoQCIuAAAAAAAAAAAAALPgBpkACLgAJUASFgAAAAAAAAAAAAMBAmBgO0JACkAjMLAAr8qAAavZQgAADAQAAAAAAAAAAAAAmBgE0FAB8EgAQwkAAIB4AADBMAAAYCAAmNAAAAAAAAAAAAESDAmBgFCFAK2FgDK4sADHC5eAE1cSiRwAAiABMaAAAAAAAAAAAAGwMACsKAH8LABnBYlIFAJfKgA_4bPZQgAASgwAIS4JQYADAUAA4WAALCwAIrKgAGq_0IBrwEAABIyAHFwAEWAAYCgAXCQADISAABA8AAAAAGAgAEGQAkuAApDgCDCwAmcWBoAXYuXhNAmofkqOAABIGCcAHmQAMaAHiwADAUAC4SAAZCQAAIHgAAAAAASLAAMBQA_hYAM4LABPguEIBNdKIzgBIYgAIgoAB5cASGgAIA4AgQsAAyEgAAqTAAAAAAAouAJDQAJocAPwWADNCwAJfKgcgf+NmloQAAAAouAJDQAYIcAPwWAEoiwAFsLl4MQJqRBKjgAAAIC4BfNOIARBIAgAsAA1EgABGVf8RgAAAKZNwAHhuzkoAEIcAQAWAEriwAFwLl8BLIE1IYlRwygETCYAQAYXABhoAABeFgAb4tUg2ABpFy8FoE1IUlRwB0EDwAAQAWXAExoAVkaAE8LAAnhYAK+FwLQJr05GAsgAsDiZHR0dAGQoAASIsACRFgAB8VYOIgABIfAAArDgAAlwAUiAKBgEeLABTEgAAAEpVhAiAHIxzYAABWHAAOLgCQsqgA3FgCBCwAAAicqCQPAOgYv_Gy+UIAAAAcZAAeEwAdhYAAAAB0jEEs2BYrCdlIAAAIBwIIkB9SoAAAAA6Fy+pA8WQekwZ5qgxKjgEEqgtz4ARsACmQAQOYR6AByLCEAPCwAAAHQuXiEWgFRgzzVBSVHAEoBHgA8uAChwAGosAAQWAKKHwAHpKsIEQBtEAIQAlAKEAHFwAI4sA90mAIeHz8AH8lWECIC6DW06EAeQIqNAAOLgGoUACOLAAC2jh+ihCAC7RdhAiD_a0TX6CMAcSyADgAYuAyDgAB9lC8Aqj7KF4ASwLsIEXSi4Ca4uRgPgRAAAEjIAeXAfSIACIaAUgVAVhWgAAArP_zYFisAAEIWAAcXABQoAGgeAE6ULwMnK01ACa40oXseIE4BlGr1kaGAf9RgCEAu7QA4uBSyQVAKAf+RgM8HwAAwqAAwgRAAMz"
noncomputable def WL7s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL7_1) (dpk j 2 WL7_2)
noncomputable def WL7s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL7_0) (WL7s1_3 j)
noncomputable def WL7 (j : ℕ) : ℕ := (WL7s0_3 j)
noncomputable def WD7 : ℕ → ℕ := rdw WL7
noncomputable def ready7_cuts0 : List (ℕ × St × ℕ) := []

theorem ready7_cuts0_ok : CutsOk ready7_cuts0 := cutsOk_nil

noncomputable def ready7_0_state : St := ⟨26112, 164672, 28545, 39936, 29184, 45301, 53248, 141021, 53248, 138496, 52016, 219646, 28545, 165216, 26112, 103616, 54657, 204608, 83841, 249909, 137089, 331648, 190337, 384896, 242353, 471039, 361024, 499584, 387136, 603200, 57729, 85237, 110977, 226258, 164225, 331855, 216241, 383871, 334912, 412416, 361024, 438528, 82432, 186322, 135680, 303310, 187696, 355326, 294976, 383871, 321088, 409983, 106496, 274126, 158512, 326142, 249675, 354687, 275787, 380799, 105264, 272894, 133809, 301439, 159921, 327551, 80561, 248191, 106673, 274303, 54657, 222287, 0⟩

theorem ready7_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD7 ready7_cuts0 108 29418) ready7_0_state = 64426 := by decide +kernel
#print axioms ready7_0_cursor

theorem ready7_0_covered : Covered (toCl ready7_0_state) :=
  ready_cover_cursor WD7 ready7_cuts0 ready7_cuts0_ok 108 29418 64426 ready7_0_state ready7_0_cursor (by decide)
#print axioms ready7_0_covered

noncomputable def ready7_cuts1 : List (ℕ × St × ℕ) := (29418, ready7_0_state, 64426) :: ready7_cuts0

theorem ready7_cuts1_ok : CutsOk ready7_cuts1 := cutsOk_cons ready7_0_covered ready7_cuts0_ok
#print axioms ready7_cuts1_ok

noncomputable def ready7_1_state : St := ⟨26112, 236480, 28545, 39936, 29184, 45301, 53248, 141021, 53248, 138496, 52016, 224958, 28545, 165216, 26112, 285696, 54657, 276416, 83841, 321717, 137089, 462738, 190337, 573647, 242353, 625663, 270898, 654208, 297010, 700013, 57729, 85237, 110977, 226258, 164225, 337167, 216241, 389183, 244786, 417728, 270898, 673901, 82432, 186322, 135680, 308622, 187696, 360638, 216241, 389183, 242353, 645356, 106496, 279438, 158512, 331454, 187057, 359999, 213169, 616172, 105264, 278206, 133809, 306751, 159921, 562924, 80561, 253503, 106673, 509676, 54657, 450912, 0⟩

theorem ready7_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD7 ready7_cuts1 113 121) ready7_1_state = 71477 := by decide +kernel
#print axioms ready7_1_cursor

theorem ready7_1_covered : Covered (toCl ready7_1_state) :=
  ready_cover_cursor WD7 ready7_cuts1 ready7_cuts1_ok 113 121 71477 ready7_1_state ready7_1_cursor (by decide)
#print axioms ready7_1_covered

noncomputable def ready7_cuts2 : List (ℕ × St × ℕ) := (121, ready7_1_state, 71477) :: ready7_cuts1

theorem ready7_cuts2_ok : CutsOk ready7_cuts2 := cutsOk_cons ready7_1_covered ready7_cuts1_ok
#print axioms ready7_cuts2_ok

theorem ready7_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD7 ready7_cuts2 128 1) (ofCl (RC 0 0 0 1 1 1 0 0) 0) = 73545 := by decide +kernel
#print axioms ready7_parent_cursor

theorem rc7 : Covered (RC 0 0 0 1 1 1 0 0) :=
  rcOfC WD7 ready7_cuts2 ready7_cuts2_ok 73545 ready7_parent_cursor (by decide)
#print axioms rc7
noncomputable def WL8_0 : ℕ := zfNat64 33247 "BwBGJIQg4yBsBRAcuSKwBOydPAyjkApv_DoPQnwW0AfxYzAdQ8bg6VMpgRBJFYTSaXI2poG0MMHmjOBZKIGdQIZTbaWQXQaMwLgPG4ACUp4NsNkdFScqk0msaNqaBtDCKBk1gWSaDwkKGU22lkF0GjMagLhqd+PhcJ08BHhUn_+zBNG4bU0AFNG8rtlHpXaaDKkJ_OaTbS6A8jZmXYeCg4WczI2AIS4uFJAkFANeGgG3DQA24aAAWgASwKgAOODxMjcyAguGuBIKAXwRAPkJgA6A0ABBAAV8XAAAGAgEB1w+hBFLBg4GjwNm6aipOCkmzFopIrDqbQqkEK7VdBO3_V5GiE_AAA2DAaTgLreEIOtod+OgEOGDcCaVSKgNIeIOgIIBpT4AACoMACIuAClQAESEIOAv8VAaHKgJpocqAuh_46D_oMAbBCAAAqDAaAia4Qg48hf4qAr8VATSvxUAH_joDyA6E+AAA2DAGUZhCDhSBAioCJhUBNImFQAQJpHQf+RgDlnwAAGwYDQJmvCEHDkHo2i5WA1FIE2YrFJFYATT2ZOX+jDUCCLSSMPQI4AAGwYQwMKXAO7lQA9k3idShWTkmlWNpSAU2v2TgchPRLi4eDPgkAAAdouOSOgqiLKFZZRyt4qTk5JsxPSUKxyBTSq5Olg5B8bMyeiUOzkb4nSwAjICYi5lCiVQilCsso5XIVJyck2YnpKFYZE6WBTSQxOlg5KJPRLHZykhOlk1AAahwAVy7gib5hcBIixWSTDkxOAUVJwcnEkoATKORCAPRKIRKJZChgAEaDgCHlwC+RUGTCVyKgJpGYqA2g+1uAekfiIAAAJBQAJi65lCfARiMRyRTKaZiIQ7SXLmDMiZIrIKYSSMViNG8B6JQiLDQI4ABGg4AX90AhLguQoOJwB_xqCP_CoBiQ9JgLIcGbgAAAAjQcASUXHokTwBLG8kipFSmTTCOUPFScSiUgzEUi0W4AWJ5FEsO28AMiGqpuUh5IwAACJy9SEpsC0CglCuTTCSw6FIJSCPUKlYLSyRS2gBkQgUmb_5cAERC4HZ0LDY8FQSkdvwevXCEHAZtJgMEkwA+kmACSPQAEYGj8AADwMABIWXetsQCkG5GxbSRWBNVKZCnhSUXTaR5RhqG0qlH_6kPARoYAACkC+Ly6EtA8WKwFrICpOAUizFpBUn4UlVk0lkskUNpVLN5_gxL5QI4ABGg4KMXiCBISRWHUtySKwok2YzlJFZUTagxaBqY8biqRSKPHQI4nZOAAF0D54_BOZIrDaNw+koUSbMWOFSfhCUUTTVJaoo1K6VSKRQHyNDNGLwARQbABW8AmFgAIcukEEMkisAM2dyShRJsxY4VJ+FJVRNpZyujDUrpVIpFHZoEcPv8goABd_6eQweSSKytTkQnJFYUSaDDJFYGkmGjDUCqRQSygQ4UqxxKpJDaJcTcyfgAZGAGGQAkuAJCwAAAAAAAAAAAjQACrNeLQJ_JFZLYfG0lOI5JoxhMVJxCXQwNmss0Uch02lUvqpbqJQQACNBwA3FYUQAKUKwdKbK9JFZBSTBkyFMtI6oV7SHFRqCTQqlkNpoQAAnSYAlatVDcUQFIOnNnoFScgpJ5SZCmW_IVqdpK4o1BJppKpW1S2FBnIAFVGidDwANrBhq41j4sgADe7kwDEwCTB_5mD_yMBVArYfAAEaDgAccQLCuopKnklBOJOAkoDUIgBZP+IwFUBrx8AAAYCAY6tAZdYBDbBp6_9k4igAABBhKAygYQAE3GwAABgICa2sGJc4qcsnTwAFlCsAAKmTwAE0bAABSPgACNBwACQcBJ5DN2ePyTNVaJ08sj0tqZPktpJJNmIGk6eLajXSDRRrRa7USTUQcoRAEaGAAEyoI9AWKZPJzTQ2FSc2kkm53MqaoAurMpF0Io1opUaL+pSDDoEMIthNILnJFYAqApBHoPATp4PQ+d2VTpLaSSTUBG1Nu8XVEw0Fb6MNSSYaiSaSJfQI4BZTLKQBDcOH5jkB+DUmk5JslNJJJo2pQnikooWYL4zkIitRMG5BKpRIpRIIyTyGTfUGVVJJtLpnCA+CsuAEkYA0XAAhYAAAAAAAAAAARoAKRgA5kAQLgBJUABGgAAAUWAACEwAAAAAAAYCK0AJIwQiuZ8Pg_0pAdKKgKJ0pSAuh3I2AkgQtPgAA3BxHx96Dhd2ADy4BU4qAFIE13hsKbhEQYR6ZYNgGIZCB6EAARoOMMpGwGLjaYsV7CApBTRsW0kVgTVSmQpA2kvkYagVSj_5SGzoEcAACwMANhHFQKgFQCLCpWTUmhmNhSEUwl0GosJuKpRkQtGa0IAACwMAXtiGQFklGiLFYDVDZIrJqTZixYqTi2um0TC8aSaG0qlEsj_0COAABkGDMHOMQlSzJM2ArMVANfalRNSa5w2ktNANJNNIUQNpFkJ+AAB4GKkPAshVBB6xYrLkMQ8UkVhhOIpUkTgZRyKQCCJRKepQgABQBwB4eIOQFoH+CoCaQEKgAZG3B_ZCAOSfAACgDgBh1x7x8AANtkTAMSo5MBhA0h_weAcYfAACgDgBRDLNjaPh9DLIohMpmUwjUZxUnjM1JsxXGSKwaTTKSQ2hZIIlCJCpKBqSkAAEEMqyNqCWRIyZTMphEekisCaCUyFINJphB1zRnCaQRKERwqBHAoj0I5EwMjIXHgs6AA+IIzZkWXfyOgABvcyYBiX5JgMof+RjSFUCth8AAB4GAAeXAEhYAAAAAAAAAAAADSsg1BUCZTABuSK_zFQTR+hw3poBrk6KoZQKpnwABPE4B4CkE7MLmSGjsCiBhjZTxUnFNBJs+zIagbeILxOTSFUmlEO8jQ5qIEAH8S4agn9IngIYKk4tCaLUNm7IlYpU1H_0ac2kKoE9KJck6WdbKBRxxGTI7Ny8OCsdbRyheNSa7iUgBSCclIFIAJ6Ng_4rAHLPgAAPAwdhdSAIS4LhoBZRUApYqAmilioAAVGwAAAAB4GA3Bs40npz8dryGtDw+BwQYvXAMBCUBSAKQkk05wVABRZEVAATdmnwAABgIA1dcAwEBNWUVAXzKgsk0oEVAAyo4hgAS3PgAADAQBqFIBgIGglIUXANWWlQaSKKS3lQAFFQgABHoQAABgIQ40AJCwDAUrh42A9CxWEUOmSKyqk2UBtKQAGGRAABBQgAAExRoPKFQRQUlVJqhjbjpUABLCIAANSEAAKAGAAkNGaDxsGLVipOEUaqcKk5VSaOo2ZykACBkRJQBdSUAAAASGjNB42DFqxUnCKNVOFScqpNHUbM5SABAyIkoAupKAAApAfVcIQMeYmRgeskVhFGfFScqpNGoGCxWB1LIAAFPQI4AAQgYBGyEIQMC8iAzvwuBiPkLFZOSaOXRFC8AWiX_QkALQHahAABCBgtACTEEWKgdiRWHoCoIpIUkVlVJs3Db_xUCEKjUQQTAAU0AAjQUABJiEZFwjAUGjCoHJzQqCaTTfBUCH_jEFBTIDyXSSAABGgopQAkZBJy4WkYPgVosVhFGeFScqpNGoFixWCEogAABuZp4GMFgAFIEEKgAI0DoSKwC0WKwijGipOVUmtmNGYpBCFRqIGJgAKaLqGAAARAXAEhoVQKDWxUDk60VBNJpvgqBD_5iCgpkB5LpJAAAKUCCFQORIrD5BUEUnOSKyqk2chsKQQhUaiBiYACm58EgAAEQFwBIaFUCg1sVA5OtFQTSab4KgQ_+YgoKZAeS6SQAAClmQL+RDcFCkHfFScWAmSySlVJrtDZixYrBCFYqAAgQmTNPAABcFAGoKgCQkGocGokVhkgqA6HYaFJORyeI2FIIQr_Y2J6AKTaLvTgAABSBUFoURkkVhKSO_9FhrkisnI9jWZSkEoVGpXc+AlJtJL1FIDODQAACEqBdiQhBX6ioPvFQHT6RUTkcnHioEP+hYG7GwApLIBlAJqAeMqG4KDUSKw6QVAdPpFRORyceKgQ_6FgbsbACksgAhIoPzVgZmRmhBAZcSIFAhIEWKwch_SRWE0mhDSRWCEw1EmIHkukkHcjDCFgAAAPIwj0v_I2SIFAhIEWKwcjVipOE0mjF3ZIrBCYaiTEDyXSSHoRv_mwAE6HgdAS+MKyL_8bkvBQIRzFisHIiUkVhNJoTUkVgpMNRBiB5LpJIXpwAAKw4AKhkHdLgI9UCgdsKjUh0CkppRP6FQJTKGOTIsh5Lv_koAAA3BwHgnwubWQBQIQokisiqcOZiagqTlkmk0Yr6Kk81EJhqJMRafgeN5dJIatOAABaFAeAPTICGXkoEdCoCUhUU0mkpCoAAbmRlDy5peALsNAAAIRLsCSI9dgoEK0SRWDkG8VJx6TSaMXzkiuSiEwk0FIdM4qG0uj0AAA3BQU2ZnSzozgmIKmWHjY7wyAIVJwihaCZOZAGqtJHIkisLpV7ejDmUhxNJZpIj5GhgAARBgAJDTHY0ElCKGsKk5VSaFvJFYXSqCHShea5bjSA3VCAAAOgA8aGoHjYMZKUGYv5JE5VaSMSJFScLpVoo5lJbVosmssnNSJ89TgjQxiAAA1A8bBjJSgzF_JInKrSRiRIqThdKtFHMpLasdk1lk5qRPnqcEaHfleAAAZoeNgxkoKxGhjbCZOVWk_QMkaFScLpVIo5HMXKy22ks0kW0jQ8+LwAAOjoB3MiVh42AcCpOEUkpVXJpE8b0VJwulUtwdSkOJpLP_k6WCkRoZdAopAFlACMHGGjicE1FScIJJQqkmTpYxRIVJwslUihFi5XXZKtplKtJFAoEc_OFAADYAEDuYNF8ZIQGQYCZOUEXqSJyqkkYksKk9hLNRIoNjR3KTbbbKWaSPSYI0MKKPQAHrOpCk1A8bCSlBBzEycqtJHfkisLP8FYqcdSkam2ygEWq5gUooMymIpJxBGBcrAAkZDSDxsGMlHKI0OYpTJE5VaSMSPFScLKA1CuRRzKS22Us0keh6RoYUkZTh3spZjpUgAwWlUsZhqHjYSUGpJQk0kPmSKzCWQ08hDE4m2yuIZg_OhARd1swA0DEvw0bBbBMnCCSUKtJHVkissDEWQYYdSm2mmyo3VgZWgQ6dKR1soAtBsHrOpAIIkFYUnkYPgp8kVlBBBFScqtJGK_CpOF0qkUR0XKyyll0axfJIRTA2kCMkCBYRYJwqGlCyY_hUnB6FOKk4TSaPcKk4Xa6AxOJaHW42GojBkaGHm0lEgykBwsaBvBMnVUHUEd+SJyqkkc2SKws1EGspLKZarexKGNIT8NtxMoIuLlYIzGWlljNH5InlNBGIlCqSY_GQwCpOFmokUaotKFZZTLVSTOWinkMNtxMpZJo2C5WLrGQEeSJygg3SROVWkjXCpOEyXLYRd4GwpDLaQJ+nkO4LMbTjxFmCUgeAT+IADLPNBxoLMkisKg+kkVlVpIeEkVgBngqDL_9qA6QhBtOIFpSobhRoyA0iZODpQgphUnKrSRrhUnpIC1DYU1EAGHIT8qsYaN5xAFJH4KCNjMuOzN2TjsfNnIUTrgGAmoiQNPGgGNDQAxoaAAagAPSJgAADART05PTgIeShpu"
noncomputable def WL8_1 : ℕ := zfNat64 33248 "CSOUGJUcAAAMDXAGKoEwpCgbgiAPARAB4CIABSAAggyAAAyDAIocArcoVhNVPkisCiL42ZykltNNbo0xBSYSiB8EiOAABsGI0Jk3RPcqBIKD0zBaYeAAQTAACCYAAAAwgAAGAgCRlQihwdEoGulQMsOpSBRGvcSoISABOZyEiVgxEMAACIyo+9OAEZQvAcikHNRGokC5WEJMOcFCuD0JzOf4kSBlKeAAKAOAOEVQOak4H4lQCIOm4p_2rDkBqhTGspCEmECCE5nI4BSAAFAHACdMgc5WIi0XQfiVA+M0dikCiNSHFys8kJMIATmcjCFIAAUAcAeMrHhK2+lBRkqDLh0AMoVgURr28qFJCQA6E5nIqpSAAFAHBTHh82CoCoRQ42D9_AUZQvCDNRSFUojpMG8pDDCTCJZUpggSczn_ZFzZSAAA2DFOShmCJ2qxfBaKSWq6Nm7AyRWTkmgONmcpCDWSivlMl9JIJtLv_04IoAGLD4BdAJpQrJbNWAkisnJNmJnCpXM466IhWxWgloQTbOZeAigPQNNKwAgNleV0NUlQSEUgQelGxRyhWFVCYkuEI2gJVQhiQwAAABQsAFi+oJYrgqMkV0UyjU1BUnCKTZivIqVhFrJRXsmS_+icQTaXQMKQRQCKUQBdKoLlJFacUSfCBczjUpxUnCKTZiXUoVgWSii0INpLJWk6VOgRwqlNNIN4gTkqAW+J15aDjxcGUFIRSi4I26GVAmBaAcmEOIA7kIY0MAAAElGdeWg_2VBlBllCsIpRl4bSkABFljuAhtAUchDChgAApADZkAIEi0qguskVjUBS5nGo_CpOPSKTZiWcoVz0ilkqmjS0IJtLoaoRgOIAAEIy84uNMqWwFIZV1GziyRWPSKTZiWcoVz0AloG38S0BFA6gbtPiZs0E_AMU0DwtBVIqAuaVAUS5pUbQCYm0ww5ANyQgroDZUYAQw0Q+tBKSWqvNhSBRdQbGMKlcZC6EtgIbdaMQKRQgAIIFwUgJgypcoX1kDbkislo1UUVJyck2YvFKFcZ_ohO8Wigi0INpLJOWeoEcmjmu1GkqUUkHZ0dAHtl6iA_LICkltpzZOpIrKM5Jsxc4VKwakvBLT6G0CJaEABJBGANTyGWQJGSKyWjVqBUnKM5Jsxe0VK3vMwBFdIXLz7QbSXQcQjQwglPWL4AhBkCPTR7ppWC1xUBTQqD_ycU0KgAE8SLwAGIHwABKhRWAASyAkCQFID9uipbAAZIrJMtGr5ipOUZyTZi5wqV63bgslFlp9HJtAwuY6aEWgiBAKKGDwBAAqkgkUFYkisiiUaouKk6ZzRmEGYteKlYFFKixXoItAM_exzZSzSQnSNDpJRNplKoxIiRgglUILWSRWF0aiAKk9VPpNZsgPxSFVJ8sV6CLXgvH8c2UsgBpGh0lRqZTNoBFzOVRtREjDmZnQAxVBQIxhFflCsls1YCSKyck2YmcKlZRFoBFC2EtKoNMphDPiMABBwOAAC3AszNriZMzMFJyoloowqVgUftG0pByBCI6A6gAAAGwoAkKN6hkB0MqJa8E2FJ_86KOGDaUg5LIDkAhtG0xBS5iAAA2FBSUh4EXYyXZi8C1pxUrJbNQ9kisnJNmKJipWWSilhaDaTR6OTb+ZaASaBHAAg4HACS4gAWMBmqoDJvrKwB_5OiPTSYBqLnJgA_8dAAFMPgAANhQADzIAkLAAAAAAAAAAAARx1SRAeDkmCAZB1U6AGIAMQAAAAKMwAAGwoAEDMAzWgAJcDhUAAAAB4uAAaBsAAAAAbCgCAVQXGQhEYL6JwS0AehGuBkAH_EIAAxRsAABsKAUj03qbU2ykGL6ciNIn0Gck1hiE_mphAY4jQxikpSnhpLIUXZI0NNiJDCqBOQAA4wQeWD0mv6fBOVOAoQpATSa5sAH3TIABbB8AAZQB7Bd0FTMESGDclKmBPpSp0EKLFkIcmkAzUfFENIAHkIAAYgCNgKwWdo2ZtjPIYU0yjH16dSaCE1gJ5DGsdNzCBQRiUQ7bJv_ktAyRGhikFJJAQgD5IrZScPyiNWPJ0+wz0mqdSJ5BnJNns1LpFqpVoKrCxmdRMlkWylkkk0HyFDKp5sJhMPfVJlRszBsVlwAOrAC0YAkVAEBYAAAAAAAAAAARoTez4W7Zj32sAhLjUkgas6AkwPAEmCIAAdEwAAAABsKLuHC8EzKQGlAB5cIQcAsgqAUoVB_xOFKFQABRLgAAJcFAAAALOHzXRBMuBIK0QlANQnKEiYAAYTAAAAaIZgAANgwG4cbOgTmuEUOAOgXKxXiZLmopC6UWrGzMChUrAihBloBRBdiNDAAESDAFLUgCQ0Ao6VBBPedCkCiNa5lQADkDzi0B7UIAAAAkNOEEwCkLoKQ8llEZ11EqPsnwEnjoAAIKEAAByCkEIFjdCEHXmMgAOiaC4P+JwnoqAKo5AP9GwEaPgAAKgwBElIR8VCKHW8LgarzKF4Qf3mzsUgTRqrMoXglCphAAazU30pAAAVBgxAASkJJQhFDmgCQGZSDXJB0oUkVgURr2sqAugAeSyQTVqEAABUGAGEpBGS4AkNANVlQQQUgUaSG2ayoqtW24P+M2sDyWQAAAAIikJQLgBI0hpKQilCsII5SgVJwKIlTBvKQs22wk20gdSyPSqoQuVlUAAAfqkGULgBs3_ysBb0qB6SkCjeQ2raVFVAqEzEEPIAVQAYcXAJvL_eMgAWTKxSD0cp8Kk4FEqZg3lMdqronTWZQhzJzA8lEelUsxQvK6JwAAeAq1IIcXCERAW_KgekpAoxMNq2lRVQKjMwHn_ikAAAEIiADApDMi4HdN_whAQyKgej3CoCaGwKgAAKHkAGB0VQKAf4QgdnZ0dsaUHxqQihwlBq+UoXg5nKNipWBRGoii4IJNp8tEEohlMpRAFNH_eSMAABsGAJmUlUCCOQqVhNHIpkMfBVVecNwtlC8IIazRiKG0y_4Ug+IjAAEaDgEdKQBIyAQZSE3sR0KQKrijZ2c8oXhFAIpoRuMoCw0IAAjQcXYLqUoWTJYEEsxUr_4XE0cltJFYFVgxs7FpdIOqk4skEim02mEolpCagRwACNBwAYuoR+pAKkFUxUrCaORSWQquQNnYqyheEUmkx0YilU2lmghTpGAAI0HGKA8lYIupAIJ4AlQqP_JwiwqC3ysEFAP_KQxAA5R8AARoOAdMpQsiSw_chbRKiKTRyKRaFUZBs7aCVEEggtBCIpVABL6EAARwODspqQG5pwAFpAOboSiXACB4ACDCEHACoKgqjECoPIJqKgBJdHoBHQ1MrAAAGAgFNFQihwVEyWEV7xUrDCPX5FScPJZnKOCpWAGIFYJMqUFSmADWYhkogAAWBgnArIuEUOI6GEwaikLLoEiehQqTh5Y44bySKQE1kukESgdSaLQCPZOngAMBIgYRKD+SRWF0kuKGJ1bp7Ko5UeSKwo90WioaNLQ2nEuh6RGAAX+RCPACDUEpVMEjOXJFYXSSh5KvojpB5IrBeLlMslFlobbaXQBCgRwCiElioALbUCPjnBiYBSF0YGSKw8lkhQVKxeS8B90uAAZYhG0AByDocydLegQJzaQZLUayOZKPTqmBWpoGOm4ISRWWSrVSyRZbVbDbS6EcPnZ+USOMQAZyRAAoVwAqWHAIE4NSKk49LoqwqT008lUmR0KQugS0Dj_xiBd6FkYmACigCd4oBzRn0iYGMkisLoWkkVl5ekqWyUmHWC8AAQ2ZhcQG5IRBAC_yENtkSbiRGElBVL1sNgVJ6aeSqCk2gUF7BQvqJyxuAxChE0AM6FRZjs7TgFiSE2KE4RRKFScLo5koeSq0M0dkXJFZ_s+LJBNGloHEwk0FUkR0ODxBgoAASEOEUOWeULwEAVJwuhaSRWHkqjDOpSE0ugAo2ZhcXpLwBhQgOgEdAADpCdi4Qg5zAkcgOhSFkjUVJw8m0iikhpZArowrC2kX+xUE2UgEik0gA5AjgCUFiMChOCRSRWEkOwYLw6lVci8MQugS0OJxRs5Bh5Gb2hAhLoAA8RZ9t4TAbMkVgHUiWDEOpZBXGTMALTGwelcgDLIXoD4EIAAUAWpMuJoVJwOsnJFYlpILRidSrWVXljMrP+loYejDGYnE4mkIgowCEyzksOHA6HgVrSBJVwhB32S4LVkwFVSY_+7BVUmACagALkPgkgAAAQyK5LGYQRPFScOosXySl1Ks1I2SKyolX_i0QSbliconGwlkA9I0MMI1NpVC1JksE1WxkvCShdJLjBOupVFUdCpJFZUQIIlOyL1hAQwhQyaYRqQhg3gidEliHxAnFcZLwkoWQIBMnDq+xQrzVRpIrKiFmLyEJfimxdLISRjQSSYRqYQSUlRwdqYGbJ5cbAROkLYkhCDmZEQc9JgLakxdQm2TAEkEoARS9B8ABt8iBmZAaU5HT8nBCDgHyFysJqx4qVgTRqScoXlOhoD6IQCSSTU6cAAIkGAUAJHQBIyAAzwA8WAAAAAAAAAAAAJuOhCDgGJlC8JrfIuAmjUmJQvKdDRxBTJQAej066BHAAESDFaDqD4Qg4BK+weAUppKF4EUesYLlYPYaDSUQAkk0yehAABuBitACQ0Aa6UKwmqxCpOBNmKeSRWJiGraWSTNQrtRWwrUxtKBHAAAPOEwPQKlYDVoxUnAmzFYpIrBSbSyK9GGvLDoMl0o1EWCgRwAD5GQAsC_1nIDopUDODYUgTSqGwpKobS6ACOG5VC6UcPqQy1CAAPkZAB5rpuOgPtlQEpCohyNpTWS4gmU0dlErtRBpSEAAfIyA9h5WGoI1KFYL5NhSBRF0bCkLaE188zBVqMylY3yhAASQXgAJCaJKwtBthUrDHRsKQJqpTIU8oWg2nuWgagXSiVS_6EAACiSsLQFIWgNj1FScCbMVikivlC0G2OS1_9GGoF0opyUK5QQEMyWyyA1BkZpwCzVhiMgOmlQApPITZBGwpEobQMkgPyCF0ohttCCagekRgBiWL5iTkr5IrS2pA1kppHuZ0ieMWRkisghpzYtV6KNSCV0olH8iEFJChgKo+f0knJFBm7HSkpAbEkIQcBeIqArIVATSshUAHuDoP5LwDfz4AAigDekhCDjIDwHtJgDrkwAdcmACDBsAAtg+CSgG0ABlcA3WVASkCauw2lIKTaA5AyWZDKQM5QtBDyBkoAcj4ABlcAeQVKwGrSipOBNmKxSRWCk2lkU6MNU7F3_hgmWSjURXqBHEDJQAZGwAA65HC4B4hUrAatMKk4E2YrFJFYKTaWRQow1AiWSjURXKBHEDJQAZGwOjoCA4hIRQ4ygqYqVhNWzFScRQfE2YrRJFYGUsk1Cek2oh3UCOFkByGwPgFMKQdKWEIODoTvKgJSBN6MbSkACCAAJZCflNtIBcDBeAduSEIOJ0hAADe3kwDEvyTAARQAHkGwW0DZBcAWOSEIOG0bBZtKA9eTANQiAARQAGSGwW0CzhcARiSEIOMgbAUQHLkisATsnTwMo5AKb_w6D0J8FtAH8WMwHUPG4OlTKYEQSRWE0mlyNqaBtDDB5ozgWS"
noncomputable def WL8_2 : ℕ := zfNat64 33243 "G6JgZAsccFoULBGAANMVADBSBeFQLiIgySQACKwQ+AAKoA9hYLQokg8AqVhVmpkipOG0mjV9xUrLELU9C5x8f4agkg2tOAACIAgWISC0KPIFaLlYDRQnzV6BUnDSURqksoVjZFKegPQyhJJof1ODCC0WioyxmBqppIjgwIqVhRFRkisNpRyMbSkAGoAAj9CDsTkBA4qBpSwkRwFIUZ9mxaCpOixCNJNGrDipWADUegAL7QiIzUcQLHFQSyPEUFxkismt_SJ41kpdMpNSQYN0vlCsD_RMNR6F9FIBr1lGDKcS6HFioO4+Zm6e5AIhcCIMGQWcXKwmojSRWFRGoxi5WD16iE_AAAFYpAACgIjDLwAppAAroGgo8gzwqAZoVANKI88qA0hkA34lAAAAQhIAJ2kPISkGJmwpAaUZ_GzjCpWDUkglQcRniFgkgHtQgAAVhwSgGi6DEKVmxAvYuVkxmodyRWT2oz03xcrCCbQAJIG0aCkAAFcSAACZBJC4BgIugAAOKgIoHYqDiE9i4mggQCLKFYAAKQkAsbWnN3ggKiOG4GAeOVAGhKFYVEa+XKjWQkBhAA+iFkIDaFQWqTADwKiJBgEflC8ByKQ6+oUxqKTWQkDXyy8SBEhgdQcik8ycBtDINPIgAQswASmFuxwDAQACx4A6A0AHQGgAIIACvi4AAKgATjiJBsiiQJTKFYTVZJIrAmqlMhSFhJoPQOJlvgoWx4SNDBAhkAgaUrABRcRIMFQFILuNlHFScCb_8yMmSKwKINRSBhKIKiQoYH1kLRvC1w0TMvLzMDHgBJiAKKLlYTUZZIrCojUHBcrExDQCmRIACAyUAAAYCAACZAIC4AAAHCgAA4UAAAAAAADwAkJfMDAEBggOVAeXKgqI18uVEUhoAAABkhAAAfIDBxDgyOVAzA6FIVH+RtKQAqUVAACNQgAA3BQAAVIAEJAFJFysJqMMkVgxqI1HAXKwADIPAAA_QgD+AsABJ0yheG_ipWFmawtJFZbSi9UwbykADEEQAAP0ITsHAAAKZSAJGQAkuAJCSGgBo2AAu7JUgAAAAAozAABGgBIS+YGEMMHwZuUKwikpCrVRSpl0SoFkTAAAOwQgAADm5BRJw6BLxcrCaj1JFZOaiNQ0FysAAcDwIEABXRkAAAHqgGCioQwRFiCoCiXOKgsIYFMgOoB7z4ACMhcUp8wMGwOA8BcrCalnJFYNeUqY1lIAE0AC6QRGAUgBfGgCS9oQG2LlYTUspIrTcJBRCiYN5SFRADKRhKqBd9aWejAAAtDgAQqXhAwGPyoHnHQpCojX2pUADcmIAAR6EAAC0OD5gbFZEBESRWFkFIcSqIA64+VDNE4D_DEAAGxCAACaJFzcgMQm8QGA4qVBFQ6lJw42qI1vqVACBoMgAIEIpIFYFdGQAAFQFQgC5WE1JmSKwKLMTIUgSXsLlcJoE02mErsjQwV0ZABRwsKGniAwAfCpWE1GmSKwAEoT5jKSnQ0Am4oTgTcMowNZQI4WUslEitHFDYMjMyAaa4AkNADtFQCESoxgjFEQiVAxEoAABiEIAAAA2VAEhpIkaDfBUEEzAVBRKJLYqAAAABYrAAAcgAaqAJDQFocEaSoDypUFR_8beVKgECAAAREIAAKUCJlQBIaAbDgWmULwaYdNxSBRYmYN5SEVrpNmoBBHop8ClAAAAEhoBcKBzZQrCapnJFYFEAxszlIGED4lRxiB1spPFamQaKAABKAUSoAkNAAACBUEbk4AgVCYho6gIQJIByFYAAAUAJDQ+hEEpBqR0KQKLgDZlRUrCkh64qAsk3+yESBQgAAJa0Ap1wAQaW7Lgs6VASkKjpI22+VARAADiWQMysAABgKAUifAEhoKgqAC_R1B0qCojXF5UF9B6ABVIszEIAACExIuwUNB68qAlIVEAhtKQtpxF4ZmaOwrtRCEqEAABoKGvk7BQ0CaShWE1S4VJwJsxWKSKwNv+locaMNQrtRIo3FAjgAEaCgPrwDOvBaDaC5WHF4B03FIA+UqY1lIEQFYEQAAP0IrgEAAAFheANFQBIaC0DklQaS0pUFR_8bbtKgMoBkCCAKRWAAAFAC48EIYLwFIZRytoqThVWUmU1lmDeUk1AAWhdTSd5OK4BAAAcQYLwFIZexHUAyRWUUosCNmcpAAaq4DgeiqkYMahAABCFgEUMl4SkspcDofpIrKKUXxGzOUgBCEyCegEvQjRFX_EIABr42SsYLwFIZewHUAyRWUUosCNmcpAAagPRVSMGPQgIAeRwAa+NkqGC8AZFSsMoKSi8GTKcxA8VKwAWwSMwAHHoQGEqg3weBmbqQRBXAEhoNQRURALaJgBbRMAAlAAX0bAABTgAIqO4LGYIEKlYZRzAIqTlFKI1HIXKwNIAOGjYEEAn6cVwCAAIWfvwDEXAARoGQOEXKwmpZyRWBRS+YN5SFmcgn4oXhJGpFBHKMUoCAAACGpAJSFLTYUh9KM_jZmpQrBLSQKgkRz+h9WQkj+0IrgEAABbJQFOUKwWSxXBSGkojmNinFSsoNJAZhIrCq0kFwoQABQgICmSgKcoViEFS2CkNJRI0bACKlZQaSApCq5vSgSWhE+koABokSPCUHqnyRWACUK41K4VJw0k2YlRJFZQaSCaCRWD2q0kegI0SOE4ViGlwDUkg2AfFScF+kisKo1MQVJw0k2YklJFZQaSCaiRWD29KpTpI9P+I0crwEE0AEAgXBkBuSclABaEAFLgBZUASGgAAAAAAAAAAACcV4AkNCCf6HgG3FQBJLAbR9KiKA0AAAApPgAADQL0pAEhoF2kqOZUFklIE3_xdhgaAAAKIDwCxWAAAAJDQ8RIrAsZQrDKHTJFYcSrXc2lIXGNgAAERABBQgAAACQ0iMTAKSrDMOiKlYcf0KFc4uVBIQAnIA9z4AAAAkND+FCcJIkCpOGWeyUOJRGqVShWVUm0nE1vLZzBqUQJKvUYAAAUlub8NDQB8pAIJpdALAXKwmp2yRWMSzURqX4uVgGyDImh_o2AuMjE1koB5hYACQkDoZ9Kh+CkQyKlYbSriw6lIAIUMgAAZIQAAC6FQFIipMlxOOn9FScMpV8sdCkDsQ8DkMEJwH_kYmpZAXsRAzci6GgOCLpUBKQqO0kaUgAAAaQWKwQQeAAFCwAtSoDoKAAAaTBrxCAGkwAT0DKA_5WCaDwAALWgA6aXWUCBcBSEIjZu84qTgTZiGMkVtOLikgKQJpRIIrhGhk178ZA9DaDz5ASAUgNXEFScCbMQxkisnpNMcGwpByXSiQR9qBHJqJQHqnD8qSUABzfrKyBJrW0qCalnJFYFHpxtKQAUiPAAFfQj9p0AMnHgABzfrKyBJqa0oXhNR0kisKiNQ5FysAAAAM6cQ8LgBaECAHIAcMmDJCkHDJgAG0LAAAkPhBhkAAGgAtCAClwAsqAJDQAAAGFAAAwoAAAAAACNBI68ASGhRAwkwEBhoAYiRSYAADSCwALFYAAAUkpAKu4yoMsekb_5UAxFqwBoAAAMoNALFYlAUAAX8aAApveFK4JEApCyRfKFYcU8KFcqYVAAMQAAqnwDYqAAYjQAAq4yImRgKQsigOnVFScOJRmqeyhWAH_l4FIAXBGAAI0JAuneJkYE9JFYWRjRUnLiUXnGzcUi6koCugAL+RiagAhAAgNAGBYkIiCdRUBIQqDj_5SJCFRQQAADrIxllYEoAGSBADYszqRAT0kVhZDpkisuJRYKbSk_UnAV0AAH6EaAOPvkwAGhDQCSBOCpSRWVUZcVJw4lGkpsKQCk10AByo9CDSbpKjgQ3LibGwUnuQ0BpyQBkhcrCag_JFYFEakMLlcBiJJw0XQAQIGsUYAD5BsARYqACuKgERFQFEbOVA6hYms1AAGFKQ+AYAAAMocEQVAtQqVgfnKg_qoUz85UBBDoJcAlpIKSQiUBQASEASQkE2VBKQtmbCkCiK42TmUKwHIC0BKSXwoRflCNAHATaSALkpeFpbCoDTkisBqIwqTgTZiy8kVgwJiU_mPhqKQDI9HPfCqT6BDA2l0sg61SuTIQkqgNQ4JKAbAqThu9KA4kisAoobzBuABOSUBQAASzIAqmlmTS0DJi5WE1B6SKwKI1IcXKwAAGoAOlInpZALGPAAZEllHisEpAgh0swqVgUQIRUrAo9iQiUhWaiD00InpZAAlAH5sAGml2pw0CgCpWDGavOKk5NSiNQpFys2gGEAAMyhA5lICvCIAOM0so5Fgc0VKyWzUgpIrJqUQuGzOUmUGs1DYKU8ugUUmhwSo5PaKDkaAhPwCiFDY98qFIDUvJIrBqTR4GzOUikmgxII_lSeGTCVQJKKkaOD0igVqIgpABOkALLlkDH5UCX6JsKSWlEa_LKgWhKQ6AABFCCHyEAFXVnIszYKgFIDdNjBkisCaCkCiM2NnnkisDDUQU2gQye3k2gwAiPkyOjs6BAK4RQ4DCrcoXg5HK+ipWUkSKZRGqni5WDESgAlAcSEyKGGLKMAAIkGARQ5eA8bBjBUkVhBGrdCpOf6RH5NzOYN5SB0AygtDoCAUYAARIMAAOpABjoAkZAFSoAAAAAAAAAAAAXtSAMX+lQLTF5V4Q2CiNX_lQAAAdwSgWKwAAEQYAvakAY_VKgW8IOv_FStTw0FEav_KgAAA7glA8UgAAIgwBqVKJjIBiFQuVgtNeaOxSAQojUKpQvBwRsATUBDCZLAIlAAQcCi7D7kEUOSITIwOiSKwsh2ipOHEozUUhN1KvPQSnsUK5NQAaCMcqGgAABImRn+kJsBUnCyHaKk4cSiAo2bikKs9BKfpQrk1ABoIxZAYAAAcZcLo8qkgTgP0oVhZDpkisNpVp2bSkkM9AAAX4pAMQGZEQAjS4axZOBMjCCoEkVhZmr+ipOG0ozU1RUrJDNQACIxWu6cEUWhNMIQIDGLgAI8XkQJz_J8KQsh0yRWG0ohOOG8pArPQAAINpw5CYHoBCB4GQthoSkMz5mxUnO6qluayUOJRGoXyhWFkBCUQ0kxRJZJCTulGGIRQNGlwI_EycCjkisLJDUkVhxKI1OeUKy+i8B_hQrgSQCpoQ4iYAAGEMhKDKSRWBGWK4XkkVhxKJusqAOpDxRAAi6hBxLIEFSYm5unW7GpCDnyRWCvVLYMYqThxKPCzYA5QrAD6DiMoj0AIPoRZHoBbsaB0dGQJJbCKHOMJEZPSvkisLI5O6SKw4lEapGKlYbSCAAt_wnBpGmmTwAIOBRVnM3Cn4ETqhCDggBwWUKgI+FQf8ThPhUAeS6ACBEtHwAAbgYAAS0F3PhCDgUhwAAECoPmHQP8mAAqAQAApHwAAbgYAox0BcKhFDhOCQHrNHYDkZxcrAojV15QvABSOQCO+qCgAARIMApI6EUODKHBKA6AdiVAURrfEqABSOQFoBGpG5CAADcDBKXldKAEhoDcTI5BcrCahTJFYFElhszlINaLXXeJUxBaVUkjlBiVHAAADA1wBiqBMKQoG4IgDwEQAeAiAAUgAIIMgAAMgwCKHAK3KFYTVT5IrAoi+NmcpJbTTW6NMQ"
noncomputable def WL8_3 : ℕ := zfNat64 30588 "iNOAYCAUBANQArNDoDKDYVHQABuBgAAgnQAABgIAGAgAACIUAARCgAAAAFAQAABgIAFpUAwEAoCBVhUAnwqD_ycJ8KgAAAAWKwAABgIAAABEKAAIhQAAAAAAAYCABgIAAAiFAAEQoAAAAAAAAQlwDAQEKyoD2pUFR_8be1KgABeFAAAAABgIAEJcAWUVAKWKgJopYqAAF4UAAAAAGAgAHlwBIWG4GAWUVAKWKgJopYqAAF4UAAAAAAEhIbgYASAz9yoDy5UFRGvlyosQJAAAAMkIAAAiQYBWxcrAzNQ2kis1YPVEah8LlYAJPEgADjJQKeDgSAABJWAP1KgPDlQVEa+HKhhwkAC0KAABghAVQKAAjYGBkFBj8qDgpsKQqI18uVFfhIAAACChAVAKAABoKAhWVAe1KhhAtUf_G3tSoAGMBwAAbEIAAjQUANBV8DoPWlQf5NixkismJR3IbSkAF2BQAAj0IAAjQUACFSBoKAx+VA846FIVEa+1KgAYwFAACPQgACNBQA0FNOJkYFnKFYWR3JIrDiUf_m08CpWADGAoAAR6EAARoKLm5OQggY_KgecdADKFYVEa+1KhUQkAC0SAAB+hB0oYAAAUlYODQDaC5WAZjpuKQqI1LUXKxSwkBMQLIBRE6WCchBYAAATFhCFgqDQdrKgmpZyRWBR6wbSkAP4GwE2dNYBVUIAAAAuVAExYQhYDH5UE7DoAZQrCojXl5UHiFgADiH9CIBKEAAA_SqWPAb4NsKlQOAOv_FSsKiNfslQAAAAP0ICHQcAADQmyii5WE1HCSKwqI1GMXK49ESWiIAAAOMlAFIEhCACnOPwb4NsKlQOAOv_FSsKiNfslQAAAAP0ICHQcAHOPwb4NsKlQWBNhSFRGspBRSsB+mYAAH6EBDoOADnH4DH5UHPzYUhURr4cqIOFQAAAjEoLaEB5hoAAUFDwDZLCELDktA1GOMl4TUyZIrG2JVRGspAAMYkAAHZGAoi0qgDoDQH1LBcrCajFJFYVEai6LlYVtILAAABxkojJXYeHI9ANBCFqiA0C5WZ3QpqfkkVhJKIDTBvKQAnAhAAB6RgHTBwAA9SsHBptSZTCCtouVlBPcdNxSUWmjURhcrCEy2Y1EAJqo1MnhFEsihcSgKVVwoDUZhCFpaBSSheH2ajbJFYVEahILlYATgLgAA9IwEOg4AAJ7MBALhCFpaDRSheH2Nx03FIVEaq0LlYNQP6owACUAh0HAAKGxseAAVYIqpAEg4GgoDT0kqBDn46_0VKwHodqyVGZCIAAACChAAAALCoGgoPqBHBUBUrC7NXxkistpRGoBi5WAAtAogIVTgH1BQAc4fRYRguKVASkttRuwbSkAENCwAAbEIAAnREAoixK0COAGSRWF0atUKk5bSacA2ZykKaSmMkxsprVCvQRizxKjgAFTIgPAaCiKHcSoLomDoUhpqN9jaUllm4AAA6jKUgACdERCktyAtl4ASXBKA+yoNpPMqEDUf_G3dSoACsAkAALlYFmBwAANBWoioJSGUWeSKwY1H2htKQ3SMAHQAmgqlIFsBwAX4bhzcCCh52fgBNiAQrKgPDlQVEa+3KhbQkAS4SAABghAHmCgAAWnSNBUPiIKClQDgOpSFRGvlyoAAAANiEAAEISBGgpbAsFfSoCUhUcpG0pCkhgY6AAEahAABuDgA8HQBIONgFgMWTAASFUgAMoLQAAOnQAAAojQVD4SD1ZUEwDoUgUQrG0pCitHXMZOQCr_9GG2oQB5goALa0AGFQB6ZUB9cqRQBFRmv1yoXwJAAFUABSEAAEUeAD8aDY5UFgzYUrwBgo8WNpSAHGhoLKAd1CAADcNAB+NBFUqA6+VIoAiozXr5UAUSMgABqQgAA3DRCgFwqANFKF4EgOm4pXgDFRGpGi5WL2FgSZkAH2S__KgAAI4JBGSgCUhfU2CCSKxVRUUaeG0pfgJECmIBKBxATihAABjDgDUFhlCsK4mTpqoEkVhZJsxPkVK1xCQWQRISIwOJdDxKMAAGMODkAGqwKQ6ASkKiUzR21MoVhURqzsoXiBh4soMQAA+IwBHoeABQAkrADy4KaVADVlQH5yoKjiw2AGUKwhplCCAORyBiVgACFEwEFIQSkBcHQByhWBRGIbHVKFd9BYsLXmonoHU0hX1CAAEkNFLW0oaACzqEho2KISJgdAuVhNRIkisKiNRhFysAagABAZKAACKJAXUJAP4uVhNQ1kisCiOQ2ZykCSCHDhv8FWAskktujAABuDgD0WZgHBKQ+CbFDJFYFGsBtKQJIDkCTCxaA6qEAAYQuAB5HB6LMwDg0uVAzA6FIVGiRtKQJIf+OgJN9FoDqoQF0AAPRZmAcEpCbpsKQKI6jZmPAqVgANQKIEH0ICrAA+AMQobBmXqQFadB6LMyDg46VBS46lIVEa2PKgPptBaAADBCAPAFAAKC0T4NhZBAUAE5jpoRUBRGZFQBRJIAPQKAfAQgOAAADawsAcEpBH5sKQKJDjZ5BUrMJbcALwOQrpVCF6EAR4HgEFiIIlxBQ+a8oVhNQhFScCbMUIkiv+rUG0uklqpo7KJXSqRR5CNDFOCwAFnXlpaLaIF1knD8DSFysJqZ0kVy0qI1AYXKwAYkGJFYAEBEoAAIQkABouWUSmoMGLlYTULZIrjoNqI1HkXKwogAAOyMhHoQAAPQ4AK5WYwsndQphFMcXKyczUk5IrlolqI1D4XKycwEBqT08gJc1pXCxIAAABJUBgm5sFjSGfyoHwHQpBdH1RGvrSoAADyADpSAKj0AAVBWk4kUQlSE2YuVhNQJkiuWiWojUmhcrJzAQCeoEBLExOIIAJvLgZnQBDrBMGQbXKgJSFRgEbSkylgloBSBtASihX7JgAAA4KwipsBJCpWE1LOSKwKLujZnKYiLGUgEoxDaBpRGAAB6HBSJ0PKCOH4HZKFYTVXZIrCSTZirYqVgUQAQUJwNtr1oGMoQDRj4YgAMSbhoSJIS8KgcyERaKgJpHgqADcBMAAjI+AAsId8PGmPHYCkJrD0kVmEkk2YtRKFYAQUiQ5cJQNpVBR6BHAgi0G6jQMjt2ShkByfDoFxlQFnSoCSKYclQFEamkAADYhAAA9DiFJwD3rbCIF56DUi5XLSai3JFctCiYUwbykijEoM5mIlNMMFwAiaRPACJDiMSgWgpuZEBsEqEoEg6bikMRsVEajMLlYEvi4AABGoQAALhIAAJVvZEA6cqEodDKg3GxURr5MqAABAgAuVgAALBwAZD7jSIBhJUJQ6GVCENio_+NvJlQAAAxAkCEAABEKCU10iA2hyKlYHiRWTUfJIrQYaOwotLMG8pBsipTKoSQJpRCK2xKjgAEaDgAAsZDXTgiUaQqVikYzUnJIrIIpKLwjZnKQAJIE1NCkE9UYAAjQcRteASL4AeHAEeFUpCYEqFQE0T4VB0DoAIAcQDSKwAABAoAURMAGgYNzIFismozyhWFRGonC5WIoPoyAQAPxihcEqmTwDcBwJQJQXR4DCnAuVn_lqajJJFYFFmJkKSMx0F0GoSE0mEeQjQwACWjQAGWYAkxAAUIC+XAnyoKQABAkwf6Rg8pMFkOUrAAf_VgAAJ4PAbRl9eHhoAk4gEBsYJcA_8qAyePKjycSKJf3BQANQAANiEAAFISAApxGOXHuAoleVAZKMjSk8nEiiUhAILABDy8AAGxCAAFAHABc4gAZcXxMfSCicpUBkTCNKTycXIJEcSgkHI1AOykAACZCAPMFAALVgENSAHESXnwGPyqWjzjoUhURru8qAAAJqA8UgAALBwAh1LGkIGorYuVy37A1NSQkisIJqFMaykACLHQIpl4sndbRgAAhBwAGNYAmXMOfA1NRlUtJCHQpCojXhZUWR6AAlAEI3UIA8wUAD9CdhDPWKSqQBsufQNYlRdFs1DaSKzKVEauELlYAAAAPFIA8QUAXYEn4gBCkAtLz+TjCAoyIOoKQiAAAAAACjMAABMKAGgrDNFmpZBUXK5a+JivzU65IrLLURqZAuVgBjQWAAn0lAUUBBiwAJFYBOXQMNUUAWFyuWl2ar3JFYZaiNQZFysogARHIAFjTgAA1iQAAVYDyZsmNO7RgLcXK5aTU55IrDLURqC4uVg5AFJ9IIA1WanAAQaEgCwq_8DTyUYJTLS7NWOkisMpRGoDi5WIQAyRcroMlE4mgZ4RgAAhBwUgIVWwAeAx+VA846FJ_xiqI12KVAAABROrBFIAAUAcQpOCh4AIEpDMiKAnC5WE1LOSK7athWKKPzBvKQAYKXAAB8RgNoAEQGX_EYOdlQKZNhScS8LxRygbSkAu0TDkABDKEBxAUsPEyAXioPZGBZJUBoMqCE9FR_8bedKgNIIS0hFAMMrAAAuEgBYmT0nTrkYJT_hmMRmxMSRWfS6UbUG0pAagHUloVAlikAAKASCUCjlVVGzMqhRfmULwmlfNHYpW8wZyojWUlkehNRuDBvIppAKInTwACNCQZMbMx6E0UmUmqhXciaN3FFSe000mzFuJQrKpVQWukGD5hoUdW2sk1IoBBC1xcADgLMEyHoCkCUmjdu5Irca0bwmzEShUrCqmfC4AQwfMItNs51kCKQRSE0mgAKwTK0yIoCCKlYCEXJIrtIQZiJoqVh_RMphIQNu1FoL1IxRW0jApAFBzIehNJGSKwGqVCpPaR+pk8mzEUhUU3nwtLINGy6G2qkxUkjQyqHUogNcgTgzKjpKAAdaJjJYSMGPyoF3HX_ipWcSojXl5UG0AACidWCKQAAoA4hSkrO7lBAXkcewUARsoXhNRhkisKiNRKFysBaFlCLcBIigTLRgQgdDaxMABveAFaRQBwfyglFFysJqjMkVhUR6AIuVgBujocgACPQgABEjQBdlIoA4ahRKcXKwMjkUgTVRFC8tJQvA7B8f8OgAAiyMAAIkaEMBCFwBCOC0K3EhB2cqCqCkNtRsYbfLKgIIAABrlYLL7wSAAJ2XAAZILQoDm5UYeViUhtqLXjbWJUBBAAegGuVgMIBuiYGQLHHBaFCwRgADTFQAwUgXhUC4iIMkkAAisEPgACqAPYWC0KJIPAKlYVZqZIqThtJo1fcVKyxC1P"
noncomputable def WL8s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL8_0) (dpk j 1 WL8_1)
noncomputable def WL8s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL8_2) (dpk j 3 WL8_3)
noncomputable def WL8s0_4 (j : ℕ) : ℕ := dsel j 2 (WL8s0_2 j) (WL8s2_4 j)
noncomputable def WL8 (j : ℕ) : ℕ := (WL8s0_4 j)
noncomputable def WD8 : ℕ → ℕ := rdw WL8
noncomputable def ready8_cuts0 : List (ℕ × St × ℕ) := []

theorem ready8_cuts0_ok : CutsOk ready8_cuts0 := cutsOk_nil

noncomputable def ready8_0_state : St := ⟨26112, 285696, 28545, 39936, 52016, 112124, 29666, 44151, 29666, 44151, 29184, 45301, 28545, 146758, 26112, 106247, 54657, 325632, 106673, 437756, 136339, 467422, 166005, 497088, 195189, 542389, 279232, 601531, 305344, 707778, 80561, 152060, 110227, 181726, 139893, 211392, 169077, 256693, 253120, 315835, 279232, 422082, 81682, 141790, 111348, 171456, 140532, 216757, 213184, 287290, 239296, 393537, 59332, 81875, 88516, 111059, 117061, 235274, 143173, 341521, 58850, 81393, 87395, 205608, 113507, 311855, 57729, 175942, 83841, 282189, 54657, 253005, 0⟩

theorem ready8_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD8 ready8_cuts0 115 15236) ready8_0_state = 66257 := by decide +kernel
#print axioms ready8_0_cursor

theorem ready8_0_covered : Covered (toCl ready8_0_state) :=
  ready_cover_cursor WD8 ready8_cuts0 ready8_cuts0_ok 115 15236 66257 ready8_0_state ready8_0_cursor (by decide)
#print axioms ready8_0_covered

noncomputable def ready8_cuts1 : List (ℕ × St × ℕ) := (15236, ready8_0_state, 66257) :: ready8_cuts0

theorem ready8_cuts1_ok : CutsOk ready8_cuts1 := cutsOk_cons ready8_0_covered ready8_cuts0_ok
#print axioms ready8_cuts1_ok

noncomputable def ready8_1_state : St := ⟨26112, 533248, 28545, 39936, 52016, 170229, 29666, 44151, 29666, 44151, 29184, 45301, 28545, 146758, 26112, 533248, 54657, 573184, 106673, 732022, 136339, 761688, 166005, 791354, 195189, 820538, 223734, 849083, 249846, 1382331, 80561, 198774, 110227, 228440, 139893, 258106, 169077, 287290, 197622, 315835, 223734, 849083, 81682, 199895, 111348, 229561, 140532, 258745, 169077, 287290, 195189, 820538, 59332, 81875, 88516, 111059, 117061, 235274, 143173, 768522, 58850, 81393, 87395, 205608, 113507, 738856, 57729, 175942, 83841, 709190, 54657, 680006, 0⟩

theorem ready8_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD8 ready8_cuts1 121 57) ready8_1_state = 93963 := by decide +kernel
#print axioms ready8_1_cursor

theorem ready8_1_covered : Covered (toCl ready8_1_state) :=
  ready_cover_cursor WD8 ready8_cuts1 ready8_cuts1_ok 121 57 93963 ready8_1_state ready8_1_cursor (by decide)
#print axioms ready8_1_covered

noncomputable def ready8_cuts2 : List (ℕ × St × ℕ) := (57, ready8_1_state, 93963) :: ready8_cuts1

theorem ready8_cuts2_ok : CutsOk ready8_cuts2 := cutsOk_cons ready8_1_covered ready8_cuts1_ok
#print axioms ready8_cuts2_ok

theorem ready8_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD8 ready8_cuts2 128 1) (ofCl (RC 0 0 1 0 0 0 0 0) 0) = 128897 := by decide +kernel
#print axioms ready8_parent_cursor

theorem rc8 : Covered (RC 0 0 1 0 0 0 0 0) :=
  rcOfC WD8 ready8_cuts2 ready8_cuts2_ok 128897 ready8_parent_cursor (by decide)
#print axioms rc8
noncomputable def WL9_0 : ℕ := zfNat64 33247 "BtYL_SQZL18s1GmkmegABwiiSgyqwVUQgE6oQEETqhAAQRCAAAVDAACiPgDA4FN5KNapA0xCAMahABjUIAGmIQlAA4iEBVkoAIEiZUt3UBiAMY6bhMRyoU2ZgAKSSEkoy8TgZCJDDcrGEq__Tg_AhAbOhYKDhIFPmz1KSkEixIBIYkAJDEgAkWJAAJSOgALKToUSUAqGBcxEA00iAGmkQAtOcEQDkAxSEAAKJCA1UU4PIMBviBcGpITKUQQJdlIqkaTIahkkg9LryVYPgiQw21Esh_JCAcUXGPIMIychRhqgTCWQDcrU2RKRVARALEx6UEwkkL4iQw21GqhwxCAkNDwl9wuYchBlwIFF4hcrAIApUyiALZOfgZnoGEkjwESGG0nIUcQgLBwNC5WQQJpRVWBSQRqQpIhj+Uqa6i5WAFHAj0Asp+kINoBChCAUPMPgpoEpP6p0ZlI+ylKZpKxdP_LxTQIIDhkIPIBbZGA9BA81kAYlll6R0H_04CIxUARGKgA_+nAATOPriAAA+pjbEAA5Q8HCAJDRjQkFBAXoPAC9B4AKCAAAwqAACxmzmjmxkAJjQP8SA3EgAoQjSkCiOBWroULlYBRAAWhRkspALQKJGjMAQAm3AAcodfJAIBwUEBeg8AL0HgAoIADzS4ACUgAIFmEWgiJwXZWKIANShWBRKIpAKIbFMphRSck3YqNbQQgU+JgApDQqy5gvg1dMpgA3KFYU0SaZTFJWSmjx0ymWEJyMZOIocaKAX0gTk2BwHwNFUgDAlQAYEqABoqkAAbZC7YxCUmgAB2CYYhGCQgVRKgVIfP6jVEqADIAAHZKKXbGISiEA5CMALUWFUHMhAlID0LKhPFIXJPHcS1S+11GJoDmymEYkgR+2MQGaCTZ6kBOBuDB2s48jhGQEISyRWCDD5uTSVkisKLVaKsZOlkkm1E21l1yZLIJlLpNrJVDqIksAA7xxGAKQnNpFIUiWL40SkWimkUpJxD9KEGmm1kOmJQHgPDGA5SySPQ00PANYKgBrBUAGO04AAwZ8AAdpGAB2NP9JQAdID4D4CpWA9JoGyRXIQqoTQqJtg8xDgkCOGUmgR1SgdMxujASocpglBhwIFFfJQvDCVEOhUrAHJUQmsFFMtD6b6N25iEs1D_4UAASGmdkoMCBRXoXKwKiOckVgE0V+kTwCyTSNyBHCKcTSGSUoFwuBACQ0AQFgATkoAEhEAAkIgACclAAASMgLQNAAGgY+WJJGJoOZQgDrEQAdYiABzKEAAfwyAAcEPAHEXj8YrpFwAaZygEqCklOyoD_ykbeUgACrIVxCKAYkiA0A0mQEoWYQOGqRbSUn60Ko1tUsqlQFNDDqRNABFytcSmgAPIgAmDUnowjxg+FNLYsm8FIUSaQdQnqaKlZNAohwU6mWQAoCjXEJoAFN+AHRo8xp_IkDRE6WAKQJpNFJQQmjRE6WfLQi6AmJGhhpOIDfjZmAImyCLjQMKWUZEgJoApA_2pCkACafQ4gbCQgsmkACmbm52BGQKqHaiYOzdDB8KSUXrh8c8oVlRJtRLKUKwCiVEwgDPlKsaMZYrJf7OQAB0UIBjN_WYOwLmqQEpAo6vUpSAUS5qkOQA0ghGWK_4YgNimQA_VZFxuJAhcGkTyWj06JIrJKTRtpk8Uj2yhNnpJppZRSsWyzSaat08hmWK2G42G2uEJkYCaY4CYSAL6EAfweAD+DwAFUABCRUAAgQCkizCuUWC36dTBaSknpNc6pSkAG2p1P2CcFkslEqEhEkqplAAENxAA5bdTJdA0E604AkgFEAJJelOAAKGdBJAFbGwAhtYAHLbqZLoGgnWnAABRJIBJL0pwABQzoJIArY2A5HmUK6SIYDANgxzWQmfTJ91noZJrPUyeNTCEWah_PIZBIslGIVEqlTyGatUtkUomUkkUagJAxgAsuYyCJgAIFBFIAoIpAATQAASH3+DIkgAGYFP1gC0sAFj10AAT57BKYKHgCAqcADBl4AA7R8EkAQcfAAKTgBZEAiFgAAAAAAAAAAASUgP9lqQIENopAEEQrVRY2AAQBYmUQCof8QiySSzUQWAkTwAFcSDdlSBAgCUIKwlaIgAAcEidNAQouKgglkklmogwZGhgelaVqZtrJLoD+FEwy260kihsMl4eTJecRSKIGQqw4MJkkeiEKhGEgGskUo1EqlEBqJLAEBrAAdIDfL_6dUMTgPoF0TYA6abAAAAVL1M1ZJJZLoFUIVdahTP_M15F2N2uuy243Ggy0BZUvAIrUyqCEQx2qk9Fotnr33T2OaCUSi2VGDZI0MACSsACOgBxcABIgCQsAAAAAAAAAAAABMtCDjtx1GpBdQCSBQTEJUMIoEx3UvAtKoGRXTSSSyXQbUsXw9527rJUKYXUoopT2YhRLepTRiZWEkFpHTCEWci0eGuW3lNV8klmogTQAGJwB0yACDQAAAAAAAAAAAAKmsCHr__Zs8jwHUDY58AbHPgALIAGSjIYi0OhkAAA2s6gW0EOfjp2jM2ZkpAsmzOYg9AoNZBhacDTW7P_hMpk3Y6dPQCIMWpT6CFpFwnxBXybMygjkYzUqoEEk0UKaAIVamSSCORzHQBVoJpNOMpPVnnzsh5kvrpBmstloSSizmirNTI9FpJFntJh6pVxySZ6OZiAEAHq0HqlPNEfQ6bUX0t3MFIBitFlsZkMtkItJ6OWuoUeMime0Ge0WqlZCg4dms9HttUZ0xs_Cb06nASDOW+tGdS6NLoN1lpFnJNmMtjopbibRkOiFCgcVkMthopkoA1qvBQ7LTGixsWy10Rs_CY1CvATiBtXSc8IbtcpmotoMdQpNSQ0U7r1_kosU+hxWk22qgEQz0Q0UbeeNxTYCQZy11ozzGgjleu8tFtBsshFWvW5TQSQnHAn_Ij81qsRsNxJmtV4SKabHSrXXEnjcBwVHcDWbiP9ozl5Ye7e5aRRsLVsmzGWx2agZRouHYDGRjLYaHYDAW9hQcQx2MiGMymNn4AAt4BrtCFEqAxxPgSyxxQrZefruU9opJnMNnoPT_gEKYqFR7LSUh2kxEWh0PgAzFpMQl0aP30g2Gm1W6sTcu9JooVl7GWR4r2OYx0a__JjYixt_pAfgMZmMhiMhiJc2KXBZLJY6KZCi42fiqnkOtRApNRLpZsJATJuT0EMlAIZBSIRK8weL6lY8fAUtkIlASaNLA0AEEwAQaCokj4EL6W02zWq3E2mVZ5szKCCEupEnAMdotBEIlip60rH0QCHslEopCSn0MCzUDPXHjeBqNxYi0Zy83mWj2qk2Yy0MjEZGFDxyDyOEhWYy0AymU3kAx0QxGSy0AaE_AMAHEzmIifAl8G6ul5ustmJJHIVQoTQQ0HAx0mkUM0k2jDUq4BmIlEKFTB+MINn4ViNH8DWbi_Zm10m8ttdvctHNpsshK+vW5qARu12mQnHAyWs1WI2G4mbWq8JnoWzp_HSLVYAGz8BwUACcQBkSAAhwAELgcDdbraQ+3mW02m03_pYzF6ZLxD6cgPkdU2SI6KGQrFYiGaSy1Wt_3AoLAYjBZzQQPDQDvTqIzUaG5saT+hP7SU28upKl49oJNGyfO5bIZ6HGojLQn4dIN1wNlpNJgspMNtrI3lGhhGegBibSaCUaa7doz08Tp6fk6fy2skGay2WmkslFnLs0aGdbDSSLPRYpUeqoEPrNjqKKEaOPaCnkwbg6AgI57VnqoANox4EJTKTzZ8C1W5k3AptBptJCox0RgwkWg0EggSUWJgWwMsUCeFMHUGEkgnNKmYORyMT8lTMHISSCSQck0mkEmmEkkEkj0amjhImB4ATRlbE4ECf8SgcgpBi0A6fg9PEKwWQLo9C2gNSCFxx4Dw0BgUBnolD8CBAYSYOwIoxYSYOwDzLQSQNJNAdLZjHtJHpJBBwYLA1daiFE6l0oCJPNYhP2bmSsBTtjHo5GLcypmTRqM4QJY5JL60yGNaSRSCRTgpGMy0UwmkynVAgCOru1CmFE6hJsueQ0THSs4kEcjE9R0rppJCTPSSRRrAlWKNJMN9rNFKNRKpRWEgRwDAt1mu1EE7sHcAckgE4GI5AAkgQuVgdSycyilkC5SMFIKWglXagS7KlsKt1AEoWQYkgOn4AlEolAovAMRqCtZOZporHE6mk0aEgRw9BpeMABwgCQ0gwXRg20tAAAABCQAAAALMfYrqFcD6FGIDEOYePxRIMoRxiOQBaDEALFJR9NNFKIBlECOAdyHgoDY1j1likB9A2KhAUHYqEAAwBoAABUMAAFRCAMDBwk1s8hjzUK4X0AHQ8bPtBGJ9CI_IQCwoEb7EAEGwp9WaCUaiDxkaGArWJw_qJ3JeQVAfwkjmQvCfqSPRAgTkgzGQH5RIMl_oOIwyJxPIdZopRGJZCVIEcB48NIcPHZGi5WCBJ6dUCfR6RQGyJDAAklUmoxColJWeQ60rVFMptpIRY4bgSFg0TOLQ+IqLAWQOI_lKmACgUJ4AGwVJ4ExEJTpCIiG0KcHQbgMHWGh0R7ncWA46lPCKXSVgogJBMpgBxKoAf2emfnj8AAKRsEISDzYCd2MuBhQ6ySBOhw6dgYROlgJSKlYf6TiilIqVgVETgrUzCAB40LA1GOmkAAsE0ADjk5DsCcAvsmAF9kwAdsTiKADqToADSBUAlw31RKHmePwJoAnipOBzhSlIAhKKXQHs8SIHp1OguW6acQUgaMwBJMVlpE+gilux5DpoGRyKSSkkmrNJFc9Ho5qJ1JiqWyrPZSUTCTXpnkM4lkcSZLV45bziYRCHNpEtuZ5DCiTQoJPSRWZQmk1ApIrPIVG6__WLdhJTUTDSpOMCeQziFxark042UXYRIxBK48AA5Q6+qCgeEadBQQF6DwAvQeACggAMaKgAANCxSy4BKNBQNSAOMVKwKNROMVKwP_KRQFSAAESjIqXgAAEJCAC+hASpKgKjKkqAAL6EAAGxCAACELAEfMzKYkOLQRQAPJMA9A8kw9AegABJIQvCoPgAADgjDiPg3KjAPeKlZPaTUXvFSsCkirUSWAAGxCAAAAKWTxMRRFoJIAF0mCggXSYCggAH+048S9_9qFJJAmwxAABGpuUp4GKSI4YkqOTGcrGKlZPaSUUhFSsCkzkUSVHAnsxV8iSxAgRCel2Up4NgUZWEiPgJEfRwBSfSeqwTq4pAoI_Q+dw0AOiIRJhopLIMqRIYBRg7BkSGPSkyFOQHqZdAKrSVaCTeyFU1nIPS7R9DQAJEhEmGh9ADBkSGPQUlQPnZSM6mKpipPaSbQSbIckVzWclBmM5hp4E6pILQXnEMkw2amkFpIkMF7sdAYEAFowAkyADlwAcWAFiQAAAAAAAAAAAhQAwZAAyoAiLAARIAAAAAAAAAAARZTGh8bHhBKWG4WZoGEwoIMAOg6kisADqSKwBgB1QQAJyAAyIUJg2EErLIhQmzQMJhQQYAdB1JFYAHUkVgDADqggATkAANwsFIOvm2YEo9BwUEBh48AMPHgAoIADzS4ACzAkDs6AwsXGwsWHgMaChYeOjZTGjozAgpSFmseGgIe"
noncomputable def WL9_1 : ℕ := zfNat64 33247 "BADkAAjcAE1gAWcEdGgBoMG+fBOhSAPQVIEA9BVOQBnZlEQACI1EBtCcGrI0NkyNDKJVO2kTzCaaaKTiUSaqpSnt6KlZNJpSRqMSLUazZSiVk4fq9QI4pIqdF63QRiJZqDt3R34yUgT6aQIufx4QgKIHyyoAPKVR+WVAAKQAI8IQABJjJWDoaDwbhYNREFTlIBOJUBRE4lQAFKMgAA1IQAAQINwsGoiCtakBfMqAo1G+ZUAeQAADUhAACgQgHAWBMNAIBKAIYRABDCICEgAACYyAACEXBaChoFiEh5FibKwAEVEhcrAo1VsxcrAKpRaI3AAWbpKQDkAvRg3AAFVDgLCeTgTYnAEBJgAgJMAEFC4AAkZ0H+2IAADQLAGrqyBGBKQnrLFanKQFPIwPQFIDvkYfAsCmegfVKE9VJ7BcrBEA8fADmUKwnJReyUKwD3BdLQCCDtkaGOTSZa6CKkqWTYAWVgDSMRkXA30gRgFUKlf+FYHpRKoVKwAGIABw0COLZ6YayBgk6WMXEwpAi4wbAFJdByPZSnikigNQD_x0BUVCJP+T4uk0NfpQAoBp_CadxUEcBxGBJAqVkkej0oyQKlazEieAHUMgAStCAmkEACV6ZAjA6GULJ0sp2RCkuj0clIUp7OyhWADkLaxbJoeVGpoTUYI0MylEu1kmgM0iWDoLQmxMNgqENAZIRADJCIACiABL46AAxofE6CnY6DyLXQMis4ECizcoXlVCrKQmhFBnHjMAC36MO3PjCAHtIngWDcLBAbgd6oUwPglQFGo_BKgAHoYPwAD5IQFUBFKMBsCDgLBgagjOpAYlKgKNRxKVAAAAA8UivxkAB8NgFGQJ6LPGFQAEVAxcrAo1VpBcrALpRtU3AUkLObFJyw8IQAvRg3A0ANSw3C0E0ICiA6cqAojpyoADCAAf5CC6AGiJgABfQgAUDwACgeAAAAA0VAAACg1JcxSBKBOX5lQBkqqdKgAnIAC_0Ltx9QSDL9WB7BUAW0OKPQIYWX1pE8rqgUaUhxLN31CvKQu00k_4Nq+HkMJJLQgsHTJ_bj4giU6gMQBJDSSDRChgTQYahbBSITaWRZKU82BUrCfqQAxALICPQI4LSCaf8Lw7MqAG6rG8nwB0CUhZ7onZcUpSFQADBYrGIAOQQi6bQBrZkABIaAAAAAAAAAAAANXNgVc0B2j_+JpsHwf2HgNomwAA4qADIADkOZnxpKNFAHIFcdYACnBPJodQEIHKC4A5QVAB_guAAM0ZAAXgKhNQ8nkMAyBNQqimIvQDz_0ie95CAIKSQGoLMQoZpLJFMIKqPnYHKFoodNMMHySNRqO42blUajUOibKFdJJNJntVMLvEqPRTzJUeg00ml0RoZpLJZtJdB0FSsABlkeRkaJ2CthEAn02AFLFQAWEABg58FGa_+VgAADcQAOaMguCI1AKcSAt8lAFEAAiS0AADo6AABijB+p1s96DcQkTCCBdLohlLzE6eAC4GrGABMNCDCUTSGE1ITkDztvBiHSyNZC58iPioVLY1EIBgJLZjDwNIYTIyySRDFQaGuNHYBqIlEotHIQUgTgPCW5PSvbMQADQC50TQyEQ4gAmI8XgABNCodAvCPCcjfZtYTEIMxgJZpPdkKGSX_t2sAmM5DYnSUCowweDeCAyqMRiMQLcTIw3A2SupB7JOApoBaQAloAATY6MQKJlQAwFrcj5+zlqzgESSKQCfFMllWai0yvect4FJBqQi0ih0GhEDIBKIpcUSIxaLSQgDkIjkJbZ3AogUEs20ODprLk6Z8CDhaADrTQAb+FEkekEBHZszHQEJvDtvCqhtd4zUEs200mVG713AN4GUtMoCkISDUcgAABToBsoVWehObM9pUmfQxybTHOmsylPeu94jIAUi3_RcvABhgELFI9HoxBDiNHAAWLjrt27WSa7VSSYa6AVCflWk7RrNthZu6cx6SRyGZTLRaNRzHZbJRGhAMEwEAhmsw0TCKh0COA5kR8pqtTHtVP+pV57Wa6ANCfj1TahPqM1PeAhx7SZyGZTLR7TR7HZaxQyZgLCAZhvpxJtVrJmEaGFAkR89atTHpu1KvVZ7Wa6DtCfz2s2GmgEe0mchmUyke00ex2WykBYQDMN9OJNqoQFKuXZGhgOAA5chO2pVyolkgnuVM5llwlQyCZbLWcCBdoeFIlswiPySB0FIBMJ9OJNKpQQHAC8sOidDjKvVwpIVSwlk28pboLux9ABiMQAE+CAMwn04k0Awn0MBwAMdoN5LTXS4sQZgmmz8wnU22FLr13ABSLQaJRRA6AaBAGYT6YSCsxSCKBo2A69odE6GdQtJLF9BgdypObb67eCsN9ABiLQBSBfBAGQSSgBEljEGpI0cPWBOE7b_+ORpMNxOp1NKhP7qbTrYUVOXcJsHkIMsoKGYtMJJIIpBaFAQBkkgkEYj0bgjRwPFtCyme3YFWmSxAn0yopdvZ2koAIIAFXAIKJBGIb1RgPDwEhPQMJPU2TqwbMC+iBWDkn8fAF9ABRjgzAAKiLQCdJEA4OAHTs2zq6hHQGNlysG+HC8WrdQH4AAeZLYAGRgKoiEMi0PHEwGgJi7C02dh2fu4BUmjUMjvFjZZJIpRqTIx6BBECZUUJQ5CaDlugQDqIhEJVBW5InC0A0nxrKF25lEckqGC5NGoZZuRHyyQY6KRAoD8kiUCrYeZLF8ijEshxwNRaQQLxCWS6SETm2gxDpZGqWiBO0UiPioVLY1EIBgJpV618_GEwmEsnk+nENuBqI5HpVKojkgTgABvg5NHdpAKglisBrJBGJZUc9dwA2mE+C9FxItt2BKs5npdAoRMjE1VC1bybKQzjB8mi2QihQn5ZHstsLInr2bJOl3k+2GupzYMZZPJ9MJdMOBqI5HpRpow0gTgLDogCQsQxcB4yAMw8AACO2YAUnksgAVhcgAAIQkHALOGTx9dQEIAdSxP_RaJiLQWIj8ACyAAfQazksgKQNLwMEWyxaG2924AGDBcCcgXKLiKBFgaKJZAA8IhAABkGw6Thuah+7hfDh+GSiQRLgSyRRSLT5lysO5HxRJppLpJCyE06CNDMJRIphMorkgTgSx2dYfdgIkKGxkJ8FUslEWiklSI_AAAz5rk4rBTQjyhBZADyAIT5kAqGCpxEAnNaAWiDj4ACmNQAAbEIAAKikBoWhsap6B2RMAcQAzoEAEEGoAA1CEf+XgBBCkBISDgIaCx5WGdMooiqEiEAlIgKQQQBJ6JDABWiAzAAb6hBhLIEiioNYm7NaMjKIQZcCBRZuUL_ToQFWUgAMQBAKFsBpoEcMobQfuVAWDcHwVED3JUV0u1H3JV7wmADOGQABvEIJIAtYqA+dAAw0IIAPTJ4DBiv0UUhxLLXlKedcoVjEugLZiFDM+4pE0og5OWgRyqYTCbTKXVKgzl7kFIqQAlDDsmUsrAAAOKgDIA4qAAQkkAJDnwIYDn_5KAHgkwAAeoDtNB+A4pHoJ1SJYG6yq20Gbgq7rKv4LwBV5CMIABlIopAaMZAGtYgIM0Aeih5j4KiAYYiX5UHEDK5fSCpSkQgf0OhSPQAo4hG0AKYFwBLOIE1NJ8HQE0B9JMAIpJgAFIACnTr_jsAD3iYDaRJeCD4DBjBsCU1UE2KUpAALIEkPQIR1LP_k40hpUqABpZVKhKwOgtaNAIrJgBFZMABRAAU+dHH_isAAAAAAAAAAAAABhIOHgEM9oEoiSSDQZqPEqd1Us01EJQrIoWSihI6dlF8CtTKIUSk0E4m22m0BTplMP0Dh6I3T3OZqXIWJ1mqi2a0mwkGmrVKFZVCKUVKHTsq2k0lhKTQTjbSydVo1s6Vg2hEfBSxAmVaA9gFS6Wegl01nphILU0ymrMoVgEeToolkCiCTkaGdTaAHkAQ2JYFDCA_JotdiIFzKSRKJkkV2kwkGmviKlZlAozkorsXMZVCiFECCNDOJhLJtLIzZSpgeAgoKidLzshBlwNtCiiQuVhtKifcoVgAA5AVmUP+KQNXGoEc8gbQyGVAXH4MvczsaDyLEUHgqIUYRkqFysCjVY3FysAsgAATNGAADyVANwsFUaAfikAmQqAEyFQEJAAIgK8+AABsTBbCxo2AgIGzEhAiQbLUgtYjCkCiUWOlCsAosORqiALQomwRgGIAAIBcqk6DhAiQMwUp4DDyhWFNaopTxSBTSmgfSijykaGFZAAZgQeAg8AViQ3CxbnICXKQCqyoCSKrKgP+JQSxSAATcrA1IIBdACMJDyLARvVgHAjSkKSs5WpykIzSQw6pXAEM1poOlI+InEE4gXQbANqNgCxXAmgdTKZPQmpQrJaUSiR8oVlUlpRFohFEJyTkmjzQI5LarPSgqCNm4CGibukKSB8H_1ICVZUBRqMqyoAMgYQCUySUiTZcAF6Mg4VKjoyRH4U0AUhTWrpk8AZIruPfk4qtFZikT7CVk2l0U0hQyW00mgoI4blHZg8HAWCgdBOBSASCVB_5SEglQACQUgAAWIQgAaAAgQAcXAExYbhYADaEAA4eAAHDwAAbQgAAAAA0FuEzZpQ4RICoplMAxZQvAo1VwhcrCWhkcgBEZT7BSB7VQAVIUcBMZMZxkDcSCogPhGZWULwKNVTgXKwAyOQAA74pSLMpqoD1EIDwApXBkpYbhb_qUFdU4BeBUALwKgArqnAAM+PgJIE9AO4pBEJBkJQOQAFEYquYgAA3IwAALjYAAJBkBoDEFn0RYmtNKCbM+H2SKwq00mkDJFZKSqWTmo1NCsnGuiC0CP2w2KqPZaVEAwSEBflgFRBaSkDpRTupcxKgCyfiRgKJpC4SF3BKMMvl4CsgKCwgCQ0A_+lAPzJgB+ZMAH_0oAADB0AAADZYlWnSEBNBSBnJFYPSSTUqkisYl0qpJLcnSwmlE21kVEhQ_9pxpNcnUyaCrzyGBDEQQDoBWJwFJAKIB7gyHwDQAAQToAAP58AQbr_oqSAdBIYaAACjSQPcGQ+AaAACCdAAB_PgM6PIYBU6gb1MplEylNGamUxLeRaAHcMF56EkwpySightCyFwEIUUAjUIsYFidVGIxE8nTwEKFukk0moCTp5RKoTRaQUQLjkkk0wkkWr6QoYd1i+ZTKhRozlmkkEbLUt+uwRElIAt38JAEKgCEXcLEyqf4NiSHQ0IMIA_JCFRy+7AFQJDr5KFohiIO6SgIkRJIEkqg5EKGGEAfkhADXpt2QkcMwCkDQJsAf7NgWjkAkgtGJFN4KwAAkkIAT_EACl_8Qs_MwAGTx5sATTNgWjkBiSQSgMaPgwgDqEIAA_EEOGgCIUYW3B4g0hgU3RgCeaMSSiBeQ0hj0JIC4kI_4TAkACkh3ZtZNMwbM5LUZiKTNmS+mzGUjEzJkvIpBGotTMVJ5KhA8hjEUjEUhlC0kulUm0UgjkPn4GknSx1s2v4idLmMlqMxFJnTJfTZifwqVjE75kvIpBGrryhWKZLRSaQSKQSKbWC_0kGS9fLNRppJnoAAcIokoMqsFVEIBOqEBBE6oQAEEQgAAFQwAAoj4AwOBTeSjWqQNMQgDGoQAY1C"
noncomputable def WL9_2 : ℕ := zfNat64 33245 "WojuVqZDi5WAb5aDCAAN9El2EAA9ChsCgMgK_qQGnyoKjUdPlQANwYgAA1IQAAQhYDTFCbhSECFVCuBKQqJRFanKQCKLOPnYE5BgSMWQAhkpAABygAN0C6DgHgMFA8QgqAQCUAAAAMQAAQotAABEAQAcJQeTEVQI4PLUK4UEIRUrKLUaiHwuVhRSKZA2ZzkACDvRKA+gkkIS4jRMBA8hhJh+mUwEzlCsIpRKKkCpWAQdyFw1AwgCLQI4ZQLOXekgMIUNkyAEhoLY2CgqkBmkqAo__Us0lQAAAAMkIAAAUAJDQDlCsBycqAolXk5UACFGIAAGSEAAAbHjqCxhDTikAwcqD_SkMHKgAMIABMEKnzUABGBYHYEDTEw3CziGIK1qQEqyoCj_9SlWVABkAAlMkFIAAzBkA3CziGICFK1MBphUrCozeUhSBWSmhYbjmFeL3oQABmDIowJgVDTsQHyVLYEWUgPQcK1OUgAR6RSqCBBoQb4p3vEoAAAtpVBg0YQgErARZSA9CQrU5SABHpFKoIEGhBvunPodgAnclA6AoBIcBZxTEAAVsmAehWyYAegAAlRaAWgSGNgBBkGIEBplMAUhTRqplMU_gOiy00eqmUwOP_koHjoQEEBpisIaiwXjpuEkmgMM+FIU2mnnKFZ1DKLlMnzjPiaaQ4kmeiR0COBBAAwqWwG4WA9SpASkCjRtSlIBRPUqQHEA2iEAAMhWA2zpQADlDr5IBQQF6DwAvQeACggAMaKgAAyADwOHkWcQxANR05gCkDKG9MpikCqTQ3ytTAgikDiIwRH_zsACCzEBRAYeUKwZ2mUywKU8UgU0poVGk7UPiHKBHUgXU2kiEgiwyBOEljB8YhJPopTwegiSRWFNpopLIE0eqzSJ4UrUqSPSSb5ChsOYNZNpIhIMtKkTIwG4WACsrUwJSBRc0pSkAojZUymAAshCCkiEG8kQGjouCKo4bhZxDEA_FICfhUAXtKgAcWkTwAMBnwAAhBeBGQGFiwB5NV+hEuEgMIFPyoCo0_KgAMIABMEIADZRkA8gEWe6rBOQJSFFESW2JWrykBdyRHJyAAxJGMoAZ2SgAA5Q4Cwnk4CAFQAKx4ABWPAAAAAhLgAAhFwCgAHKHAWE8nAAArHgAFY8ADcmIAAEJcAAEIuAsBwqWcoSwioACG5UHEi__UoblQAToOgACuIRVABkRkE+oktt5AnAXRozAlJVPG0bwqykpIJQXRo7BSAP_RiyAC5Dh+ADem+9KXeRB_o0dgAGKlZVNoUQDFSsx8rADELu_mJAgRQC6F6D4I7kHgBIaAAAAAAAAAAAECDyLCBIg_YfAGqLlYEmqmqLlYAAAAjUIAAeaMQoPIsIEiAATkXKwKqnIuVgRAXgwgACPQgAB5owFhoHADhuFg2CQNyYgEQlQBVZ2VAEkm7uagAJunFIAogNQCHRg4cvASkFQLVVlIAKTNHYFFBnqEYg2BSVQX6VBgw9fhKBkC5bAlIB8VSvKQAYqWMwP6owS3QiyCkqhT8qB0AGqQAoyABFwAEqAEDQAsSAAAAAAAAAAAAGkUh5Fr8IRGQJ624uVhKaqwcoXgA_cwbgUUP_IwCkq+aViIZUBoDHFhwh4CyE0lIbazMwhlamMQuVhNCKD0AigKxGe+ZApnspDdGQGOkT1LlCsCyBNGoXKyjbRHitTlIALRifqXiig5ZCgRxQGjMwjkqpqVqYYYuVgASGmWioCyGR04gBcrLiMQVqcpAKiFwxP2MQRQSugRw0j0o1UtiVE6N3MaAEhoDASAAnmVAAJUK88yoAAAAHikCchIAPhsAouARZIDcSAcgDWLlYGWSI9VIYXKwAqmEAA_6JLlOXA1AMWULwAJjQG4kABmkqAAwrV80lQAXiYgACLoQBhAlxUBYyAgTQONaZkwCkLlFyiC5WBVTSFysBxyUD3_DEABh0I0jmKgABNFYWMSAegGkLlYOMSqqoguVxUC5RcKRyAFd0I0_4YgAagAM1ghM2mBkB_4uAPaTAB7SYAPZFwACOToAA0w0Axg+B8zf9F1KjoAABxUAAOKh6ABNADPx8aSaPQP9FwCFh8h1MhAKQukbP_KFYCV0ymKbCLQA3wyLoDkA4l34ClZQHIACFYA4nACEYAChACDoAAAAAAAAAAAAAnWCaTRVh0H_ioA6RMAHSJgA+UZAAKLOgAFfDwBPbLyUJVh0H_ioA6RMAHSJgA_8ZAAKdOgAAUkWqBDJrLTDvJCGIeipXcSiB+UqcpNIVSqrM4fl20kkKpXUYggM_DpzLNNtpZHupUkBYSpZ40CGTVABkvMIMRQFSu4lEDQpU5SWQqgxHJto2rFdDbgTrXSycdRLmMpIBwMfaj5fG3cuI0NBsEgAHKlQFRcqVBaBKPoAABsQgACNDRCiNDQbBIABypUB9qLlSoLQJQAAAbEIAAjQ0RYAHvh5FhAiQGEKynAuVgVVOBcrAmlZMIEUA46MAAHkWC+dAQSCTFOhCBEgbkxAH3KgCq3kqADI5AAlPjFIAAzBkAFNGuFSALICDipWBGEIogNKFZZCaWQU6ZPAunGuiXkaHixKAD+iJLBFXuJAVQM6TKDKFdNAogZKFZxJoWbToxNNIWTjXRICNDfA1AAbMwblmHIjCBEgAPwlQFR0MVKwC6U0A46+Yih6EAAZgyL2jB4JBJhwFibKwNyYgFWlQFVHKULwAyOQAJT4xSAAHmjAJYtAPQDvFSsOdIxOUymKWHFwFkpoF04i8Yr4zpGhgFkLRpQguLOQWK4SRqABsoVgEzTKYpONhF4LNFQ6kTzKF0410NkjQwCyFo0oMwbhYbqkAB8sqAqPyyoD0i8FEA4ghpCAAFKhAXRgAAAZDAADIYAAvoQAACoYAAADoZAARZdQCrDVE4AJsVATQmxUVQ_KnANQAQSrFJAAfqwAkxoPlGAeg342lIPQCJEcVitTlIpCoy9QlBK1MQhPSmjvRgugAJkCOAJUWqlcxqMRgHoEpLGHwKhWpymN6UFRKiUQnoILQiiAADpSCaSYADLFOhF6QgD4YNwFelQFRV6VABkAAlMklINJRA6MZACbVv8WhQIwa_PgJSbQqLqCpWAWSpKRPAunGea8UEknUBjUANQFtEjmyRo5CA6GNhJi5YqV22giyFKeKbCUQs0VYqRPKtZKtpAkrV1yJ1BJpl1glCmKg1ARhFFOhBsQgMMbAQJKgN9KQAyhWAD70ieAB45CAADIKgjGaLTyFQCkA8Y8AHjHgAnShAAJRLgAAyTt3RzYaDwbhYNREBhjYBOJUAJxKgCiVOUgAA1IQAAQINwsGoiAAvmVAeajfMqAKJWtSAADUhAAClQgHAWBMNAAEMIghIQwiAAQCUAACYyAACEXBuFhoCwEhuFgACjzUqAqlXDZUAUQAGoFxSgUpD_hocgFCNGYCOSYcBYcC0FZjYBXpUBUVelQAZAAJTJJSAigEEnGQDCKyMhqALsoVg1AVplMUgFnkqMTRaFC_7SUTFYvnGug2EKGD0ox0G2FysAII1R4s6BaL5GQ1AAuUKwCiKSaBZoooUieVQsnGuhHkaGgR6SY6B3SoKuJFZZBjLQFriyhWO5MpjUQYpTxSXQLNFMOkTzSKEWjaXQRJkugnUqkn9I8bDUJUDpTRgCFmHWRw3CwARioBho8AMNHgA_2hAAPLLgABKC4Id5gAOUEQkcQQoAKx4ABWPAAF9CAABMZAAAZHgDoiw3CwFAAc4lKgJv_1KcJUAUQAihkZSgQpAKQL3GwGoYOAsUduAAxKVAVHEpUAUSM6kAAD5SLAGQAHw2IsZADUsNwtBNCAwgOnKgB05UAUQogAH+QgugBoiYAAACgeAAUDwABfQgAANFQAAAjMOHAWNUfAyYuAAGCqxgCoAikUACByU9RaAaAf+NgG4WHMdAzouAKSTABSSYAGTJwABgToIpKQADRKReSkCUAtyVAIajbkqA5mlFBAAZUhDuHpDLZSDp0YA5REw6rQiCDEBqY0kVlpCiMYuVhRQkfDV5RERQ0FUtDoJByBFlspFIxEAnSwBiCwDCEGqj4CUkmwjXUymCkkVg9CKUbPIYTEinEq6hBWGgEykegAFcyRdvoQEtLGYDV3JQrDphDxKU8UhH9SMEWmj0HoQTqIVWUigQxKaSLKSiNVRJYPcQH0FIUP3yUSZb_BGBqv8oVlEykkGClPFJlruMEoi00enk0lGenWqh5QIZVspBlJRHKN0SWBB58FXDBuBKQMuKUpAASlBBWMxARQ+yhB11EpSUCSB5TNkNyAEjIVU+AvBo_AWMVKwCisQqVgEUY4hQwJaFF0IIstkoU7TgBrjQqp8FlDYCUgdaUpSLQpJQRKACAEIIv_S6SgGxGCkAJFQewnKImnKfAKQLllQFRzOVACEtajEkCOgbf3JQJQqmjAERUqEMmcQUIBqAPUoVikCi44qVjkCrPZyUQMvnVoG2eQzCORjKQHKiSwBs7wpEx6DoLlGQFJAKIAAmj4AAIJ0AAA7RMnOKeQ6qRRaLZEl10envKFZVPNVpr5UymZS7SSqQZzbajRTLWRRoEchJ5DNpJlspoMtH8HDwHdpJiCEUEhQvJIPW6lCsqnkq00UlECLPYaHzssgohMllX+x8OlAhmU+yJLGtJKpgQBOSOdHQAEdAEhoAcLADBIAAAAAAAAAAAQsCLgqSOG4WCAdASMuAh+TAF_CoAAapEsADZx8AAJQXjQbhYKo0ABCsqAs1GFZUAUStakAAGpCAADcVANwsFUaAAjiVBCSOJUAUSpykAAGpCAABsTBvFxo2AgMKAPJsA0YCV6kEEEYXKyhxMUaqFYuVgAYQADHoQAHHzIBUekAtNhCLqyH+k4BFA8AIGHgAAAANFQAAAJwzgReACMpAFJKgkgUkqA66jAUQAOIrDEANsLwNwjQ_IkwU0JP6T4q5QrCrTSi4gqVjEek5rQTFUqhNZadbRiyABjDZmFIAh4gfWOepqIgmsnAH1JgAhZMAf6IiyAAD86AAc4bFmGjZpR2BIGwKU8JI0wqVhVKNRHAXKwAAACKIwADnDYqzkHgEkTLNGjKrB0RWABsXKwqNVBsXKwALkfAABBQiaFkAHAEpgapbBSylPAb0VKwKJRb0VKwAMcbMwLoAZUCOaffNX+XDuBNSZB4E8nAF9CABQPAAKB4AAAADRUAAECDcLDdUgrWpAaVKgKNR0qVAAAABqQgABSoQCgAL6EAAyGAAGQwAAAACoYAAACaZAAS5dPwtAAE2Kgv4nBNioogTQFoAWBOK+rAACBLgAdiWFo0uCSMFGogLxGlIE2ZCtTlJFAnCRHNkbD0igDikIAogUkBKK8USF9JSBiAEQBSYxWgGVAArYyAAIchBFAEqGQBzyaZUI2CEBRAlKVBaJSqMpSoAOgRQASrwUgilkCkRkAL5XO5SjQjBTRCEBozgVyhWCkBZ5HKMpBoAMRaDX2oOoIwRa2MQA5AAI3ABNYAFnBHRoAaDBvnwToUgD0FSBAPQVTkAZ2ZREAAiNRAbQnBqyNDZMjQyiVTtpE8wmmmik4l"
noncomputable def WL9_3 : ℕ := zfNat64 33246 "okBVBf5MtIqVhOXqplMUgRaLOQ+FysCqWaSPRoIUMwhxutpApHzsF5kZgyECJAAcXKgKjKQCKC6KF4BZ88lETUIAAch8XoB5DmaMhBiQNyYgNNlQFVGoXKwByTBLgByRQx6EAWQsxUARrzIAwgEaKlYaaXhyplMUgEUeEULwCySRwaBHPiGwYaqYwGhGs2WeJBMQlrHyhWEhEJHClPFJUQiqEOm4pK7USySZyvFAhhxMphqpJYmKGwAJjQFwkAB00qAqPTSoAiktALIJeQgLtLwBxFgLGxd+YyKwJAYQHTlQA6cqA_MjAtALIMIQjCACIBYHQEjAHk3ZRkS4SDa6kBzUqCo__UualQAGEAAmCEABsoyAANN2MZASUUgEPlRcIm_8pCHyoADCAATBCLoAKsMgCMkzMGRDBIPoqQGQyoqtR_+pZDKgA6AACVeCkAAKIyAVLpALTZWQJoBrBoAMkNAAAAAaKgAAByNma8ipOAwE6eUkFJVaatlMpj0KlYB3wuKoVky00HWgRzCBNIICQ8dgbRnNGx2BIGwKU8JI0wqVhVKNRHAXKwAAACKIwAB8j4qzkAIhxqedCDMakBnEqCo__Us4lQADvVgAAYIWylYCCAPimTk0YGTKVMA8xUrAolE8xUrAAqgLPQgeGhGEKpdBo5EC6NZsqRIng30ynUQoMpCLURfqlchxcrAAAAgMlAAIPJirAEhYAdoQAJCIABIRAAJwqAAAkZEcFgAABsMzNGQRECAjNGQEVBUQzBUAAABHk4Dy0DEAFMtAB7FmaMiQjwUKVqYSQ6RUrCTUaj2UqAAOiSwAAWEpBZALIKRhgI9ea0yAQ2oVxAhMC5WFRqLXyhWAA8jRmfcOgCMqEF0wlUKwIwMUDwE08c3AgShWFWmlFAhUrABOB07AAXuhfeWi6YQHmIwwOZB0BYpE8NtRFNVKpNJWmU3FlCsAFqsDRmFGgyEFRoEdrSlHLpFAEclRwC1RzNGWYh4CmKU8Nob8kVhVpuW06UgBwChmKQAKCG0ACQjQwXHT8bAQHoeAqgzlClIVEoytXDYXKwAAAA9IxKBYAABY2BTEx4kDLFamBKQqJVlIAGEAA3KF6piABHosDoCAHkPwzIAqgEpGWgVKwqJRWgVKz+BQvotRCUjFUABpCMUQA+GZAJGJmaMkeDQFECJ5UGjFL_6lE8qCiPQyAASn0ikAAZoyAEUpM0ZAOCVqYABShWFR6UpAFKFZOSsgyFiuFhOIRnQgADNGQGvXhoCaV1ZKMKR8DZzqpNFIZRSS1XWSjE0LJhNtdHSI0NVykAA1LmjMQxK8JBuxSAoyVB_xSKMlQBRN3KQABXkKYD0AAxJ0AoCTNGQBOVIDaJUBJ_+pbRKgCSE5UgAE2KxZYuIIBdAQuTPsbDTXg+EpACFKg_8pAhSoAMgAEpSotBVQJKoQPsbF8YgKICMipWAdFKeaZSnikBgy0E0KzIps5l0oINSUK5NCilGBt5YADJM0ZE0KwJQCACIAQARABWBKAAX0dAAZYLgZoyAC+hAA2IgAGxEAAX0IAAExkAAEIaAOEhc4bD8Xp4OQ3FisEopf6UKwGj0ooxKFYgQCPSKVQBiBOUCOCEolEA3GjMHkEYHzChs_8jBwSRWF0pp+ShWGUHoGetKwQRyFRUIIpRj0pANQNR3oEcAqUETBAnKGSKysjkmj5JFZ5mYyg5qETBW4lUgjmUhGkaGEUmlEANGDcqRrzJlSMAdAYGUKwHtRYYXKw2gUcCD9lIDCQ1CCLTQGZmjsBbEa8yCw4ECi4ouVgVFyxUrLrKwURiSlPCmgODQgi00BmZo7AsNGaMg2EQD+UgE4lQAnEqA_0pFTFIAANiEAAECGzYyBNBJmjIAD_SMeoqAoh6ioAo_6RgACDC0NYHhaB8I2AEAA5Q6+SAmDgoIC9B4AXoPABQQAGNFQAAZAB4HNeZCBEgQE6cwA7lCsDKUQ7lCsCqTRhStTA_0VAJ1CCInUAAA40TUzAUQELlCsHXplM3SlPFIFNAXKU8KjSQwuhEUS0mSkEkGRBDKE_2wzAklMpgCkulNNEpTxelCsCm+XPiaZSo0melBJU3CWkyUgy1xxMjB0AHKTXmQQUCitTAQuUKy81F7SlPFIFNBUKU8KjSQeegRwpMlIIukgTgEDFmvMpUDQEMUp4TQiJIrDCVaa38oVhRKNNCMplMKjSQaYjBSZKMQDkXeHgpJSR6JIrCyL5OJpNyRWF0_0nMwPqSBdpICWQoakmI61WSgzAmRgWOPA69MpgSkC0alKQAppVADMSESTqXe1kwelIgdACYcAAAAAAAAAAABZLccPwu0kpI9e8VJ6qVSaTXTkisLoytInj2kx6YjS0tYv0me0Ve6BDMNxqslIMtFMTIwNj5ubFwglHM0ZAmDgFYnAZhJgC55MAG0PqCABOQAPlDwLwIyAwsXGwsWDyLAvCgYlEBqxcrAqrVi5WBLQYiRHAAk52SgAAdhwDyLA5CgKIEAC5WBVYAFysJUEwAABNUYAADQUVYNws4hiAogSpKgKjKkqABuTEAAGxCAACkHANws4hiBTSEBp8qAqOnyoColgVIAANiEAAG4OAbhZxDEABp8qAqOnyoColf1IAANSEAACIKL2FGuFiNCQFECl5UBUaXlQAeKYgACOIRlADIRkIAoxaRIM_oQCci5WBVU5FysADCAAY1C0IhAAaEaAcTIAnCMAnIuVgVVORcrA0wvBhn0VAAAABjGgPHUFi0iQaBQgE5FysCqpyLlYAGEAAx6FoZCACMx0CvixCxIADoEcBORcrAqqci5WNQg0tBhGIAENRngGlMAAASkAuh0VDxXhYNvIQFNyoAq03KgAHerAAAwQp6AAEOixfRIJsoEcAQhcrAqoCi5WAKQ+CqBPQou+z4CyTSFo8C4BgJAYxCAj2VAVGPZUAAAADBCHsRAAFWOgIHaAwEgACIFQEU2qsAAg5iAABIfD2EgAAAQDgABskwQkGyTAAgpiAAAwdD4EgAA3vQrwtFS5v_iKeAsAAAceAIpjwACkADMBkAB_4iBRRYuokCBAGsXKwKqNYuVgduRgcgAPMRiiBFAyosHoNwsGoSAogSnKgKjKcqAAAADUhAABuFgFHQEzlCK0JAUQOrlQH_1Lq5UBUTkqkAAVxCMoAf2MgHgi0mA5EgMUhAH7KgCq3kqADP8DoACU+EUiZiwAA8unCFEgTEkRwBBFysJbUR2lCsBZKxfKaFJuJhFQoEeD60BFAARDYAX6EB18qAqNLCpWo4WAuml0ymAcTCUvQgO+IwAHgAGyA7EgNehASkCol7KFYBdKaAcTzMV8oehG0NQpwF2PgwEWQGJAQQDANFOKlYBRECUKwOjLQTQDjXTZ6EWQzOnBPQdALtkByJAalCA+yVAVHQhUrALp_9MphUDbuRiKHoS4CxmAERAGpAORLJQ8UeRgChFSsAomfKFYBZjCjE0A410GMjQzYDQUTzaQBL1uOkvRgFIOjsYPjvEC5lJtBIIF4ePowLldRJayhWpykCo0EIitTqIE5po60SWTRiEUAMDFkliQPnQI4R1IRUrAKIpAJo9QmkT6iBI1S2SRpSFDMNRJpxsP_FaBYwfBcdAN+0PIsIESAAFkXKwItVVsXKwKifYVgABHoQAAeRYB5Fg0iQPQARRcrCE1GUgVGCqFP1QrgATVdowAAeRYN70BhY2FGHFjCB8SIBYxcrAqqxi5WABCUCOAAUFCkU1AAb8OABadBEJOIYgD2PAAIIgABBEAAAACYyAAAMBAEQk4piAPY8APUmAB6kwEJAAAGx0AACIKC2rGuFiNCQeKYgKXlQFRpeVAAUQACOIRlADIRkIuHRNxIDCAnIuVgOxeqqci5WABkkCOAAVVCMoAGpFgVcibIrAYQL9lQBVv2VABgpCAAMahcmagAOoLBSxNwQmAwgJALlYXuWqqkAuVgS0IoACF0aGjMAFSz4ABh0AhFgAAAAAAAAAAAAHBZGiYTxUBBBIxsnIuVgSaqtouVgAAASQzpwNQA0ikAIKSREknIA3C5WkwmCLVRuFysACCABCxGDavZeA2ETBCxMnU+QJwGNJHUF0pKo9G_qlchhcrCKEdAMiQwqkUBUSVHJ1NxdAxATJw7GwQiIHo8AAE8mAAnkwAKYQgAAfnQAAQiIC4ENjwALbDcLBqEgbgxAAHKgACJUAZQAJoAYQgAA3CwDcLBqEgbgxAW_KgKjb8qAhIAABqQgAA3CwW1YCAMzIDsSCjKkBy8qColXl5UABkEIwgADBC_ofABjpOFSAXRczkoDZisB78qCo_3VK_vyoABjoQAALT6ADMbgAIRYGkJA8RAAACCYCaAIJgAKoACDFoACAhsAI0yjA2ukzAulSAr6VBUajX0qACogAGYUgAIBAioALAueBdxBeCyJpWphQZSFRGyqVyHFysihLSQCMRQABAgEA_RkFMyAh7gCUlkSAogSkJcKVNJStTEAXKwBko8QQAKJIxhOoAtk0dgPACQ0BgJBOpSASKVB_5SEilQAGSQgAAZIQAAAEcSHkWQIAhUK4EpO9MVRL0rV5SAAAAGNODTeQCRqwAEhMZE46KBHCaChWpnvzqgykINRKpVi5WBLQ8SMAA9CcnBhKoBcVYABg1aRseFSAAAgVBflSAIFQAf9WhiACA1YQhVAUEvAfGg8i1LF4BFplMAgRUrAo1EdhcrAI6QQfYvAZ2Rg0gGdOZRAiKRPAB4LjInANTsplMCUgUaiRouVhFhOlptCI_QQMIDSkqOGE6z0FmJlMAD_MyRsA1dqoVwOWlQVEq8tKgANShAAA_QtTEQcQAD8OZCkWq7uxID0KU8nI00oVgUaiNAuVhRIIGSDMI+MIFFICKIVAjkE42UB4CdLBuBgZsApKwP4kD7VCuH_UKUkUqLS1CuiouVgC7Rw_QRiAG4UYm1EqJBEXjB8B8HEa8RQ2VWcnRNMJJnpSShWbSyTSiJgqVk0LjFUdItRACK+ZKjkGQgDAxYAackpQ0oQSCkn6EoISUKzaTlUtk0oykAOiEigAEUAD5BEDJ2OgIAFthuFhAiQfWVgPJlQVGqi0LlYBlAAmgCFCAABEFAO4sIESB+6hXCgooKlYVGohOLlYEJACGhZpKAABEFBbVxcaDyLOKYgMIAOi5WEQF6qg6LlYH8lCefOSgABHoQAAHgoAlBMABDhwFnFMQNyYgAA4zUAAEQAFKLQAABgIBQAkHDcLOIYgbkxAcjKgErK1OUgEUAiWLwCz0pKGBIQAAAgiyw2IDCAMYuVgpRct1FbRUrAIoEQoXgFkkhFvclAYQAAZBw8ixhD0zEAcQuVgPheqMpAIoEYoXgFkkkFUIl41BhAJ0G4WcQxAYQPwlQFRYOUKwCSC0Au1IUi8qEGBmo2g+4eJeXIxaBYwhm9SA4SVBUajwkqADUTEAAPRCx01AABAx8_NCeQwkh+VqYUGUlFqI7lamQ4uVgG+WgwgADfRJdhAAPQobAoDICv6kBp8qCo1HT5UADcGIAANSEAAEIWA0xQm4UhAhVQrgS"
noncomputable def WL9_4 : ℕ := zfNat64 33246 "ujgDR2AbQLwhAASUIy8AA2VcHQAshYB75QvAqr3yheAAshb_B0AAVkCgD45UQIPBuEgJ9KQEIi5WBVXvlC8ABZEwAAPyBgBSysA3CQAsiYB75QvAqsIi5WAE+lIAAH5AwApZWAAvZRaPABHIgKJlQBVomVAAEciDoAAFYMFgHGSoBzImZEwf+YgE5FysIfL1VTkXKwAIGRAACPQgACdEQDmRAf+YgE5FysO7L1VTkXKwAAAAeKRX4KQIVATEKgNAEfVIDdZUFRKu6yoAAEZFwAPFIywsb4GAFMFQADxYBrVSA5OVBUajycqACCRMBlAI4hGSFgAVEVBLFgBiyABiyEkSh3oAB05QvAqrpyheAAAADxSP1BQBy4mAEPhYuBrwEFCw8UgA4MAlhoAKpUABVKgAAAq8NA8Uk6CwAADjBQBfEgL2lQFVe8XKwATkNAAA_Qi4BwAAAFAwBkEgIHlQFRgeVAB94OAKICMUjBBwAACgoCIFBpoeAvWVAASVq96yoAAviQAAP0JiQkAAAAYqAAdASWezTzKgP7K1OeZUAAEhABYrMSEgAABEEgegfAPeLlYFVvaVAAUAeAAB+hMSEgAAAolR_x0AfqWivZUAVZ5lQAAFxGYAeKRyB4AAABJUDOJAAIuLlYFVREXKwByJRqBBKrNzyGSURoktiQkAAADgqBEEgAHTlC8LcK1VbkXKwCegf7RgEGpzEhIAAqw0LAKJUSMJABZM4nMoLlYFVdKULwJ6AEEDBycxISAAK0_PQA+nAHgwAENyoDjUYblQAf1bgVI7ACUQlcBwAAAGAwGqQoYEpA0v4VqYPi5WAIcEhSBtJISaRmJBwAAABbYBAGDS6EByUqA0lXmJUACBAAB+hFwCgAArNwIOTAEhoAwGAAYKVBZJWqLBSoAOgAAlXgpAAAAGAwAHpSoBSVfSlQADkLjtRyBhKEnQOAAABEGC+gCYLlYFyXrbnFavKQCsKU8cjUDbbaqD8So8KA4AAC6MDYHgTCYNwJSBRAKqV5SASTeB8AAD9COQJAAADDKgABZcqB0EQ5qNlyoAmgB9CYiEu5SToHAAAAazEHkfADipWFRKJACpWFZCxpo7AtLJrnv9TYmCjK6DgAAlAzBMASGgJRIH6GQDpyoCjUaJlQAdHIAAlt0pAAAEHiUFhLah8MSihryhWVEolFYpQrCe63TiagG0sm1UYPAUAAtAb0SAiHwxKKQQilCsqJRKLmyhWE9pt2jqagG0s0EvSVHhQLAAEDRnJybgE46ARBgKKHASXKgP+qleS5UBfSIgAA_Qs_BwAAAIjoBAGAYgGnKF4FVNOULw8MbX0iIAAiUYuAUAABcKBiAA28qAG3lQWyKjaerQgP_LwHeQk6CwAAAAAZhcrAqL2ShWFsio2jcDyGAXaaDlQI5yA4AAAGRIALZH3hyoCo_LKgPpNwQQC6B3kIuAUAAABIaAXSOH4EpCtFVLEYomRKFYE2ykOEB+AXaaDpQI4AAAqgsA5AHkVKyohRFCUKwrAnWUW4eQwC7TQcqBHLgFAAByA9CwACsi5WAxBWpykEDZSggWZAjj2kjQUIuAUAABd6GxtbCgLAmAJDQmwkCTkieBgEqAm1HAJUH8zYABaAWpSAAABYExViMCTkieAQguVgTaqQguVhNQAFoFsk4ygcAABoAOQgEEyIAzRUrAKIgShWBRNKsWwagXTjXRwaBHMsHAAFGAX04AAAQKgOIBAqEiGQhBwCEA5AIafGCCgAAAnVQBIaAEhgSorAD8JgABBMAf8ZgAyGkDwdAAABISYAMZIngSRKgNtRzWVCSjIAKHwAtBiBgAoAAIQAQQH8lCsC5Mm+mi_JFYkYyKKB1i2DUC6ca6ODQI5ggoAAozcCkkxj40BTEqOEElITaSvhWrk8LlYVaKADUWgbxTkHBQAAIiCQc8JgEZFSsB_ilPFJUSyWSghBLqaHDeXRfaBHToFAAAASGhTxxGBFDqDVKFYWcjI39U4UhpJuLQNQLpxrpc9CAAA_ozExJaUjFIHymiFrAcAhAlIFE1KUgAIQANiIQAB3BAuCGwkBBAsuVAf_UrLlQAMUJgADSIRVJIAccWBDYSBihMBZcqA_+pWXKgAIIABpEIqkkAOOLAComDgFeOIwssVSkAogIKlYXSiWKKhYjiM2mkugFHQI5ZKIAAC2mgpBrBEAPQiAB6EQANYIgAB+GQABKhIADSkABCPAAdJgagB0mACGikAAQM6JP+DoAJYNAB1DgSRQ2A1FFpwaQqVldJtRlIGU1YqqtAABDQh6LYyZQAVYFgLcYLwmgpC7TWiKU9yhUrAAmi1TAsIEUJpdVVNxD0aJc5AupMCnXEgOktUwFslC8CrVW9lC8ACi0AAKlxTJ5RIv+jYCiA0AHQOKCFgqoAMC5WAURSA+BetgOEJ+GU2a4mExWhEkcn5FYAAeg4O8LQDCyhWB+ZSFIFZJ6AcYPrxq1CCaZTqGoh4F6MAsFTCx8DFkYA6hcrAa1U6hcrAGoxZGAwgAEUhaGTyAmwiADQJHNHQdHQgJSBB+gpSkLSQTo6EBxAJshC0MnkAKUBUFQGQ8BNAgCVBJQKqFeAJUD0kpKhOAkgMV_KQD0AAQsABJGCdoTUBMD8E4B15QvAg1V15QvC6PSCAVECLttGCNSEABKCHyZNceAelFJQbHILlYVSDVUcFysLpRAotCeyEAqfVMpgPQABCwAqiRxGD6zyGAKSikGmgvJFZbTDEdUtpTRI49C6UTaXRLCNDCaGEshsliuACcWCwJgAGllQA0sqCKVRWLp1lCA_45AAZCMUZFEABIA7hIsYyAigSk_mjEF26ZTFIYSrWRCCE_CWnEyq5jEUoQAHuDYGwGjMQ0NiPgeGeQwBSBBK2mUxSBZIIoZCfgZQLjI0MJp1qIK2FgDVKQBGSCUACG5UFWY__UoblQFEBRnkMLCA4RCA2gN8GgGsEwZWSB7HgKIEKyoAqwrKgAKATkAqdBSAygEBqGzMAXIcSKPBfQOZlCsNKOGaWSkKQKyf9PIYHW47AYjVqEB1AA6ACdyOIwnpPd3oRoSRWFkok06ZIrKD39WqtFAKePwMttLoodAhgbbSUQJYwfJejOQ0ZCwUH8Sz+BEA9AToNACdBoAB6AA1YqAALgBAFulgWOgIQYQWKxSAZVMpiksIMILFYhDjYQpaXAJQIYfV1OHeogFQNGw2BhYsPBuEhOBwQiIgJUlQFRh6VAAOomABCAyUgAA3CQANyYRQ4IAUAjhg+A3koXgVV05QvAAAPhiQGdOAACKHAEQUBoGBdgsB+UqAqPTCpWAXSagXHrzEVPQgAAYhRR0YCemkmEvSCQLPIgCdkwATsmAAWgAFtOgACTCQDmJACyFjEREPfKF4FVcQXKwAVAQJwABBUEzRgAA5iQAK1IRQ4AkRUfvEh75QvAqrsSheAAjhg+AARZGAACKHAEQUxgaBQJo7A_KVFxLv_1L8pUAC7BYAANiEAADEKLm5jQIIcMT_w0UQGwFysCqtgLlYAFfGgACvIzxmIABUiQE0JDkEUEQAnyYAE+TABahCAAFKdfuWgAE0JAEwcMQIGRASnKgKjKcqAAAADUhAABuEirAAKsAWUkUAI5EBFUqASf_UoqlQAHALgACZIRJAAco0NrGRRB2BcBmUqD_CVUcylQAJdIgACZIRlAA7AkHINwsYQbkxAVlKgP_K1OspUABAyIAANiEAAG4SAbhYwhUxSATiVB_pSE4lQANyYgAA2IQAAbhIB5FjCD+VCuFBTaUKwqJRRqUKwKjQQcK1MAnNNHmiSwAA5iRCxYNwsYQbkxASpKgKjKkqABuTEAAGxCAADcJAGosYQMIARi5WCzFy2PtQrykCoisRiqAAL5GFIRAADMSB1BYwgYQOalQH_1LmpUBUTa6kAATBC9IdAAdQSB2FA1FjCBVAViNKQqJAVCuEguVgU0WL4YQABfIwpCIAAZiQOoLGENrqQHNSoKj_9S5qVAAYQACYIXpDoADqCQOgSsqHkWMIQEVgIspAehEVqcpJuGwPSKVQQINCDS1OAADmJANwsYQqIApAo7EUhSB3lYoi20ymBdoIMfQgABemQDuLDkJKhUymAG0oVhTXGplMUhNKtNCdKU8TopF2gz0_6jANQAKDB8ABRAFIWfTKZRFIf+VixplMPCmUwLoB0UI_gsAABozSgAHKHg1QBIaAUEBeg8AL0HgAoIADGioAAKWFi40cYWGIPrIgL3lQFRveVIEAfWRAAJmQhCV0BhxUAgLH1IaAFID5yYAfOTHUAFIAAQToAADQcWY6HwsXAgCCyMSoBwS8IgGblQAzcqP_MwEvCImhlAVQhAAAD39DIXocAAL0mABekwAH2IgABmnRZAAegATm_mMjCAAJ4mABPEwAKUIgABVHX_loABECQHJGhIAAcBUADgKgAKIAA1j4ogBFQaGQjIjQkBRApeVAVGl5UAHimIAAjiEZQAIELABcD_0NitCQbQQgM4lQH_1LOJUBUSi6kAADBCKoAAfeZDhEg3sjASkBJStTlIAF1CmFEAigp1Cn4zBWQKmLAuAbtpmjINgkAAOgqAilzVgABbpwAAUj4AAIQsDMGQahIABxJUEJHElQBRKnKQAAakIAAIQsG97CwsbAv6GQvQ4D7EQAvSYAF6TAAAADNOiyAA9GQjIS4UHimICl5UBUaXlQAFEAAjiEZQAIELAAzF48TgNhQUZUgOXlQVEq8vKgAMghAAAyQv7HxhAAGvMnNCQKLTKYBTipWBRqI7C5WATqGiCAA2NCDqA5k1gKiFibAN1szBkDkKAW6cAAFzVh0FQH_kYAAApHwAAQhYGYMgchQVOUgHElQFEcSVAQkAAA1IQAAQhYLauLgWjzIwgAOlKF4FVdOULwAAnMPAA8UiyDEA7gsABMS0cwbmEFlkCcA1xcrAqpri5WH8VIFlkCcC6Ay1GxwtAxAAlK_Mv9HwLoIkYEpAWQrU5SFRBdBEjCugUJQkBNRlOIA1xAuDMGQEJyIDBJUBUcElQAQnIgLoCOEIDaALgSA0ZAAPUAfD_2OiECQcYYgI9lQH_1KPZUAA9VYAAGSEUQCoAAQxJFOiLAjRSrgCULlYFVjqpXlIBFeGXACXLYAAeka5CUAAAFYOGcwbjhEgwICTi5WBVSfFysADSND3WXFkAARKNDxeLCAAy+GZGFEgHIEpARSMVSjFysAkIRFUDaacBvUCOZQunEPtEwM0ZBsEgAJUlQFRlSVAAZFWAADYhAABCIgLlxcAKkzWmQgRIG4MQCtyheBVXpFysA4xUAJodRmKQABGg4qwB5N2UZEuEgMIHryoCo+vKgCKfALgCyC3kIADZRkAKESRTVCwMUWL4S0RBcrCg1GUgEUTSWLwDJJJPCEL_6MwBIjgAtpMpgC7D8rMi1iQWkAlxcrAqJsCpWAPQ6hQvDE6kPSKD_QI5dDaAAORszMKJAVQX+TLSKlYTl6qZTFIEWizkPhcrAqlmkj0aCFDMIcbraQKR87BeZGYMhAiQAHFyoCoykAiguiheAW"
noncomputable def WL9_5 : ℕ := zfNat64 30835 "BKwAZKAAoQCI6AAmQAQuABFQAEmABBwAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABIQBguACjQAMWAFiQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAKAgDcFAASDgACQcAAbgoAABwsAAAYCAAAAAAAAAAAAAAAAAAAAAAAAAAQA4ABgEAAMAgACAHAAAKAgAADAQADjIAINADxYAAAAAAAAAAAABISA0CgCOJAAUGgACg0AARxIAABRMAAAByFAAQ3KgKjDcqAACbQcADxSAqAUADGwALByFAEUcRgOELlYFVcIXKwACKOIwjoEIkoFPBwABa2qAHiQGgUH_iYCSo8ASVHgA_8TAAW7LgAAJaUADDQAMo0Be0qAAMrV72lQABlGgAAgoQDahKwAATgsA6RoBmhcrAqrNC5WAF3B4AAbaEElARgJACFli9yYBCBDkqAIclQACEACHZ8HX+ysA3cSBsAA5QqWSARBgFoCPx4AR+PAALQAFilwAFHBomRuZGRuNBQuPBQsbjYE1ClSUNwMAiGAOoMAPQAegAHUGAABMZAAAGAgAYCAAAGQwAAAAAAAABgIAAJ8AsMgAAAAAAAAAAAAMBAAAAAMhgAAAAAAAwEABQEAbgoACQcAASDgADcFAAAOFgAAB4AaKgAwsANEhuBgEQwAENyoD_6lDcqAAAAB0pAAAAExoAdwYEIUA+AuVgVV8BcrAAIYUAAbZKAAAAJDQAI4UA9wuVgVV7hcrAAI4UAAdZKAAARoWnICWEgHvFysCqveLlYACWEgABEowOWMgAAmCgIIEQGxSoAAahX2KVABBAiAugI4QgNoAuBIGZ0AQBgAAJlQABMqBcgUAeICAAE58AABQGBKAIA6ocA98oXgVV75QvBIAdUOCgDAAbpKJYBQAAAJAHAURKgP4K1OiJVNoOACQBwAAbEIAAAAeLAACKpUB_9SiqVAACkWOwBAAAAAGCgAHiwAFIsBFUqA_+pRVKgADsAQAAAABgoABhUAPFgAA6coXgVV05Qvq8FAAKACAAAAAMFAAAHTlC8CqunKF8Xg4AAfAxAAbQjeAUEQOAABL1QVEQHtioDj5UBUePlQAe2Ki+AQeQHRIQdKGAApaUFAAHRYC3pUBVYaFysABjBzSAYAAKKQfYGFEFAAGhYCHgDocAA6coXgVV05QvakHH9i4AB4EQA0EYACDAkADgUFFkIDy5UH90Iq+XKgoIYiIjxAQPQCmIQAAAkCmAKBgEERASkB+alKQAHp4gIAPDIQAAEZKAG1oB8KAAhuVAVGPZUAA2jI8QEAAMEIAAKIcABgMGb1oC9pUBVXvFysABXjR4AIAAfoQAAGgovQA2bAPhQDaMgI9lQFRhuVAAHiAgABghAABRDgAMBgFeNAPeLlYFVe8XKwSAZvWg2AQADyRgAANBRVgYgYgaApuVAFWm5UrQKADEDQAAbEIABwqEABMqEEAB05QvAqrpyheCSmmwA4oGCCAFxKAAg4NAXUZBkk2AuuVAFW65UADvDI8QEG0AqKEAAEIWAuoyDGBkAZwuVgSaqZwuVgAHiAhEy8ADxSAzQsABuF1GQOaJgMrlQFRyuVAA5omPEBBpAU8hB_lCAdIvBLSgBKQ8W8KhXRcrAqqdi5WCQBWg8G4CPmkQDekYCCBSwiAAepAEjIT7VAPsHQB8h4APkPAAOQAEpFwAAGhIpQCYTBiAUDh+LWVhmRcrC7Oaq0QuVgkAHFAwGUAjJQd5OHYA7yBOBdRkBgh4CUgVGUgF0VsaOzxAQHEEiIQT6XgBZCwRnIzAgAwqAAENyoCow3KgANVCwAA8UhDQkAAACyoAAOnKF4FVdOULwiACDQoFIAPkobQOIwAYqEB4AGKgBwsAAJ5lQBVnmVK0CgAD+yMABtCAAHAjAATKknh4AB05QvAqrpyherQKAAvppAGElHSmYkgG0m5sAElQyDEABakqA_qqV7UlStgoAAMIAHUIABwqEAGAkAqhIDqJUB_9S6iVK0CgJJf4uALoI0QgAHCoQAciQdIMgNYlQEkq6xKlaBQAgoaAAEehAAOFQgAIJwHIkH9RAmAuEoXgfaquEoXgAHiAh6TEAGdOBPAsAAAVzgAQkByJB6RGAlIHEBytXlKJgoAT2TAYQAABKBuAA0IAEVAAB05QvAqrpyherQKIoABhAVElB_k2A4SnAAoKifVi+EtjIBIhcrP+qRVUiFysNIBCJhkeICIIAAASQTgAQoQA6SPAKg_2bAHhKF4FVPCULz_x5LA_2bHiAgAHgjAAE0DQCdhAEjIJY6AAAQTAACCYAAP+OwA4loAAAAeVChkQPGMgFXFysCqquLlYJQHjGTEAYAABKQAEkE4JTGxmQULjQBkKAUgSkAqylWwUGTZtYAcJFYH0eSUDNUIABwqEUtKAMhQAW0SoblQFRj2VAAUAmPEBAADBCAAFopAAyFABbRKyaVAAMVq+kSqMwUE9EEFQAAj0IAAhSsVoAyFAXQGeFysAsI0Oqs8LlcZgoADmSKwAIDJQAAHF6+AGciAZCgLoCFC5WAWEaHVXbFyuMwUAVBIAHkJGkTwAAOL18AGQoG_LwGUSoAAStTlIBBGbnkM8QEFR+45DgkIAAWikENaAMhQQhMgMflQVGo37KgC2iUHiAgABghAAC0UgAJGQCIqAYCgAAFkwQkQgXJMAABxCSAgWgIIAADIUDpzBuBKQqKe1SvKYzBQBIJGAAPahANQLUKwMgBIyDHCQDYUAHhEYbJMBBPerAAf+NgAHeLQAAAtWb3oANEgABDcqAqMNyoAAAAHikPmDgAPh0BdABMHIUBNAXIXKw+omU6quQuVgAPkWAAJmjAABuLgBELQAwSfICAFIC4yoD_6lDcqAAAAB0pD_g4AD0dAWALRJ8AIAAhuVAf_UoblQAAAAOlIAAPR0KfCwABPMqAKs8yoAAIfEwAPFIfwHAAQjoM6Ij5MxYC6BldEXKwG0rVVthcrAAMIobAAgIlAAQcMgLwARkRFgLoDoC5WBLk6qt9KF4ADUAAfKcCeEgqCEMgbEKEJFBYMzKwAtC5WFRqotC5WAAAADxSCBgUAPI2IsPDb0PEmDgWhQAEl05QvAqrpyheAN8HgYwEAAbUIAAOBcACwmAZCgAJKbSheBUFqqvZKF4AABx+2LA8E5iQcAAADIUAFtEre5UBUedlQGDl4HJ4gIDiB3kIAAIRUUdCI0FOKYgAIblQFRhuVAAAAAuVgXUDAB6OgIYOCaJBCReAqGVAFWoZUABhLABAAFVCAADgXADmDgMBIHALwAAZJWEoBwEkAA_onHMVgCqEYjoAORIDspQHdSoAAStX7qVJUDgA4x47AJIMtQgEtdBZxcC8KAciQf2XgGfFysGpo1ViGULwAE9AwABAUgCQhEBSNgAB7QCfKAJmQVISAQDgAPJRCIAAKaAACGGYACZJ0AsKAciQKFMG4HSRocpCogbUK49i5XbASCqj2lS2BSQlElAAQcMgAJmQOcSAQDgAAFkwf_RgBZMABVACWmkWgAHmHQCm8bei0FSsAAdOULwKq6coXhWGC4ABComAaYlBRAK+GQEZOwAE8yoAqzzKniFQAP0CgAAAA3FxHh8eAgFqSAEyKgMDlQFVtSVGhh4whJDxAQAG_QgAEElwAtTYBkKDHycA08qD_CcGLKgIoB4gIHIAtkIAADAkF4AgkgGQoEllQDdi5WBVXTlC8CmmEIQABwARajAPQA1ChsAAgkANAVAGMLlYT0FCtXlIBJEJokM8QEAVRVSMFIHgAACKJA7sTA7KgCuFysJ7VRsFyuegUFJP_IwAptWBdoRVQAAAKHBcCQWGPiegui5WE9BQrV5SrQKAkhBACq4pGiOjFRDKAAG0SGUGgEIDABwLlYMZDVQ4FysAO9ox4gIC6Bs0IA8gAucjYCmRB5UqAlIT0qykAAkIT88QEcyYgH0oQHkBDY0AHocDlipWBKQntL1CvKVvBQVQwCcPwLoAWUCOEU6k0BPjB8G5kB5GwDIUFQi4BqRcrCe1UJJQvAASniAgkgC1TguIfAAC24APFgAYkADULAXhKgKjzsqApISTxAQG81YNwhAAAAriQS0GgFyFysBrahXlM9AoKSKXRJYBVf1o3gUYqIA14aBsAZCgzCLAd1KgKiwUoVgEkIp4gIn4vBVKroQG2sgbcaJkAbFQDIUERAk6VBff_qVPSoAkkPko8QEEkbArAAAEIWALIVAMhQADZi5WBlGOoV5TGYKAjPTIh0ADH_w0KJSAACELFvF1dWAMhQE+JFYEpAqIaipW98KH_LmcEwEisDaSZ6HJQI4f3QH4DgFS2AAKqABiQD7hUBy0qAqPLSoP+tQfcKjxAQfQD7IQcQWAAABYkAcHB8oqABMXKwGRqFeUqOCi0gOgkVgAZ0_kmegikqOUUACbmaUCIMgX4TIwD+FSsAon8KlcZgorIIQJkYWUC0qEB9_4pAxIWAAFJHNBwJ0JkYDGipWAUWNFSuMwcFkDEEyMDKBgVCDKdf_KQNuFgbmRmBjYWLgZulAFg4BLEQF7SoCqwELlYACkAL8TAHUIPEBAAAKcgSAAdOULwKq90oXgARwqANxQvJyAETghAALAAowAkLAFAwCUDbpUAVdulQXIWgEoGUAvSEAABKACRYIgoBgMFUhoB7xcrAqr3i5WAAshIAAPiMfYBgAAASLBEFAMBgMQLAPeLlYFVe8XKwAqkNAAB8Rj7AMAAACQsAGHAAQ3KgKjDcquQbA9AAABkhAAAQcGgAB05QvAqrpyheE4iIAAAG2BgsAABjwAOsrOMqDHQAAEyoAAmVB_4eAASgArPgAFcFwM0ZDfUgFUPAVlKgABqFespUAAAAGxCAAV0XAzRkN1SAW4sBWUqAKtZSoAGuvwAAbEIABXRcDNGQY1IAC_5UB_9Sv+VB6IeJpL5OAABghCMgYAAFBQAkLM0ZA8KgALTlQAHFavacqLEGwAAAEFCAAANjQEAbkwCEWa8yAQRAwQ6AdOULwKq6coXgOQAC6DGU4ACSgAhFmaMgAdkQHqSoD_6l6kqALo4A0dgG0C8IQAElCMvAANlXB0ALIWAe+ULwKq98oXgALIW_wdAAFZAoA+OVECDwbhICfSkBCIuVgVV7"
noncomputable def WL9s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL9_1) (dpk j 2 WL9_2)
noncomputable def WL9s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL9_0) (WL9s1_3 j)
noncomputable def WL9s4_6 (j : ℕ) : ℕ := dsel j 5 (dpk j 4 WL9_4) (dpk j 5 WL9_5)
noncomputable def WL9s3_6 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL9_3) (WL9s4_6 j)
noncomputable def WL9s0_6 (j : ℕ) : ℕ := dsel j 3 (WL9s0_3 j) (WL9s3_6 j)
noncomputable def WL9 (j : ℕ) : ℕ := (WL9s0_6 j)
noncomputable def WD9 : ℕ → ℕ := rdw WL9
noncomputable def ready9_cuts0 : List (ℕ × St × ℕ) := []

theorem ready9_cuts0_ok : CutsOk ready9_cuts0 := cutsOk_nil

noncomputable def ready9_0_state : St := ⟨26112, 77428, 28545, 39936, 52016, 73728, 29666, 44151, 29666, 44151, 52016, 73728, 28545, 73728, 26112, 77428, 54657, 117364, 106673, 191092, 136339, 235243, 166005, 264909, 218021, 338637, 246566, 412365, 272678, 477943, 80561, 113664, 110227, 157815, 139893, 187481, 191909, 261209, 220454, 334937, 246566, 412365, 81682, 117879, 111348, 147545, 163364, 221273, 191909, 295001, 218021, 372429, 59332, 73817, 111348, 147545, 139893, 221273, 166005, 298701, 81682, 117879, 110227, 191607, 136339, 269035, 80561, 147456, 106673, 224884, 54657, 151156, 0⟩

theorem ready9_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD9 ready9_cuts0 101 217) ready9_0_state = 40804 := by decide +kernel
#print axioms ready9_0_cursor

theorem ready9_0_covered : Covered (toCl ready9_0_state) :=
  ready_cover_cursor WD9 ready9_cuts0 ready9_cuts0_ok 101 217 40804 ready9_0_state ready9_0_cursor (by decide)
#print axioms ready9_0_covered

noncomputable def ready9_cuts1 : List (ℕ × St × ℕ) := (217, ready9_0_state, 40804) :: ready9_cuts0

theorem ready9_cuts1_ok : CutsOk ready9_cuts1 := cutsOk_cons ready9_0_covered ready9_cuts0_ok
#print axioms ready9_cuts1_ok

noncomputable def ready9_1_state : St := ⟨26112, 128744, 28545, 39936, 52016, 106240, 29666, 44151, 29666, 44151, 52016, 106240, 28545, 73728, 26112, 77428, 54657, 168680, 106673, 274920, 136339, 319071, 166005, 348737, 218021, 423286, 246566, 451831, 272678, 477943, 80561, 146176, 110227, 190327, 139893, 219993, 191909, 326233, 220454, 399961, 246566, 451831, 81682, 150391, 111348, 180057, 163364, 286297, 191909, 360025, 218021, 423286, 59332, 73817, 111348, 180057, 139893, 253785, 166005, 331213, 81682, 150391, 110227, 224119, 136339, 301547, 80561, 179968, 106673, 257396, 54657, 151156, 0⟩

theorem ready9_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD9 ready9_cuts1 104 193) ready9_1_state = 92726 := by decide +kernel
#print axioms ready9_1_cursor

theorem ready9_1_covered : Covered (toCl ready9_1_state) :=
  ready_cover_cursor WD9 ready9_cuts1 ready9_cuts1_ok 104 193 92726 ready9_1_state ready9_1_cursor (by decide)
#print axioms ready9_1_covered

noncomputable def ready9_cuts2 : List (ℕ × St × ℕ) := (193, ready9_1_state, 92726) :: ready9_cuts1

theorem ready9_cuts2_ok : CutsOk ready9_cuts2 := cutsOk_cons ready9_1_covered ready9_cuts1_ok
#print axioms ready9_cuts2_ok

noncomputable def ready9_2_state : St := ⟨26112, 128744, 28545, 39936, 52016, 145508, 29666, 44151, 29666, 44151, 52016, 145508, 28545, 106240, 26112, 128744, 54657, 168680, 106673, 311938, 136339, 341604, 166005, 371270, 218021, 423286, 246566, 451831, 272678, 477943, 80561, 185444, 110227, 229595, 139893, 259261, 191909, 397174, 220454, 425719, 246566, 451831, 81682, 189659, 111348, 219325, 163364, 364833, 191909, 397174, 218021, 423286, 59332, 73817, 111348, 219325, 139893, 325565, 166005, 371270, 81682, 189659, 110227, 295899, 136339, 341604, 80561, 251748, 106673, 311938, 54657, 234984, 0⟩

theorem ready9_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD9 ready9_cuts2 108 161) ready9_2_state = 138222 := by decide +kernel
#print axioms ready9_2_cursor

theorem ready9_2_covered : Covered (toCl ready9_2_state) :=
  ready_cover_cursor WD9 ready9_cuts2 ready9_cuts2_ok 108 161 138222 ready9_2_state ready9_2_cursor (by decide)
#print axioms ready9_2_covered

noncomputable def ready9_cuts3 : List (ℕ × St × ℕ) := (161, ready9_2_state, 138222) :: ready9_cuts2

theorem ready9_cuts3_ok : CutsOk ready9_cuts3 := cutsOk_cons ready9_2_covered ready9_cuts2_ok
#print axioms ready9_cuts3_ok

noncomputable def ready9_3_state : St := ⟨26112, 285696, 28545, 39936, 52016, 239000, 29666, 44151, 29666, 44151, 52016, 239000, 28545, 171456, 26112, 285696, 54657, 325632, 106673, 436387, 136339, 466053, 166005, 495719, 218021, 547735, 246566, 657096, 272678, 683208, 80561, 278936, 110227, 323087, 139893, 352753, 191909, 521623, 220454, 630984, 246566, 657096, 81682, 283151, 111348, 312817, 163364, 493078, 191909, 602439, 218021, 628551, 59332, 73817, 111348, 312817, 139893, 484273, 166005, 576535, 81682, 283151, 110227, 454607, 136339, 546869, 80561, 410456, 106673, 517203, 54657, 457152, 0⟩

theorem ready9_3_cursor : U (walkCut TOP BK TOPD BKD PT REG WD9 ready9_cuts3 116 97) ready9_3_state = 189612 := by decide +kernel
#print axioms ready9_3_cursor

theorem ready9_3_covered : Covered (toCl ready9_3_state) :=
  ready_cover_cursor WD9 ready9_cuts3 ready9_cuts3_ok 116 97 189612 ready9_3_state ready9_3_cursor (by decide)
#print axioms ready9_3_covered

noncomputable def ready9_cuts4 : List (ℕ × St × ℕ) := (97, ready9_3_state, 189612) :: ready9_cuts3

theorem ready9_cuts4_ok : CutsOk ready9_cuts4 := cutsOk_cons ready9_3_covered ready9_cuts3_ok
#print axioms ready9_cuts4_ok

theorem ready9_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD9 ready9_cuts4 128 1) (ofCl (RC 0 0 1 0 0 1 0 0) 0) = 194901 := by decide +kernel
#print axioms ready9_parent_cursor

theorem rc9 : Covered (RC 0 0 1 0 0 1 0 0) :=
  rcOfC WD9 ready9_cuts4 ready9_cuts4_ok 194901 ready9_parent_cursor (by decide)
#print axioms rc9
noncomputable def WL10_0 : ℕ := zfNat64 33248 "DjsNplNxlQRQCCB1LDOQ6xCAAAUkJOCIkIEQYJbh0qDSIQPHYeQttG8eiVBYQAeJAe7KJTGKEABiwiB9caJahYqVhdDtmjsOJlHvFysMoBWYBSewIjqS0d+hFwEgAAIqfBo2S0SpQrC6UWWmjsOJlJqIi5WFWygkYoTghOpdlouJGhyGUg6SQCpBjRmDYAJDVqGRyBo2XrLgBlCsLoAY6bhxMoQAuVk0y2UBvFysEJ1JadmRgAAnU6ZrsdsQOwXAB6oBaFFAFB_8WuKVBdCCf2dPfwHYZ2VBZQAQNdhIwlSACKTUBRBEAGlwcChBDiMnIgipWHU8lUOJluAnM2Lgi10kgD00kkOmKQB7w6ABdGkABrgCQUNwUBEwmAJoA9gmAAJR0AABk2AAABN0QTCWEIKXqdA_MmA_umUwNoAB_lWAAlwfAAIUC4mkABzhNFcAwFsIyCbCEAAFNAD_iMAAhAqAAAAEKwHOWYwPIZ_hK2AVKwgjCEiOLTCZRy6hXCKA5JCfhZMoYRHyNDAAMou4kHAEksO4UQQ8qUm4sVhFCmGzcNNlFPFysIpVCggZS0iWUI_M_GUegECAA2YQyLCjI4bgoBlhUFElWmUw2gfIuVhFA2aeQwemUMJudCAAOoAGgodwp5Z5DP+mSrCpWEEKKkTwymURQXKwggCLPIZPa6GkTSgRwAaeQJsXjSEnBK6ECIMUUeJbi8qDSH8PHYeTaBBKF4WEADyZRKcVQiezUCIaMApvSAmYQ3BQESiYD_icAPsJgAKwZAAAxNgABRHwAiRIawp5CA_JiFQqVg9GI5DCVUhJwqi5WGWqgMY8dghMpZKIu9AjgA1DP_hIAeAsNYUHRrJMAQuVhBJyGU0k5Ug+FysMphKIAhMpdFMZecjQwJNZloRABFC0cDzoxYOklQPQRh47DDZTCpUGUBRDp_Ayg1HaoQEkAAG8LJ4dOOGgJYXKz_x8DkMJlNsnKsLlYZTCAl4DuCEyg1IOoQEmsjUBU2YLMgJDaAg1QkQiAYCUKdBlEqALoAA4qDKAAZQCxLQcdkrQBlAAaZGFID_whtMUklCsIoyw6bhlMobwuVhVAHoBAiKoWRgyNDDiH9YpgF0EMOG4AkB+TFkJQrCKTQNmjsMplJo3C5XWUiKpRKoTY8djkQlUsll0x1QRUjlvKJVrIXQpAnDidnj8JaU3zhlAQ2lmUvmLlYYSqE2cgpMpNzotC5EKGW0KqhXALoAE5YBgJTZ0FFCoA4hVNJGEoDKBNpOACyKAPgAC2LwC9NIBxVGnKIF_LAMBMeKgTANAf6YgCegAAAZGRgAP3LwAC2IPtAhkkEwVKy6RSjbTaZTKZSlqFcQlV3ShPM_pxNBCVTCWQMCNDDSAxStgF0AHMsPh88E6ACqf_bOYGkcynBlAbUnAADePgAFuLwXKeQ0KS0EylPKKiZix20umU2syZsdRKtVB+LxSSaJSqVkQvAjKy2UAD65fAAuZPQvQFcVqYFtJJlAxqhXmINl62A5oeNhRQAYnEA5GvCqC1bQWgWQwjZrC6VQahMjCqBHSKFUrCVCFDLWQMtLwCcoTyLOXcETHT8BiTZrGJZqIV_OiqBIQSD0HQaExClRagbAEkAMKsQoJWr4loLljp+UmomUIJFeOrUUIkUJEFQCxg2CZq7Q8dgpEKLR7OQDcokcQ1patTENBKGZN66ZbDbTacTSOlo1s_RoY5KtVqrZSheHQTNR6QZSHUKDQuVj0vx87IIlFNFDsAQmRDgQXmgSwMkNnM_4vF0ou+zoAJuOI4SS0lIhZDGQ9FoBBA0AHGT6Ftq3lVViaOwmlk0lEolEwiBQo5FIpJJItDgPHwD_4WAIdlIdQuAloejUFIWQPBwADvCSpYHOFqcpNrat4HLPoYBtAOsEwAB0EgSkQoABxBsALRWiKE84lZnoihgv9AZraOS6VS7r0hnJVgMtB_0cRgkgjkiykSQEAyiAACoA6xlks7drqtVFKZNziXTDbbqXSqqZevkiJkeBqNVKspKWMH8CNRyQZTGUKIpMl2EslkkkWkhSFiq1l67hgQ_y5HEsl0L5kCcKoAdJIOSUiFI4nGnsS8AEpivgWjCqV7iAwlKmVUOJYSwLsgQ2KpXAjNJJ6AV8EBzGUjSiteAroDhRKSBA0CkA7J6ADpqQAPqIg_4lAAAAoloDQ8AyyxMrsDVFID270AOpUgArQNAVQAHoB_pGI919CvoEvUK4wVWEvtnMw12okeVYAtuBJoBRS7ARaQC_TEAoaIKFJauxSnlFMNtLtlNplBIrUyCPRjKUUJGHpNnNVABLVsPs_g72GVlsoCkl6+BhzyDDoYZSpjkwxqVjaOTLWQLytTByAg1Efn9z4chJMCGkBylbALoAEoT0uPXdwi1XS_plMKJVtpZMNZAIzYyiKVMkjkUgAaLPRyRSiOfgP5FMpREzKQXQMTiC0AKJREYkj0JcrUxxh5bACU8fxaLoOK4B5y8lFWggT0FaGEZ9VKvygqoM1Ci6RUp1kYkEgklSStTFs5HJFLp5Fo9HJFLNFnpLMF_lI1GoJQAinhIjtID8On4BRIpJHoVXMh6BeRaDkAM1Ty8hZKIGTXoFVFoOQmjgUK4Ulq2FSCSSqZVGhiGMC45IXJwcZD_w6HoXS+gUikkD8z0ACYtWpi2gn9Mm5RabWRCOSCVXMo0MOjEck2um03gobGM1Jplcc3c2zv3uEi0Wn5FoAS3awABjbad0iNkEQwEHJFOisWxDJRqSXYoUcKiEWj2um0Mh0Q__OjK+FyZq9f4SEQ6G0Wg4i0yWs0lWrNrnJBptREopypeOQknj8B0MDjIhFsxqttSoNFw7KRilFgx3FMr1_hIVjohKtpXu1bxaZLWUep0sfrNrlI1oNJFs1S2gRyTgY7JZq1g6f3G2xkSzGc3G4pdev5NgoeFZDKTLYU4t2sBwsr9s731cipfpI5BzOSyHRSJSC1FCjhkQiEamE2puFDcZCo1MJ1EO9f5fDQNCIUdwMRxA0PACY0mS1B9BKBaFkCodOVJRKA2AOoDkIpbQAAAQAkNAXrQK_PgHTLQE0AC8gAAKWIAAAUPAG00MsZVqcloIfzJuE1iahTrNFoJJKrxUaG9w8hzkgmoUqdlPI9HM9KJluqX3736CCOtpCqHUHQcJaySTYKQdUB2EkMI1JLZFIy30kygzJIIE8i0ek0PpgSyl0D6zsA4SqgYtYUEekpB5ly3KR6OQoocQlbkFBeAfRaAAkDoKoA2h6AMBYmJsCCYkqGAmxYvy0cjUJorUxaK42APopBaFUAc9gwql0DlB8BoW_kTAwfu4XkpQ1G0wkUg6yQioi0egPAeP4pB6FEwIVSiBVI+AsgQ2tW8LpRCSUdMpl2wkkelUjytTB6MSaMQfPZdJI5JJhPqensGZNYKZJ0cjDUHoHgAJSABpwAJKABHwAM6AJlwAIqABEwBIaAAAAAAAAAAAASAwYs9lJRj93DfL1RCaLQcN4SR6E4UqdJHoB5IIOSvzEHkAA0gqFEpARUgZupAPkbgIotlSAA+gABZcgABRLQGgCIuAJDQAAAAAAAAAAAAwUPACQ0MS7AWxSAbG9ABm1IKoDkUYAAEz0AAEeGgYWggAJWAFQIYSkIoPpw3j0ymUTqoVwMipnAJoFULIpZGh6aLjKUQC6AO5qEtPIZiswbymWglFo3kUymVZ7FUZqVQB8pE8OhZKydZQqDbWaqQFdALEjlEPUEQibChaFpJJocQyl0F8sVwygUcLgOlWml0NWgQwy1kDny8F7GS88h87ss5KiSKy6QaabazYTKfNgzoYVqdlI+oUwo00mz2OlVPC1WZympCh00yk0CgJRdLPFOx2FBwkzoZuNsRUADSSNBUAgYA2FysBMqYwchtNI3soXg9dk1hKQOpLRrKEC2ax08gBBKqAYCDYNBeomAIIG+lZ9xMAAABOQAApFQCjQpAwpdA0bJal8oVhdKI5LS9lkzk0h5YvJ7ZQAaBHqIETqZZaOWspE8Fs1jp5BqAoIGQigCgI0lQXRt54_DyDnSoDCAB5J6agQiO1UBdhkAunSG4KAiYTAE0AfcTAAIwyAAB+dAABSKgAJVQ3BTAzoL6FQADkyWHU2gAGmj4AGo7Y+CiAHMNgAAiQCYOKAKyadEVCulJDybSDacABaTIAAWx8fqHgAahMAgoOG4Kq8fB4BSAA4l0lQpFlAYedAdT5y0BBQOJIQBm0QpBSTD4HeqQEOzh+f8Zg2ipAASQANiIQTUqnEAABCwgk5jZ2yhXItFwNQsl0CopUwwgfGPiSlUIJ2dCHwLApJpRONKwAYReJj4fJ5DBqpJSpgtfChTULNdCdK1MqID9zx+SUslBKCMQakEsyk0qpXB0ABCwThz7EJ+BNCCogyA01kWiJTJ4XSqDfjh+BlJodxQgGpND0SsAdoWG4SeMfAMRSAR01AxBlTEEkBDCEBVBqAAEegVQEfixQCQfEI0sTFUDpLhy3hZroVQs1EP0I0cDCEEN2hAJSqbfwFWe2IAA0sRseQyajMVKYLQ0hZLq7GJLytT_2NU1FykA9A6VQggikaGbQcjkoiUqgDwFjCcN7ADyGTUZypTBaGkLJdXUxJgVqZhpoA9A6VQghCkaGbQcjkoiUlSxXAFOLZGYN3hID8mp7FSmKRaVRMNG8alkumFv6hXmtNJpJB6B0q+0Rn5BDXIUOIg5HJREoCVCuDs6NjYTZl8ET_zyGFVDqhTAGpaaygc6qIUQDRGS8KqUEbwhQw+lE5U1CPFamAGKWBQPIYGAUK4A1DSdJeKiU0CWgVQgnnkIuNJPwNQexSpgcgsOH4VSiFUmjUNKOVi+Sk4fh4UqZTSaQQcn0tAEjSUqz0gu3KiDiBSuNJHJpKLYFKmDo6AbHD8KpRCqTRqGkuirOH4qlKmU2WidvZCJaSUqhBCCBbjSRyaVrKShlKmASs39NSKYcPyaFEMJNbsaMyqaR2rFuclUppJA+gQPoMlKs9EoGxCf0m40kc1kojaTKYKKFpI9poOJKjlE05o7qJlKcyYyDUSjTS6TT6t5etsYQoclKM9Ko1RieQyTcbiOTLSQlqFMVE0j13KNdJemUwikEalUw1mcsWVqYilamvuViSfVxL1ski2ajUqjkA0m40mY2UogETKYqN1KNdZ0pTwWykWnoVqdVKImj52H5Wp0UmhcvFoxvJNJItmo1K06eyaVx670kPTlzpMxspRKIDALYBAXDYnGCegJcpAAHWzrwKkAA5AAqh8dqAEwKQBgYaVh4CRlm4D4OyKQDVDBuGmsv5OqiUkCWgUSenzkL_gFaSSAGBMphUiRHYYcPwQQmUwJp5jRnWTTWfqnVRJNJCey2UhRJ_nwSQ8h1W0gySo4AhEymR47OgBIyAHlwAGiAIhwAGKABwwAAAAAAAAAAAtRsBFwsHAA2kAnLh3McB4MABUmAS4bMwAUgAKQAHjnD8AALhAnBeNMRUbGRsVOzknHaUH71w3AwRAUhWRKKuYNwBsZQrAHwmQlAAHUfOwAA3AwT05Pbm5vAjseAh5OQm4a"
noncomputable def WL10_1 : ℕ := zfNat64 33247 "BgA4kAAAAAAAAAAAAGSLFAFVMNgGQbMwkgEWu9eLpaFlaysA9CygGpQgHo5AAJiLHeFJKOm5+8sXiELlYTd0KRxCyaSqNQqlEJkZOwCHEy1UeiVXiNHAelWUiUIgC4qigCgflQI9JgJwOQAwAqAC0gAKTOg_0fAAAGi4AkNAARIAAAAAAAAAAAAJQWAAyRQBQD8joDUTsDk4gAAom4AAEh8A9AABkiyYhyfDYPwnxTQorp3CDZSq6sAA7noAAIaEA9JIABRRZCi57BsZQOh6E0OoQTKXtViigH0CiAAPSTKRS5kAakWL8i0odA5O6cPwmhxCCZQYy1XCTYQSVBfw6WSj_1SqIcRGAekmUnFy4qSkHi4EFCY0BGRUCcVwHgzUC4EdkwE3joAOYTAB_02AAUmdAAAAeDJULgnsVAf+TKYHTi8JKAAW4hAAGZPiygCekIAAVcB4MYIuAxRUA4A+ABfKQB_hSLIABgj4_+zAAEbDyJSxmTEyxUrBzWBSHJJS6A8Wq4EhTMrDkspJAfCgRyyj2k00IwnSwAC6wxpYzJicIqVg5g4pDkkpdABLVcAMnEhByWUmgNhQI5jk6yj3VKVTRJCdLAF2xGelwVPKgF8HD8FphP4KwAN4Om81ACrqEQTKAZSSgdNuRIYXC5eTRiKTKORsplMr5o7rMlLo9CwtV6aSQQlwVKY5ntlJIUSirZGhy0wjUk00CslSzBACQ0WOWMyYsAKlYOSiOQSl2MR8OparhNHMhKo5DKTR6WbTl+oEcso9_ykUyaK6TJYIWULzpli+ajEUk1OYpTwamjsYiUuj1nStXIoB0op6Om5ZMoFNIwjQzSXRiEkFmiSydnTuBAALMAaUgCWUANOgAJkANJgAosANEgAAAAAAAAAABag4PZ0gAJ0ASEgPBpWEwWCJgJ6AMEHgADkTAAASMgAAOQEDv3QAESKAKDKXAIEqABAqUwCVJUAA1AP+KQGpSAACcRFbNjYIjkkaChODQaxKgByASXKgAoqMSF4ASRjudCAAHoOJwZmRnFABm8DlQgAJsAVWVBVGmnkMBNtL0tAAgZL6AOAACSkeqDgAAWrPwTRhBkSIUgbPQ8AwCpWAOQACZUBkCn_EoABqFEAAKQMACEuEEGADoVAEgPgAPBUAFAAAAAAggwACc4LUXCCDFBKE4ADKgDNIQGUKCVADf6GwAEZDqgEoAAIIMAoDZKgCQUjQVoM2AhJQvB6NzPH5TTadyLiEgUAAjIkBSAAAAJKwPwqAhNG5LU5lC8HpPSmm0wKt6IuISBQAP9DUZEgKQABGgoAAOsDaKnejYJklQ1LoRQ4fkE42kauVEJ_gDAAAREfKQAAoAoAihUSlVMG5LWNlC8HoPdSLVNNo1FYEpYvISBQAKAZjPfQp6qcAARoKI8B0lQPZo3JatcoXg9J6U02h_VvRFxCQKAnxKAMxkeqnAAEaCgAJIwfOuWQMgdmTADkAXoTAFAAAH7nQAAbgoACaMFGKiBDZuS0_pQvB6T0nppPQFwBQaNRJB8AGYz_4SW4pAAEaCgFDw8A9yoAONAlmjclqiyheD0HpTTanhW_0XEJAoAAZjMJemnfqOgAAbASJETKaNyWh8LlZWQclNXq0bzcBcQkCgAB9EKeqnOWFgAAEJFQ4Zo3Jb3IuAaHZ6CmqiQVq5Pjp2QmC_HLibMQI6ZRbHNOcsLAAFCA6SoARNHcTDHMG4LV7lC8HoPSDTTaL5W_0XEJAoAAZjI9VOC2gAHQPGVHyPBlMG4OdKgegZkJ+U02jcyohP+gYAAOxkR8pC0Wk1bTMB5ADCVA0LADwKgEknwf_ag9JUQkAAIyDIWi7AkAAAgNUOBdMG5PZSD0ogwOH5TXLtG9hytTFpCQKAOQDMZhIw0yeEwmC4gtg0ZgDuDmPJj+mDcmz01hUrB6D0gk00omWv4FwCQKAAGQyI2Uv8CQXEJtGxOgF8qDSiw3CwAjoALVi4GIPlqehFNKgFoWgJAtBACchkgUpAFmSkszYBJRUKQlNsyA5pUf4Pjb58E00i+yoBIAAMQyGAUgQhEuhahSBsXG5mdnbM7FScMh1yAoqAJDQ+gAHoPg8Q1BwSo_shBkAAahkU8tAAAAEjIorXHBipgQK6VAe0Qn4bTSL7KgcyUAAehku0pAABuEgAg1wrMqLIywIGRKishuEJ+G00mdC4HMl6MjAAPQyf8UgAARBQD3640AVb0XYEnN8C4LIPSKbTSIha9MXA5kpFBCCf3wQPQyeOUgAA3BRUlIASMgDZUAAAAAAAAAAAA2dpyExHQAkNAOBQV5KgHKHD8LSTNKg_81B3MqA8gH0QgAAACQ0SqULweWULwByFpFdFysLtlBsJIrDiq509mmgif0COAAAdACSsBtUgANcK+ngCCCoCYp8H_G4SGVBJALIACWkJ+AARoKAPlvAF9oAkrAsyJ_o+CVRUBXQACR8AAH+moADy0AACYKAOAyCgJUAdw4fgaTNpUG7moP_HwHUOJHBCAABMHAU18MgUYXKwByF00hNi5WGElzVnAegdRPDlrJyoQAAJgoACSsDMZBH0qAHoGkv2VBWJqDxR8B1DiRwQgAMWEQAElY+QyDWJUAOQupdbNYTwuVgaQHoHUSw5aywKEf2RgBkx0AAZWEqNGYdDMFysBFpo7C6aQUhcrCz+JmA9Zw_DadS0jMEaGFEAQePA2Nh8fQnIARVhOWkABqhNAvg0BQIyAGiEwABiHgAAOFQAABgIuQEYpC+54aoGgZ5QvAAccPwNpw8uCSZT0KJHLJgTqGBdCePwACNBQBN94AdtB6CIoBr_yEGESoCsgAFdABA0kDGbItVgAAWhQI4TRUMg1iVAACPHYXTSE2LlY6BiNID0DqWDaOZOdCAAxYRDRxcMSgomLlZr5aKI5C6aSjJw_i5WFkygZ84fk02nUy2kbYjQwACCESMKQpRofRszBIxcrAD6aOwsmkLcXKz+qxf0YzAPQ2nUtI_1AjgtAAEcJlIGjMEBFysAepo7C6aQmxcrBgzMA9P+N1xLSFaRoYWaiAjpIjgA4YghjRmfdQpSAV80dhdfaya12J0pCyZQJwfOxybbiGhmtJQQs1EBHSRHExGNFBHFyswlUoiBNHYxKJpJooi5WSaqZRGKdOSSYTiZTSVTcIUM1ZInFArU6iTSKENKIoBY5o5wQXAoEmArgdACAiYAKAnQAC5ToAAag7glIASVgBykABFgBgkAAAHGQAAIOAAMh0AAAAAATBIoBpYysETyoCeh2JqHllQAKoPgLIB5EIDoAACAwIDUCigGhGGjM_ehBsLlYWTSSQu2XHic7ouVhdDozZwHobTqZbSJ3QI4U0YgA8IZAQAuVjUslEchdspNOcXKwsmUy2nTkNp1KEzGkQ6gQyCDxJNthOJhWQQHwBdKwAGKGVpFwXVKgGRHjsLtlGDFysACxHzsDiWkLygQ4yETKBa4eALRXEMfAWsKg+CsUUsITuKgAHoAEhj4CIAbIeAAkrDkaIC5KACA0AEYqAJWEwAf+UgAGBFQAAKC9BYr56QiUlV45o7JoTzR3USjYSaIQuVkEo0mWxNTpyUS7ZaSaaiM08h0mKkWm2EilKPHYAht2CDJZOioYhz0qAPCaOwDKZUAA_jx2Gw2YAggADCKG4NgAFuAIqw2e6AHlwABA0By5CAChBwAEkAABxUAABASK0dlRkboTkEw6QAGqE0C+DQFAjIAaITAAGIeAAA4VAAAGAi5ATGsejEGBFysAcymw2V8ScsIuV_gQkgLF+ygKRqbTrRpmxjE98jAACDCgACbQSSuABVQtAicIe5ajBVkqALoAA4qAAqogaSAHloAAFoUAShSCKz3bFwAtARC1PQspSloWzkm2UiwnFkmmk6n_mYvUhQwACNBQLnHQR9KgB6FsWYpqVDkA54fDUOp_9qJVIQABGgoBEDW2S8BawuCyCeQn45NNlJTSTKAzI4flWojcdS0mZUIAAjQUCooStjoACogdSiBUAB2YJtH23GYPICsj4AABwMAAuuZ5GaMVBVNOAJoGkAMobuUiqHUBW58AAKAKAlt1BRdITRX5ApAT0AkgEx0YAP+HQADwTYAAAwEAAGuFS1RwyiBIuDMZAqU+A_8hAHYz4AAAAigAAGAgLdM4A8dAAqoAiLAkXAwOg1shAABQQAAAAFEwAAABKLQcmSyCYRlBMjKoSSTWTCAVSrk1tahXJrElamQRyHRrWTbgJk3l3ECtTBkI0MQMJjIBMnUJE8i2W6adeSqFU8SRPrJlrIlVQr03_qsSQOwcNyqXbKWSaKmRoZRNKAAC4kAGnQA8yAJCwAAAAAAAAAAAtQCzvAAZYJUFVolEEMyqFcBaRw_CymplYAByVQsjlnDCbhQg2j2QgAsCdLEtNS4ABz9KVOi0EokGkk0u0kzStTns1JI1jJ0DJm6ZWplkylkm0Fep5DLppMNlsNVOuYMwAJNQA06AHlwBImAAAAAAAAAAAFqAB+ca0YogptMpgAF0XeoUwAI8WM6iGkAzZ5DMJxJoHujIAMHMIKJLpplwL41CmZbqZU_OW+w22ymUiitTpoSRjGZjUazZaiTaCsE8hl00l2wvMZsdVICYMwJQ5WbGwc9bRYlNORgl4rAc+KgNITQAMv_1IA7orAABGgoK4UAA5w3m6AQlwJFwACDIDqSEAJ7NgAJIAAAAAYCK2NBwsAWlwAAAAAAAAAAAjcWPuaEpuzsVBrFcAwEHQQUNAbeMgCPRMAAxAAWoVAAAGAgAGKQBEyAFlQAUWAAAAAAAAAAAAOwXgAlUKQM0AwXgBU2CigWUr4VBYQqsfOwPIB+T4AAKQMBoDEUhGiEKQNESUq2KgylDkYDaAV0AEDYf7ixNxCAACkDAOiUhrBoiSkS5YvDKYUJoEcDaUT9jB8MJtrJaSO3Uja5jltZd2gRwAA1gwY38aAElYNoRG9jQG6LlZf5eCqHEyksC4K6Ae0EjSSQZIpAAAQBgHu5wAzgkB+BGAC8BwAB2OgAAAAAwEABJGXyQg1iVDeFIHIbTKcLKgWgEEDKAOYOZhVCAAAkFAGgeQyYgCKlYQekJw5DCZRFhcrBaUQLqeQySmUny0YQ+6BHAABKFAADqk19EA0VABwaAE4hAFND4AAAAsgAAGAgABiRwB8GIyoBAR47DaZTPJUDkAogZSKDkNmQgAP4EQ+kZbkQg6KVH9kIP6aOw2mUWcXKwcgAcTKYGUMJH1CAAJ4dAYpMPIZMSlFSsIJNHIHEowmV0CcYQuVg5KIE0kplLKUHDGOuRoZ_0eAD5ExNzMKBvnkMmIPipWUEHJxMplF1FysloVlICCSUwieWjWNBQI4AEHAojw+zjSEAA6Qb0uAJBRQBQEkSosIARGhh9aU9CySoOWMwAIGugjRWAAAEHEQBIKBEGeYRBZ8qALI05yARZUEWugAaSSFhFIAAAADpAEgpeB5_g0GdyoAaR47DaZTcZUEUAggdSwzkOsQgAAFJCTgiJCBEGCW4dKg0iEDx2HkLbRvHolQWEAHiQHuyiUxihAAYsIgfX"
noncomputable def WL10_2 : ℕ := zfNat64 33248 "CBfBoCqx8AH2HgAAAANFQAABgIAe6EG4MK4yB3pUUE_yfBRto00qAKgAOSKCEEIAAG4MBoDuZg7BgPqiSoDoEJAfgxNpFMqJKA5w2AADYhAAA7BgCblwBIKKAKBcC9G8qAnoUbaOfKiS_9PgLCVBMYiDPlIAAAAkrBVi4C5F6OJUf3QiehRto1EqJLPQGuVBMYiDflIAAjQUAUsudsae+YNwurmLlZQSq1o4fhRNtRDaULySz2UgtmJMYiDpE6eABBoKAAFpFkTD2KgOiTAQWOgAwRMSWcgaQ_8ZADPOgAA3BQBfS55c4ZFdZ8XKygg9BqbTkRcSWghjZaMoMYiEU4CkABBoKAAOZBSy4CFV6HJUUEnoNX+N28ZKVEl_2hAGEGMRB0ykAABAGA8AgGQRwuHYMj_ys6swbklmIDWujElxkvAMlIoC0BjESCHaUgAAIAwAezIKuXK0GVFrpTC5WSTSHeeO4NTaC0AyWg_tLpaH40ZgMYjDZ769OAADcFASAEzINEXGFGwUQAAwswPgAAAB+S0AABAGAWPhQAkrBSyJLwyDRpUMPVgehRNIpEqJKPQAGMRQI9pSAACSFAIiLoHPhsV19xcrAGBw8ojGkyU04OTktlC8ko9FJZIoWlzODGIm0mszTJ4AEGgoA6ZkAJLl1Uh8AawDgEBkRUBuFRJR6AAxDyLgVgAAIAwA41YMKXAY+GVpIlQDQagVNIs8qFMlHoE0Mg1CqmWYNkpAAAQBgpj6EABaQXDQ9ioDokwEFjoAMETElnIGkP_GQAzzoAANwUAiouJUsZuCMgqtaLlf+2YmjIjx2aSSbT2BcNZLQQACDGIg5qcpAAEaCiFu6kpO5XDMaclOQB4RAEgoUgoghEC7ioDZ58BtESlQAAAkOICxWAAAAeEQORECwioDNZ8H_G4RGVIkBgAAEhxAKIQAADAYAK5Ek8TAWMsXgD4OH4W2eitLSCABrCowgmMnEB8nAAEaCgAJGQFgiB2IgcqVAdBPgtokMqAAAE_zGjiAsVgADkgwADzICSRB0TAcILgExIT8LaTiLgAABMZOIDxSEwCQAABSIgYyYASlC8AFSE_A4ltC43A0AB_5uBMZOIB1CAAG+ZAAPbgAZkAUqgZiIAGFQAyj4AAgVAAACYycQDy0A1AdcPAATMgYBEDmRA+cqABscPwtIc8qAAAE_5GjiA6UgFoxA95UDIDNgMeARCIAYFJQEwC0IDqyEDh+FtnUrS0QgAK4CMIJjJxANJwB4wyAFICEIguEjKD_SoCehWRu3iLSohAtAAAmMnEF8pAACyKgBykQXCRIVIIylQA0Dh+BtESlQAAAmMgDxSCilIm4_s7AC5qgCtCoDb58dzUv_NwvEqAAAjJxAWKxTB78A0UQCCAMaB9jYTvVAEhoDgeB+BMASQARxMABZAEhdG4mwAAAcgiBzIE4CrKF4FVXR47C2lWgJcAQ0O0UwgmMg8ZSnrgEC9FAAKwAIfAciJMh5HB0AtADshPwtpOQuAALKCYycQEykMf8D1lAQcdAFxIgQ0kjQ8OAiDHJUAIw8dhaQ5pUAAAJjJxAeKQHEAogAeqguEiHkQWkLgFrnkMLaUqLgAABMZOID5SAggPWMFQAgOkiB3IglOVANQOH4G0lEXAARYPgExk4gPFIBqNQdaXAEUIkCIvAEwJzKF4C6jx2BtJSFwAAAmMnEDGnB0Go1CHZcDozMzs3K1NnKgJ++GxkQdgxPQ4DnFysCih_VmFhFwIEww0AmzUFqK1cAAHYMF4TiRB+AuAnrdgYto18oXjaGIBmCE_Cs1E2lI0IAAPoUABJWAKlwASiAJCwBtJUA6xCfnrBa2kxyoAABnkMCyG0f+hAAAAElYBEXABaC9FqegVtqHVZWpQvDgacBBLiWS2naEYGDFQAABNeAJKwA8uARnKgEPHD8_kLG0y2VAAPS4lkNpuFCA0mEDdCQMzdyAEgoOQo+ZEE2SoApxw_C0lzSoBiAYEJ+BJDaUTQgAAA5ClqkCcHfFysAUB47PlnRtDoFysqIxBUpw_DCSabaRqqBHAAxYTAASGglB9JQvAKQeOwNohouVhVGIJ5OH4VJiJNNtIq1Ajg5ACwCwAEhoJQd0XKwKo5Jy9Ru11FFhcrB1K1MYgfk4fhhJNNtIrlAjgAAAiI5AnByBcrACUeOz7J0bQ1RcrKiMQX2cPwwkmm2kc2gR6wtRFAMoIQVLIsnjiMDjFysAr5o7A0g5i5X_xGBiA7D53SR0ydLLSUE0gS2TWAKQZBNHi3FwR9KgB6HdGDWWtKg8gZBPQFIaSpKEAH0CBnQLJJBEHAGGIgGbmQATYeACbB0AAYUuAAMoCDQogw55w4rCAJQvAHIWkFoVRiuBCKo5zyGGEikkyjYWL4H+ShPFQDoAgHUWRoSAYyULwHKHD8DaIeLlYXRiA9PmMRFAdOW8nShBxnocQLwMFaETEhxWDKC5WAOQtILYuVgMQHMfOwIph040gkkKGGUo1E6l9C4ACQ0YcPAsguVgByPHYG0HQXKwGIU1OH4EUNJ2tCDKUQ6lEC4FhIE4dBbRcrBb1xSHIGkAIXK_nJRLR64JOnNJKKTTTxBSQqgQzwNG+u1GonEwi0nZ2blRkdGxUDkKAwlCKgqkdz4LCM7KgAUafAFQDFIQAAKwYAG68EgLgGAgAIHQAH8mIOwdAAABdAPLQAAJgYDY0FkXwCEuAYCAQkPAD0ARUPABgo+AAAAATAxXgAMyAGFwBIX_A2AZWVAXtPgNpIcqACV58H_1oNovRCAAAUgJNmCTVwA2mEIKHoGW_lQUQcgaTrZUABoD52BlP_NRKhChgABCCgALIQghQBJSheAno4fgbRoBcr_oNA5CFh8_Amj02j40COAAEIKAMshAJqIbgqsgA46AKAIW5Mwa4qAAD_AUG0XedAABCCgNQwTVhADzDwGukIAP4PAASQAANFQAABgIACRkCoLgDayoA9CE_BLbSqZUSUAggRe_JRpE9oQAAQgoAEBcAieVAT0DaPLKiSgM_Pg_InADWQgAAohQBPS+vj4AJZQvA6T0mO5mTWH_KF5JZCFHEIAb+4ysoGNCAACiFAbHxoJqwgB5h4DXSEAH8HgAJIAAGioAAAwEAA4uARPKgJ6BtHllRpkoDPz4P8JwBFEIAAKIUASsuABJKF4HSekxJc0Zw_5Qv_k1SWQhRpCAGjGygsUIAAKIUBsbHgOgvD8obgC0EkLSpD5_7QyCNtGzlC8syWmgt88hxkrNROJIBGAAMENAABRgNJcASGgDKyoC9p8BtJDlRJQJXnwf9Wg2hzkIAAADSXAGnlQCGEJ+FtFGlC8koBwTyGFZqJtGKoRpAIAAM49ZgIFeAC4Qve2EIOAHGVAHDPgX21ApJKAYQAA2IQAAIQoAcqkIQcAS8oXkZB6B927WFPKF5JQPtG8DaFRCyAlQI4AAIQoPwKUXMIrCYBafsHgJCE_KDbRGZQvJLTQlgfOfUim0GwgAzB4B6AFqL_2YgI+lQIQelBMa3axJJQvJLTQyIfOXUimlhBpoQVkAywsDIDHlwmIksAWiUQ9nVhUHD8c0G01Fj5QvlPgyRHTSLUQCHD+ElNoNhHKmk6W8U6AAAECXAEhoABwqADEfH_UICMFQAA6OgCTDEAAAA+PAY8DzF2ZkQH7i4EIGxCflBto5UoXklppCxWnoU2gmUAShHEWykAGEAVBcB+FhnIgP3FwIQ8iE_KDbQ_pQvBDTQkQfBTSwgGUIQIBEkIBoi4AFEoXghqo9PRoDs4rdrqLkyheCGmlRZwcP4rJxTSDYRyb1ElgZAkjk2CRHAQuXeQXAPXKjaREHqQn4ObaSFKgQ00ItHwU0sIDUKgFN0IHRsVnTkdszGbp7shJacdACQ0C0LA0csXhVQeHD8LaVVQli8AAnM1FUCbqUAAAKLrhXBEFwMXQVIRAWqRgAAw8AAAABleAABcDACbrhL5UPoCxKgImIRZTKMrKiogkAASj0ZEpAAAmCgA+1wfsqjgiPoHRKgCCWUyg0SheVEEhq4qDCCUe5eGgAACQMAgQqAAiTHGSBCbxcZUWh7Pf3IVlMJVV2ULwqgkHvPCoMIJR6GXwpwAAGgYAfpUEI3AAAYOg08zBxCoAAA_4fAHloAAEQMAjEq3o+Rc6ewOmVAEGo2Uyg0yheOaiCQR8VDkwglHospSAABcDAeU1NSQgCJeAD5wPA3_QgWFii4NJVnogTbVfEFwQQCGAcGUAFyMAAEIGI0ISGw_euEIGDoSRJg5snD0ACx8AAAAfPOgAAhAwADGowYaNgpOgXK_tCxdByEXQLRrCvlC8KoB8kB+HEygSURgAAvhQAEhIBgIAACEhAACgoAAAAAw0AAAASEl3kIM8lRXQZh47C7aSE5UADJD5NAsGUAraEAAApjQJzXAARIUgoBexME0wUlABzCYAP+mwAB_zYAAAADXAEhpeZCDWJUV0HIXbSRXKgAeYfAZQDXoQAAAap5DJiD4qVlZByN+WL5pGElC8MMqTwB6HUyhRLpI2ET4AAHRFFWeQyYykrIllIchZNIx0oX_9MqaAtI4fltMKMlooi8EaO4xozklAWaYNwDVPIZMZSVkHIlW4sXzSIlKF4VQB+I0MuhlALOhHCSgAAAGGQgnfTKUlZANmjsSlmyiMSheKAVgB6bTzS8A19CCSMQEOLF8HRFXEhPyYhAKlZWQc6mJizZREpQvfssXwAem2+ztXQJ+IwAGLDIAEY0golPIZMQfFSsrIOQspIas4iUoXlkAHqlnDf5xy_MxYwK9IxhJKAAyAQwpFHIhPyYsPKFZWR+5o77YjFmyixyhePEVgB6bf6OxlAx0jE0EIAAQdWO9PgqmVBdGEHD8JtdGYlRFAG_olM0gAsVC_MnAArg+BFUUfPyDMVNlCsm1kojkslkJbJrJrEyhfUSbSQqjk0m2ulluClPno80CPkRKfcgPxiQTCSRiXcrOlJ2EANYAkNEsYy4GBDwA5AGRDwACkNgAAJGQAAA8U3YANmhdTyGTEGBUrKyDkLJpFZlC8JoA9Jp1MILF5dCsanRhSOQBVyZTAGGxApnkMmI8i5WV0P4eOwu2ke6ULxyAD0qjhGYCviMAALIuBjBMnbMfO6CMRTbSy29MpjZNHZVLNlJqWSheTaLQFGCiOTLZS6A9YWgR7TRZaElOQbMydwSmdnY0CmSRQBQbBIEHEwFIjoAPITAAWYubgAK5OgAB6ABKuDKywHgyGBoFGEwExkIASwTAB_wuAAQwZAAEkAOdcEkCkaCq9EQZFKgM8IksLtpGelQAAF0FoDxSACiAEAQADLBS4oDwYFBMAIh4ANpkAEkHgAJoABrjIAAogCnrg6QkjQVSMuBz5UU0SIfPwgmUZyVAAAVSrVQHikAAGQBAAKEBEqgs0kAwEAVgeAc4ZABah4ABqAAXYqAALoAAUYAWhABDIAKXABSoAWNAARYAOJAAAAAAAAAAAABkixQBVTDYBkGzMJIBFrvXi6WhZWsrAPQsoBqUIB6OQACYix3hSSjpufvLF4hC5W"
noncomputable def WL10_3 : ℕ := zfNat64 33247 "BAHtPgNoOkqAD8ZkAAYBWAagf9PiFADaEAeFoQVgMeFwCvTyGCMVgKtnMucXAAAAA_QhiGUAI0AQizxrQH8C4AOSE_C2m5VhaAAmhxGAAb9CA0gWXLgOjIAPQgCQs8K0BYIuA8eeQwtviVYWgAcAeAACChAAAHQAbrAGkIAiNAAgZpGsbAj4qAp+fCkNon0qAAAABchAAAHZ+7AVwsUAsAXkoXgCKOH4TTaC1KF4XbCB3SRWBNAWqXAACCKF4AHi4DGLPCtAWKLgA8tT0LbVQSlC8LIAADKiJoRcAAJQOxtjOgOtCBDywIKCBsKAsAXAByQn4W3xqsLQAA8HAAYVQgYgBFAK0RAjpYGgrph0C9ioCegAEyoFJMQAC6I0ViWgGmE4AhxcDQUEp5YXAJxanoDSct9VFoKQAKmHwDP04IN1F4AsmGA8i4GgoAWgRXstT0ENtTgrDnKF4KSKBbiBeFRHeLmMCWlELoqJetgABMgVZcAdIgaCgFWlQBSzyGFtCulQKQP+lQAVR1ikS0AbyrEKBlcIKZLA0FAL4IgOpGwA+QmAAagAHyNgACCAL0vBoOAFoeDVh6R22t4VnBFysFINYThyEpLD_pO9+jEtCuh3Vi+BpCQmI2AATIAaXAExYGgoBBBUBMU+D_zcJDKgABEHAAAAAAKiuAbiwBVJYvCqj0LbtpWaKWLxAgAiDuDDwAJpRgYgEJIGBKacAbSwCwRcAHJCfhbfEqwtBaAD0OAALqhAAIDNgAmy3OIQxBt5UBms+C2jCyoFoCjB4AA_CEFZAaIbAAqlucQgHIli8Kwqw9CruVtKpPyxeC0AAAVujAAOgOiNAFJEBelhCFiqDWyoDIZ8BtESlQLQAALIPRCAcgIGMgAvywYgE0oXgT0LaP1KF6eCIWgPqPIYVmbCkcT0qEFZAjCbFCAhZZelYwgbMsXhVR6GG22gVmili8ki2+xcAGkArKjf2bgACqaOwA3yzHLQGWC4BOLU9A44VVhaRRaVwmAP_KwBBJGAAcubEaAEEYA0hAAj4ACJAAACJkAAGHgAAAATGQAAEiIALxsAqlhCRjCBMioBYB8AAOKgAogABJj4CCAXYyAEpLDCEeSoAV54_C2j7ypSCELXzJwDUAB0aEBJAl4bAC5lk6WiKG5i4B+SE_BpFis0maC4gjE6gAAOjQgALRmwC1YCflkUWumMQDVKF43NOABIT8LJxPJFxBFoxAAAZqhAATrNgBJy5CKxtxoFo3SheHLVYehbSqqMsX_SQhaAFk0gE0UY2gAORDjY+PjQ+PAJmEAVaVAFJPIYW0TCVAABwOOMFAAGT_D0AHzbgAA5wFrCAUVXlQF0z4LaLDKiCgaGPgADDqTqg40gC0x4AGmEAzQXAByQn4HHCqsLSCgAADOU51QcaRrhMD+h4wwGxhBK74AkLAyDCUHK7SYDqx0AM1JgA_8ZAAAdOgAAABuEZWlBh4uADshPwOOD1b_xcQUACUgEkUnTBxpAHGDwG0oASRgGIsAUSVATHPgNokMqP4gwAHA4AAHSsAAKs+AEvLAWRIfQPYVASFPg_83CJSogoAAAKpWlcPAdAKmfADgZgDYs_wfAAMWOgtoeYqAAAAA8tSmHgAEqfAaAMRYBfwuATi1PQtoB1SuLSCu_QgVkTAAEfTpTDwAJdOgAqCwBVJYvD0I1VHoUbbtpWAqWLyCgBY+fgAFWk6Vw8AEpjoK8MARiwDlxcBoFoeh5ttUlYWkFqIIMRJYU0P6JSQUaVw8FJCqHw2ACwLBCAAyheTeYgeh1nDvbW6KwtIKAAAGBTpXDwLQLrWjouZkzG6cxANxcASGgCqyoCgp8AHG7eJhKgABEHAAAJQAqyMAA4yA3FwBVJYvCqj0LbtpWaKWLwABEHa8ZgAASgGOU4nQFGXjSbR0E+li8KqPQtuolZopYvAACQRsAPJOBKOwwbgKaaAIAu5w2AsUXAN5anoW2q_qLgAACoZABnTgSkkBwCcBoAaZgAOcABMgDBcAClgaDgHo2joADh0AAKJgAAAAPLR_wm_4bAAAUS4axIBmpUALc8hhbRIZUB_o+AAAZaECUAVMlCGAbRIaxLaj8HbC4BdCE_DbbTcBcAAAADxSBKZQBaLQBGCIaxKDKkE5SoBOxw_C0hzSoAAIaADxSBKOf8HQUQSgZAqRcNYkAtFpFRsJU9BaaTTqyMSheAFXrSEAVGphAlIwJQ6E0oMnFDGgAJCAGmQBEuAFlQAIaAAAAAAAAAAAADTLhrEokGR_8qOeULwgg9KabVWKzLC5eAAAAPJOBKOQGxJ08DcOdAKpcAoIucNvuGwK0KgMlnwf+bhEpUAAAVkBYrAlnICBEYAKhcApIjRPhqDhSoCYp5DC2iQyoAAArIDpSBLOQGvJQAay4BcRHWRDUOfFwA9C204Vg8Fy8AAArIGdODolnIpC6ycDs6CaZYIgoA8g8BRAyAD+DwADkABRJcAAoouAEAXBEFAFvKF4CgDh+BtFNFysKKA9Ai01UzlrDnI0MEpJ_snGGoqDSJ4G0IzUjY3NzYHENgmtcAwEQQ1iVADkNntQTEqDCBtAAlM0kIAAAwEABKuEdlQXAyBAIxcAQQ0mnWC0akoXhdBoWQNoC2K40UgAAXAwBzVIEjXAEhoFQJSVEhEhnwGkDeVBZAMIACCkIAAALcpAAa5FQemWLyQ1UegaSrtcuCzVRD58YRAmUj68EkUY5AcAAATtSAezQKjUPSVEhO2IQZDSFRKgsgGEABVaEFEGoBRxMAalSAYyZxUG1Fy8SyGqj0DSVbulwWSqSS+IT8wj1ApGZMddpJ9HklRyKAA4xYu52dACSsf4jBTMqAUscPw0m0M6ULwg0tAUQNIB90IAABgMAAGuAJBQkhUrkYJ4lQBpjh+Gk2g3yheAFQlIDSAa1CAAAAC1wBIaQqRgfuVAdhPj_zVbRv5UABglIAAK6EAAAIoNiLlZARmByGlZLRvGnlC8MpVAmhxMtIGIJxI1EC4AAHRowgXBYgRwZAXKwCKHjsNJtHDlC8ISLQE0DKBrRGNJVAIRiwgqhEUGtFysE0xAODx2Gk2jhyheGEqntEImhtMJdU0iQyimkAIKoQAaFZWZGBJZQvAQkcPzaaTaFjKF41xYzAE0igD2TOBYpGAAJShALIqTl+RodNCZFysuiM1IcnGwmkdmULyqf0UqLU9CJr7FzGaa6UEIo9PTLQFEkkqdlIBLCnyEiKDWC5WAOQytsbtYs0oXilGaqhTQ42WurRRivyMFEKyAAPgoRQZ4XKwByGkm7RvG3lC8VwzFUCaHEygOYL+mkY02jO9PiKFZADwAIrCKCjC5WeqYgcn00vNaN4ukoXh45WCCTQ2l0AIKBHC6SQ0iaipWFFFSdQiBHAsxcrAHJtMIim7WMJKF4FXhiNPSaGkugL9QI5FLpJDSCrJFZdjuiMC4C5WVEE4eO0CaTaMzKF4WQJKwE0OJlA0gjEUWkkNIwoqI+VGwC+xCKGuSkgFyuwmEqjkMptqL2C5WGEq0VkiE_JsZhQ2a66XSDQTcoEcelEelZqr0yBOAEoSIQCqlcInlQE9MI3mrjTdvHllUtmYAegpAAA_QqCEEAAADXCENCRQgYkVAFEDjBpSAALczAABUPgAAbDwAtwuwSJtiBHqoQouVgMzOH5ZMJpCILVcBDBfKTKwD2ohhCKX3RiSUEWgAEpoguHhPIQA+JgBaHQAbpKAD_iUAAek6AAAAAxQZjwsEYAE7KxVA6itU4ACZnQAAVD4AAHKEAglES8rUwBKRQiJxRKqOQnOvz6ckEXutAQrQI9dewxFUOIaxOlgGRHszdO5BACitTAX0QJzCFETWoV0YKwAMSifwUgDNgxZJJJAPcmSwExpQCbCiBW_QtBXpiAAulEAAxc5AABZABECMAitb0lmY0qUweWVACksl0miklamABp1QpABiACLISQM_pQtL3DR2AB_ts5lkoj0I6kTwAuY0c6BJwAb1BizSJSMIGsUoWUUQZEK0KOAL9AjkketdPIYVQANJRADq4MWWlpRhAxelBOJlGhqCC58AXQa8nD81IADiAAFkNoEYUYdbSiqsmsCQpEsBsSdLKJQR0itXAA64YTgAC6GkDj6UKfqFcwhWdCjgHdQI49HItABPycFmnSUABSRomXS6ZQA4J0sHRTpYwVzHVayw1CjkWg00mkGeqyUp49dapTxSHR7PaDPRSIVkIUOe0WgsmAh5NJpdrJmWTOUkZLUiqHp0qeBURqBoqRlUsmrAGE8gAGFA4kTSXisBFVKAUDI4UxKymlS2CaT6GAjlAj0EJIKtWpgFUulkABQIkBhAT6lBiDgAdKAQowAw+AAAAAAAAAAAAYCIVSpGNM5bww6lAUkylNWoQIAK4bNYAEWoYullAuAlAOBgY+uwbNYKTTpYDBkymYZeKpFKqABxAAvqDGGPTUYQM3pQHhoWEItoRFYTwkC8RguAeQCeFQABTHIAAAACEjB6erisz6kB+B9ARseOyyf8XjkasABxAAnwBFkF0qWwM3pQFmoAHSgBiEAVMgBhEAAQZAAYGgAAAAAAAAJFwHj54Dt3IIAoVqYBFCRGXQmjlVCu8o+AACXQwgYGulUolGnYpINu1ZyDWSyWZWpkmGxQnIolKNNKMdMkrV6L+xOLJREaPVbiVS6WSaRSeu+BNGuXyqVaacSkgAHSgEKMAMKgAAAAAAAAAgeAAAMBAeCgYeAIV4fPlBQZAAMQgLCAUPRgAGMXAAAuNgAAUHwagWLeAAxQ3ERRDWKkAOQiG1CaVIAI8HwABsEICqAddGD8LAAfEGyxgBRuOBN_hGA6hEBIo2AElowAC0AAFxsAACg+LOBFQcZwR2PgR2Vu7mlAnNsHYMF5ElgAQuXgTXMIT8DbVTslC8DCAE1jSOUcCaTXJ08AAHYMVdWAbGYBaVBcDA0NqcDoABx8AAGHgAAAAMrwAALgYACSsXMTBE8qG0IxPQoghbN43MqABTBUAAI9CAADcFBzhM7skTlFBAXKwik2Dh+FE2hGyheAGiCoP9LQBs0IAACoMASwmTlFEMXKwikGDh+FE2gxSheAFfCoCyAWVCPYDAAAAOmhoEqJEwWhKgikJDh+FE2gyyheAFjCr9ykABaUIAAiggYkAUgTlBlIRQAR47CiShu1hJSheF0EMfBkUhtKoMWOs7oxYTrKlMCsgAQrgbgcmsTBm8qCKAsOH4UTaMvKgugAFn_SMBBlLPh8B9D_hsAIEoWNAjykIoUQ8dhRtIF0oXgAZFobVQKFcBzZ1Gz8fVGkrycgxYPEuAqWjS0SBOf7QjcFSsIoOQoneas4CkoXgD2KikugAcdAjnUuj0TgKujROjs3inYAdtguBpXExQRilC8CehRNvhFYvZQvA4gNAID0Dql9OAABcDFWhgDfSAWlwTAxxAShEAXo2B6AyCYAAAADK8AACYGAUfpALUIBgIugXwaAqsfAB9h4AAAADRUAAAYCAHuhBuDCuMgd6VFBP8nwUbaNNKgCoADkighBCAABuDAaA7mYOwYD6ok"
noncomputable def WL10_4 : ℕ := zfNat64 33241 "BckYADckPhUzBKJCATEAUMpABPZ6AAUO7BZ_49APQRgNUcpEskh16qhXBOh07lpBrITaqNa7c9WKNdJKya2vHDcumUsJtXE9fxyXbSVaTRUwCQ8CoPMZBERQH0gSwJyAR4VgAPIB_BqIDuwZUYOwDbQ4QwAP1AClIAInABEIA0ZACA4AAAAAAAAAAAAoAT7gA_UAGUgAKcAtMgAAAAAAAAAAABhC6JOnmEohlUK4TkYldK9nQiFqvRgyAih1FplpsrFtGhP4Mc2k2lxD6AIWGgcCCg4AGkhFSYFtlQAcDhuAQjKgA9qfAH_GYpIhE8KhKeQHPkwH4o7Z3OGNjIqAAU4QbZAARsjhocgigiADoAtYmADcB0AAvg2AAAAGJwAFCADnQA4uAJDQAAAAAAAAAAAAcqkS4jAXM6CUgOSYisPgACudAAAdOhgBQAAGgaeyAU0zKhgWBRhMB_weAFGEwAYmOgAFTGwAAIgIA57UCo0gkNMADGiEQghQ6A+oPABgB4AIAHQABPy4AAA8Al2QYYwfhIxDGULz6QQX5g3FpFlIbcoXg1DAisTQUhJNptVugR1qCQAABry6GDKHhEKZKLouITuM2IMdkotN4bC0De6UWaCBTTaTRbQkAAAQwketOLlYFD_hkvjtNKMlx2yheGKVqdJAjCE_DCWS0ho0COtoSAAAIWZ9edatHhTKRaBRaTGO0HOxUH8uWmUL4KRaSf4Vp6EGskm0lGvaMAAYQuI8nOwQarAtLIAlPN8dIYHgdcXAD0notMQFxJ8gjAFk0gf2aiggADDGgA606B9RUAKQBvJsVQD_58gQAY+fbiRgAkYpAPjYeBHbupxQACnDaq4AkNIKDwNqIgA6AKwHgAJIADdy4AAKc5w6kAApwgyaygWDIIoIgA6ALWJgA3AdAAL4NgAGUCwAHptczoDi+MuACBg3HIAIUoX3UKSVQTIT8Asm0spxQI4BlFMnn_zoAERkE2GgEYsgglLqJC4IPPTb_yEAjI4bi26h9xGLJBAooYmzuAAJQgmGACxoqwePgf8sXgDEAZRceMoX_RdqSf5RgehNpJVNpQSql0sk0cQdNwbAiJlqpUACUqAF4dAByyoALNIQB_xuELIQJFoBIxmB0CnNQHmyAA0wEg1_JWAVkwApAErkxJALTn1VABCJ0AADYaAOmrq0XPTHizNWPli+Og1nIAl0GXDmkzkCbVarSaiYRu1nEliNDlIAVV2Dx8AI820xljomBdpUALEwbgESyoogE9qoAo2jeUtQgLoAAJsbYYq3OPVWaj0LlYAtNtFBiskoXlEATKeP6qWiUg2jd0COFFDzIUAyAAeICJNCwgr4C6pxEEoioAOgAKCoAAZHwAZQNpJkoD_h4DfLF4PRg+VZiWguVk9FotNJBHoFyuF5QvpIUUnJNqIGVUikWlAhmmg00NpVVIXLyVHbtFKQAkZC8pY3kWBexEAHQBKw8AH_joABxBkAAxYaJsF5WQBIawQabyLAvYiADoAlYeAD_x0AA4gyAACpBNM31Y8vwWBQREAHQA_g8AA5AAX4ZAAerHgdjR2dDQYwYEwMFRDYCyBQDtpAEXAQSo6sQQA4kB0IAAMYMRMSO0NDQhoAHSgBh0AhLgGAgACBwAAAAAAAAAAYCAAonAIS4bgYACB0AAAAAJgoAAAADcDBqBVs4BgIAlY8BbQAhA8ADIDgAAEJcAAAYCAQ2lDcDA3BgCSTACEAfOdAAEgKAACCdAABuBgJBKqcAhQiJBgBqBRQHnJ0uhhkAANxYACAyUAAIkGASqnESDADUHoIpKjhNEAJ0sHkPQDnPJcG0AoglAACJBgxBJKcAtPiJBgZhQDUCigPOTpdDDIAAACAyUAAIkGAPEnAEhoCQKB3h0AAf6SgAAriwAAHToAAASenAEhoCQKAagUUB6CdLoYZAYQEKXAVQDVJQAAAkdOAJDQEgUFUTYAAJIFVHIECAACk+AAACApwKAqAJDQEgUD0joAA_+lAFUP+HwABMV4AAB8FnpwBIaAkCgMWaNwKKBSVAGQR0E2nkMJrRaDWQHJUcAACWvBhi0AtPgaCgWBQZoOgBqASXgFQAAAAQToAADQUA1FOC4OBYFA8A6AugBJXcXAECU4AACkfAAAuDgHDJwEgUGQDYC6AElnBUEFBgyMAACc+coLAABeD1U4ACXMSZADUDCxpQngE1_xMjCyAn4yCaAGMSgADEmQDuk4LhYz5EGPjYC6AEmKBMB0AiB5HB6HQDPoQAALhYJ529BYqcACNguCgoBQMrMG4CEAJNxjYAMv_QoDSVUI4jAAAuCgA2JwRs+C4KAkDA746AAP_JRtiYDKF0AABibAAAuCgrBmycEwUqYyD+BsALxKAJIFBJoARctgLSQh8F5QgAATBQDZU4cwoAxxw3DqUUHssVz_yRDLqXBQSaRRkLVcBaD2ovpRJYAAcwoCBKcUAUjgiDCxsEkUgBBcEdBQf7JxshaAADYhAACgCg_Py8vnR2vPzWnABhERIMBlouBKS0PQtpVU2WLxzoUAAACwRgABEgwDcDAMLKgKYIT8LaKzKgAUoLAACNQgAA3AwAAV4AIpAAUYAGhAGC4AkHAMBAAEDgAAAAAAAAAAAkFESDAWCLgpwkAQQn4W2q_qLhuAcAAABBQgAABuBgEEFQExT4DaJDKjKgsADQiAADYhAASQPgIkGAR2WLwqo9C25OVkxFy8hIHAABAYAwgwUYESLwB_R4CJBgO1FxNgWD+IT8LaSFWFoYWRgJIFUAuKEAAEIWKEApEREgwFEi4AeSE_C2_7Vv1Fx9IaCEgABTFIELCQAACEuG4GAZ2VAYJPgNpJkqAD_yEFJJ7OWsYYhAUIWAChqwBmRESDAauLgB6Ft48rPSLl48gWAAAsgsEYByAf8eABCXDcDAeMLgBkIT8LaOlKF4ANUPIYFkonEs2hAABCFihGYGVl42hAB5cASGgCqSxeFVF4cPwtpVJ6WLwAAsFAAAAAAAeZADhYGx4CwRcAUk8hhbSkhcAAFgoAANaIQAAAKFgDkSxeCVFoehbSqT8sXgABYKDQzYwAAggAKkpmwAkZAAioApEqAG+eQxnrNbRJZUAAAlAB4pCYw4AAAJGQAOuAWCLgP4nkMLbVf1FwAgA6AAASyHAAAA8yAKrKgCknkMLaeALgAokZABNDuoQlkOAAIaUAeVwXBxhDrqouATi1PT_B9bcZqwtA98dAABhFUjCYQ4AAAsMwXBwHmwRcB0Q8hPwW20z4XAAAA_YyB4pCYQ4AA5ABzMAOphFDgFWlQEJEJ+FtEhlQAZQCOgO1CEyhwAADlKhFDgDHlQGXkIDSOBKirhUEQZodAR0YgAlITKHAAVZGCKHAJtKF4Dbjx2BtHhlC8qoVAIas4CkDzcpqoJKNCEyhwAFKALa4RQ4ugokqAFyeQwtokMqAigByY6ACChCZQ4AAAFqwXysKQg5QvAHoiFeNoHkoXhTQaSULwLIBu0ITKHAAD5CRVMvtTJSheAsI8d12um0WSULwpoDaLlYFkihhlGHJCQAB2AKLYRQ4RiMCKioBK58BtESlQBhDoB_o6AaysJlDgAKslCyF7CQ8NlKgF0IT8LNtGXlQfeKgAAENAA_QhMocAAQYLAEYL58gyTCULykg9pNZtovFZMpYvD8hUAAAIlGBvA0AF2CKHLGGiU98LgA5IT8LbrlWFoAAAAP0ITKHAAAihyxBo_yVecLgA5IT8LbmlWFoAH0BysQAV0ITKHAAAE8uAJCwhBwBACB0ABtHI7AEZEoAAAUC0AAAKC4cbhgCkujgqAsEXAePPIYW3xasLQAgAAJhFheEQlEOAAAAMyAUFwCwRcB4s8hhbfCq3_i4AIAVQBMosLwiAARs7AA7rgiOgLBFwAEEJ+FtqoJyheAAVQBL4sGAeA6AQQGgBAQ8AGERyDwhyoFCFQF4T4DaIlKgloAAXQXhMJfDgAAAWZAFi4ALQqo9AS7ZvW8rU3slC8ANRKqCdAhjkAsuURocJBsCBcAAhpQAHXAFUli8KqLw4fhbSqT8sXjkABGHVcOgAwIFMMLgAABIyAICwAAAAAAAAAAAAwMD0eKamnKSKBo_lwiBDJYvCqj0LbiJWaKWLwUgBYFgAIDJQAEHB4AAwtXQ0BTguAFyeQwtpOIuBSADLBoABWhAuwSAANAGUsNwcQQWUVAZ9PgNoxMqABmysAARBCAAJoPABLZh9DgOKmC5eRkHoKbalJWFoALoafwXAAJ3RiKhZAYo0HIAQZgAVsNwcBNEcVAH+PgNy3AAEhAL6CuWgAAhDQAEC4KaTDcHATVjlQABpRQlIJKgAAAk_4MgWKwD0ACGrAARcBmlhuDgFLPSoDop8FtJElQLQMFFwEkJI8JCAAkC9AEXEhuDgj0VADKz4B4O28TqVAAE4uCOmkegB1CoXTQgBowfQ6TQsCySheAOQAi0ax_xcrApqkHvSIDDVQ2OhAdTSDRxoGQDLLD6HH0sukC4DQLQ9C27YVhaTALH8OiIAEIEdVijAAIEAC0sPocfQukXAT0Lb1VW9UXH3S4AAACkpA+AaBSDSQgBB9DvBLQd4LgKYnkMLttN2FwAEUAAZKEAxADkNAAaEh9DiyWUopQvAqnoOH4JFInm2okFKF4FW3SMKSyCWezGW1H4iURUAAH0OHIWWFFysLslb+VhyU201FOpQvG5lxRIIlKoJSqQRaTTToEcEptpo9nrYiJGTIA3tgCQsCQcAqsqASOfBbRIZU_waAwh0AHIDWVgAAq4WZAGaC4AOyE_C1NRxrCrf+LiJhMAAAA_QoUFQAAOQnLSXMYLSxlC8JIPQsm0oSsZMsXgpAAAHIW0YtC8ADmfw8AA+WN+XMYLSDlC8JIPSSWTalRWMmWLw_MVAAACJRljGwAAAgzqbiZ0y8DHCoCQp8H_m4RKVAAAAGEQh6ACbh4NfJieMF8FZlC8BbBw_JJZNoaEoXgAki4M_5NgAiwjD0AC6DQAEhYbiYA6RUBEs+JUHRpEElQQQAKCZEYADysAAELWjt2AC18GhYP6ExRyxeGliS1XHoW0qqjLF4KQADIAFtGK6CQAcoeEHBYOhrDZYJQvAEN2sU4cPwmm1EytLT5BUApAAIDJQAEHB4v8MdjcMPADhcAMEgFOi4ATyE_C21X9hc5wOAAAADqEe_DgAnpcAB0uAF5LF4VUlxw_C2jrUK4tZ0GEwABIwfAAoMlENqoHyTImQAGZAAq4BbouATi1PQtvi1YWg0ABEHAAB4RhKgUABAgCEWACiUbEQFZC4AJSE_C21UWgAAAA8UgACpyz4AEIuupMAXksXhVSXHD8LaO1Qri0AAEjB8ABbiUFVAJ+ZEyAHJcNAVSWLwqovDh+FtKpPyxeAAJQ4ogADEJEYAC+OG5HgAeuADywug9sqA5efBbRs5UbYiAK7CwACD0IP9JwD2ioAEKEArEgiEgBkFQB7T4DaDpKgA_GZAAGAVgGoH_T4hQA2hAHhaEFYDHhcAr08hgjFYCrZzLnFwAAAAP0IYhlACNAEIs8a0"
noncomputable def WL10_5 : ℕ := zfNat64 33238 "OKZA3NjZPTgtEiDYGECJAy8yAyjkBqhkqA2CkzEMoRPgKItBSBNMpgABPCglAfxEIIMGwSAsh0BZAoFpIMdAH_BoAARQtAABCCiJpRWNK6cdKQAkNAJgwAc6KgASpU6csXgFVRwhPwA41kP6BHAAAAA5wJgwAhyoBTJMAIhKgAfCfABtFBIQAAEwYACTUAgFAE8qAUaTAFeC4ACCABWbOY_9CAABOFAFoUCYKAfpUBJUmAK8FwAEENLMQBZw3j_0IAyAAALZgmDgKonyoCSpMAV4LgAIISYYgCjhvH_oQAAOwoHyKi9HwFXKgMLkwBh4uAArp5DAwhtJAoQAAOwoAAOsGefAdAuAsEbJwDGRcABezyHbQuhxB7oEcAAHYUEVj09A8MVWC4CSgaUShRli+yxoUgJ7bQwhxHsoEcAAHYUVJ2AAUIAMZAFC4AWNABxIAAAAAAAAAAAAJjOCylwAGiEIKVcfAeyoAAKgZ0qAAD9gkGkA8tAAAeCgNjQEdXACqYHQoCaAwiAEIAQImABMSEAAPw2AAB2FAAFVgwBxGD0ZZQvAXidJRKCWkoWldAGwhPz+TUYQ4jA0COAADsKAzD4Uw4jB6EUoXgSUA_EXFdAbwhPwLocQgKBHEUFAD8B4G6z4oI4jJyC8oXgTRTXQJIWyheF0DyK09KptMquYy2i_0COVQAOwJE6AROpB0iCCQcoXl0Mvkx5A6UXEkmgS3PIZF_orD0NIglAjgAAtCgAmqwWw4jBo9FOULwjwnSU+lmG4AGWLwzXQJ4rT0GmUuhtFkoEcAAHYUAPBqJaMEQPX1FwA9OIJudvdHQhAG5nkMMgGUm+hAAAnCgAA6wGPOCo+T4ZAhAP2IQAPIyAAYB8AAEE6AABOFAE76lBLJ3hWA1ERJ_+wQDgyoAConkMMgGEj6hAAAnCg7lcxuiIkZtIKSVSuQQkgMIk5hpIRQslC+Uj0tAXE9DI9IIYZXITfUCOAACcKA8LxbspArlmKY06geBu5UBJEIBFdmVAAPQCzrUfdQgAAGAwU4p2hk+HK4oaBcDAEaNgNoPoDiydWcFwAAVPIYAcSAqEAAC4GIkEkGBMDAZMqAAhIwkqADVCEAG0aShAABJBg3A4R8CYMBGQ2ASgE5y0XAgRSVXDIQBFOpe1CAAAmDAASGgCTSoABh87AHUlQfgcgVQiQwMIbSKKEAAAjQ0UoCBeBcvA0+YNw_wXCCyheFtDYKxBAwlm2iZUCOYINgABXQ73gEA4yxeAMQLglxuyheBpCX55DAuhtKCGUy+8Xikl5FDYNjpeBBj4AHRAEAmw1geEIA7k6HOVAfQAP_IRtF1nw6IYAACBP_LS7SxeBMQFIj0oXiAnI0ijlaegXSybREqBHHRDAAADqZk5AKZsAOQBQ5UFPHICCBdEZNweRCHRDAAAaA61IBpx4XA1ByAtNpFwNTSDJzx+BZcwmSzaJxQI46IYAANCEimrQUeLgEQGjsAGuULw_81ATRCfgWQ2lQ0IAAEwUAPBRTVoKPFwCIDR2ADXKF4f+agJohPwLIbSoaEAA0QKAAkZKyDYbtYtK7k0umIeRSmkuTuULygmVhasUZ6EWqkk0lFyKBHAAA6FAB90lCNrhLQJNKgP_nQA78qAD_yEDE1otI_1CAAcKhALpw_LIaRglC8Grl0xcGZHX+xVLVHlC8IJlEVKw9NJFKpJNI7NAjgAQcGiBqQFxxFvPFoExlQAwzR2AHrKgAwEhAH+2ISAhDohgAAVkv83BvKF4ExDqCSyheUGygF5CfhFLJC0o2itUCOhoKAAA_BABLUlqtEk0gXATEPIJLKF5QeHsmsBLIT8CyG0TWgRwAHCoQxR4NaHlNwtAmI_509gnUoXzOQqD+pmzhPQi1UtI9VAjnE1IglRNmMxA3cDgnOHXgPauAB0wBIaE0C+EwEYh4ALMTAA1Y6AALQbAAAA9lIAkNI6SEhpsFnTYAloABrUIAYk3A_kIAAAPGhAEhp_ciJaAtl+bAPZizg2n0XAM1PiaAU02kg0IAAAYwrW48S0xZQvAmISQT2ULw4gDUQn5tBiKIcSraEAADQDdbjxLTFlC8CYhJBPZQvDiANRCfm0GIohxKtoQAAYwoGDx4lpiyheBMQkgnsoXzOHji6JaAaiE_DCUQ4iHUCOcqFgABF02PEtPeULwBiEkw2XG7KF44Bs5lUJ6GEolk2iR0COEuj4agAy+RHiWtbKF4QZbMQk_4Kpak0oXhEOjaVbZJw+c8fhhKNVNo4ZGhg5EIHrhoAP8Mw9FHiWopKF4DVDJeEUEYlC8NoBFqIjGEohtAjI0MJoAQccRgvCcsIeA6ZUB2o+dhJBuZUHEAggDynDeJhQi_yEAAEAROPACeEBPFkmh4Er4SoCahJAuJQvDiBKM8hgUS2kF0JDgcdZiWftmwBXRdZ0eJaYsoXgTEMwjAa0oXgAow+fgBtOjoQdTSBgAaJsXGxTgeBqZUAQg2ZhJAyZQvLP+HIBhSE_ADaL7QrkFw1AAB4CIYgCQ0cEPAnsqAQoaOwkgq8oXkU4gEkciYlINo+lCAAANQ7fpalrgSheBLQihci5QpQvLNFm4BZB8_KphKIbRqaBHAAc4ZGDNikzDwGxOUOnABbMLI0BVfmXB_I2_+cPwAWgDLFZWCE_ALpxFNoEcAAhRcARJmBoTZ4FQH0EpUAQUsZgESyoAJ6AYMbirCEYQAHpOgFKaB7RgCaVAMyPgBQ5UTQD_yEQQc2tW0lmhAkANpLQADpsRiKWKMBHyoCnp8AXcLgAGqeQ56BbSJqEJQmgAAhWIHRGAyZUdQ4wfABRShfLQAsR8_HoBtMtoQGUDqhcA6lFAj1UFKUL_9LwTEkzkkiXGfKF5BCii_Tx_9JAj0EKJpDaI0Mi1EuqKSpSC0wRkpAwZcQ4VJwfwbBNQCcknKjTDQE0AchNONDGIbSkAAQouA0A+qXSmQGDS4E8GzMciBJi+QuXgxoIUUsoksptRrJtGroEcigAb8sZgALFzgUjEFSsmp2yheBMaDYRJBsqkoXhRIJIJWnoWSiWTaFvQI_+S4mgAAAtWNMKlZNWMlC8B4RkvKJhBE5QvCiBPS_jEUQ2jckaGGX4isALQCqqwLSaAKQyexUf5NmVlUxDIh8GUJjFwAAVOH4pAtJ+NCOIAEEHQH2FjwhLPKga2VARrLGYAocqAD_yF842ANo_1CCyNQaAABMyAFiwAcOAAAAAAAAAAAAAOUgAZ8ASMgCQUAAAAAAAAAAABNjRAAZYBwqAEQ8ANQeAOxnwAAABFAAE4rAACRgCJkAREgAIUAAAAAAAAAAAAGVXBtaIoCZCJ0COTYD_pcATkNgAJIAFvToP8KQAB3FSczyE_op0zx+PabYpSmstMtdHI1GMfOyKVaDRQmjUw02omlEakCxGhlEylEKotRWrkDFwsaAAmIACvACE4AWjABTIAaXAARoAeFAAAAAAAAAAACPhxW7G7knwwOAnAJhQR6NgBoCBkoVSoqgkE5GgnkMCamUbshB_paABgNAGoKgEgUAmFAUI2COgFUFudHEFgAgFAyAmplFodlIDiABQAArQAEuEulQCAUC4DYBCTuHgs2FSjjnQAEEGGQE1MotABiVRrRY6BW3ACRkRLigEAoANEQAiB4Aa4PAB_g+AAiuXAAC0ACRkAGKgB4sAGEgAAAAAAAAAAAAARYBSJAIBQGDKgP_HwA3EqMYLGSlYIRnkMDKGkmShAA0AAmgUOMHD0joXAMyNmYB_8uCsnXVZpZ5DA2102kdEYxg8AhJCEQAJjQSgKBCDgjkXAN0PG4A04uCshXxCA2htC1oQAhP5EQRAADNB+QpZfuRAvEqA3IYNwAGJUAAZELQC8N2ZgygYQEIBkA+4UaBsBGwuLoLuMG4A0ou_whBZCqQQMpZMpdMcjPMUgEIIXHDB8Dx2dGRkBAB68ABWgCRkASEgAAAABAIAAAAAAAAFswKoSGMSAqiULgDBnD8AEeULwLID2Pn4HEym0W2gRwByefyMQAe5SKASJobQllQMQA7gJDLKgLoT0DswHMNo7xCAADcHADsEi1EhFHjsHzFwA1DKoUuEVlC8JIBFquE9K4JxxsJtFDoEcEIOTyVQuQDWJAEFFwGUTh+AEPKF4FkAOIT9HQcG2wm0qqhH1loHJ5ADQiJXACaoAELEeBIjRFEMXF0AAADNBwAf8RgAE4DwAAArZSAAiTCEwxBfhsEVAByH4uBqXQJJUQEwHMtJX9CAHJ9G4N8HAaA+RJhCbX5cTUS5QvAGoYQPaULwq4zVLYBAQn4HENpGNCAKDk0k0LknwxmVpQQg5AhqIuAVkbMwA9pQvAAeJ4_AwhtBAI0MPJ9CqcuHgB5MwAGSEIOFoAF6jR2AQLKgA8OfBOpmDaUGQgPoBpxoDQ4yhfUQyhHKF5mBWlOXTEAPmULwpNFAMnD8OldqtpKoLkaGNaDdTLVayIUYPgABagbNkBTpil06UBoyYD_pcAIPJgAtsfAAJ7OgAAZjRUgA_qIoVqcJMoYSheVUOobMwA2ZQvCk0UHoV2qilaN5VB8jQ7zQTqX1Yv1Euh0BISsDQmiZKgANFQAlTY8gAvKpSAEEkgBV8+OoAU_KgsAqV00kiByheSUEJYvGNlnpLXplC8ghRQYh87npWQ0iCUCG65cxk041rYqaPpSni0AB3MHk3gCQ0_41Af4iADoABoeAAKh0AABIyAAC_u53FQwAQzAl14AkZCaJYAnHCKB1iIAOgB_B4AByAAokuAAR4LACUUgSnVBdcQSAuBo7KyAXyheBNB6B87AwlpKCUl1Tx_CqJWHEYEElCsmq6C5WCcTYYhhBqk0oXkN_ghD0SkYLwUlksoMRChlBOpUSqMwgTgPuUKyavuLlZF_0nTUbZYzDCORq1UoXh2G0GegtBTVcUKVlHyoEO9yNQbqaajVUtECcDwWlhI0Fe9JgMgVKwHkXB0AW1PKgAoIAAbEIAAGY0GIBrxlVir6iMNTllC8CYmD2IDWlC8MgBVEJ+AG0kShCUqnkBlQ8AFJqEbKFZNHLoC5WBLQwn+DZNJQvAAMZw_PmKwWkAUjQxiXTyFU5aPAAB3gEUkSQ8FQmA_xUBesyAAAAKpVEAOJDw+D_D8Af0eAlAOSKwjMxFPoXKwJaF0_qdE1UK4BKQDKQkhdAYnkMc006hF5QlC0ArlUMgsDQiBOpMAKQBK6UAE7XIABa50AAACn0h8LgDLfTYD+xkAJFTgARw9AABRQAhiEAQTqE04l0D4B7RkvAHTqQ9AD6AHgagIJlAH5owAhZIfDJwSUSEAGIAkdOACgT0AABdAFYIQHoMUyeYSinRWphOZbTS6TkCytXJNdopFrp0GrOw8sZkkikGqzlCj0byxfttVptFRSiSwAGpwAQ6ADGQAsuAIDQAIOAAAAAAAAAAAAKFh4aAqNIfy4AzL46A_uZACP04AEUPQAA6HYIoAXJGAA3JD4VMwSiQgExAFDKQAT2egAFDuwWf+PQD0EYDVHKRLJIdeqoVwTodO5aQayE2qjWu3PVijXSS"
noncomputable def WL10_6 : ℕ := zfNat64 33237 "HIECBaHAkEqAqTABGAWAJR8AGwIgAAIJ0AAC0SABgpBGHE3IiUq_LgAUgEqMgAYA4jAAGJakoAA4YsAOhOC0O8whH_DZE5UEkAWgoI2AG4DwAAI9CAAI0LBycgAgiC0OBH5UCUqAAACZUZOGggoAAFJCAABMHAFocagaJSrkuGkGDcAAZZYvAKqWxCfgBxrJGUCOAAV0OKGhFQ85ww0BAEacBDrgSBjxmwIYuAAAGwbAAAgQ4hkHikHoBIAAEKnBFiIFQYKA0AFzYAAG6GwAACEP_JwLFYAAEIMEoDvTgXdcCoMbQAcdAAAAAs46AAG6XAAAeBgAEnwJAzjCY_4ZHXKgqgASkLgOobAQgA4kBUIAADoMACpOBllwJAwDEWxUAABZioCr_JOGyKQBopyAAADoMF4A0UhcM8CoMA5jIBhEAAAABhAAg0bAAAeBgCdJwKg3vjIGLyi4EoAdBcxcCEBmyE_P0BwxDaUHQgAAQgwck6GQgwVOFo1wNA0RR4AHHQAAAAASTpYAEWzYAAFwME9OOk9SDcDAAsIgAAwhMAAPwOAABMZAABuBgACrQAhOADJQAs2AQlwAEeAAAAAAAAAAAAAXIhuBgaBQBoKgCyAAOKgPqEQAAAAAbgYAAKcAKPgEZUAwECwOAAAAAQcAAAAAAAGAgIkGBiFAAf+TgPanydC4AALZIQAPFIAARIMAFQiG4GIoFATUqAeojAAESoAAByH0BcrAABuBglJQKWnALSIBgIBLB0ADQBBR8AAAABNqAAAMBATEk4AaIgCYsAwEBAGAAAB8EwKj4AAAACbUAAAATMgDREAgDAAAA+CYFR8AAAABNqAAAMBAAbIgCQ0AgDAATQmAAcEwAAAABNqAAAANkQBIKBIKAAQETAAOCYAAAAAm1AAAALSIAAgImAAcEwAAAABNqAACkHAKQcAEkmALIAA4qAKsEQAAFA+AAFAHAD2TgFpEKQcAaY6AAIiEo+AAAAAyvAAAGAgADlQpBwAACsuAAFkwDUAAAAABsHAL4cAZUqA5AfARRZhcAFRkIAL+NADDCIAAAkFC+HLqAgD8XLwByFBh2dPDLgP6HxjSRWQQJoCj0YAAAXw5dQECYi5eBOQIp8zptZcAPR6A6xMlgTRRgJodSSR0CsqSm4AtIhSDgCyHQFkCgByagAAAADK8AAAYCImJD5UAJDQ6gcBmC4D_hUE9nILwXAAsiKYgAB+RgAABqGgDMFwH_CoNlOQZgun0ZCECSJkAARZGAAI0NAA8rgiDgdQnAlKgIeCwABMqAP_GwAATBCAABEHAAbKmqyInuZC4D3xUBxDGFwAAAAZ04wwsAADVJET0RZYvAFIHGhyUdsuAJv_jokgbTfxsKbRhTCiMAAJQAkNNWkRPc4FwH+ioJ6OQQQuAGdEQAAH5GAACdAA2cABmoKGjYryBGD0jJQvAigEFFYWkiixLgLOGQhC6AlAENCl0aJLOpdAEFDRsnUOnnQIgaAwcABpALYtG0RRsALSIpiAARZGAABEDASBODApCgG+TAAf_CgS5MAVaIgAAAABODBuAElYBAKADREAIgeAASEQAR+SgAATGQAABgIABCsAPLgASC4Agh0PMGyRC4AEaZWEAAJ6EAADEKAAQrBVGQCiLgP_IQdDNBsfIuAC7mVhAAEehAAAxCgAEKwCkuBJUJFwbPNh6HQGp4C4AAKIASk4M6cAADEKEMAEKwtIobJKy4uXhFmIHzR2HQmJ3S4LpNIIhTBvYQ0lGehBm4lAAAxCgnJwUAFBQ4wcEhy4ATmDccgDVh5dMMSAGgmQAB0koADIADocMxKAFhEANAeAAbEQAR+SgAATGQAAUg4BzEkCE3RZcFtjacgDXMpcAMJMG41AAepzRgAIOBwAEjIGBOAExMALAqADqHwB_5OAAAMHQAAGwoBQUAEJwAJGAMkQBEaAAiQAAAAAAAAAAADQHUzJyCazYAhRsAAOKjeBwDLCIAACufAAAYCgNAaCvAnx_5ibgXBYlIHoA1ScXAE3EYAAIsjAAArDgBslwL3NwHCoIoARfOhwFRvBIAegAColYAAUAcFYBRYznpMRidMXAD02jkjEbMbLgDtBMAAEWRgAIOBwAY2I5iyfAkwigLl51nvsDacmEBq6MuAOdF1BAggJRRgAIOBwAxlZRQ2fEUwp8LsCUVLGw9AGAWMwA50TUEP_IQCGkYACDgcYIeEudKmOgLuVAUgOgAq5UDkAAOgDQQgAA3BwDEgPwDHjvoq0XT+li8B0Rw3OIHAy4ml0HxIRdFIQQGUowAEHA4BbsnAFlNhsAUs6AAJlRvA4BlREAABsQgAAMBRGgKdSAEFwB6MEqCapsBtBiQ42N4HAAAAB1CE1DQAAlIPSwlC8FItASDR2WWgldS43gcAAAaOUgAAGocXIEiUgJUPIaYC4DM1A2kxSobZSGgAByBcxKB2jAAQcDgZIKgeitKF4A9DacBGG+FyehIAOpNQAOKEBAgaAH0C5O5QrB6vsoXlVBqWWBp5DIklywh4whFymfBTR6AXdGBNBEHQAFAAYUSAVKweodKF5VQ7B03DTQSgZcnoSAEcTAAAiUYPIAABuFzF_BUD115UAPQs+fRiHxkAABYGAAHikAMRyDqMgVABEsGqTAlMqA_sdACFSoYgAAArJCP+tRdASmRAARVgpB670oXhVHKvDZmYTKPSipcZqZqqSQBIkO+hZIo1Cq89ElhxLpNQC4wfAUcJC4QVA9bGULwJiBsZsYZ8LgAJwaMwAG2oQcbKAmkaLublbknQ8MVAEKyPgeQYbAUMqAc8bAAEyoAKoAfuUgUiEAABgKAANZFjDRKfmlwDUciQJF4ASMG54y4AKoKSgwYTgwslAAIPDgBNKTQHQSkJRcB_5CCIfsOG5fi4AukrAAAj0IAAjQcDiD0EyheDlTJQv9gjAY0wbkk0kExaXABVKIYqSgwi90YAAjQcHJ3hgR0qAUZMgFooUIAcrbLgdxMA5LVGwhNIPZ7OtOAAI0HAC2spOGjqBbSYCqJcAFfJgAz0PAAGbOgAAMBQA_WYXRqcgbI2ApadABVSoAKOkQf8bgD5oQABGg4DQJZZ6IrUhTgRSTAf9LgBB5MAAdAAT2dAAAYCgB_scEHQHGEhcgRyEEBbzo22UXAAWcgTg0NoCI0IAAjQcB4CKMgn1YYkpC46gPRiEQNmZFwuACQhMFhP+CQP9CAAI0HAFsUgGllqB0BtBGVAAHwBIIoB_wuMoAHiQgAAMBQAD1IAIhADTIAEVAARoAUJABwoAAAAAAAAAAAAMxWVmLiKQpPgByUGgkhCYcgDMzR2ZT+bMAslCAAI0HAAIVgEp8AIIgAAAAAAAAAAAAB+YAspADE4AkjAAAAAAAAAAAAACA9wlLMBg3KJ0hCAGpxGoZ+LgAnJtABNGch0fF2kYAigCpikmg0ZlE_whADE2+QMg6AXAANbSAHYkYQgrF0_onAoiBOS8DCxp3FgAVWABqQAJOAEnwBouAAlQAYiAAAAAAAAAAAAbcgdzSFImroXlKgBSBhEqfSVAAtgmAAEehAAEaDg5qcHDJQMxYADhUAJg2H1CQJqOgAogAHUcCsAABgKIUhAQNbXAsiIIQ6tSMB_yIAQgACCIAFoAAYQ2AAAwDAEOUgCRkbAXAZI6CagUSckYOgAXxUAAAdOgAAMAwGgYpmSEEeHwAniYAAQTAAqiYU0ZAABg6AAAwDADPrgRhENwkj0qBJRUB+w2AAilQAXTiAF0F4hAAAYBgIoLgLqVAaYPikhOouAAtobf+FgjogtCAAAwDBCBHC4nIuKrXYuCSEEHMxk4bOSLiCgRQAJ62RSAAAgDAEtLhMYsceC4sgVVLYtCSD0ijmY3wNpNFxBQIpFQCe29TgAAKgwHgDcyBVl5SV4uPIqlc_pUAE9mIlQuLsFDUKME0AIK4lIAADAMB4AJBVPoQEjBeFl_JQvAmJSa6FwmwuXlFAGAjQ_+nRRKJKSb6MAABDKF4wuKqs0oXgJMNmZSQOoXLwigNtPIZ_BOKIFVkYFoHE1yjABLFoZQizGC8LLIyheEUGoSZaS0NkkRz8h82Q6IoVSiCmFiMRVElgAA0ABbUFptU4tV23FysAXJYzCSCryxeUE_8bA9CKTQUg+UCOGEuh9zYP6gRxVRbhJyKrSi5WC3S4YlFl8XAtHmHwNRaB47JyTQUiY0COSTKXSajdkaGYo2NyoCAB+YAkZAIi4B4+AAAAAAAAA61AAAYBgFpwUDp1xTRcrCqaouVgQZaEU6qXIFLgCzKIsdlm1xsGkqiUo_7RgCIAE6Gck4ECUgK1lyJMAB4qAE4bBRA5h0TQBaFUA_4rGIQgAARAwCCWYMyKQgwQ6AdSXH+TIBWkwAR4mAAAgnQAAJwYUJIhaasVkblC8AYlGNSMGjC6ggAXZqAJbQgAATAwAoWJj4uKqCMoXgFROH4SQ4YXCX6yUARRSABwUIAADwMARhWVQLiTVYylVdAehJ_6ZBpRYMgDyEiORQARGhAAAhBgDqFZenUPyoCEtAAdflIwFVEoANQAqvAVgAAPAwAHtZ7ToBjFpOAGpx_4ZAigqAAxCMAAFc+AABaDAEB1qjKqKKQTQD_xkAHPJgAJAdAABBOgAAWgwAAAAAAAAAAAAGCLFaOFiuUaqVTScYPpicSK7AuqsbD0wk0wgfBFMJhsoMTNqNK4+AAApKpRKrP1CuaQehVLGdtIoNR6XQij0eUgPzCXTCSagGC8bCgR3XtndzTBfKIBFBQ2Ts3Kw4WG0t3ggZiyQC4DBlQD1ToJIGqOgCiUQADqSxSAABcDEKCoZyUlN2BsDApCgh8bAWQKAdtKUjoAqwRAAAbEIAAGwMRMSGjpSNgBhaACKQAVKAJmQBkiAAgwAAAAAAAAAAADAQAIk4A0RAEhoAAAAAAAAAAAAAwiG4KAAEUTAANiYH7BwAAADQ+AAAcDAEOogmBg2BQAAAYQmHcRABdQACXlwAALgYAvJsABIg2BgMAwAAAYQmTEfAACQAAQlwAAQgYBQM4RA0DOINgAQQTAANCYABSAAVsVgAAPAwBiiIAkFCEFBsEgAQQTAANCYABSAAVsVgAAA6JEDwMIESBERcA3MkbgxdyAJiCkm58AAZKIAATwoAqpEDwMIESATJkALQAAagpB4hAJuSgjemUwAAnhREgMcqBqkQMAxeloANGwf3QgAAiVAApAAOkKQAATwoBglcM4Kgs5EDwMeQAcdAAAA4qAP+FQAA7BaAACEFADzLgVBEDwMmwmACB0BFAABBMAf8KgABjK8AAEIKA0AaFQWgiBAGDCVABU2AAACJUACkAArYrAAOcJgA6FQRUiBgGOUXABo2KaAABMqABSAAdGUjmjkAAAwyoJsRA8DLLLGZKYglxTaCKQCpBkAASGFc9AAMtKVKYyJOKoAAT4qCYGagXABo2KboVCAACZUABkAAiApERADimQNzY2T04LRIg2BhAiQMvMgMo5AaoZKgNgpMxDKET4CiLQUgTTKYAATwoJQH8RCCDBsEgLIdAWQKB"
noncomputable def WL10_7 : ℕ := zfNat64 5772 "iTgCSMAAAAAAAAAAAABaRAAAAAAAAAAAAAFoQBIyAHlwAESAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABycAGSgCRkAOLgAAAAAAAAAAAAAWEQAAYQmAAEYFAAAmMgAADAQANE4ABA6AAAAARgUAACYyAADcDAASMgB4sAAAAAAAAAAAABaVAoBQAADC4AAINAAAAATagAADAQAQgwBJJgBZHQAAsmAD_HQATqMgAADcDACADAwsqApghPwto8sqADNhkAE0TShAABuBghpSe3NzeBACY0AAAAAAAAAAAAA3AwNwoHhlQAtAkjUyoIEOQS2LgMoB3EIAAK+xNzenABqkAUTgCZkAAcdAAAAAFAKAAAMNAAAGAgAFpwCEvBoOADAZAASkAABAFAAAAAiQYAB6kANPgAx0ASGgAAAAAAAAAAAAE04AeXAAHHQAAAAAhEjfCQAAAC+BIAMSeDQVeY+AHZkAAAGEClRUAARZGAAI0HAAHTkDCjWrF8FrNy4AAABKAGEJcgPwHklAAFdDgAJpwCEuTsOAAcdAAAAAC4uAAAAAMBQDcJEERgEGVAFECsmTKgAiYZAFJD6IQAAGQoAexcOYkrhYrgtTmZBLQAApg3MEbAB7I6DaARbCpwABGg4iY8AIpwIUqBAG1C1CkjoAAMIFJARSZBRBCf+RgAAjQcAPBOBAGGmnABo2AAAp5UBRAqgcQAi1XGoIQAAGAopSelADakCIMCNyoDhUAAtAAAa5MAAFI+AAAwFAAHTh5Bo_+VF4LgAADGQ0AAACPQgACNBwAB04LQ48g0f_Ki8FwAABjIaAAABHoQADnEoAGicAMCgtDmwDR_0qL0XAAAFw2AAnhMAAD1CAByBAgWhwJBKgKkwARgFgCUfABsCIAACCdAAAtEgAYKQRhxNyIlKvy4AFIBKjIAGAOIwABiWpKAAOGLA"
noncomputable def WL10s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL10_0) (dpk j 1 WL10_1)
noncomputable def WL10s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL10_2) (dpk j 3 WL10_3)
noncomputable def WL10s0_4 (j : ℕ) : ℕ := dsel j 2 (WL10s0_2 j) (WL10s2_4 j)
noncomputable def WL10s4_6 (j : ℕ) : ℕ := dsel j 5 (dpk j 4 WL10_4) (dpk j 5 WL10_5)
noncomputable def WL10s6_8 (j : ℕ) : ℕ := dsel j 7 (dpk j 6 WL10_6) (dpk j 7 WL10_7)
noncomputable def WL10s4_8 (j : ℕ) : ℕ := dsel j 6 (WL10s4_6 j) (WL10s6_8 j)
noncomputable def WL10s0_8 (j : ℕ) : ℕ := dsel j 4 (WL10s0_4 j) (WL10s4_8 j)
noncomputable def WL10 (j : ℕ) : ℕ := (WL10s0_8 j)
noncomputable def WD10 : ℕ → ℕ := rdw WL10
noncomputable def ready10_cuts0 : List (ℕ × St × ℕ) := []

theorem ready10_cuts0_ok : CutsOk ready10_cuts0 := cutsOk_nil

noncomputable def ready10_0_state : St := ⟨26112, 279315, 28545, 39936, 52016, 95837, 29666, 44151, 53248, 79646, 29184, 45301, 28545, 109229, 26112, 279315, 54657, 319251, 106673, 400218, 136339, 429884, 189587, 483132, 218771, 512316, 287658, 540861, 313770, 566973, 80561, 124382, 110227, 154048, 163475, 207296, 192659, 236480, 261546, 301888, 287658, 540861, 81682, 125503, 134930, 178751, 164114, 207935, 221610, 273343, 247722, 512316, 82914, 109312, 112098, 138496, 140643, 221327, 166755, 460300, 82432, 108830, 110977, 191661, 137089, 430634, 57729, 138413, 83841, 377386, 54657, 348202, 0⟩

theorem ready10_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD10 ready10_cuts0 111 390) ready10_0_state = 52028 := by decide +kernel
#print axioms ready10_0_cursor

theorem ready10_0_covered : Covered (toCl ready10_0_state) :=
  ready_cover_cursor WD10 ready10_cuts0 ready10_cuts0_ok 111 390 52028 ready10_0_state ready10_0_cursor (by decide)
#print axioms ready10_0_covered

noncomputable def ready10_cuts1 : List (ℕ × St × ℕ) := (390, ready10_0_state, 52028) :: ready10_cuts0

theorem ready10_cuts1_ok : CutsOk ready10_cuts1 := cutsOk_cons ready10_0_covered ready10_cuts0_ok
#print axioms ready10_cuts1_ok

noncomputable def ready10_1_state : St := ⟨26112, 259144, 28545, 39936, 52016, 165724, 29666, 44151, 53248, 79646, 29184, 45301, 28545, 142253, 26112, 259144, 54657, 299080, 106673, 420389, 136339, 450055, 189587, 503303, 218771, 532487, 328000, 561032, 354112, 587144, 80561, 194269, 110227, 223935, 163475, 277183, 192659, 306367, 301888, 334912, 328000, 561032, 81682, 195390, 134930, 248638, 164114, 277822, 261952, 306367, 288064, 532487, 82914, 109312, 112098, 138496, 140643, 254351, 166755, 480471, 82432, 108830, 110977, 224685, 137089, 450805, 57729, 171437, 83841, 397557, 54657, 368373, 0⟩

theorem ready10_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD10 ready10_cuts1 112 75500) ready10_1_state = 116289 := by decide +kernel
#print axioms ready10_1_cursor

theorem ready10_1_covered : Covered (toCl ready10_1_state) :=
  ready_cover_cursor WD10 ready10_cuts1 ready10_cuts1_ok 112 75500 116289 ready10_1_state ready10_1_cursor (by decide)
#print axioms ready10_1_covered

noncomputable def ready10_cuts2 : List (ℕ × St × ℕ) := (75500, ready10_1_state, 116289) :: ready10_cuts1

theorem ready10_cuts2_ok : CutsOk ready10_cuts2 := cutsOk_cons ready10_1_covered ready10_cuts1_ok
#print axioms ready10_cuts2_ok

noncomputable def ready10_2_state : St := ⟨26112, 285696, 28545, 39936, 52016, 215405, 29666, 44151, 53248, 79646, 29184, 45301, 28545, 191934, 26112, 285696, 54657, 325632, 106673, 529646, 136339, 559312, 189587, 612560, 218771, 641744, 247316, 670289, 273428, 820177, 80561, 243950, 110227, 273616, 163475, 326864, 192659, 356048, 221204, 384593, 247316, 670289, 81682, 245071, 134930, 298319, 164114, 327503, 192659, 356048, 218771, 641744, 82914, 109312, 112098, 138496, 140643, 304032, 166755, 589728, 82432, 108830, 110977, 274366, 137089, 560062, 57729, 221118, 83841, 506814, 54657, 477630, 0⟩

theorem ready10_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD10 ready10_cuts2 115 105) ready10_2_state = 146546 := by decide +kernel
#print axioms ready10_2_cursor

theorem ready10_2_covered : Covered (toCl ready10_2_state) :=
  ready_cover_cursor WD10 ready10_cuts2 ready10_cuts2_ok 115 105 146546 ready10_2_state ready10_2_cursor (by decide)
#print axioms ready10_2_covered

noncomputable def ready10_cuts3 : List (ℕ × St × ℕ) := (105, ready10_2_state, 146546) :: ready10_cuts2

theorem ready10_cuts3_ok : CutsOk ready10_cuts3 := cutsOk_cons ready10_2_covered ready10_cuts2_ok
#print axioms ready10_cuts3_ok

noncomputable def ready10_3_state : St := ⟨26112, 277350, 28545, 39936, 52016, 80285, 29666, 44151, 66919, 141794, 29184, 45301, 28545, 166816, 26112, 277350, 54657, 305895, 106673, 357911, 136339, 402062, 217743, 485098, 263044, 514282, 291589, 542827, 317701, 568939, 80561, 108830, 110227, 138496, 191631, 280290, 236932, 309474, 265477, 476290, 291589, 542827, 81682, 109951, 163086, 251745, 208387, 280929, 236932, 447745, 263044, 514282, 111070, 171460, 156371, 200644, 184916, 367460, 211028, 462266, 112220, 170978, 140765, 337794, 166877, 432600, 57729, 212117, 83841, 351196, 54657, 305895, 0⟩

theorem ready10_3_cursor : U (walkCut TOP BK TOPD BKD PT REG WD10 ready10_cuts3 112 154647) ready10_3_state = 196188 := by decide +kernel
#print axioms ready10_3_cursor

theorem ready10_3_covered : Covered (toCl ready10_3_state) :=
  ready_cover_cursor WD10 ready10_cuts3 ready10_cuts3_ok 112 154647 196188 ready10_3_state ready10_3_cursor (by decide)
#print axioms ready10_3_covered

noncomputable def ready10_cuts4 : List (ℕ × St × ℕ) := (154647, ready10_3_state, 196188) :: ready10_cuts3

theorem ready10_cuts4_ok : CutsOk ready10_cuts4 := cutsOk_cons ready10_3_covered ready10_cuts3_ok
#print axioms ready10_cuts4_ok

noncomputable def ready10_4_state : St := ⟨26112, 285696, 28545, 39936, 52016, 251938, 29666, 44151, 53248, 141794, 29184, 45301, 28545, 305088, 26112, 285696, 54657, 325632, 106673, 566179, 136339, 595845, 189587, 736336, 218771, 765520, 247316, 794065, 273428, 820177, 80561, 280483, 110227, 310149, 163475, 451943, 192659, 481127, 221204, 547983, 247316, 794065, 81682, 281604, 134930, 423398, 164114, 452582, 192659, 519438, 218771, 765520, 82914, 171460, 112098, 200644, 140643, 467422, 166755, 713504, 82432, 170978, 110977, 437756, 137089, 683838, 57729, 350389, 83841, 630590, 54657, 590784, 0⟩

theorem ready10_4_cursor : U (walkCut TOP BK TOPD BKD PT REG WD10 ready10_cuts4 118 81) ready10_4_state = 226609 := by decide +kernel
#print axioms ready10_4_cursor

theorem ready10_4_covered : Covered (toCl ready10_4_state) :=
  ready_cover_cursor WD10 ready10_cuts4 ready10_cuts4_ok 118 81 226609 ready10_4_state ready10_4_cursor (by decide)
#print axioms ready10_4_covered

noncomputable def ready10_cuts5 : List (ℕ × St × ℕ) := (81, ready10_4_state, 226609) :: ready10_cuts4

theorem ready10_cuts5_ok : CutsOk ready10_cuts5 := cutsOk_cons ready10_4_covered ready10_cuts4_ok
#print axioms ready10_cuts5_ok

theorem ready10_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD10 ready10_cuts5 128 1) (ofCl (RC 0 0 1 0 1 0 0 0) 0) = 235228 := by decide +kernel
#print axioms ready10_parent_cursor

theorem rc10 : Covered (RC 0 0 1 0 1 0 0 0) :=
  rcOfC WD10 ready10_cuts5 ready10_cuts5_ok 235228 ready10_parent_cursor (by decide)
#print axioms rc10
noncomputable def WL11_0 : ℕ := zfNat64 33245 "RFBJwhC0C_qFeBCVbHopAi1UCal+0IwhdAb4qWwCPcQmYiAZySzBAiD_zkBzp6AAHKQAPQCyVQdcjAAH6RhsxKjMVAbQB+nD8FoLsVq5tF4AWGiSzSAVT+qERSwxn_BEAAAlJJ2SVA8Bg1gACUp5CjIIgElEho_AItVLGJxBKpQTCKYXNYBhACBhCXC9+GTeAg9uAuQnAhCJaNURyB2pKKIFUugWQ7hpqArIG4T41bXCARE0AAAAAAAAwgABPNhQZGlAjBPQAIoY1AvrrRNJIf+QI4ABvkILCBKBaAAYfADi4ACPAERoACJAAAAAAAAAAAAdpGjoUEJD0SGUZKMT_jiMmiX_xcOnDAZFFMtMoVS2clUekUWiGQhEQoZ+FzGSSbRSKVkCrrUBVAhMaPxCnhODU40KQB5CJDFoAxKmoQlABbZsADhSDiD4jXQIIEdAJD3pC_whAa0UhqDW5BEATYuIpFAmICgPFz8t3MBwIUcI0FwhFIlCEhUQgAEej0gjEgiJGrWQSKRQciND5uABCxO2gtZOjgl40XiEUjwJF4AlCh41HIbVWrbOR6ORaMQchMnGIxGIhDpBQAknQ2iQ+yTVvAgiWU7wLl8lEslFIARLJRCF06zkgj0UzWUKEFgqTiCQI9Jos1JJXQCoXYjcQJoABGI1CEvJQgA800NJ4BmQkVIJJIIAOWjuADRGHbiUkOSFHDJtDxuOSCCRjNReYYD_hDFUsnZV46iUej0cjGgqSJFY1JKKkqORSSHrZsYAasYAORAAh4NeMfAXQEOKGcA6kBAAeSSBdLoGiloAaWtAAFxsaJD9xCEgGRRIYeBIdgtUMBgAUTqYSCTRaBVdUoayKBaRFVkNW_2hlIUBgQcYx2AwEayEAhwAIfbS7QbrdWJt3Ou02c1Wq1FmJEnd8jR5rMaiUSbRRFTlNW8YyGCl2iuDMF5dIL_XaTMaqhYCH20u0E57l3lM5DmtX6bOarJZa78mR0WazEozEagfSo4Cqp3LeABAWoEokkBokR9tDh7SsyXwoNpLNNIJhJtNaiULyKPRyOhapITQFCQAHdGGOIxFt3MISA1IJRJIIPDAZxMP904d6lV0miUW2Ggj0C5WYRSPQL6AIEeliWqhCQLynT_ACkOQf6GAzyAVU0hGZiHoCACPgADEGwMAA3X6iBcErlvCEgAI0TgRSIZRJICjCh55NpdO6pVdPNtKt5KNhvJxNJdOpdGlsWcAzJBxPcQQIBXUiGEkEphgMAAvplM8nEwk0WgWSyaxe3gGkRG2kiX5Ak2qlkg00klET8BD7qeb77V6pNdstltNhQ6fQ6S2kiTgEZs9lNJlKJVbGxZwDABF8ABphVujV7BAjcXgs0kAixTJIDxCAZ5QIcLSjCeT6gUCUbDeTqdTqdS6I8XNYBhYOmkCqBK1q3lUog3EyADKfTCAEfR6UjMXQC4gKBmYSWgIKPlHCh9FZ8CfUSeATIqTiUUgZcgBi0zR0APRyPRz_AsZyEBwhQyCRR6fSLgegaHhyCRxDsTMACREfgHCSICEJwEEByRRSejQgKoFqD4DSeQgfJ92CeytbAi0UNwcglgCRzkAAEiQyiOCRhyKTOKEAAfQBYE3MB_DDRQWi1gpIjKq6CReLRB4QDKo5CvpcAI4fmEejEWixIEchoJlqpNZIlRySF0D5sAArwAxaADHQAY2AHmQAMaAHiwAAAAAAAAAAADQ2NCQjEyXkwiCsgeUCCUAOASMkqSNgCDVR6ApE0I0Mwk0mitkoaEwXwJAeq2iz0t8jLkVJ6ClKUgZKI1BpgSSNRaTE+BozqpFEo1FuRxqgmEmk0kkOYguiioZHD4FUyootE6XIT6aSiLUCPxgSSMRyTFiJg3KtFAegQxqLaTjh+gmEm02i0UKkvWw9BwaLPOAmS7_mQFUBCRQvHIlHI8JeKIAhGIACClquAOl4AszMD4nicJwqAAokkCRykN5KpgBEpAjgE0uiJEaGAVS6esZgLrwAEbAHqoUTJCARAdqYgNkHwAwkCAAYgAR8UgAB6TNODiax4sVgyRg1kEB7TRqNgRkCkdaGoIyJhiTUmiUojZkaGBpBmiSwMIDgIADTgASUAKPgAh0APMgAY0APFgAAAAAAAAAAAFgAFiACLwAFWAGnwA4yABDQAsWADBwAAAAAAAAAAAgaELAEK8Ae2hVF8ACNgAJMIBEAVQOoHwBEFKAAegAAmMgAA+HwXgoAhXiDFsATJhAIgARGwAAZPSgAMIAAEDIAAPh8FYIy3wcUk8DxsGXHzcAemUBpapbAB6LQCDQRvKBHBxzcRRCGESI4fg86AEzIW4WCTR8Bb5GAIclRQhWAFoBRoJdNCA2gQGQgPqQ8zmRcCEWQBIOQXkDwMqPgGnnQAb8mABnRUAAUgyAAAHgQmyQXmDwQeQgIfIQAdsmABxpUAAV4yAAC0XAPARuEEemo8Jo1FwABBAG_kwCENilwADED4AAegD5pgAU0FhEKYWBOycASQCBpMBZAAKsdKrHwAAij4AoaMQiRFgTqoVwKKHX1oU6ULwu1UBhqlsCaRaCK3QIZdAMiQyfJQBNAOArBoCwHKVgEtJQAYMqPIBeRSBUBCOdoRZiAbAFFAAB1g+GMYCTB_5OA6shADaDYAOYKwAAUj4AAQyEA+HC4O0AQMgAQ0APFgAIcAIIHFDYAAcPAABA6AAAAAvbuzA2tkABrinAA8HIE4DRiEALdJgAVIqWwAJDHwAAhjoKQWLHRepjwSnLBNA4BgIUho5WAbQfAB+yYAHXFQABeDIAAik3Kzc7RgummG4GCuHAXAiAHoBowqABlhY3AA_ufAACyCgjtQBCzBfI4bgYACw0BTQuACkDwADUAA8xkABGQASCw3Aw8Q4NZEQBdixWDU_4dL3KF4STLyZqBaFZKaVGRgJKAQIASGhPhxGBgCBOBdweCaA5yheXEygLj4WhWSmkEFyRHISSUCTCQAAm4AgNBH5IBkOA0iBHADoA_4uVgAyIuVgFNFNoEMECOQkCJAyCZJYbgpewkGuC4D_x0APhJgA10ZAAL2MgAAyA3BQJhIA7FwAojoACeTAAIAqAABMZAAAAARYQAFDcFF1FgcyaNwBYnkMAAo1k_qTATkiI+zaxikAAwpUpgCAgAFiAKLwAwWAJhxCOKAYCAAgRAAAzQeAD_yUAA4UqAAQIBCxYAYHK0NB_RKcsbAAAmcqCz_peC5KMAFUAAyk2UIAkYsHgkBJmSbAKkDiGhG4uXhZroxdCvEUis9CqGwRpqAZSqWRCfk6AioABZgSIsAIjllGgI6EwDLyxme6Lgk2VBpsoBGNmYFlppAtCAOv9UIAAQiw8KOCIOAAqNAagNgBdA8AE9AAZiVAAAC+8IAmHBEHXaIgo6ZAf+LgBLg8AAxAAAaVAAABKhYAHHB4JKYJgAD6ljMFoEDKF4YTD_lyDrGzMltJsNNHWI01A60EE8bMwNAZ0XAXeEABvgRBj6D3EIAkgsAC2HgAPWTAAAdKgAABExMCslgRBohHwEUAAAHFQEUAADSnB4lYnM5AasXAD+DwcCgHI0MCrplMtpZV6YNyqkxOOULy0lmigISheV0mk2miBUCOTmagACagoEQaVCEBdTRuA3J69gCSC4NIEHjIAqzkCcz00hPg0dgDoCgRBlaHwAE0vDBfAC9FR_RaIILaMgAATnxMRSAABIigRBjxHwTgXgLCAPQAP9HwASSaJ8TH_yMBxQuAApXAMqIEQZKR8ACVzGBINgzgEb1IAP9pE8ACxCETmkmUAAAOkACjiFkUCIMCgyAOqkAIQuAGqHQAAAFEDIAAkgASMgo5cBVCgDtkIAmhVCjisTUAOgfySpCK+Qic0kohJlWAK0XAJgooCoABSFHAikiTwqh8lWJqAGQEpFkJYdCJzSSiHYloAqZcAIGgL4UAqwhW0CaFUKNKxNQA6AlaojSEcuhE5pJRC7y0AgYuAqhY7FwDtEIAmhVCjisTUAOgf0SpCK+QiDOaSUQ8WrA6UlIC4LguxWDgVgSokUrJRQq0kbidVScilox03IyBMR2Eycl2jE5mpJJCo9UtgaBly4JuFAiDAbdRgmiXESeC0D1qx_I2AwICUii0ZejAhGpRAAUDGCxuhQEqJk7xTyGTEoWgRww2n_ikWlUrl1utdFQihcNNxLJJHlBQcCCURKIQyAYoWN0KASz0mI9RGjhFESoVxgCtXBSRQA0LFwEDRjOJZIJgQIJREotaORAGAKBYIIJG6FYE4sZDElpRQgjUZorVwkjUAjCxcMIlLNFChoEcAqi0Wy+JgNAmosboUIlCDoqI7B6EUIpF0YraeWgmgYcCBEcg5HIEdGIFVzHQCgDUKQwSAQhQwHIFYjyGGkBCLFcLIAAkyWLfYjVCMGQPCNDCKORiBdAAkNAIwp11CDwh0AQQ0gTxYrhZAx4kTwKWIwZOroQRRyMQ_4vAEMCxtRJZyUCGA1BxB8eg+dgWmK+FVABMSdLoITkQlBKpZHs5DPy8DoASGgHoUoIDkl07AkEB+GkBicE6WK5DhaAAEmSywhFDIOZChhFHIxAyXQBuBSCgw8hgmo0ZgDkygKyWK4AElHqRPsIlJGDIr5ChmEg3kOhiBkuk7O1M2TgIgwbD4DqA6xGAIKKwAZITgCKGSraEAMQPItAXCgBMKBEGDYfABVp2OIAeZWABQRcAf+Gg4yEAAASAg4XKi4DSDgFEUCINK1CDrScAADzi5WF2u00HIEkomUu0jQyYzUBaI0Ai5SBEGawpHpjIAAACjTQsoAEBkInM9tc3BacuAMzFAiDZVQg8gXADUMIgxGWCSKwJpJAAogPSYzkwnUgQaQwEwUQIgx4j4I8GwDRCYAN4VKwAVKsYwAB6TGcgAABo4EQaMh8BFBup8BhDLJUWE_0lACmzWAUQhwhExnIDzloAAO8JuigRBmWHwN4MgJLMwSQAAMIAH4z4ooAyxYnhfhF_1CAahpj4IIYQGCoVwogHQaM5LRrQSiKcQoZMZyYTqFGYL4AC1YANFP+oUFBqOCPgcSRDPphAqgm2CmAZSWjWglEzKc9JChkxnJhOpZAYwXwRR7oEMCfmDcijEckEulUmo0SpZfVCuUxYr00pNNKOyZx7LRqWxGhlGmkEejGc108lUJC9bDsASMQCMbs0Ob8hBNY2tIEk81EPdKxYQshlAoNNJ9IQLZqYTqWmXgCSqxFyFDRwRsBLBKAJvKwAYEYM8tCg00V6eQxyLZqYTqF7WLYOpaZRAfplShxpg3Caj001EC0K1OugU1CzBnIoUZQqblFOIJFFM1LJ1D1Llsu53FAAKEACPgBpcAJKgCQ0ACFgAAAAAAAAAABVgUSOBEGDYfAIAeAOoAxhSADezcABIxCAA_4vASDhICCnMuKkYM9pgCQsAwEBIyAFpEAOQBRw8AGYDoABZpUAAFHGjY6C4ZYbgaeo0A9AMAOGwCTJMAB5yRWAA4gyAA+iJA3NhAeOAYCA6FAFYaA9wVADNh4ABaAA8guAAgmLEvLi5iTkJDEhoCOwI6Gx4fXhdHSxpC"
noncomputable def WL11_1 : ℕ := zfNat64 33245 "YwXgBDjTSTaMQISAALMBilXYETrToAaA5gsVgTkZpQvIyGEaOWMwAhxppMBGFoAOwIgdHScFIOCuHAIQwUbDSLFYA5ZyULw_krGKZgWgdTrTR26BHAAABXDgEIYKNhpFisAcs5KF4fyVjFMwLQOp1po7dAjgABSDgAd1wpB2t04D3EB8AUgaaOlrlC8ABaB1OtNEkI0MAAKQcAwTCBUKKoIUDjRMAKJHgAvKTAAAhLgAAKhQBrVIBpVDGHZmFg_6VAKQLgB5xcREwgA5MlggTrTThqEAAGMOAOyXDGHOOFgAolFDaRJqfivI1KF5EayYfhm0hA4nWUxUAADGHByGmIKQcHIUNgfQcRgNQBFisAcv3KF4XQCXlC8OJ1OtNFnI0MDOqsB+j6OAGMKFIOIYLAGggPgD0AHyULwunXmJah0LQ4nU4i0A6gRwAwkpAEAQiwpBwlhYGlDiMAJRYrAHL2SheF0B5xw3DidTqYRvCNDCyBdAERKlxDQc0HgBSBpw6WqULwugC0EuOx1ppC5GhhpABNlC8ADbEXYNAHS6DUUgXMOlvFysSl0ApxozDiqpg73GmgDkaGGkoikyhaC5WMmD1zxoA6BBEkXK6yE5SoXKwugLbKF52ZyNNxpoNpGhlEyn+Cqyhui5WYNmNioBHjhSDgLChsADDiMFiGwpAHLOyheF0AWhxsk7XGmj0UCOHwJF4ARQBSBQxh18BoA6BNnIAKMoXldFkMwGYyXhoBuutNKCoQVZyFTaAPkXEyFDYJMID4DkMG4pAHLsC5WF0CCGYsZhxMJxKpFGYjQwwlGo3Ewu0HEYACWIAKNCvCwA+ID4ApJoY+OndlC8LoAxAAQ7cyqIuRoYYSj7FSuI4oeALExAZpoHbFASCwDDGgBWFQBSQqACc_wUgAugfHEABvDCcnRjxg+vEUNhGQIMprIWkOjrFysinQEoGiGS+om0OJVAaoEM0mEo1G42EuhAfMEdlRuXpw8BpQAFVAAqYFAYK4cAAAAEyoPzMQAAHFOBIIQAAFAYBH58ISpgVBgOhQB0ABxEAAIIgAAAFLGwAAFQYC4sdi6O1AFCcNwMAAAkHgAL1FwBKVryEFAFCfAAAfBgAOLwRdOIkGAAkx0JZMAPZLgnIRQPqFcJSU2mlySo4AAHwYApycNwNGRGADjq4aBsTAhAAch6paAKaIWQgAAPgwAw04B6hESDJhJgADoSCYAZGXBpHJ_RGLISkpph5GAAA+DAbfm4Au0ZAZ2LgOIOEoXl6i4og+IsZhKQmjeUIAAD4MAQomAJCQ3BQHCEIADzjsGHKi9hdTQADjSQxCsAAARIUAxI2ZhXWJlC8LaPXvlC8TwYLyaYVkHwtCUnGmhZUCOAB1caKMAIsxEhQf6RnmGDcAWgbacHzQyheCE0ymD0WhKSaTT0CMABiwmAiQrlhUf8aqsnkMAWgXxw3j1oZQvAog9KgYLwlITTGiMH8oIAAiQoCyxAwbgIxiFoHEesfKF4WaaD0bRgvCUhNIIA0COH8oIAA0DMkw3BQTeWm7nkMABErh3DDlQU0AA40kQErB_J2A4QdAHiphuChBEQCANgCSAQNJgAACOkQDoAA4R0AMXOEA0w3BQgiIP9LQEkA4lgyYAKqAA246AAOEdARIUyAoXgPQAFLVcotlf8jSzKF4SSaCxFquFWWnGmjDEaGDEmrWVQYkfOwJBQAYhAAy4AYVAEhoAAAAAAAAAAAAlhmBc5wAFCG4K3kjAAUaKCkyihSYABrDwAANjoAAA2No5kBAIREhQGFtJ5DAeoYLwOI9DOULz_S1TRkB8MQlITTZyMAAcQiEPDAFAkU0MAAAWKgABBMXqLv7IQAAA6V4CCBlw2D6xIAlBszCulJKF4W0et5KF4ngwXk0HstCUlNVAhFNQI4CUBADiOogyBepIpoYC4BkBMgqAEokxeguAjuVAAKWOgACyAWkSWcOAAZUxAXEHJ8MkqL1FxJACMlF_wdHdUgC6Hcj4AQKiHK0HAIjZNYAAF_Ki9RcUQWaXBOSmgyUICiBPgyBkBFCXOCQDtgoAigVZqzipSheXqLiiulaJaEpMtNDjoEcA8yUAWUOAxaZAC0Jctwn0oXl6i4Ak5QvAihNAjIUMDqeb6qRMQZlxkAkiQOhwAA_WYDJUAALJi9hcQQAA2Z8EYWgIIA1AfBoA4BcAcMqADfkxeouKIABHQ7h8AAJUWAKYiAeRozAFof+ahCJQvAogXpctuEMiWhNC0oEcBaBn0eAhOyOIwGiYMwGSlC8LKPXrFysPihXKSDEVS2XZzLSmjkkaGAtAc8RHwpAfqEWQ8HQAVszAsLgAfJUF0mgmReAP_Jw3hCAWgQGGiNBQeDmJAJiNmYAtADzdrqSfIXKF5eounoNnLGYAknpjJGAD9xUACMgdqSG4SAzopAXwKgBcJMXsLgLHlQADMjoACogABQgk18JNDgdDgThQTlTgADB58KgmCmgAH_0oZ4xAAf+QgBAEKEHajgGAgARGwF8CoALsPAA_8mAASoZAAVEAxwcOAkAiU4fgqNiAOI9LOVF6i4ojnj4CUhNoKeFIAAegCAw84LmJBYo4ACDDcJAAEkugB2SYvYXf+UgM6XAAAmPgAAA21MOAkADQWA3kdADCSYvUXAf_MgAKQHwAVAAKYJDmJDwDgAg4rPJPIYGlxasLQINFAYFjMIiNaCADQiygVDYScABFCBvCQ5iUZBeI4jAqgCQn4Gk0KscUoXhNINFHqIjBeERGtBGLeESWFUCoRCSBoCMgIMKGwsgOlKF4G0cQXKwd2iSwceUL_RExPSKTQJCFDDLZQ6CtjJeIyGTSD52f2Uk9LVcBRhcrC0iSi5WEmigQwuVhZHpFJoiNAhhdC8zYwzQSWk2ACuYfGNpKWQF4lC8DaQNKF4SXpJUcFBlC8RRkT0ik0e0EuvFWTWFaCK4Ml5hgi2aBZBwHEA9qhorAogV3KgBxhUAH_i4AB+h8ABJQqACOhLeRf5IgjkuWwCylC8DaL9KF4YR6BLSheBBIpNEhIUMDSFQwyXAaA35IcCIAqgdcMgB5pMXqLiiAAR0p8fAaQIiFQAQZoBOHPkRIECyALQBCJQvABzqpbAggSRiafhQgNIVCwBcAHWbEVxHwauWgBaATPKgAc6qWwnYjBNPwoX_IIYmkQhe4uAAkNGAHwKwXLYAtAL4FysAHOqlsOUIQTT8KEUU0hULYFwOsMkRkjpubaaVQLMpCiZRMHxXC5WUR7RSglUsz0c0EmjyTpYw0CGcSnqFcuxGggDyheToaA_UIACHDcRB0ABOhcAKBKguwYTgzovAQXgIxNKCBpCoTeLiNBQ8dGRcXA8scOYkAAMJKj0UP9smcgjNKS9hcTQlISkpIDE8hgAdtGgDFxxAEisB8xg3AFIU2bNYUQuVl6i6imvjqUgRTSTR6KhCfhcT6Wf8KUxABChDCY4ExYAFRcB_5CAEuDwAAADuDIABX48Ac2OAK6MG4ApAdTRnDiFysAIKJlamBFCaFOQn6fC4uJ9CYgD_jmLIE5IiA+ExAlIAcIuV0UAqJJApKLkpI55DMswZySccCENzBmDoEpQgBUkKSjhRIg6AChmYUgF9SoP9JwFUAD6J4_C4gJsNF5GgseMi4zHgIyH24QFqgGAhPFwCUDphEAM0HgAEoAE4DIAAAwEUpeBIyYiQaaA8AUzyGAAEKi4MtNB78IyJzITjTRFykAwICAAIHhAEg4BgJvAsFdAFoA9oqDKVQ9EZAAApPgAACAOEARDgAIEAwEEQJIFCCIAZIPAB9gyAAAWRAAAA12YAkLBsDNoEhAgA1ACAlGtKF4aTSD2zR2BlOtNJ+oQAAABIOAAAAAAAAAAAAAO5gmykASDhuBiXKQZQAAAJoFtnoCb_puA+Z8AAAAjXgCQcAAAAAAAAAAAAAkZAEg4Xg+CBysA4oiCSESi4ACqBuJ2KIwxCAAAAArwBIyAJBye6EBRABkSIwkh1YuHrsGMsgGJSngXTqUSs6EAACpqYU5BUu8ASDhuBiDGj8CSA2gwbgBnSoAM6GQBTRN6EAAB_G4YbF0YDMSgB2EASDhuBi0CwYUNgA+0VBdKOVBlKoDUApodpCAAAETExEg3Ih4HankM_qnFU0YKoZchFwZaaTEJzISShFLClPAdUVAAJUJiJBhfjh8A0IT8pv_kLyKMFWkmUOBcvDLTSYhOZCSUIpYUp5RQnJNReABthBRQ4bgYMwsChDoAAOs1CTJgpoAAIRZCsAAMQBAQAkNIOiwRRiARSmldYWULw0okUK5RkJ+BBKF4TZyPaDLQ0oEcAAHGyaDYsEUYgEUppXWFlC8NKCFCuUZCfgQSheE2cj2gy0MqBHG+CBcAABoqYOCwBWY5kAAZKjgF1TJQvKiWQZU1ZwOzkk0ENugRyBwkAAAzdIAcTAEhYFw5AgmA+AI0VAAqh4AATGQAAAAAH+KgCQsC4c_Y+AP7LQp5GDKUQ+ZUE0MgAFUakelIAAACFMzUjZ8GJ04CihlCjZUGGzzEGyTR2gS202gjl0IABfh8CL+1CAmgGPQI7Ljosg58oXugRHZhAGpZKPWGIc0EcigRwAF+HQUgQfiAAmwBIWTXFHwSHSgIaoQAEYqAALpcAACY+AADBABKsAEJmZ0ICaF0SygRzCYVvKQtkoXw0ATJjqoUEKJlINBGyoEcJyBSQ6B3ZjdLGnIQW0gB5MASFgGAg6H_joCmhUAMoHgAA2TAAAAAXIeB2q4CnLFAFO2IgKoAbDyGAOPJgA3GVAAO4OgAAACO8BslgGoUCINsAaNdKQ5MCaSSWUql17JQvDKUQxnkMUi0Js5HsZBroEcjocQ6RQAQAkNGiiwIgMmYFFKaBeYlOlC8NJVAyZQvCbOSLQRCKBHPmkwAP4qBdauLAsYyZgUUpoDJiU6ULw0lUDWlC8Jv+zoi0ERegRwACdFQOgAYOpc2SEMHyqz0AghVFeL1thZQvHbNWcosQQn4LQmzke0EJCgRyMwEwgABUFnyNkWEwaOHgJMIksAOGULwskkIrFjMioTaCSRQgKKMQAEkJPkbMXRgucPAMmRJYBDkqDD_RKAWgE2gkR0IBoRQAbAXeEAPJgCQcQIJgPgCBFQAJweAA0ZMAAAAA8SeQ87oQH2OH4CNUCOU0HtlC9wCFYQHklC8Js5nNBAXI0MekEmjFjnoUEACSMVkhAPQAhJEcAXeULwk0iSgZKULwCDQTYqED00gPeRIYHxoyu6FgMuePwG9JUcAKCUL6KaQA5lC+SgEEk2hAbQOKIwAjjL7WIp4sCoj5+BRQBTpQvBtJKoKhKF5Df2nRFoINNAjgMps5gEUAVA0GyUFoWCAykBb5GAIclRVABaUQHzUTaCU_QgNM1AAAlZHsfDyFgIYdAf0YgDCAAsg2ABaGyPgAA+HwAurNYD6BwsFzjoAigGmFICyBUAKolJPHwAAfD4UUUl+CIDJERQScIQtAv6hXgQlWx6KQItVAmpftCMIXQG+KlsAj3EJmIgGckswQIg_85Ac6egABykAD0AslUHXIwAB"
noncomputable def WL11_2 : ℕ := zfNat64 33209 "RBQSgAFqQIEg6enJiUi0AELFZYSqd8Lh4ipfADIGkAvaEAAfImBFwSCSmSloAYWK0kEVhKpxguHiKl8AMgaQC+oQADnCYACQsnGLBJTIi0ClhhFYSqBs65EXBZADJLNqAU3awFrIwAAAKkKb3JgSsbMz_7sC3VhNYai6I6oqWLwqgB5FDYZTDQQfujBxJIACgljPnpMYTthMnJkI0MFIVR6Ag6AiULwqm1joShULphBqBvQI4aSCHkVIlRwAazR5BMGdSYCvxQvFtZ_8jG5C4mkKWgAyAAtFCFppAN+oxOis3NgC0yQcEgkomZaBSUTCVQMnQtC6BogaLs1Wo0gC9QiNBQAAAVDJJ4WAFRUnINVBTUbC9dQrgtCyBFaCMl022H3Z8LRgqMTEAUalE6IRFy9CYwfARZIn_atAKskV2EwgJsoX1kAbSKFzSAHp0Y0zCRgAek7O1J2igNiSBgKBoBBOwqAqgVABCyYAuQRBkABMh8AB_4qAKXLAAZIJgo1gcHHCYDzhUAGFJgAQhkABwR8AAaQAAiwQQOCYKTOKGwHJVQ1hYrLC6BWpzluBcvC6WQDodbDIZqGZSJ4RkygJkULgABZgYosASaTAdgOgogoEqC6B_QeA2nEBwoRxBY_unHEGniwBThYzRYBphUnKC+pKmoUSrSR1lC8LpdCBwwfDibbaQe8mRJCmnGYyEPwgXB0XAQFpLB4wobgqL40E5ADkWNwACZUAAFpAB0pBxLIZRyBsAC6WG4KRgJB8AuA6wZBZBSAAKQAEnIR_5yAD2FQKPCQCoKE4uBSBSF0AaqltWQ4jKoCkRw2C+moAihxNoGtS4AANcImJgd0sEQdMYqAugAABBSAAD9SECyTgFisHEogUmKgABUwKuWCIOp8NB_w6AAogJuQpAB_IqAAZSfH9nIAa4VAGMZgBcsEQcrAiAAAcwXwig6pWP3KwY+LhCAAthCDiYQJuFwABFYACpAB04AChABj4AOZAAi4AMTAARoAiLAAAAAAAAAAAAA61wRBzOD4NrHQHVF4AYYpAAJQAHMnwYf+KQADTGS81SFDAczGo_sOizPaTcAyX39WlDLVcok0ezsVpbGRqWabXQeKgRxCaS6XTSBaWrYABUZQRvq5jHIVRyVJcthNa2WM6yOxarnEmkEqjGMlZptdoqBjZm01AjhU0l0umkqioWrYACk4BCXAAABhsAAEHgAAAAAACBkA_oEduZ5DKILw6b00AOLluokkHzqluyg9Bb+EYN00AfeZPYRoZZMtZrNlEPrFsD7OdAQAanABkoBCXAAAAAAAAAAACLjUMG85wCEuBAKAJIEUDYAS4bAAAAAAAFB4twmjMwcVm5uZJx2pm6cC+Vw3Ax5BIBiB14uAFCkwABkABTB0AAB8GKc5JwbgYHdBwGg4BzBUBORGHQAaQiAEEJkrAAAfBiFtQBCzESDAABKBoAiQXAfoSHwH3_jIAportCAAA+DARIMGPgYm4UAEgcRgGeS4AHq1SxmAU2g8TRgAAPgwBvmYTLfDcDABEAagDSCYAPunQAANjoAAD4MBteAIS4AQHCEDABSEgAFDQAUsqACjRkAU0PChABUAAB5cASGgAUhIASA0AF3KgAV6XAH_04NUhAAAAAuYUgpZxEAACYaAIhFweWEj_x9_IyAKaK7QgAApBQAgDIEB_EQCODoAOWVABzAyAKaK7QgAARBQAgDACqHgCxmwADYiAAMJMAAAAAiCgNAK5MSIUgQggAANZNFwD+hge0iMgEITRISMAACIKAAiVAByYoAo7TcAAAAYCo_MPAC6LgOomhOAAAEQUAT0mBAGQIIQVLYAANWaFx9I2FoJsMgEITQjSkAACIKCWvAFpcBcJgQBgAAA_kbEFKgAB6XAFfE4AAARBQGgDpDQshYBZhQvAPwFwH_mYPAZLwDrTSFqFRAWAAAoB4J4DwARAsVgTlHpQvAMoeAyXgHWmkLUIL7HwABQCwYWHqcEQDiixWADXKF4EbGYloB1ppc9CDai8AUQZEaEgLyHwAAixWBs86WqULwNGMxLQDrTSraEAXQP+LAAhqhSEgYELAD_ioAZ+VAHQx2XBCTrTShqEFlg6sgAAfEglDghYNAC+iheAf+LgJVMwawyXhCTrTSfqEBXQEuRAEodfQpKLAAaLFYAscoXgAuUoXgJbjTQ3SFDAwmEIQoQMzNKLjpHagAxaAJDQOyMABhBkNABnSoAKCHQBTQ7SEAAAATWgh0YADCDQaA2lUi4JKOATv+HQBTRNqERoiAAACYtImPJyRgAMINhoAR+VABxI6AKaKuQiCABEx4HR0HmTgAIoJBoLzHRrsufsJE5B6n8sZgFJoJqkqOABBwSEHBKJicABFBINBeY6NdlwTkHqfyxmAUmgqeSo4OCFgADmkoMcGQTToBsA9LDFwBXQ+GIBSSRCMQ6GAAANhKAH6EEYEYALnlwAPRgljMApJIhGIdDAAAWAqCoGNCACGDUE4+CegzSoAAelwBFQKUPAAAZslBrkuA_EfPwDThcTFfC0D+SxmBpKSdiRlSEwAASgK4mCHRgiaVAAT2arKLgAEAZAHGc11Qg0hEAAABvKBYQg_+RBHoyAAyOAqAAQpcAACc+KUPAAAWBsJQdmPgBaE9IEdGdKF4FhHpRjJeH_SY60kCGgR1SEwAAR2oAwCjfHEZ7kieAYacIQ9BONEkDL5cA5B6p0sZhJSk0FFiVHHshAkgEhjzs0YCCAvj7NJUACbKF4AFaMl4BTTRaEQSilpIdjwSGPJBRJYTVFlwQRyANQZ5QvAag9OOWLwEpSi4mkEaiNDIIlopaS6xgiPiGKjs6NlID92gQReDQV9taAECBeJj3S0A3C4CKClCxkA1AqAAAUgoPb2NrwAIfADzIA0XAAAAAAAAAAAAAD84OBRUDoANTGQARILgBMx8MQCmlWkYACDgUABIyBFNgASIRA0GgBvhcAGdDIApom9CAABEHAASFgiDgimwAJEIgaDQA3wuADOhkAU0TehAAAAEhoEU2ABIREDQaAIkFwBJY+GIBTRNqEAAAASGgRTYAEhEQNBoAM6VABnQyAKaJvQgAAAAc1khsz46AAQg0GguITHzS4AHsCyxmAU08EjBFAFuFwOmUkyizoAFrjC5WWU+CUmOy4AHqKyxmAU2gpGSo8tC5FC8ABHCY3Z0AETSrhBcBOUVli8AHqISxmAU34KFl9GDKRcAFqAHZcdD0dABE0qBoNAF_S4AHpASxmAU0p+jPQIgqABNx4AHDgJgVXJEdM2AAQgF6Gh8BcASaPhiAU0TahDkAwgAEwKrsirOdAAIQPZExX0uAB6issZgFNoKREqOOQgwpGEABCBUKER0zYG_GwCFSCcAGbKgAzcZAFNE1oQ5ASgAvLkhjx0zYBiBB8mAAXlC8AFYGzMArJidCIJDRGDqL2HgkMeOmbAAOYgPh+PgD+RcADMDZmAVkeigRyCAeRXw8BcqOzo2UgD3bBoKEUdABxAZDQG0UwXAQQY1GMgHoJSKCMAAG4KAB6vAji4BgI+xsAAZAkLAACyYABoAAY5WAABsFB6enobGjsuhgBJWAnDgFoNAF2OgAzpUADXy4A_+nCFEIAADAMABIaAnDgGaNAazPgC_5cAD1F5YzAKbQUfJUcAAAAFXACBoAF0aAHKdAESC4Y_gcgzUfDEAppShGAACeJAAKRgAVcAC6NAOEPgCzZcYTiA9NGWMwCm0EjSVH62HAAJsiB0CL1wDhwBULo1DQWCoOQUgO0oXhtANchPwHGOW+2hPEKGAAFsKAHdvBOHAhQfjwGeHoKoERKgAbMbAH+zIRIhAABSCi_ACnMA6rgnDgmohS4IpPs2BCEQi4+M3B+g+ooBTToCMAAFsKABKXAnohy4BaCEfpGi4UfLg2gPdzF1tCo2hMRK9NGAACkFBzhgA9mAK0wTBwFEHg8B_k6AM2FwAIWOH4AQ+00l+hAAEaCgAipQTBw1xoGBHwAAdSjlQAERLGZ8YCopTRxqEAARoKAGmhAEhogseC6AAGFlZfBcAAIi4+kBUUpo2tCAAAB4oRBo8F0JqWuViegEFa3wUuAB7_AyADRSm0EE6BHIAJAAAFaQj3HkEjx7pivgAUE0crU4yFwBdc+AA0UppHFCFoAD3HgdHbVDJ7MEqGgFIGzToAVyVBxAV2WMwrKnFNGFoRyBYAADoJUNAKQNmnQArkqDiArssZhWVOKaMLQjkCwAAt0THYGgPWSKwELmjspICtKF4bQHo7jJeV2mlNAToEcagAZseB0AFhQuw0BHyRWAOT_qUBPyxeUTaO4D1VBkvtkdV2mlNNMIwAOQAAWFEGKG13DB8FlFScCalJPyDQryhfWbSAC8oX2kuk0pobNAjgA5AKQGezI6BfCoAgkVMbFz5yxeHUBU6RPtcdFmmz3ZqafyRo4ABAxIFKSIBy2c6aDnS4clFAWh1BeKsdc8h20Oq7TS0jAkaOAHEyoBArORA12znTSey08pw7KLOQbZQvLbUR6PXdli+2h0URqU2gpVRI4SZEhiUWgACAgUoAkZBjpIBIaCLSEB_82ADikwATdKgAFNHQAH+DIAhwcZCRAf9MngEROikhKQuDqGZYvg9GNsjqu00poc1OCMmUNaGQAgOAKFvIgHEmUwD6Apo2ZsXAG0j7_xlbQ6Apoh9CDCVTKSkBTMiNEtxNAmpSQQeULw0gDG2h1XRvpRVQ7iNDDTVTidaQsU0h4lZeZQwGO1A9DB_1jUCTJFYE1KSCEgZQvJNpAQUcNzKXftJxtpo71AjgACiEg6wmRteHDZx_kpXSOnYRlKh03J6CRShfWTSAvssZm2uk0pooFAjj2JgGoA2WRWCGjiLOOnYBmak9BhJQvrLcGYBxhkvtIFNF5I0My1EADaIFwdAgW0FA8DEWBsR8EJLoA+BYAAQBUAACw2AAAyHF6ilMrUzdiO3YAIOiJBgrhwAAADaCFwZWJg7Gb3AQALRF6EAAB8GAbgYKAcAAAACyYMrEwAAANDoAAD4MAIw6G4GCgHAAAEiD4aJMGViYAAioao+AAA+DASAEioIQTESDBxKgAAAasyLgBiSqMgMoTf8IRVFIAAD4MAZImIkGDiLAiswfgAA1tOXBKQNDjMe9gMgDITSC1VOAAA+DBKAED4CeTESDAf8AgAAayaLi9xcUQ6PeyGQATSDURGAAA+DEWWloFgrhuBmsiQGUKAKQB+ZUAHmy4ACcyEAAB8GAAkNAThwACbixWBOVUlC8MlFSRWDOPZaBdaaQSSoEcAAABsXCkFJEIgmg0BchYrAHKZShefybgwj0zBgvAONNKKAAFIKACSVAEhoSQ6AASIULwDwxcRk_sxFWixmAEONNG8oQAAAIgqdwPhCA0BphYrAHKKyhfIAajIYR6QYwXgBDjTSDu9GAAI0NACZKhQHi7HQA0B3xYrAHJ6yheKYyGEeqGMF4AQ400k2jECEgACzAYpV2BE606AGgOYLFYE5GaULyMhhGjljMAIcaaTARhaADsCIHR0nBSDgrhwCE"
noncomputable def WL11_3 : ℕ := zfNat64 28630 "LSIAAAAAAAAAAAAAAAAAAAAAAAABZ8APMgAJUASFgAAAAAAAAAAAALiYBgIBQEB2g4AAACDwAAAAAAAYCABgIBQEAAAAEAoAAAABQEAAAYCABIfAMBAKAgAAGhQADEuDwAsAAATNGAAAMBAAAAAAAAAAAABnAQGAoCAnYcABoIHgBXS4ACdhwAEBEoAAAwEAC0mAAAAAAAAAAAAAAAAAAAAAAAARIMATsOAtuNABXS4ACMjQAEBEoAANYMAIDRgBMaAAAAAAAAAAAAAJDQCYMAvw4DsgcADnLgAF+HAAHWSgAAAAJIwCAUAtA4Afw0AGdKgAYOXAFNELIQAALMhIYkNAGAgAlCQAAAQCgACUJAAAMDgAADAQCkDABSEgBDCwAAceAESCwAAAAAaBgBIGCoABwJ2HAEbGgAcZcABdRoAA5CUBDIGAABgIAIQcAT42AAhDAAAAbYiAJtQAAHgoAuBgAACpMAALJgvUTAAAA0OgAApBQAN04UgY9QEAACQqBAgEyoAFREwB0AfqEAAFIKAiQYKgAHBsRozCoS5jFoHEey0AGEDB8PVLRNRpaMAAFIKLclBuBgAzBwAlyYAIEdABpCIAbY6AAAKQUQtqCEDAEsDgDBDQAckqADmBkAU0VyhAAa8JgE8GPUBAQMSATSdAD3C4AOYGQBTRXKEAAEIOATwY9QEAF0BbhBcBOeBFwAmY+GIBTRXKEAAEIOLUB91Q3AwHri4D_5sAJ+KgAteXAALpPgAAhBwAA0IAYVAEhoAYLAAAAAAAAAAAAAHCwPhQ0gIE4DQAPiheBOeBFwBKw+_8ZAFNE1oQIQAB0AJDQcAEChhoAWgd5OsEFwAZ0MgCmib0IAAAIgoCgALhLF4FkLG85WQXLwAejkAppLFLIqMAAC8OAA+hAfz4GAoAAAqTB_4eBFEQAAAHQbBsAABgOAGWVBEFBUAA4QqKgGI2CheBBnP3S4P8AQPZhGQIEIo1AAAXhxXm4ACqgFKSICgBUAO_KgLIF+Ml4GkppBNCLAPAAB3wa3uDAAo+dgCkAcrVKF4CUVLc5BaBhGNNvshEvQI7tFYAGDhsAAR0AAiwZKOEIOAAKKkwAdgiAB1ZMAAf4yAAFIAAwoLgoKgAHBTZw_C86lOQByr0oXgWBYrg9loGEps10IigBpAAOwcFwUeoCBNJw_A7kFAB1QpQvAsgMQMICUYsk40IAOJdAVAjCj1AQbUDgABFisBxJ0tUoXgVQKmULwMJpppiNCALoLAEgAAyQnhR6gIFZoksAUgC1SheAC_SheBhLNNDzIUMD6XQlobAzLgAIuFURwhBQAbRIC8BUAIqHgAGIACWyoACHo0C4yL0s7NhAaqAYCAEoHTCIAZoPAAJQAJwGQAAQg4pbUlASEXIYkG4GBMFAN8mAAACJUACGLgAYgAAAfBgAWkQ3AwJgoB+DwEthIAAWTAAAAAuVgAAPgwAEgoIgYEwUAjxYBGgUAAkIgABoZAAAUNgAABuBgTBQCPFgEaBQAh0qADUyEAG0UEhAAB8FgANxRBg0Bg4AAJgUAV4LgAsCsQQA4nTEYLZDwABEg0BA4ItjwGpA4AwOWLwAXqeQwA4iGUCOBpARqLAzKytCQg3AwJgoBLjwBYzYADcVAAABrYuBcrAAAfBgAQqQpAwALxYD1BcB_06RcXACJBYAAEehAAAfBgAVlwegwALxYAgJYvD+NROXtlwAALQCa6UAAB8GAGQY4wcDlRoAIRQvAnMPS4ABKAGTR4dCUVyBgAAc4OCo50aBoBIKF4FCcwHLgBUg0JQAjq6koABB4UAEwUEMhoAWgZbOkpFwAiQWAABHoQABGgoABIBoD1BdmQOlMlE5RcXABzhoAAEahAAAuCgcEWr4LAALjLF5TXHHjucqFLgCSgAOFMmkJQAALgoE7FgDItCqpMLFY_ZSJ0wa5z_suAF5EwAATNGAAA6FAAbZkaFgFQFwAtCaYUunSqi4AFQMIwABiEdCAABcFAEVUgtEldkxWBuAAPtZ_aFCfNgBoQ8AABsQgAAXBRh4ZvdidFRcRIBaJsZgQxYrDqYZz3QuABYCwlAAOhfQgACNBQAAhY1BIvokAtAEMWK6qdemMU5+0XAAJQAqcPAhQgAKgABAaFgSKeIFwelZKF4olgzgpqpxMM5gQXLwAeA0JQADlJQtqpNAAtkSSWIFwdcXKwBTVbj8ZiNYlwAGRT_hmABDZFGPLOmoATmJE7NnZyHnY3TnNqAIVIUQYAGg0ANQ6AAYlQAFKFgAA2IQAAHwYAmBgTBQBfFgCqGwABIYFI8AAnoYAAFBkAAARINAQOAYA0Amk6AC6FwAB0AsqbBnkYAAggAhSgCSMABOgBgYA6DQAAAAAAAFCIAACAcABIaHUDgzoPAazPgAwJcAGlB4AmpKxKAAAACTUSCQsA4EVDwEKzoAPUXAA+QaAAJihAWQBlCwA8CwAATjoCaATKgAJ8NAEiIABghWOLgAAARaQgJyFpwMXQ8LgAk8PHkiIJqDERrHFwABbgElSABNIgB2nQAhwuIiA1csZg9D_6EHfQrHFwAACqCwGzNHYA5LiFhy4KoDTh42X4ZiqTUVIjWOLgAC5Jw9HsSmkHBxAeANkdNwC9BcAACBouZQAiuhHWkjMAKcFgdnTuBATkASkQ3AwJgoA7CQBWjYAIEdABpCIAAAAB8GIUAElxEgwALxYFwDCUSoAcrILgACIg9moDxSAAA+DARIMTYOAASqGKF4E5vQXAzAi_8rGrBoAugk5GAAA+DAAQLiJBpxjQKQBaBQvAnPfy4_8ZBVC0DhsEIXZqKhRgAAPgwGgBDOAJFw3AwFpAMlJMgALJUAAkho+gNAAAAB8GAiQYADpAnAfQULwJM5VMXLzSyEASVKYGQYkEuzUmyjAAAfBgltyMAJBwRAwAshYDXhcJ6KicrCLgigC0GgAA_IwAAAJiuAG1Q3Ax9BKhMAp4qACJEwAfMGgACgHQAAEAYAQDMNwMYo2CyAC0DCR9zIuB6AGocNhRqppBWaEAABAGA0AfsxEg05RoLIALQB6PksXjRD4KoRwcNhRDSOSp6MABBwKA0AJDQGXKwgCID_xcB3c6aMXAAUYaAACChAAAAOyYLxI_ZMCOkIAAHydB8LiegAB1+2bAwlIEpBwAAFImRoOFI5ZmqahAXSLgJyuAuJ6ABBjJ1moU9OBhREAAA8JgCQ0LKTAj5CAukXAf_OlwFxPQAA6zUGIpAAAAZiZGhY3JIrDL_1CAMsXLwJy40uJ7KQAgxk6zUQYnSwAEJESMHQWkTCpZIQgoMY0BZAAuTAACCIAAAAFisABRwyBkZmQD2TCeFGnHgMYiSwLsFwE5XEXE9AD6CEKTrNQYSkAACIKAAMzABFYAGpAB0IAKXAAyoAYTADhoAELAARIACHAAAAAAAAAAAADRMwnhWADYACAGwjoAAAA6gAxWFuCQAAaFhoQYcnsmBziEAMQKGIVei484pAB0A4gxhGALGDQAmMVAvJCAGMqB4LsIV3i4KIB0xg+AcQdkjAAAlDgAdqTlhUGXJKEAMa_owfVHEb8yxeCEAShJpJlC+eQzpqMABBwSHlT5SRIrBOp5DANwWM66dTCBlKF4AKyIDYBxIJehGAAg0JByFwOIzTFCcEXnkMylE08WMzKSQgqbKF4TQFoZDCHEgo6MtHo3vDoAAM6HEbGiZGE9MUzALTKSTWiEjkoXgApDJlA030Pg4aBHOJlqoGjxYHTs7FQIEpB2FC+Mg4gAAdESCKgCgMl4Un_zMCd0IAAHYUBnhUA2TBuAMQ2j6kLuBcACxxg+Acf_oRYZGYQHAAAAXDknHqcFQDEAhRYzKbtG8gghC0_knAHcIDZRA4kEu8jC0CqAEvCV4CoBiCmEo7BYzLSJ4QhaADvxg2BbQ+YjFUyh1pIuYaJeduQAOrAJkIAOHAAAAAAAAAAABBwKg4fBZAJiUIMig9GLgAjSMHwDjQTESMABBwKA2LDaOdAEikRIMAYUiGKU6AAkkNE2XE9kYAOgE1EFowAAUgoQ8OXAANERINKcSBlRUnAiCkGJV_sdJSLl4wQyAAABCIwyoKAAACQsD4NTkSBUBUnCyCksJV1AdPgLl4AdeHiShNQzqMAAAbEJBdEmCyR8KF5YSqRsLgAKANIehgAB+hAABPCgAJDSnIkCoCpOFkFJYSrqA6fEXLwA7APElCalakoAAAAkNKciQKgKk4WQUlhKuoDp8RcvADrw8SUJqVqSgAADwBJXBmFCGKgMQTAHAKgAXRUACBAAFUfAAAiCgClFQZhS4i4AJJPDIzRUEkWyTOgACiASkWwOUgAARBQCgN9CAP1T+AsBjiYBHhUFUB3FV9h4oIAT0Atx8AACIKAIWXAKvkwSQCxYrKqVZzrAuI78JCACegM6UimDQAABWy84CIBf5MWkSgWlVBARcR2hKEAE9AV8pCUCgCGy4Af5cAl+TBJCKFitTRsPSrOcEFxHZRIQAT0BUikAARoaA8BRawIwyJrGg54ZAa6Lgz_9WBZpUR0AFJPQCoKxRjIAAAnZd1BkC8aBcxUnCSCkm1Uq9OOidFy8jtBAApPQ_gPWnTlGFQAABXi7mDJmgQeBdRUnCSCkmlUq9YOkAFy8CpBAAoPSUlC04BBEjAAVJIrB0pOx0xJQADvB99IAuXACh4BgL_ykF1DIBRA8AGUHgAAAAAAEQUEoABakCBIOnpyYlItABCxWWEqnfC4eIqXwAyBpAL2hAAHyJgRcEgkpkpaAGFitJBFYSqcYL"
noncomputable def WL11s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL11_0) (dpk j 1 WL11_1)
noncomputable def WL11s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL11_2) (dpk j 3 WL11_3)
noncomputable def WL11s0_4 (j : ℕ) : ℕ := dsel j 2 (WL11s0_2 j) (WL11s2_4 j)
noncomputable def WL11 (j : ℕ) : ℕ := (WL11s0_4 j)
noncomputable def WD11 : ℕ → ℕ := rdw WL11
noncomputable def ready11_cuts0 : List (ℕ × St × ℕ) := []

theorem ready11_cuts0_ok : CutsOk ready11_cuts0 := cutsOk_nil

noncomputable def ready11_0_state : St := ⟨26112, 158173, 28545, 39936, 52016, 90763, 29666, 44151, 53248, 110171, 52016, 108939, 28545, 85468, 26112, 285696, 54657, 186718, 106673, 238734, 136339, 268400, 189587, 321648, 241603, 430587, 270148, 459132, 296260, 688731, 80561, 119308, 110227, 148974, 163475, 231789, 215491, 283805, 244036, 312350, 270148, 598046, 81682, 120429, 134930, 191853, 186946, 243869, 215491, 272414, 241603, 558110, 82914, 139837, 134930, 191853, 163475, 220398, 189587, 506094, 105264, 162187, 133809, 190732, 159921, 476428, 80561, 137484, 106673, 423180, 54657, 371164, 0⟩

theorem ready11_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD11 ready11_cuts0 108 161) ready11_0_state = 41627 := by decide +kernel
#print axioms ready11_0_cursor

theorem ready11_0_covered : Covered (toCl ready11_0_state) :=
  ready_cover_cursor WD11 ready11_cuts0 ready11_cuts0_ok 108 161 41627 ready11_0_state ready11_0_cursor (by decide)
#print axioms ready11_0_covered

noncomputable def ready11_cuts1 : List (ℕ × St × ℕ) := (161, ready11_0_state, 41627) :: ready11_cuts0

theorem ready11_cuts1_ok : CutsOk ready11_cuts1 := cutsOk_cons ready11_0_covered ready11_cuts0_ok
#print axioms ready11_cuts1_ok

noncomputable def ready11_1_state : St := ⟨26112, 221920, 28545, 39936, 52016, 90763, 29666, 44151, 53248, 122304, 52016, 165862, 28545, 96880, 26112, 285696, 54657, 261856, 106673, 341228, 136339, 370894, 189587, 493198, 241603, 551257, 270148, 579802, 296260, 688731, 80561, 119308, 110227, 148974, 163475, 271278, 215491, 329337, 244036, 357882, 270148, 643578, 81682, 120429, 134930, 242733, 186946, 300792, 215491, 329337, 241603, 615033, 82914, 166455, 134930, 248776, 163475, 277321, 189587, 563017, 105264, 219110, 133809, 247655, 159921, 533351, 80561, 194407, 106673, 480103, 54657, 382576, 0⟩

theorem ready11_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD11 ready11_cuts1 110 145) ready11_1_state = 77277 := by decide +kernel
#print axioms ready11_1_cursor

theorem ready11_1_covered : Covered (toCl ready11_1_state) :=
  ready_cover_cursor WD11 ready11_cuts1 ready11_cuts1_ok 110 145 77277 ready11_1_state ready11_1_cursor (by decide)
#print axioms ready11_1_covered

noncomputable def ready11_cuts2 : List (ℕ × St × ℕ) := (145, ready11_1_state, 77277) :: ready11_cuts1

theorem ready11_cuts2_ok : CutsOk ready11_cuts2 := cutsOk_cons ready11_1_covered ready11_cuts1_ok
#print axioms ready11_cuts2_ok

noncomputable def ready11_2_state : St := ⟨26112, 221920, 28545, 39936, 52016, 129510, 29666, 44151, 53248, 122304, 52016, 199982, 28545, 96880, 26112, 285696, 54657, 261856, 106673, 379975, 136339, 409641, 189587, 531945, 241603, 596768, 270148, 662619, 296260, 688731, 80561, 158055, 110227, 187721, 163475, 310025, 215491, 374848, 244036, 471728, 270148, 662619, 81682, 159176, 134930, 281480, 186946, 334912, 215491, 431792, 241603, 634074, 82914, 166455, 134930, 282896, 163475, 379776, 189587, 582058, 105264, 253230, 133809, 350110, 159921, 552392, 80561, 296862, 106673, 499144, 54657, 382576, 0⟩

theorem ready11_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD11 ready11_cuts2 112 129) ready11_2_state = 113479 := by decide +kernel
#print axioms ready11_2_cursor

theorem ready11_2_covered : Covered (toCl ready11_2_state) :=
  ready_cover_cursor WD11 ready11_cuts2 ready11_cuts2_ok 112 129 113479 ready11_2_state ready11_2_cursor (by decide)
#print axioms ready11_2_covered

noncomputable def ready11_cuts3 : List (ℕ × St × ℕ) := (129, ready11_2_state, 113479) :: ready11_cuts2

theorem ready11_cuts3_ok : CutsOk ready11_cuts3 := cutsOk_cons ready11_2_covered ready11_cuts2_ok
#print axioms ready11_cuts3_ok

theorem ready11_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD11 ready11_cuts3 128 1) (ofCl (RC 0 0 1 0 1 1 0 0) 0) = 126943 := by decide +kernel
#print axioms ready11_parent_cursor

theorem rc11 : Covered (RC 0 0 1 0 1 1 0 0) :=
  rcOfC WD11 ready11_cuts3 ready11_cuts3_ok 126943 ready11_parent_cursor (by decide)
#print axioms rc11
noncomputable def WL12_0 : ℕ := zfNat64 33247 "BUslUAkkpdcbHgjoAAjQUAoUqxoeLIN2LlYI5o3mTMGcpB6acLKw9CqWSqUXUk01JIEQqVjUGjkAAjQUFIfH39eTjsyCc9IBaVDcDEU_4nGAIgFKEQBIY2AAAABYrAABuBgELLwC0qG4GFIAOOg0zEDJDcKcQgAAAAWKwAAbgYDQTJVDcDBAHgg2TAPhJgD_x8ABNAAggdAABuBgEQlw3AwJTPIfhSoKs1xyVAcZBLQEF+wTA9CiBEBv8VIAANwMAp_cgCFeIXVQ3AwEGiICNhEADkAAAC7xsAAG4GAAkJDcDASkvmhcgMt+lQGkHoLISgi0pBbQDwIQAAAAGqAJDQBjxUK1Qht5UBpOgHwAOGUgtoB5kIAAAdAJkVKy+aEnssZykDKMQPHYEkCiBtaSnSw+8jAAAuCg5wmHoF+KlYLUMl8pAyhyjx2NoZNZFA2KZTInPxtpIEUACDgUAXCQ9AvhUrBahkvlIGUOUeOwgDRnIoGvTKYfTbSQCagRwAEbDwHjHD8C+FSsIJ4jJfKSmmUNgeOwykUCKplMPptASnS1OKQRbHFQAASKNAmOm5RJqdShWEGWgQKlZTTLaBOHIYSKRSmh5NJxEiOC7EaGLls5lWcikcgxAL1HBQJFSNgBYRAHAIgBaJcADVEIAA8RkAAbQBT1waESKAWHoFcLlYD8MmcpA0g9Ak0iTjKysBlpoA9QgAqABAwmAIHoOOKlYQRsGS+UgZczJw5MMM1BDaidPD6ZSKBskaGTo6DaWf9LQoAkVgBeMiYDh+DkipWEEIhkvlIGXNicOQoIEVTJ4dTKRQGAjQ4bVTaWSqMcKF4pqPDUpJRyhXNQIRkvlJJDL+pOHJdCDQQLqRPHI+ez9zNjoPaE4oMNpJlJtRDHChsKR0ZAbk16Y0NQkikG7GC9QhUrA0k0chZIIDoTp4GEsiBHANyNDCgjUFJDB8HZedGQ8AoMwXBQRDz9kqAYjLKFYGkJMeOwJIFELbtlOCAaEAABEGAPavc4TUkoNIyoBiukqA0g9AvSUEWlILaAh5CAAAiDAHaXgANUpJQdIlQTGf5UBpCuHjsCSAWlSnWIWLb_1OB9qEAABEGAQCvIKNUkoK5C5WExRWULwNIOQJNFDDplOcy020k_CkCZQI4AEHAoqQ9DDQ8dmYUAJMQZpg3AUhpQocNxSBpKUHD8CKHxCoLb71OCFaEAAG4GAAkJAiDIdMG4CkNKDDhuKQNJG44fgRQ7AVBbffpwPfQgAAAzTBuACixWGk9xw3FIGkTMeOwIoCkLbTWHqwJFAj0SFgAACZIQAqqAUeMFRYSLysqA2k5D4CCAnCqXhMGkig6NCAABEHAFKYNwFIARqzjUs5QrEjJxpD3HjsCKApA06aSgEegRwGoFvjYHlQRszAJpIrLL_A2FITTSC+PHYeRqIoCk+2rGkBKZLAigAHyNgA6mRbBo2AUhpBMaOw8lCsDSD0CKFBCoLbutOBCaEAAKIyA8PAAosZmYNwA+UKw0jUUhM040iJDx2b4aqKApl4TBtpINLQi6gRABMQFJZehGwESRWE2yihDx2AEkIJIpl4TKuWjSRQP8jQw2lGeh2UiJuXsQOghACKoAQ2KyKQ6gFRI8pLNo1tKXnySD4JoAHWohRVCAABMFAASRiIFUB2VBDoiAbmPAA5AAAAvwbAAAmCgIIAjZmAryRWWUahNJFYs9Ksot48dhpIpkxKKK7V6qmkkhdVgigJ0ViSAAgAHeCZ1QIaEAAd+mTAbT_qkkQ+AIQpQACiToAAE4cBLRkzAZKZTDLNROlCsLKACPHY9CKFNkynRQ08qSghShAAAnDgAsjTNpkCBFSmGFnx1KQNI4I8dlEIocSUgtoCd0IBIYaTgC9UCHLR7yU25Snk0wsCNm4pBaZZsJw5JsCmK_QQkk2ulH_jJrJINiRoZNopSQOuYNwdACAsgqJHP+WMwKJVMo1FILbKDkolKaiKV0Sj7JlMqppKclTwJCiR_5h15AAnRFHIZLwprQlawqYNm4pJjFxlconDkMmnwSSaB1cvlhADQhQxKMF84lGegISbAKDICwKQBjSoAZEfAA05S_YzFtALafAAAnDgAJIwa5g3AohpsodADKFYGkoccPwIoFaVKYW33KcEK0IAANwkB8fHgnXSKIyHoKQQgEMjwBTQAFYfAAAuNgAARBxchYqC2IIRLxJNgGNGC8MI6FqvKT9qFaQekkGk0LGG0JDrRQ5EQuhSAABqFADSVh+DZmU0UiiWTWNS6lCsoJhEsHD8glWgkUkiFXMcxtppJIJ1QI4AAWQoAfpkGICkUj2YM41JqUKzSabKbROHIpLpFAIRQnDiiFsx00kh2UYAAFIUASKyr0iqahAAHfpkwf+biogBPAyAATSdAABSCgDPIEZUyheEVEClPJJhGpQShWUSy_6ThyohWphBCSMS6cTCQQHAjQx6ZSaAQ40Zg6AEZqlSBGLQVymUwwjVchUrCcpBlaUnDkuhFALRwzMoYQDnoEf+YcACBAhFeULyih6Tp9Jrs1EKUKxCKU8svak4c00P_nRJGNVDDcxCAfaBDKJZKtBBnqJLIGdGwupO6cEWWWsGQ5BJBEAd8eAH9lwAf8XgAFaGQAAEQYqQPDrm8TC0D_EQDHSYAHoABaIgAAXGwAAEQYuzMpHZlBAEBcNwMBqgqAY89KgNJwI+Aig+wqAsgDyQgAA3AxG39KAAz4PrTAMBEEKgBGPAGxHgDUB8ABFAAQqXAAAGAijtwRdfAMBDgGgN0PAHOHgCLRsABFAAA0VAAAGAivJY+BAALEETXgz1cCrogGAgAJEwOQDBMAfoNiagTkAByZsAAAYCAG6nAMBKvGD5_4ygsULwiy1iJQvA2gTUOgRpGhhRmoExEYAAAwEA7RSAYCCpKaMlRPZqvAuViBEu2b6iEpKIDJRJYSbDVQfGhAAAGAgAJBQDASbxoJ1FQRSrpUH_GYmedAAnIiCagFGQgAAACRkSONBMAqCKUvKg_4zEzzoAE5EQTUAoyEAARoGA_MaDPRUEU4aVFxMpOSLaUBDEiCagGAQgACNAwFXjB8BSEWaRckcoVgUXDfYQclJnIe3IgozUQhhZGAAI0DAASYgoFccqNAykmAX6TAH9DoIIBhCagNDOgABQAwML0B42MZivgqTh0ii01JIrRejW2wk0clRovGDYgipTKZUZqIQmqKRo4ADFwYhY8PACRkASFj4xoOvFQRVhl0pLiZQHp87KSBAciCagEMQgAAFIV+MHwFJRZOFySShWHEygHTh2kQKpIFvSIqM1_kRAs1CFuEQAAecPGyYt6Kk4RRaR8kVltsJNHJxgqkzmWgJOmEESMqM1EIAuSo4xhKcgABBsM9GD4DhJFZRYBFwpLaYRlpo7KS9c6ACJAjKjNRCA10COVwSLvBE4A6gASGkDRoBSEWEJc6IqVlxMoaQ6dlJAj2RBNQDVoQAAAIeOMHwYu1JFYRRaR0kVhtMIY0oclJnICeIkYUZqIQ6GjE8Fr3lQAZSBABvEdWMHwYulJFfizYii0u5IrCxuG+wg5KTOZaeTIgozUQhgtGbYVTkACbAQ+IeNkxc0VJwii0f5IrLbYSaN04djmkzmWiECJGVGaiEFgJUcYgobAAAfZgNOuAJBwRB07RoMjFR_5GL3FQBOQgi0DCA1EIOPPgAAANBkU6MHwFJRWnFzoipWAYct9hByVHrCUDZ1CuE1ANWhCUAGgGzMAAhkSiSKwFJRUQFxIipWW0whkzh2UWcgT9UrlWexECuoQAtBoAAkdkCc6Q8bKoxkoRQClC9MpIrDaYT2J0sc2EokUIrSEymbSiNRCAp0COAVUMl5+E6EfUsGFAgscHoc4UYPgxFIRXEFwpDaYfLpTsDpuEkggMQokU+geZGhgUQPCQnMAFEcLIc4UYPgxRCSKwii0FJQrDbYYdJw5CTOQUcQJwojUSkE9ujAWQAAaCnCjB8GKuSRWEUWipJFYbTCTVInjkJM5AzxgvCiMSqAYUCOADRqALwIDGrkvRoMWFR_1GL+FQB_86KDLQMITUQg3c+GQFAAAHGKgnkKGEWyhWUWWykPM5b6yFAPn5LYqAA0_YPApkUpEeDpiAYUagBEiw3IwfP_GSASRWEW0BcKQymELmaOwalUPTKRQhYU1kehjVGCggpADgLG6lSBODiSRWEWVxcKQ2mGkjtNHYUSiElUChPCjWR6D2kaGGWggFMUK4AYGolUgTl0FIRSeFwpDbsJiG6lTUqIAjFKef3Uq6ArBGhjEy0EBZCZTDIzyGSgmRgxktRItBC5JJIrKJtMNJYsdNwogSSbRSjWctmwA4RoYtMrLEaGAUTFHZulhQKBNQ0oT_RFQSkopv0qPZuVlPjnQAMsIgmoBskIGoBANIAkDNIg4BowfAYxYrCLLUIFSsuJlKdnQOZyAVRiMRCB0lYCNBsAB4C4ViuRg_IQoJIrKLf4uFJ1tphBzJaTOQ+Aj6BDoNRHMhA+qBHAAnhsaQAJjbUD2dxoEZlCv+6NRQlBUrPOsnIBzKZYpQEhjJNQFaIQAAJ0qMmFICgKlZRTj5UeaIuV32YnNBnID1yKggJAKpKwHQAAbspnYEAA6QfiSCYKBQLAhYiASIRAEzjIAJKEQACeDIAAwgDAFgmCk0jQMRSEX5pcaoqVlxMpTs6Br+86AAYiEDoKwdZSBRAiAEABVxGuWBEGq0LA7keAdKPAAtAAmgASLLgAKWiwAAUYA2TAERYAAAAAAAAAAAASeuFIKGoXQKizCMVUKgCcgA1BAfgASxPiagAAawKFIKh2aNwNeSKzBTZzBSXEyhWTh+UkACagEcVgchECUScABIyANlQAAAAAAAAAAAAzIkIIUTZGjk9HJMcpChN9pQrDaXSPCZLB7KQewjQwex0QlGa0FRiEgNOMV_MlAM6kgAMUCIMCwuB9BkA5IiAJ6AAABJQ2AAuuZAA+kgOBnPmQTUGMVANJ7JOABvacAAZM6CyAJCOgBEGAaYNwDEdNw2lJDaVUeFQVG1qUFJAkgCIQoYWTjWQ6afAGupho7xsg46bhFII3k6eG0wmEKrRvCiBNpoUSDS8mAiyFDJqaaiTVLyE_AGHVBX5IJw4FhcEDEYBv6UAf+bgA4ilAAMWNgAAAChkGoeQ2PgdN_vkxFIKdk6eG0wmE2lNC76UmBQnnWmkWUhkpCJqZSyHpEoUFpRszAAh03CLhBCZInTw2mEwtgbtYahOlhSSaXSegEPQIYCjh_NTLTQbolRwpASs08WbFkVMfOxzQQSI1RLaFq2jeTBTgCagTRaEBQSa2kB2aJLJ0A_GQazUbh0Rk0djEijbUymMTbNJiDaU0N6pRRPtNIspCeSETUylkPSJQHkSKxbGzMFhmjumkUWSmU6qAbQC2qUA9Inm0AANnkMkzUygDqSo5UoMCggZomJbywIg15yoLPGQDdEIA_AzAARQAHwmQAH+jIGwcJhZmLlQENBRuZFx2bQSmVByVMAwECYWAFhEAvkeACXFjMABqABFoyAAAMBBHcm5+Tk9iAh9KTm4a"
noncomputable def WL12_1 : ℕ := zfNat64 33246 "yVHhcrLLSQ45g3K1s1Xk4GoZFGP1RAIoFmqguseBkAwKwARQvBjRcrJTJWzFysstJB8fDXA4Uwxk1k0GolFp9KpRAViNHCfp8ABbI4jHGSK_lnwBQuV0GUyUihcrOphpI6MwbnwWImg1DJZvJVKINeRo4T9PgAuwCDXAJxp_IuA4BcrJT_kmlWULyy0kL8YNwBUhcGaaFUCQKEUQsgENHgF0YNuEKk4OrKFZKZKC4uVhhpIzw2Z2xUgBiFa6FEAsSNDOtdLIFsR4nRkpQZubAGAhiFQE3JgCWkwaCQgAByDQAAgnQAAbgYhTk3wQbgYGhhM8dH6h6GgABgWADnFwAAFA+AADcDEaAHSoiQYETmR4DYJKgI2AATkwFEIIApNoKGUgPEFAAVgrPeAWlQDAR9A_Q8AhIeAALCQAAAAAAAYCASizALSoBgIUhN4yAAOPAAFhIAAAAFisAAAYCAAOpAEjIA2VAAAAAAAAAAAAMBARpXiJBnnkicJoBhPQYNwBWxEAEFRYACAiUAAIkGAaYvESDBAIE4OQC7pwyCCAABcDIAAmqMAAIkGAbGvDcDCUHI_C4C6Do6A2m+noAC4GQAAjUIAANwMAp9eA0FQ3A3XCYAC6AsmDuR8AACkBiAdhWAADcDAODwt6hhoAjLr1DCYaShWUlSpQrLSRUdFysACKNAABlAJUpQADFQoACQsIQVdYqD4ZUGki7HKgAH40DZEIAAAGSEAAAvAkKTmSUzoqVhpIqaC5WAtACiIQEeLgABHoQABGgoF4EhIkisJIpDShlAjk2LlYVExobBDRCGoB5ADgowABGgoNwATXAEhoKTGKUKS0kUUxcrAAgjQB9weA8OzAFDQgAAABlcFwkFMkVhJFJvxk3kUXRcrAAfDQYQ+8LAGEBVSMAA5omAATZABK4FMkVhJFJpNk2ZyKLouVgAPhoMIf2FgPphAVsjWMUgAAAgMQA2uAjJFYSRSAIbM5FJsXKwAHw0AFEYY_IFgAGJStGoJdJoAkiRWDquCUKRhqUNMoVnm0kWUgAPxoArMPATjZgBmoRltGAAP2SpZpSRWaRtJQpPJpAMjQw1FysAB+NAC0KgAFckYOK7GK+BSQeJvBAWjEzUVBKQ288Rt+lQAMd8DQATg0dkUADRIQAALhIAXzEFIAVIlq5KFYaSKqYuVgAGQvyELQ6KFCIr2HoCSN_RgAIOCwCnZFytiJIrMIKTyjZk10ESBUrAAgjTh1IAAwwXDKADKEaVx0AABrFytYRUnMITskVnkyq4QocpAAgjQT0QhSFQwgDE5EjHX_q8ADFFDZO4JSAjoDftiiDsWFQbPKg0_+RpMlQAD4mAmkUAHuIQAABGgoq6mbAJpUCANsAqDbJUG0i6jKgAGBMB5DoVAKIA9lYAANwMAShCCC1QHAwB4CY_81B_yYABERBpAAkoCTjoAANwMANwuAJByNBRUSYE2lQZRO5UAA0JgGgADH_osBPlYAAAKgXLsJHqKgPoXKw2kU2xcrAA+FQDRqMQAYxUHHKQABGgoDIKiFEwExJgECFQAbQGgPwQgGP+xYC5HwABGgoAsxdWxc+woXhJTcVKzgTZnIspJqUEwCZTAaNRiIQBjFQRMnTwACNBQDgpDRCiYEkFQDECoAAGzUYmjT4Bj_8WAuh8AARoKADNxA7i55gIVB78qDKReelQAEBSAaAAMYqBPlYAAjQUAWYuBxIns4LFZBJLhShWUTKcBAjykajkkm2SiqA39BsMRCAMYqCJk6eAARoKI+HwTMXMSUtwQAkNBSUwShSGUZyJDAMXKwAShZ_wjFvh4nhg3DSVQIOIwAAFFHQpHwJQxShWGUgykAEoWfaIxvQeJ4YNw0lUCWSMAAYI6Cih48ZIrOKJQpDKQRWFSsAEoVQDpOjBuWko6WRgFegRyokEBcY0DYAtMgmSRXJSSKZqZSCQAqVghASl0ZyxXIoHVsGDcwmkoi2RJc1JIHEqOAAFQsZgCD4gRxE0uxKglkVH_nIigVAAsyYAAB6ACxWAAB6NAAHlgpAbpQhShWMTTQVuFSsAEoWf9oQqseJ4YNy01EB2iMvYajoAAA7MgryRWEkCpIrDKQRWFSsAEoDhYrkUDrKDBuGkokUJKukaOhaCAG6LidKRslw+dtyKk9FJKuyRXOTKQSjFSskwRAtEpdKpBA6R40ZnE000ihJNegRwAIxEQAVhZRK6SKwFJIRk10F0RUrABLR1aLJBUI_2PE8MG5xtNRAx8jEEugAE2HztkpIrAvpIrDKQRClCsAMUSI6yAHRsGjM4gAYhGhlU62EP0LQhJsdqR3AqCIe8oViU0w5QI8pAH1ExZAI8GwVUBA6EAAC0KAJAjOgtX2KgZuUKyiaQBI0OUgE3iYFtFC0RsASqgO_QgAAWhRHgV5WAI4yZxV9lGDMFSsomUi7nKgAMoAgSCFUBk6EAAFUKAAFvBAcaripjh0AVUS5QMgD_x0AFsjIAAGx0AAAYCAhdrG4UoT_XHopD7yMAAAAFYjYABixkAAAYCAKRkvScVJ6KDyTp9RMv0EIU2kCinEAOjKMG9d8g1AcUp4GlEYAOvFwBaSImTg9pOnlEykFIZQrSAwZz3mjsq1UinUogKgaRjEsmEk_sQgRegRyzQQBRQsDorahd3ZoKDOgaK2G4GpIVB6UqDKRZwlQBBLIAKaTKYAAakIAANwMVZOBI9IbgauhUE3io_4zCAioA4gAAFFgwwPAAAAbgYBuycNwM1omADSSX5FQA9_kRBFAmAAACgfAABuBgE5KQCIuG4GBpyRH4OXBpLO1SoDSPQAAMIACxWAADcDAM1UiJBgqEU7xkvDTWSxFysDqQRxDRcKJJACyipQnlBMqVE6WAAIkGCe3NS6A4GJIrFhJQpDKQTVFSsuJdCSGzcsQZAASYHgAAACoMCNBQpHtJQJSRWGUglAKlZcShrF8moMQAClDwAM0YOhDAAAUilEoDpQrDKQTVFSsuJdCSGzcAAHcDwAZ05iQkAAAUgK8kVjdmjOQVNlCsuNZBqFqcgGmFCcDaAnRGNAPAAAANrplEkSkisBSGW+iE6IqVhxLIKEwbgHwEYSgAUWRjKACZRIHQBpPBOFP6OgzSVBlLOlR_laEpbg2AmhNAACLIQAAJwoAAhsUAUfskVhJUOSKwykFyhUrLiUFYvk1A_7BHECGgHNRgABQBRSz4F_Kg2CtvFQSksvtELx5UHEsnYjoDIMS6AAZIRKwAANgoAzZcQUTAIgqVllqojSkOJdOzHQGSiABRHIMiVicDQAABmy4gomARBUrLLVRGlIcS6dmOgMlEACiOQZErE4GgAAD3ly7ZMAY4bkkUllMGgR4AFSsOJdCNGjsDJRHIJXxkwURyGQyydPAAg4LAD2MgNpcai3IglIYcdI35SoOJdOyHQFEACiOQQkrAAAuEgDSl6TKzFSIJSVTDFRG_KVBxLp2Y6GIACUKI5ApysAAC4SCmpqZslA9SRWBsSRWGUgikuNZAgHTcMIAHRxGSzcqqAyZGJIXAAABlF_tTkukisGclCsNJPUKUh1LoGw6bgBGAi_wrAAV1CHJ1AAHQATxBYkisA+kisMoCEJ+KQ41kmoYRWJE8oJRRxGYbjVSiFCUY5UXAACnBAAisAEFjCyRWElV5IrDKiBCfikWnGsk1DCDJMllBbOOIy41UokUUmCSo4YQAApU0VJ6CSX6FSegmWegjJFY6Hbm9Zy3lkizUrpJHNBEIcaqbVMpkUUnSSo5HRmAih0AAeLb0kR19FCekkl2RUnIJlnovyRWdbiWdeIw1C6SQipQHEYcSyUQRAlR5iYQAB0AaGQAQWC8JFYCZJFY5MsCEIUlxLIhQ4bjymS+TSiiG8nEskUGrowYQAAAILNOQIxLPfOJUlpJl0YhP5JFZRNpZBqaS6A9JAQHzbbSyMhSDxKMGEACpQbsBHaQSmWKAKrofAH_04S_9MgC9SEAH_BoABCh0AA6IeAKRXDcFLCKgQQlAHgJgC2hsAAZAASMdAAAADDYAkZABy4AQJAAAAAAAAAAAAPTbwAGWBAGGoaOPgL7FQAAAKKGAABGXAAAqNgAFrwAFaADpwAY6AGGwBAqAFiwAAAAAAAAAAAAFp8AAAAAAAAAAAAGzLDcFHoOgU4nAJoNgC6yEAAZAAWCdASQAKMHvqnwHDUKYaSH5o7DbtpWCCAEGPhCABGlCDr_5eAuklA+RtPRrSUSxOnhlpoCDZuG2ojekKGAD2QhtKIDsEaGHX_C5j5wtAUhOlgBfRhBCqJVNDLn5SfwaOw0lUTEjQ0CXQIolDjXRaAYegR__kQYQLKJQPGOHyknD8cgXUyeRTKUTcHDcsmkohBACKagYTlkAFJu0CPVTnDEA8JInlmO4sDE3oAMPgEJcAAAAAAAAAAAIeHjQELG5unAQBnCEwXxKgylNSo_43E0h0NB5AigUGKIQACEhIAIUAA6QB8qBAG9oVBZkqDKTpKi4l0ZgbNwPIEQCSBlKArAhISAArKx2bwbm5v78dASaUINqhuBgTBQTuKgADb_48rgAEkAEhg0+AADcDAAHTgBh8AhLgAAAAAAAAAAAAB04AMfABjoAcXAExoAAAAAAAAAAAATdOAGHwA8uAJDQBRx0AADEAAAAAAAAvCcAyPgCQ0AmIbBJQAYn7PjbRkAASkBwoQAAActOE8WPMHAi42ZhJQAYpKPgA5EhASkLtUEYAAJ4sATdOAWnwPhyBBRx0AADEAAAACCdAAAfDgBbpwI8uOTNgmIbAAAxA4gFdi42kpP9sQB1IrEXAABoaOzo7bmoKYTiJBgFqGjMP+k06jIAOgMTKVSy+5w7glIJNJpv9GAAESDBeAXyoAkJDcDHmMgR0XKwmLSC5WBtAVHkMIKAAHQIcpAAAAGyoAkNAqlwHsKgESlQG0iwfAAAAAsVgAAA4xUDoMCHjBuv4uXg1mLpyheW22pUVqY9LDBSLRY6IEIpNG7pk8ABO4UAAEuAYlQNAwHIyoJjj0qA2gKDyGFn8AMAEkAFkpAAEaCgEyVQDAQriIINkwD4SYA_8fAATQAIIHQAABgIAsxcwIkPyUkbKF4TFrRcrBiaYcrlcgh1AoDmsQkgQOgNscpAAEaCgFDcMAoHxDC8GxSoBje0qA0kWj4GIAAAGxCAABMFABqPucJqZLwefKgGOqSo_ghGkusfAxAAkgA_UIAAjQUAK0+MpKpwvBt8qAY5BKggmkMweQwYgASQOn_g5DaEAARoKAGcfYwPPKYL4F8LlYTENBcrCCaSqR5AfgxAJqSQOgNpwjAAEaCgpD48C7LwaIqCYGNIAMgEholRNTKYQVgmlkAHoLQgcfAAEaCgCWlS1S8HwSoNox7OVAaSLB8BZAAlILoPgAATBQBgirnCYUaxfD35UG0Y9lKgNICI8hhVLIAEpCxR0AARoKAQgVMInIAWrYFiLlYbRiAYqVhBNI148hhVLJVAJJKXXGx4I6AAI0FAKFKsaHiyDdi5WCOaN5kzBnKQemnCysPQqlkqlF1JNNSSBEKlY1Bo5AAI0FB"
noncomputable def WL12_2 : ℕ := zfNat64 33247 "BzFA5QvAAQiwGknoAHk6WBvJOAAg0FBWA8y4ATVDcFAEuLj_CkFFKgAGh0EtAAQgGKVgAA3BQAii4AKLDcJKMOG4TQdFysNMxOgXKz_adIAqADJNESWCUAmjEAGIAAAFMgJxcGoTRaFysqw0Y5ijYuVlNFIAZIoJaxFwxCaMQ6ElAABuEgDYOE8ZAWcmAKyTAB9Aegr02D_ycAOk6AABsHAARLg1A9BUrAgMGdp5gzlIBQT_g1SQ76VAytMpzUJwIxxAYAAAExcAaDj1GiRGDeijsCpWGFtZgzlJTZaOaCBmkjkUlGLlYFGaiEYolRxaBNAACmXFALTUFgFSsMoxQUVKwCggZJIKe+lQE0ahwRGCSMZ_NweTTgB8FwNiSFIWr0fAA8iAAoRAAiEIAAlFwAAAAaQCiBQTh0SjIITlQYSH5UAA+RgIIAEUa_0JgrCsAAPQBAT4kE4cHJAfhKQuiEZhcrACKBkghfwqAijUDXoRIQtKxBpD4FQBMXImGjuzBENYKlYYRicIqVgBBAyST2RV9gqAmgEULiXQpqVAA2LgCQ0g0bAOYqVhhGIsi5WAEEPvJQfYKgJoDgUILj_JeCWZUAREvBA6GofxKgwjHd5UAEUAL_FQ5FrJwDp0Iwjm4gY4OgdHZmZlx0AF7wTVOAWFwAEiDYOAAcdBiMaACIgAAAAsVgAAbBwDw9TNk4DFLgEJENwUARIuCKEpKgADxUEtAAOgGMVgAA3BQAFC4Jw7qBsDNyhWGEBJgzlIEUaIWKwMkkHQVBUCaAwpGAAMwLAAULmYFuoGwM3KFYYQEmDOUgRRohYrAySQdBUFQJoDCkYAAE4cABwuTUEdlCsMoxRIVKwoolwuVn6hokgFQJqojYFpIxxAYAAAHhcAaDjnGhqRSal8oVhhGLeyhWBFHJGCxWBkkk2ioKgTRr_oiF8oksWgTQAA+lxQCzDDpuBMShWGUYqfKFYUUS4XKwMkkFIVAm_uNgm0jBJGIGU04ABG8BELgIUkKQsAYkVhKQugCPHaIipWBFHJFixWBkkgFQJo1BjqMEQVH4AAABLgSYkE4cvZAfgggqVhhH+YM5SBFGiFis+sNEEAqBFGoFzQiQgB_D4APhdWx9CA2BUxUrDCMZSBFGiFisAGYVBUCaA4VCJDcS6FnDIAIRcASGlljYHHlCsMIx_eVARS6BUAAVD9CcA2VCJDcQINGQBES4ADJggdf8NgfMVKwwjH6JUBFLOFQAeOFhyADM0Iwjm4gY8OgdHZkbmZcdKRsnAQhcCIMbI2AzhcrDDMWcFysOI1AAFslAmgBeUgAAIgxCm5LOgMxeAWlwDAQhBqR0EUdUdAAIBYAAAAFisAAAYCAA4XAEhowQaDi5UUWY4zKgAGAkAAAADBWAAAAFsQAQuE4HjYNRSKaK74yZpQLlYAD8SApI5ANJRHIgtElgAA5DgAHlwAUWHkStSNH9zJTRUrKLMWQFysAB+JAA_joAAAYgABQB0hxow0bSkIoxbCULwQgAATQTg0cwDqoQAANg4ABe8ALRgAZkANLgCQsAAAAAAAAAAAAACXFAHYrGgyZkKQijFLRUrCiQThhUAAxA0gMGRgACdEwAEy4AaJFAHX_GgJCUKwijFLxUrCiQThxUfsGgBiBpAHmhBVAAAOxcUAdpMaJiFMkVlFNwZL5SVGggfCpWBkB6MQNIDuEYLj9JiCqBETIyTnIANQgCRkAOLgAJMAGDgAAAAAAAAAAAAHS4QgeNg1FJRVkmDNKBcrAADJSRyAaSiORPMmMFqJL94FAAA8CNExDCSKyijE4xcrCyDkWgZCjh8yEmA2lUI4oykBoAAAYykAPLjmxoGrBi5WDkYi0QIDkLkNBiRCAADPw8AACMkxIWSKyijGUhrliuA3iRWSEOtHxRA2jOVgaWjKQGgAACLFwADhUf6MgFBUAAAVUagAGqB1YlAkAAQ5yDgHUuUlGgaoyKlZZIoxbKULwAAM7IQQHoDiAAAEaIgCYsQbIuB_o2eCVElGJYyoANwHQAEB6HIAGiUjKOQCyh8DoJZU1MaDAZUU0tSVAABleQpBRA4gGIQgAAhDwAsi5BShe0IeNl3+RsKbTTVAGzM0hcrLLpDYDaBkB6RkMoE0qSNKQAWwRAOAmC4ZShewkYP10fpsKTyTSemDeUgABkBykFGjIaQnKKkaUgAtgiAXBnR0nhZvBnT8NPzkF4JRHGqAYCIMHA2IeAAB6AB_o+AAfCVAAAGAgGRJw3AxJg4PfGwSWERsALR6AdAiKBHCa0UFGoQAAbgYNQAOXESDCEFZFysJa2guVhaRR5w_PUEQC2yIKzUQegjAACJBgAJDQi4kCli5WEtLQXKwtNRGQfOwpoNZIgi1mo0kWOiSwAAAHhUIQUAdsqARGVAaRx50P4IgAAKgERCAACEFAFVPhCCgAA1RUHXmoaWdEOho_8ZAAdIoKPWgAAhBQSgA8uAJDQCUhj0u36VAaScgTRqxhaUuCogGeQgAAAEJcRIsBKQlobi5WFl00nDkCuMV9s6xfKstColW3CkEUAARIsDoAFMjxkIK+lQE0SoDSACPnYeDYgtKXDEKIBxkIAANwkAAhWPaQgKgVKwlspHpZQchYQ96XAUepKwPhQgAAbBQBQJEELZlQE0SoDSTkBobehYgtKXAUQDjIQCKAIAAoEiCC6CpWEt82VA25qzk5AaG1hDE5cBRAVChAADIKgawWIJW4+R8VKyqS0_hUrAyhRzR2Agli+EtAolUB8oEcJ6AYEaJmXu6mnLwSffAIS4BgIA3Q8Ac4eAItGwAEUAAAAAMBFeAEjIAeXAGKFysJa7guVhaQ9Jw_ABOJEFZqIL2RgADMHQKQBCXRsRAMKLlYS06hcrC01E0R87CmgpciCs1GkhIUSWF5h7oRcCEABCXIYOIwEEFysJaRAuVgad5KU5CmhL0iCs1GkiNkqOFdKtNDMCQMgJSuKASAuKVAhluByoDSHEPnYgQLvGwH9mIJXoQAAoBIAFaEUAkAYQuVhBlqaC5WFpDgnD8QMxBK5EFFGoUARgABQCQfgF4uYkSALsXKwlpBi5WBp4QpTkjpNCXJEBNqP5UovQlFtDanAAAXhZGhIAjRcrCWkwLlYCZaNZOSOmEBMEisCog6VGP9t1xNphBmFC8mQC6vACA5iRIBQxcrDDLU8FysiJpECnDsjtNKtlWCaOwqtJrs5PUlRwCqAATkuCIOA7OVHbm6Y53KgtIPSOgE3IglIAjlYPIlA6q9AEwLkaEgKspDa3o2ZncLlZ_xKtK8VIekdGoADGMgkhOnAIEAGb8FAYQBa+CIOFoL5IgF0EQBNQAsgZAAAmMgAAhDQAwy5iRIeguQuVhLSeFysLKTQMmjsjs9qIAwqThOWkrF+qhFCgnk20X548BovNmJSNh_A1OjIJSEtJ8XKwRu0awgx87JqKQqsRAPf_pQHvQgHEBAATSFOzMG4FaKlYS0KxcrKTZRZJw7G9GC+Uz0eyEAM9pNJA6JUcJ7RQMWNEyAEhpEoyCUhLSfFysDltGsIMfOyaikKsEQD3_KUB8UIAAA6AtT4BJXP+LQVZKgltASoLSaIPgggAH+S4CvoRxAYAAAA5cROULwVoVKwlspKKZf3Jw5BiXT_itLQqJVOwpCSkaP7wKAAC8BBiofRq2gycoXhLWBlC80Q3WkGakPSawUAAQ+sMh+6cDEAnAlAyBDSpbQkr_KF4RZaqQuVjkmjfaai784fk1gstAHIIRiG1TJ+fh4KgCzyomwIQvAR64EBRBCDDi5WGmWupKF5FbKTZqEGgk0AyaOzA2UwhRYUjQ8+DwAAAUC4AaFFWPBkGRlCsrNFaeUKwMpBg6dgxJIIKKlYG0khSpGACqAHQFUXFEPBkVwhKfKFYXaKzEoVgNZgzg5BaRQFIGkih5VGBjXlGHpZAEGjMAB5cASGgD8SoBvZUBpLjnQAL8KgNIBlkIAAAEAHlwBIaASkLho2_SoDSAQPnYEkL5FQHEA7yEAAACALjkNgHllCsKKVYqVh6pmByF8EoBSBpAj+hA9Jv9j4MEIQNi8rf0oAamsXIrrGDcAoFysBaYAuV1kNIEA+dk1FIVWIgHtJB5SN_cmCCAAAtLgCQ0Z0bBKQFopC5WBlP_HTs_SbCkPsEQD3eKUD3UIC7WQoWRAEmLyoOkTGQSkBb0MqA0k5moBfoiFIPQGjoRhFJduqtBjo6J0ZnR0bKQSffAIS4EQYA3Q8Ac4eAItGwAEUAAAAAiDFfT086Tm5LSjsDHgA8yAJCwAAAAAAAAAAAB4APMgCQsAAAAAAAAAAAABCXAAGkQAFCIANEJAABcOAAAAA3AwAAQDwAKB4AGUPAAFUaAAA0VAAAGAhpICBBBkdAuD_5Mn4uABZCwAFwGgABHoQAAiQYABhfSQECkyZr5cElPOXAAoBIGIAAxIEoADVGAAESDF+Gh8eAEhoCMOBa5cElPKXAA+RID5EisAAA6yUAAABDrgtBhpVHwClIrUqCiGti4AA6DxFYBJqEAAGMKAADXEcFjMDJli9UgALlMl7QXAAGTKqBOBbNQ+lUmkkaCiSwAAxhQCgZJeC41whBQAFSYADpMAB0ANtJwAC_zoAAKQMAHGuAJCwhBUxD55UF0c7TKgCwg0ACjy4ABEaEAAAARrn2Hk8mDcEjFSsLo5AEXKwAMgTR9RsF8sZgVf+KQYIRgACNBQAJK5GhIHhszBJBUrC60o0dykADIaSaf4NgvljMCqUQwcjAbYeAAACVxZmzMzBuDfyhWGEcgcLlYAfUUNgATUsZh_5WAdWhAUQAHyOk+mDcEkFSsLo5lIAGSkDUTR+RsF0sZgVSiE4EY3q3AAAJphEZQ2ZgpoqVkUujUihUrAGNDRcMpNBqnksZgVSiA1UCOBJdopAPQAI1wEUXFYiWgbMyCJ4KlZFLqjDhvKQAMhpJoNQuljMPpVKIaxRi6iUIgAygj5HzoDZmDOShWF1qBo7lIAGQ0EnA1C6WMwKoATUCOG2ogVgHhJwWcsZLwTuUKwsjUARUrAQCOIwpCxcMJNBqqAyXh5JpNBuCNDMJtqIAoxg+Ds2MoM3fgBeuRoKAC6VBGQ_ghB04xUAGoEWlYA06EAAG4GIcAGZyNBQhC4H7FwSV3xcF0AAGoGmFYA06EAAIMGANOpAm64bgocgBAItfJmFlQdZaTJi1gAOQABkaEAAG4GLUAVVwhBXwi4KIlRKSOZUWWkg1ADGQ0BVAUqhAAAAEhJGgoWgxguVkpkrjSheWWkhxzBub+aiaBWNgyBVAY4jAAAACa5GgoWgpYuVkpkq+C5WWWkhezBuWmmnLzaMgVf8qQVMRjxJ8ABMgAiuEXLF4KoLldVBKUyVjhcrLLSQvZg3DTTSaxkCr+xSC3SMAACcOAApXPkbH9KF4JaLlZKZKsYuVllpIXswbhp8mmUyaxkCrUQtUjAoY6AA5Y2FoEgLldNlMlR4XKyy0kOOYNytbNV5OBqGRRj9UQCKBZqoLrHgZAMCsAEULwY0XKyUyVsxcrLLSQfHw1wOFMMZNZNB"
noncomputable def WL12_3 : ℕ := zfNat64 22470 "pwAZKAJIwA0qAHCwAAAAAAAAAAAABaEASMgB5cABFgAAAAAAAAAAAAC0IAIXADCoAkLAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABChAAAAAAAAAAAAAHoQBIaANfLgkqNy4ABuFAADQKAAOslAAAAFUIaxoBr5cElRuXAANwopIANAoAAmaMAAGsaJ2PAB5kASFgAAAAAAAAAAAADzIAkLAAAAAAAAAAAAAHFwBMaAAAAAAAAAAAAABagBTEAGVgAiEAGOgAJkAXKgAJMAKFgAAAAAAAAAAAADRUATFgAAAAAAAAAAAAGyoEQYqQkAAA4qABNBwAAAALFYPzHQAINBRzxQ2D5y4JKocuALajQAWhCgooBgEoAAd40AB8rBoKVGLAWAuCSlmLgAAACigBcUgABQDQCjMzAoIASGgC1y4JKeUuAAKhQ4wgPgACEAxyUAAAAPXgBZUASGgAIDoACR0AATDgAA9ItAAsVgAAAB5UASGgANDYG8pAEjoACMHAAAOQAWKwAAABsqAJDR5Q8CkCo_8nCYioAAiFAAAAAnVgAAP78nACQkEQcBsOAwxcH+SYxBcAAVCi4w8AAABBQgAAB9DgDhwLXLgkp5S4AMQLBsiA+SQAAIDJQAAUhoB9DlTIQM4LgkrxS4A1UTA8xuAagAEWRgAIOCQXgC4qBQKEoEKOj+hsEqOgAgBwAAAADBWAABEHAPodMseCTBcEH_ZNFAuAApgLAAAAj0IAAEQcH4AcLh9DjADwFcLgkptS4AA3gojAAAAAAjQ0BoKMgBpmAArwAZWAHFQCAmAAAAAAAAAAAAAhXgIhUJIUABo2CSgABMOAAAsmCEYB4pAABJCg_AB6EANPgCRkAAAAAAAAAAAAwEAIdeAXHwhBSEDoANv_CIABoHAAAAAUj4AAIQUBoAbKgCQkGYtM86CwpUGn_plNcqAAThwAAAALFYAAAA+vACioAkJBEHDGJgA0bBhkoAAnDgAALoALFYAAA0ASFw8iSvTh+VVkhcrDbMVnlC8ABGHAAAaQulG0oAA6JkABMuFUOBecPwt2VBtGNByoABIHAAB_hqAB4pCiDIAAAdywPhS1FoAACZUAAlDgAAAAWKwFUAPSUAIAuCEKAEuTDInYEyTAAGg4AAAAEC0ARAJUdAyNzYBrKg5CrCDmSheG0Yp3KF4ABsOCCAHKE4AI0pAAAiDgnAtrMAtKgRBv_EwfXYHQYQKR0AAmDgAAAAWKwAAIg4Apa8AcKgRBgLICnh5FBUAAgDgAALoALFYAAEQcYYaMl4ANKv5ECYNSRWEliZQrDSRUQFysAAiFAABFHIE40oAGzgBgAAKZADSoKRX6RLcKUKw0kVJBcrAAIhQJAAIo5ABclAAP5ECYLqFQftKg0kXdZUAAAA7FgHIACEIkgEAAAAoqCk16lRmKlZaSKj4uVgAORYAACaADxSOADAAAAGQgBBcAMKgCY0AAAAAAAAAAAAADZADioAMoVmyUqOBUrLSRUfFysAByLTqXgAAcgAjQgABIowAwIOADSpHCYGpIrCS+8oVhpIqRi5WAARCgAAijkAMqcBlAAFIWB6SKwkgHKFYaSKOQuVgBig4AivAOgAFoIdGA2gH4HgArVwhCTmyYFtFR_5mEIFQAB4OA2lUAACcnwAANhoAXBcIQksIqDGJUGki4nKgARwkALQqAAIoVgAAljQWgMMq_kQJs6RIZSWWFSsNJFU0XKwACgcSGCykSgBQQhUG+kTwAH8jh8J6eZHSkbv78nnY0AJqQA4uAAkwBISAAAAAAAAAAAAASGgDPSxmBZNWULwfAgXAAAEIkAUVKg3aUAAASIkA1ssZgWTflC8TARHwAAkgfEgOQ3AJUSgAXwEDwAAtUBYHhCChOCQYZLgKsgyoA6mEAADSBtB8pAAAuEgE0KAbIZLwLKlyheQAEgGoB0ZKuklAcQ_8zT4RgAD5FwANgYLgoA2hkvAsqPKF5AASCaABJhxG95KA2gZZ6IwEUCiCDgUAHgyXgWW2lC8gAJH_ToYhUQSp2So4W2DysGUrqBHCmkEOKpiIkwAhbg4FADULGYFUQJQvIACQGkAFCJQABFEYAALIkVYzPgRBQBuixmCUqyPKgCuikAH_ioMfOwBjUIAAGw0AAk2CIKAOgWMwKptSheNeGp6EoPgD_6UAAEURgACNDwDghBQAFioADpMYmGgEwpAAAABBOgAAUCQBLDYoAoAhRcCURoVAGBYgi0ACdpsAAFA+AABEHALPg8mAEF4GgoCLhcDUqzFKgBUxkH+lIL0GQAAj0IAADQUAApfBoOADYWMwYoiWK4tAADQXAENPgFoVZKC3JwAEHA4BQKKVfuECwDwmDMFhLlsWnTRoCCAZnNNDSWMwCSigE6eAA_kIFgAKZhCCgrLmCxmBVYwXKwAcgVQsgZAbVSLQJrQgAAhBQAEhJGhJFSED0ixmBVYwXKwAcgVQskZAbZYLQJtQgAAAlCsNoQS0zMlFVDhcrAByHu1CuDqjZmFpqoK_QgFMfAEEEaCuDoQRaLl5_RKKovC5WADkKiWpOnVGzMDSB3ZGAugCEGRkA_qQIgwlAAEysBMqJ6ACkloHpHwG0AxyEAABEGA3DAEKkHDtgRBgCbFQHyYgAil0AOoIwAAQToAACIMVdKBcFAOGLGYFVsxcrJplRBOKGwFHDikC0AAiiMAAC4KAAHnFSFADQLGYFUEpQvN4E0tACqEXDYBqRQH+nAACpCgFN7+rnb0AA6QClCG4GUMrABA6AAgm0AAAAAbHQAAbgYABqENwMSouDCpUEtqqVAaToB8AA5AADYhAABuBg3AOycRINm46ArRcH_SYsBcBkAAE2EwAAj0IAARIMAAROAOlREg2bjoCwFwSUsxcBkACKA5AAAmhAACJBgFABWENwMgQiDYZUAxvWVAbQEh5DAAAogBsUgAA3AwAEgoFAYyAsCVCoBSpUH+m4m8fAAUYyAABkhAAAAEgoSQYyAsBUipWAx6KVAbTXB8AFmjIP+LQBzUIAAAbgYyAsC3CpWAxGEXKwNoJJAfg0JGAYgWQENoQAA5DYAEYsRINgYaA8BUrBnpYzlIWTSCAOH4EUDoxAs0krR0JMSo4f7PgACJBkHDB8GclCsF9ljOUmnlo0g9DKCMB0YgVQMuIwFEBxg8TcyKypKAQ7YiQYpQobAhRcrCYmmLlYWTa+pWHoFEkoAxADypTwgnAACJBirtwbgYBqBOYeHoVAAJCoPOFQAAAJz4I1BQAAArmG4GACMdBxArHQABceDzxUAAABGoKAACcMwC0uG4GIoI6Lg4gSj4AAsPAAAAAZXgAA3AwGgWFeG4Ga4pBJAkKJjI_+rDFkIAOgFwAAGxCAADcDAIEXiJBiqEkrRozCQmoKF4DntJkLQB+BcvAAIDJQAAiQYN0PDjbEAJDQUhg3CaewuVhlmL_yheAAjFgB8o0BJADUJQAAINBQ4jBuCbipWGGYjuLlYUeTHQNQABUOIwOID1EYACDQUINBRPjBuBuC5WGGYuiLlYUQAEyHQtmoABFEYACDQUQoBDUgRBmvGwV1Kgw__MrPlQaQKgBBIuAAA2IQAAEQYtUHApvhozCQ5QrDCAUwZykNpFVUdKkKF4ALQLpNQChEYACDgUHIA1KwcChqDEShePCYNcxQOULwAEIsBpJ6AB5OlgbyTgAINBQVgPMuAE1Q3BQBLi4_wpBRSoABodBLQAEIBilYAANwUAIouACiw"
noncomputable def WL12s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL12_0) (dpk j 1 WL12_1)
noncomputable def WL12s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL12_2) (dpk j 3 WL12_3)
noncomputable def WL12s0_4 (j : ℕ) : ℕ := dsel j 2 (WL12s0_2 j) (WL12s2_4 j)
noncomputable def WL12 (j : ℕ) : ℕ := (WL12s0_4 j)
noncomputable def WD12 : ℕ → ℕ := rdw WL12
noncomputable def ready12_cuts0 : List (ℕ × St × ℕ) := []

theorem ready12_cuts0_ok : CutsOk ready12_cuts0 := cutsOk_nil

noncomputable def ready12_0_state : St := ⟨26112, 285696, 28545, 39936, 52016, 162022, 53248, 163254, 29666, 44151, 29184, 45301, 28545, 138551, 26112, 285696, 54657, 325632, 106673, 476263, 159921, 529511, 189587, 559177, 218771, 588361, 302319, 616906, 328431, 902602, 80561, 190567, 133809, 243815, 163475, 273481, 192659, 302665, 276207, 331210, 302319, 616906, 105264, 215270, 134930, 244936, 164114, 274120, 236271, 302665, 262383, 588361, 82914, 192920, 112098, 222104, 140643, 250649, 166755, 536345, 58850, 89452, 87395, 197401, 113507, 483097, 57729, 167735, 83841, 453431, 54657, 424247, 0⟩

theorem ready12_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD12 ready12_cuts0 117 16492) ready12_0_state = 72089 := by decide +kernel
#print axioms ready12_0_cursor

theorem ready12_0_covered : Covered (toCl ready12_0_state) :=
  ready_cover_cursor WD12 ready12_cuts0 ready12_cuts0_ok 117 16492 72089 ready12_0_state ready12_0_cursor (by decide)
#print axioms ready12_0_covered

noncomputable def ready12_cuts1 : List (ℕ × St × ℕ) := (16492, ready12_0_state, 72089) :: ready12_cuts0

theorem ready12_cuts1_ok : CutsOk ready12_cuts1 := cutsOk_cons ready12_0_covered ready12_cuts0_ok
#print axioms ready12_cuts1_ok

noncomputable def ready12_1_state : St := ⟨26112, 285696, 28545, 39936, 52016, 161245, 53248, 162477, 29666, 44151, 29184, 45301, 29322, 237166, 26112, 285696, 54657, 325632, 106673, 475486, 159921, 528734, 189587, 558400, 218771, 587584, 357322, 671909, 383434, 698021, 80561, 189790, 133809, 243038, 163475, 272704, 192659, 301888, 331210, 441216, 357322, 671909, 105264, 214493, 134930, 244159, 164114, 273343, 291274, 401280, 317386, 643364, 82914, 192143, 112098, 221327, 141420, 349264, 167532, 591348, 58850, 89452, 88172, 296016, 114284, 538100, 58506, 266350, 84618, 508434, 55434, 479250, 0⟩

theorem ready12_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD12 ready12_cuts1 116 73211) ready12_1_state = 110120 := by decide +kernel
#print axioms ready12_1_cursor

theorem ready12_1_covered : Covered (toCl ready12_1_state) :=
  ready_cover_cursor WD12 ready12_cuts1 ready12_cuts1_ok 116 73211 110120 ready12_1_state ready12_1_cursor (by decide)
#print axioms ready12_1_covered

noncomputable def ready12_cuts2 : List (ℕ × St × ℕ) := (73211, ready12_1_state, 110120) :: ready12_cuts1

theorem ready12_cuts2_ok : CutsOk ready12_cuts2 := cutsOk_cons ready12_1_covered ready12_cuts1_ok
#print axioms ready12_cuts2_ok

theorem ready12_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD12 ready12_cuts2 128 1) (ofCl (RC 0 0 1 1 0 0 0 0) 0) = 120859 := by decide +kernel
#print axioms ready12_parent_cursor

theorem rc12 : Covered (RC 0 0 1 1 0 0 0 0) :=
  rcOfC WD12 ready12_cuts2 ready12_cuts2_ok 120859 ready12_parent_cursor (by decide)
#print axioms rc12
noncomputable def WL13_0 : ℕ := zfNat64 33247 "BGQoxg+CzkJ_6tKNpVc+ULwAUhJMtdvqnEPKF4TS6bSrPfqIwAAB82AARpk0iAz55DDaTNKgDthUEkAWgG0HvoQYY1HQGPBYAANMASGgAIkaARBOA8hhtJSlQBwoqCSUQ8oXAWkC_oQAAAIASGs+XMZXxg+B4EJ+RbKOPKF4AXMkVhJMoJlKF5RJpdNoBdQI4AAB4G74gCQUcnoFgvMfAF4HgAIxEAAPiYAACRkAAAPwR0AJDQCeSdWHgAOeQw2iLyheAdsKgki2GoFoSS6aQuMjA9EIXQAAkNCyDB8GznkMNIoEoXgApCSF2RKcMEoXhJLppApqBHP5pksATGRA3Mzo7fk4NrrgCQ0PkFBmIyAVkPAHUiIABKABBYyAACnv42dBGAgnM8hgITKF4AsEkVhZQovfKF5tC7cQO8jQwRwHc22kAbAYTAAWHA+jwMrQgDjlQBHsqD+rME3S4ygbQImhKyagMIAEp5P+IVBA7y0o0oXgD+yRWBNBXxcrXcnEtNoLSRoZtJoTQQiQJwAHlwDaAwxGJCVAALCphyEZZtFwAAAD0lMlAAaAe65IJyCpyEAxcqAO3FQAC1TyEHUCeaEASQJcPAGIXg5ABXaJLNKVAHxyoLKH_i5TiEGmXYEeIQBNAto8BoEPmg5Ik2h47KIAANioADaTAAGEqAABIfYEAAGZLGYxAVx87AdSULwAzhUnC+TEEpAmm0DhIUM9DRvHIZJoKWIj4MgYuSyYeaIRAI5IjgN0LlYAZwqTgBRlIBpAgKBDNJRCSADCA+DIAzMyVfRMAAkaGGnVK0tcoXgHySoLSoRmBaTSq3EFVoROQmgcceI8_pxcAJGRBiOAiEgBkZAM0HgD2xUAAtAAeQXAAQjFiXAdSsA3sgGM9rpEAFNCAJaVHkBepUGQAukkDqFm0IAAUQsAP2ybrGg5mfAPaKgAUj0A4yXEUAHZHwAAJRIBUdMFBkFQWAQB0AigeAAAP9JwADQDIAAEQcASpijBGA8ShB29aFtFoIFWXrdJLdNQDEwlluISdQgACNCQBQZCEGgVufAK2KgAmh8BiKo9AAApHwAAIhIAAPUHpsLQiDYKsBVABr51OABqS8AeQNefAAAiDgWM4fh0UOjP_PIdhAci1XnP9kICIJ0+kllCqXUcrF+e124g31AjmUKIB6zR2AOkFdedWbHgIIH6VYAKpNAUNGdjTEaiYjCVE6l0EApAACkARMSM4fh0majOxPIdhA0itXHIAX0ieSQCqyBatln9R8XbaBNEKGYZgvkmimm000MgAUVgB9URDkgAxAXobAG9joAPjIwADxyoAAMgzKhILgg4edgiLXL4aDoaMOgJ2FQB_4qAAUZUAACYyAABEHB2UgAJGAGmQBsuABDQAEWAAAAAAAAAAAAABvgUJcNgfAAAOKgAC5MApAV8TAAUBeAABEHAbGgEiuAGTQgghsSoAmJNQO9mywCakzXarqDSEIAAEQcABz8ZSCCMPKgBQpMACtypYBMHW4gwlCAAI0JAKEUlAU4KIGF8a1FwuDqCkJKVTCSrPIawCYe0E6_+ZiSKEAARoSAH9TAKmQBmPgHLFQBSQP_KQ5FgEwAKUPgAARBwAuhaBwQhAQSshQSheXEHmkwYQIZKwfyTriB9ULAgAAPBPW8AB0hPdMASGjVTICiA94eAAACiAAvwyAAAAPawAKaBeA4yjE8hg2o+fhZHtFysxw_ATQ4gPIVgLtxBCKFgQAABOIz_qEATEJ+LayNULlZcQJo6pgvmEOmKwFW0g7NAj11gislULKApCSGj4CqU0ogAkpOABMisBEmo2gXZCAAFeXB3Q4jT4hPwApBHoeJWphpAkmkuhBpSVkrUyyXSqcQDIjQzSZST_RKD3x0AJvGAeTS_J8BMH72BZ5WKIAZqIAk4sVgAKWQqyAA9Dpk6f7BCBNDx3KiFUAOsIFwkgBZJcLx1Dv6FbTZBsASQhlMnoUpJ1pJBK4rUyrUaaTQK2Em01Ux8k4qTnMTp9VJphMJFoqGkaGXR6hg+fykcg9ABMd+QpXZaguIPTECMAHyJD+VHoALJ9D_40FmoYFIdAACsLabZQupJSGgtBHg0bzCXDkCkilXJ0NX3CwNKAg49AkeOxiBA0kTgCK2i0TgspwbGXgB6AIQCquZaKaBFMIAAArSIHjTKZ91a+FJItJUehHgRoY844bgKRaKQHLC0yeLRSJQqBGIQGGRKIQaAAAlSADpQBJGAHjwBISAAAAAAAAAAAAAjOlNBaaVPKaKpRI8tAls5AEsplMYh_wiCCk1SikAD3XL4AB1YAIjABzoAeXABhYAaJAAAAAAAAAAAAASCZiA1Cpgr5SnkEmhT0CPaI6HoCcMFYlFoELFKeGQiCYyDfAgGDQSBkDSAA_aC+SRDBwUgIM_KQDrj4A7EZAAUQAAAAUgBZlskPI9dCmhZGtokcAGIAAEUp49DCnpmAHp5ACfGUMACyGW12g1GmkGouqUp6wEaGLVjFicWgpJWMG0KAQzHabGQCAYyYgkP0Fy4YDHtJqNBJJNGClTwAyaR7VQTodSymgOD6GAERNH9FQIABeMmO66UQ6AmRYeSTLZRMKksCiGUmS826tfCrTSCjxOp00eiNDKKBCa0VAmnP5UPUKOS6TQ7rguABAQ8k2WyqUSI5JKaACZVSrhVq+lTxqTaahSSbQcCWM6LfYlNQRbCGc4nl0mh0IaSbLZSSBN0ymACLDWZCQjarKYbSk5i1oVji9jNIAG0oEArVaiUSjCQI2LDy6XbCQQDmqUwQVivsjKm5VqNNKJR06XTUKYbbaQMTdrtN9PItstdpoBlquVW+kCOiyUwQEPLrIGLPZaCTR7TQHJjXsd9CqyFMp1kq00Alk2gbcsZmm+mkIthppdqIdYEdAoxYeYTbZSKTRt6ZTA0PAFGGa1EGspDsuoi9_B_0TjyAVoqBAkI5KM9DoITFh5JLtdM8qSwKIAKu1KuFVi6dLHJVpuBJptAo0W+pOagTilDe9BYw0nE8uk0UhDSTZbKSQJumUwQdivu_Xq5JnMZLNZpuBMNlpIppSngGatd582qWyDQQvq1+mk0aimUyUvAEPLtdrqi1S2RZ7TQV5mxt3XsZxPptNJ9wOBMJtNIQdUpmk8mme0Gwm_UJ5dJopGId0UBl0ymUkkUJYiUwLDwcJBQUNTdqV8A_p0uFCETRaqBHFpBAYkXSj0FNwI5KpFDoKGIAZJMtloILKUq4CmIGBjMyHg8NRpAaClPCyEUIIQCMFYJfzERMAyAKmUyWFwdEsZBiAQDB62o4Vi0CiB8+AijeQKMEE4wgUkiOEUBSJYvGQDkk6eAYsRjUYxkCmBAMajUexorEICkDQc9A0uMmv4YsYScOpYMQeCRHACkDBcAJ_ok8AAxAEf8NgB6hsGbXCkdQKArARdLCQAfIkP_+YgAslEABMRsDVAAsJIOQGYYNwLAQH7dKJ+WrmAJnDWXVMlj0Z8fQyiSTXycHS6AZaCVR7_k6JIMmABZ8pSHI9AMhasOpX0MjvQGM0YADoAVVyS8FWqhyACoEtBFADIGiicl4_gbZq3lJF1okcpIBl6zFfjMrAJ4Wq49CSVQvyDAAIEAQMGdKJTXruA8Fi+EENYiSwkgygcRu6diCAZTSFU2gfQqj1QBsA9FNVi7e6+KFc2LJjptJPUjRxTQSaQQkGS8DJdMJZdyya6DTTKaTScazacCTQavEMHxUSgdGkFI+gShWAi6WEgA+BovMoAWQLqGBJu3h4DIE+EB4FgMqXUS5OXMDLSSDnwmRagR8_p09AM100KxfCgkQTp9lNNlOIYE+3BAE1BstAwIrvA8Nr5lI+h1NoAUFan9BWADoQHzCAFkAs7WUhNaBHCqNRTrgyB6HoABpg000qpXQgpc3ALyTgCmgcAFqDoABDBkAANSdAAhkATEgDkoAPHwADioAAAAAAAAA0NBQ8LfbQA8yAJCQAwcBpAPgLAAAAAAAAAev_FXMkIGdvH8LIgRUtmEwnE6nGcjSAVcLG9RDKZQJGgR5UtwOSKF3pR8A4chUyZCBAgJEVg8hXRSABAgACPQgABflwCgOGSFISDifAgQGpKwAUQAowrAADcgiehAAeOOgZCwmzARsUwBEnBChgQQkhuyheC8bOYCaTp4ZTCBXFS2F0qnUKIIwbS6AABkFmv0ICxIT8qI_8oXhxAASlPDThJqA5SpbCu3UFLoR0DYjIAAHcWPcunIhBAs8hlRGRlC8OIJmUp4aabNQVkC6gflCCMgAOjIrJgBIaAPKgBkZAAaHgAHB0AAMEIAABpUAAAPj4cbAGwkqchAQSshCyheG0HTkwXZwLwR4ViafyOjaBE0J668AAASMWgWjnwEELpKkqCMOwclKiwgd_WoWMQXUFnoR5I6AAyBtTIRkB+AQQq4iXnVlC+K2UGJGjMIpZwCxFX_ysBkYnkw7GSgp+rAAB46CRt4AkZBCgoPcwfg0BQhgCkAV6TAA_5WD9jNcTSaIRg6k0AAAEjAEDIAkFAAAAAAAAAAAAAENQrfSAFGQq2mABRR0pkBNA+mZAAABNAAaEZAAAsJgOR4oEMB6F0CeaOw4gnZOnn9GYCiNFQrhtYkxHEBwI0MOpdHpOSSihsV2CJ5DKSPQIJ0s_6xfKI5IppyUvfkViaKSaFJAklR5rVaiZQT4hQ31K1M41kekGYrMJk4DUZ45lrMyEDzDyGV0RYcPwwhLROAAqgALOMn4ef7rwExx4HwBHjPgIQD0rt2FIcj23DeBNDCBRZioV0CYS6+lw3gThGhh5rs9HLoToMlnHg8TKgBIyFbRRmp8FjEIMIo0qAJWEwAE0AB4iE_AAOQKIwVmwW5jT8nAxS8GpsvMGgAkIQPQGZUACCKF5NABiAB6VCAABEFALnsjkBILKGQCXB4A_4TAALQAFJlQAAJgoAC9kABpl1HgHNJCaKFJgBSJMACxSo4gAWM6AACkFAIXU1wJhrKQIxQguiCSoOoBFkpVBsZ5DMIXUHDIQAAHwoA2yuAsdPgyChBdE9lQbQJCVC3yTMAXSiACs0IAAUAcBHPeF2UwRD1YjIP_IQEehxWAAAVaQgAJ6AACYKANUxkrbkIOHoRVTFhcTbiBpqIAJU0bmUtIr3IIKoQAAIgoBNHEAB1gANMiSbATQGnEwAKhKAAQZUAADg6AABMFAOm4hg2kg_+MgAKcJQBQ4+AAKRUAACYyAABMFAAM9QALSABWTuoTizoPrKxVQAGvfU4AGSGxpAAvh8AACkSAApUwjYKoBGNmdAzVOAcYpAAIU4AAwgcSKAnVv+kQAC0AYEBCjYgJWZkIEYplMopvBWLIFV0ymVQCXpYzNIf+dggihBJRaAG4oktRZ4_KKahOlmmqlFGitTJpdETJ1JKIBRbyULzCWQ2gz1AhmCXMZNJtRCTGSdBj80ABh1SOnpGQEUBuyEAbaQgA8EdAAPlMgAIfjwOioSAxcfgg53chC7XDkWe+VB+QyAaoPAApAAJxEAAB4uAAAcDF3Gx5+Uhs6OwMee0ZeUjZLAx8bTkpKOjsO"
noncomputable def WL13_1 : ℕ := zfNat64 33247 "BgLgZARFLgBym5EhgH9QgWaQCyFkCCcAABEGABATAAQ4EQYDQMEJAylsOgAEhUAAB_paAFisAABEGAF0fAiDAhBgAKLEy4AY_YLgroAU4LQFUshJgKjAAARBg9BYsPAbUAMBgJ9AQUELgDoJUCvCqyktAPLSGoaGhAAAUBgDMJQZGmCCzwKAwGgYAAAAJNFQf+XgAIwHQAABgIARBgNAwAEcC4Ad0lRwk0VGU9cXAHU0jyUIAAAIgotYkAAAwuXgM8Yr5FChhcZQxKwtAAx0dTTParI0cAACIMANiqEUKEqHAJQ_oZIFLF4FdaigRwDCMLKF4B1Bx6BHAAAiDCDgUI8ODDSUAq0sXhPU4MV8igDsYM4LQ_uhHUyz0jiVHAmAwALQAQiwhBQBMEoDLxcAyxiooBlBaAddgNRlZGAiCxAACAqSoIgqJhECGBwuATQuXhNTCRQCyY2LgDqYfzHzwEYAATIkAGwqEUKAmxkoJo8uCatjXMZFAqu6FaWg9DSYZ6yxKjgABFDgNABh8AhLgGAgAAAQkAAMMgAAAAAACgcAAEyBnFwNBUIiIADBxcA9hiAElRwKJlPSFwF02mkMShAAAuEgNBFCoEnwMSKABEoXhPa6RQel0VjDp9SH+ULwum06mWeixQI4AEwyoDnD4KK2CGAWgdTXiKEEMIScoXhlNk2czqSRmE6okcAogKoSAAPxFtHwf_RhKAtATMxDESo5_5CHAMwLQOp1Br6EgYqD5BMAIDEW8z4IcoEcABJQvAP8xUUABdlC8DadQUqgRyT_MmKiGyRoHcGXJ6UAy4QWhQEkTqMCkbAXADFUSWCEDKJ0ABV09gk9CDjBQAAEPKgAVMjQUn8eP_jwTUM38LgGNsRJIqFkgGXAHH9TBfAOMFAAA2Y0DEkaPlQWIIFsoXgMsYqKB4VgzgtA43X_jMfcRhlQcAAAB04AIjAFy4AULAARIAOHAAAAAAAAAAAAOtGgS0EHMlJKULwntdcGiRyWhhqIrSheCEgrRvNtZnp30SOGYMJgAAASGhchoKKEIPgWgKCYjMJEcFpVxmBaBxNoLxQgAAFGJ40ADkaGJAOgMJQvAQoxUUloArSheCG0m0BdoEcgjxrAAog6qQADTAV5oEYaAq6MATcqAE6IxFAGDFw9A2go1CAAja5AEUYrYNgIXowPR6hcAG6SI4LQC5lC8WhxNoTjQh6ADEzoBb8seAgjybM_7j4UkFKF5VGhHQX9AjzUSlEGWlC8ah0NoOXQI49GIaSqApdO4A4JSOzpOBw68HBJ4IwfAghISxlC8P9HRdfEjQwpphqKHC5WBcQh0hQwADBBwToNKf2IArlwcCqcEwEUrIJEoXjFUoVcxUUAygtAuufGoysjAEEmgAAKWC4KAE2jCBNHFwEVmIAiRHALoLQDScJmGdoQATQ_Q8APEuAcCxUhTVyICLKkoFsxFoMQwgQSI4BZjklW2LgGp1JIM5GABqAfgAxaJD0QCEWAHxQDAQAAAYeAOmGwAD0AB3hUAAABxFigCkkExQWEJUcBo5YvAXgwXyKGEMNRCiULw6lW2mWemESo4APQAgCAA6oESLFAFBQY7NHcDe5YvALpFCqOUXLYVEoXhpOptMoRQPIPQBmnFQH2tB55YAHHAMBRkCCAXAmAK5HwAd7KgAGmHQADvB4AKzMABFhrCqDDwYQAs5YvALpFAMIgUoXgHUE1oEcJ6fTqTRhDRsDRcBug4OBU4R4P2IUMA4ZQvAEJI0MqMlDB2DOS0C6mUrwjBdqIHUAHTXBLp4EQY1gsH7kIAtBMAPQQgAroADlDoAAAF8pAFpYAHDFAFAB0QJYH+C4PJzJi20iSwSgEEHodQxihBRMJpC0SUAIgwRRYCxoQAAYeZrmMAJJHQB5A158AAEJGABgtDcFAD0AYCkAJeTgAQqbAAE5Pj+ykAF2RgIIQgGsNBIIqKwBRQAU+aOwPpOwYFQgq4sTq6FykoEFhSNDtMdAxByJVGLVcLJRLpIEaGAkuII5MMqFKnNQioQQI9x2QzU2ghRJJdKJhQAmSwAWqyQKEAxJUHQRtUtl0sgEdAjhBAd+cPxaFxA9iNDCiSS6UTCgJMljwJMaxChk1VUWM6CCURS1XMNV_wpVFXqCUEamE8SlTmpFIJcQM8hQyLRSLXSiYR5oksOylBjQm5gZMbADS0EGlgRBnhDQEEBaJUAY6RgA_wXAAPCQgAH2EQNzY2AMBBsDgAAhFQALRCAAUZUAADY6AAAMBAI_PgctMCgMGwOAUgAABhCAHISkoAOIKCOgAADAQF3oXGgNrg0dWhjoA9SgK18AwECYGD_yMAAFUCqhrxCCSgC5PgAADAQBaL4R6RAMBAmBgqIExCoABAdARQABoE3loAAAwEAbQeAYCBMDA6FCAPEVAGqF4KqC0CSgZFfLQAABgIACRkGwJgAIcAgDBFhGAANoHx8joKqAATH+yUu5SAAAMBACuJgCQ0AgDArlCAAAD+6sAAAYEovS0AAAJbJ6+KgaBQOSSI4AA5D8eQylIT8KqTUCSkxJJCFKeAABMGABChBoyYNg4B+iMAAbWPmkHwVUAAmJJSYpAAATBgD6EwhBwE6EYAAHskD4ckfVUY6bASUmJJZMpAAAUBgAHlwaImAJDQB+iMAAbQPj5HQVUAAmP9kpdykAAAHWJgA40CsTBUhGAANrHzSD4KqAElJiSV3KRJAAASCTBsFQVKRgAD_iA_3mfBVTuZsBJSYkmfikchKAAARyTOKVOAJg+4jAAG0j5pB8FVAAJiSUWKw1AA4pUDs6O04BOrhb5MIQdtQ+AigBwxmB7pY+C7VT+5sBKSYkm9ikAACIGANgXAmyYQg7_xMDFF4JyAOToHkPbJ8FVJqBJkpMSSRJSngAAiBgNBWpMABDi1h4CKUkBjiUbqPnyHxRaqTUKLKSYknGCkAABoGAVGTE0DiMMKbEaGUkexZLgkg9TchPyLRaqTUdsiQ6LKSYkltilPAAA+DAH6J63Io2DxtFiI0MohGwuJpJGWHjcehFKIBRIopBaMTnLQAANgYKQ8np7GPHakfITUAaLQDAQJgYAC6KMqAB6BVDbqEBFk47AjVCAAAMBABMDAAJGhhzVaKqULwDthUBpSAzAtCunUFqoQAABgIAZBgTAwYjQgaetf+LgDthUBpSAzAtCunUFqoQAAABMaAQBggmhAKfKgDJhUBpDYRcFdOoKFQgAAAB68ASGgDuUIDLRcAdqKgNLoGY_8XBXTqCiUIAAAACXAEhoAL5GhhWS6lC8KKNRSBpML_VIb5QvBLXTqZZ6VBKjgAAAAS4AkNABfI0MKyXMoXhRRqKQNJhf6pDfKF4Ja6dTLPSoJUcAAAACXAEhoAL5GhhWS6lC8KKNRSBpML_VIb5QvBLXTqZZ6VBKjgABOzoASGikw4KCC+lquUcoXhRRqM0kVllsphKJxyheHGy3Eyz0bqJHAAAAJDRSYcFBBfS1XKOULwoo1GaSKyy2UwlE45QvDjZbiZZ6N1EjgAAAEhopMOCggvparlHKF4UUajNJFZZbKYSiccoXhxstxMs9G6iRwAAHQAkNFJhwUEF9LVco5QvCijUZpIrLLZTCUTjlC8ONluJlno3USOAAA7Ok5+A8FDECAI0MCyLUoXgApA0lEZgYJQvCunX_DMbIRhiAAHgoBCEv4MQUEqsGloZ5QvABSBpAX5QvConV5TMZgRgAMVGwDmHAYZMYDWRoZ_lWLJhSheACkDCYS1KQwSheBRcs7czKEUAulEfEtAB5EhoDkmMQADCC4AskVAUQvsXBITyXQw6EMQsgNuOgBAAw0MIEEKcrVVGZQvCijVX5IrCa+FgzmEov7KF4FW4mWeuDQI4xKNpAMgKGwZgQM8XABxoZQAIzeTixlQAC8qAggAHXiCsI+VhiAARoUi0KCEZFoSJQvABSQtXMZpAYJQvP+t1de07cwsAjGEAAMBwA1ZpFw4VBrhCAYmVAHZioqgH+i4ABkSEAAFkMNg6BaFBCMi0JEoXgApC_rmM0gMEoXltrr3HbmFOEZiRsAAABIaC0KCA91S2Y0oXhRRqC8kVhpVzHZTCUSJlC8ttdbG4dzLPaKAAE6A2a4ZQXIhQwObFwAKQwgDFKF4bQCHKETwiAAAFepsKzGIKCDUsnfKF4B2wqKCARYryMZgilZpJ17MzBFBEdAAGcWAHGpfCrAUEGtZRqULwDQJUUFbCxXl6wZwii2u0m6hyxGHHGQAAeAmVIahqDzEFBBqcNUtnzKF4A1FJQSqZpkxhFHtZpJ1ModGYiuQOgACpBdC_yFDJtHwX8oXh9Agk0w8KXgCGULwJp1CcyMBdABYFOQgsVwIItI6CglC8uoDtPIYAGrKF4V24g6NAjgiXLY9NIA0jJeTLJIsnBYvhi5ChgENKF4dQMCeQzaWUEVlC8w82bq7cQoojjoABaGYAOlhdC2KBDBqETKF4eQIJXTSAtSheW2unUfDMZ1RieEUpscnAAsu9F4P+IUMdsfBQSheHkCCC4YgBalC8DLcQSygRwGERFsoCuBIGZs5jQAYvAT5t1hYWgNxGhgzJaFoAKQNIDBKF4V377h3B3aEAByImAAkNBaFBAe6pbMaULwoo1BeSKw0a5jsphKJEyheW2utlcO5lntFAAABqVwBIaGUNeIQDFSoA7QVBhA_8XAALkQgAAADo2HpdXQgn1QIY6Ewb1UtpQvCijUUzGu2UwqxUKY3yheKbbXStO3Myz2igASUAEY08IvAQQaqaWK5uyheACkMNlAh5QvkNtLp1LU1T33qMF0AApjR0BnR2PJwbXvAEhpvI6AggKyHgAGw8AALiIAABpUAAAHyLgCQ0skXA9JWAqgf0RidhUBRMpRnoXAJTCXROC0AAAaAal4AkNAL3IQYsWhaAKQMF4STSC3jRmU0ynUG4oQAAAA4wfAe55DLSHXKF4AIskVhJMoFdKF5TS6basqx_tGhQdAAAASGgDRg+FViZ5DLSVV7lC8KKNRSEky13i6cN8oXlNLptqs9GSiRwAAHQADvBfFIBhkchBtDhlQAAxMoCfSJ4F02gjRCJ4RAAAGBGD4NTPIYbR85QvCyAOiRWEkumE8QXcsRiaVTaWT0iMH+FIAFFWeMHwnoBBq1j0i5WVUBS7dgzgDrC5ebaSrVYvm0FeoEfMSsAA1CmVABPMAC3gDZcASGgAAAAAAAAAAAa0nKCOm4T0e00bxsRcrCyA_CRWEksgLQmkk28AVhHqBHCoRDkykUB6ABIaYVNgnofRo3jVi5WVkBSEkwsAYjphcf4TiSbQV+hAAAABhoxyCbBPQKjZrHpFysrICkJIHTC4SsnEk2hcBGhhdMoD2C4m5sNGbkG2aQAMuAGDwBIaB0B6ArAeAOnHQAAWEgAAAALkABO4DNNADxP8FbwREC9zyGG0UCULwAUhJ4ozAMEoXn9E4qm0FroQf4GgAACQ0RRkKMYPgs5Cf+rSjaVXPlC8AFISTLXb6pxDyheE0um0qz36iMAAAfNgAEaZNIgM+eQw2kzSoA7YVBJAFo"
noncomputable def WL13_2 : ℕ := zfNat64 33245 "WgFEmR47AMoLQEPOntHTRnMrI3vF4AAoycAFlSOkCeBo0B+DBeAVv2XAFEmR47AD8I0cSkUACKZSKAEdIE4OgBa2BAlQkiQhw4BaH9AqsBcAVf9HwACQABkacAAEkSL2rnTW1oz2NnQAmLAMBATBgFWJADfLgCRYkAAqxIAA2yUAAAATMgEwYBViQA3y4AkWJAAKsSAANslAAAGAgAGHwA8uAJDQAAAAAAAAAAAAiBtNFwAACCYAE0JBJoqAAABsdAAAiBgAMswTAyEnIFIAV0uAAgjB8ACajwABM0YAAEwMBoAeDAAATKgN8LAYIOAC4HBgIYAhUxAAAoAoApVUIQUHEKAQgeA+FoElkJ5BYzAygJQAH9I0MAAO4MAA+qEIKA0DAAQLpdj4P4FwAAn4yAAGehAABuBiLAaFUIQUB4GBoxw_Ao+LLgCCOQMoF2JGYAH5EYAAO4MHoABUgFicUAUCEGAAAUTAAABgDgAECAACgBgAJGQfQeAPBgCoPABIKgAXREABFAAl4jAAAfBgEaDwCAUA2iIAXBcRQCjEwAE2MBcADokB2AADYGASAPHENGwFgVcRAEVKgCEhMRQAigAZEQgABQAwZ1MLC1IElqgGAgQgwbZKgCxlQAhDIAdkRgAGrnwAABgIAANUAwECEGAOpUAPQ+AMoAArkIAAKh8AARoGADStAqiYbgYDoMH_RYDiRg+AtALAAAAGEHykAAG4GAEAnAfCobgYDwMAFzmZCRUB_4eAAAPIGEDy0AAG4GD0BFkwRAx6iIE+LwAAAAAfySgDsxAeWgAARAwBACYQgYbpsDcGIAAjGNAAAEkP6MQPFIAAIQMAZEmHMGDId5KlmeYL4El15cAtCoHDBuBJBaKkBJAwr_TJ4AAcwYA5PMFKJkaBucFQFkAAkINB_peAAJIGE2ikAARoGKcnpyU1AIQYBgDwBSSoAy4fABRJKA_+1Ad1CAAAiDACIMCEGAYA8AUkqAMuHwAUSSgP_tQHdQgAAARBk+BwDaIkYFXy4Agj0AktcLFZJAtNNFE0Zw_JUcAACIMABNiAB1QIQcAHxFoa5UAaCPgApklAWkD1oQAAEQYABTEABpgRg4NJpQdDL0YuAPemwAcUSgpptBV6EAABEGL0AB1QBIWCYKCMHAAWRrlQBaA+ACOiUB_1qAzqEAAAgYUF8OBRidLAyi0AOuaNwHpJFq40SWFNtJRMpG0SOciAgAL0DIVQLhQHZciwaiheFF7GXAT0egaSQqeSo4FdoLdGbHQQAARhQAdFoGEOCGBEfA+gAPQOLpQZ1ElgG0MtmEYnAUAABYA1XgANMEwcDQmQlB1_4zXwLgDzhsAHFEoKabQVehAAAuDgQgiJ+aOwAcmSwu26Zg5lC8AGwcNwA4UlBTTaCq0IAAjQcABJiKNNHZrZapJWQEMmMDJQvABqTkrUlC1dqJLCjTTTK1OMpFAAI0HAWJYzL8dNzKOxRJZpKphNKULwBqxozpIUUWlQSo5ZJtN_iybyaZTfoEcAAjQcYODfgA5eAMOSJ4GVupYvABqBSaIFy7USWBJNvzlIy0UlAUAABQBXHh4CdJksNqVmYWgG0jYIoGUEoA2ggdCAAHoIGFB0CSLbbOZKGIJZQvAJqACv0SWUWm2kUKl_hm9YjABDioMoAAw4oArzA8BJDbI5iFeULwAahFOtpQtXaiSwJJtKJlFAjRyOhJAAoAo+Y0FbEoNozsqABqAHdEoDBD8C1UIAmjUAAD7wVFSG4KAKulH4njmKtKgABCVU9ajBTTqCTEIAA6LMAFwWEIKcCTAST9zBrCRlC8x8tA7Y4hgtAJIUXxDMCX0IBTPQABySw3BTwSILCG0ADJxkAEBkIABQB8AB6RWAWtvDTKYBgJvg8G2koAkgAAH5koACVhsAAFZKAAQnABD4AQbAIRYAAAAAAAAAAAAAkyV+QgJIbSQ6sQjZg64nCkAiMlAAGxQg2gEjUIHkUICSG0S6qWyfjECDEiOABT0SWtxGA2hsxGDaTeXgooWEPLNQIYOCSo4bRTC1XACLWQBa4ZKjmEINNwAxQI4YQuh69GCkpjQAYnADDYBCLAAAAAAAAAAAC1ABCcADPgBBsAiFgAAAAAAAAAABAw4SN3MCLjcDf396AGZYIwofQ8AE0FaVAH_j4AM5JQFmm4E2oQHQAzREB6Y0KSa7I0dhdJIryheAD0rxMMRtaMLTOoksewwflI9NpNMpFA6AAhGD4AIBrMzKLY0DFzR2GEEeULwAelEYh2YuM6iSyrKQ0hl+ajEkOgAADI2DISwbDSjxYNIGwCoyYAHoAFTinwACujoAAwgCQpg7gcEwsuMaC3B0F0GuVAAB_pWAAwlkRzUkZSMIdAAKAIBfFhEHkvjQIUomDcIpFEOULwAegtEMo0sWmdRJZKR6bSaZRAJUcwh6ZUpjUAwEwb+7OgOwWMwuh9yheAD0A_8RZ0SgAKHoRtKvICYBrhcvAAINYMHFHOH4DELobUoXgA9CCBECxHnRKAigAfQI__YIqykwhgMuI+bFw6zRvJQQgYNxcC5bCulC8AqPR6TQmBcCEJSVHKIFksJ1EaGcZiEQGDECcnZ0pA0icFpNiEFcASEgGAqADwEEBXREADEACSABbQ2AACnPwQDJFAFB1DgGIDsyoKUCw9HoA_gUP0UADeiEAB6EiBmbG0ENAQ+jB58DY5wDAQIQYKmNQA6iYAel0ASYHAAANjoAAAwEAGJKAYCBCDBbBCCag9LgDp_caAEmBwAATNGAAAMBBqAC0IAIXADCoAkNAAAAAAAAAAAAANlwAwqRoOAUSTAWbLgpJQmbGSQADzREADuTgACNBwOgAhaC4GIIZAAbQIFQfzGgRaEANCGgAAKR8AAC4GALgYgR8G0EoOUMwtCq0zYiSBpAA5TcAFVCAABcDAAFRgBpkAMLgAYsAMEgAAAAAAAAAAAAGy4GQYFY8CqUoBIhcH_1Yf0lAAAAA8UgZMHAABRaoLgYcA8GpUYBpxUAf4Rg_8DAOQAG4HwAALhIAEJcAmKgiBgGEJE8DKLQhmhACZsfSEoAKAAALpSAAHMlADOEgmBhwDwAX4ZiqlQD0GYD8wMBRAAakpAAaYJgAQlwI0qC4GAhklByBm_8XANEZsZJACgAAC6UgDoC1koGRkFmZklvQAxnESDAA_s2Nshy4IzYXooksACelC8A_yZB5UYAARIMABIyANlQPD8AAAomAAOoQAAAAHloAAGwUAAkZAcypVl+BFSZLLDHhmFoVWmLESQugB8BuAEhLlIAAQYUAAEyA6lQDAST30GF0khdMpdyheE1+apTMJqUSWF0ALptAEkxE4AAQYUAAyyCAlbDkV9CXiUBlFoBsGbH0hKMpdADqACbFIAAQYUFJTA1N6AEkYA2VHfCwTcMgqnpC4D_7FnhKAAAAA2hAAEaCgANlQBISG4KgoLBNwyCqHnKgAFKMAAAADpSAAAANlQBIaTLFgijEKsekIkpQvCkgOZsdJAAAAmClAAAAfaoQgpeI8APESWVEGuULwKPMRJAB6KQAFQoQAANgoAGV0IQVHEeCKLQouFPIZpyheAYckJQGmWgFEwgGvTgAAbBRWgHhCA_1QBjBkFELQVAAJkZhwsLQKAAAaU+AACEFABGLhJCkjDiMIonjZmFEgifKF4UkwjsTJYAUAABbScAAEkKAAMVAciYoArHB8BJAdK1M88XFhLbsRJBD8oGAASH0DLKQAAbgoAnBUUAVKo+AsgQPB6JT4lC8ByYfOJQGQkgAkMpVDzKQAAkQoIycxJZ0ZMz+nJwAFVAQgwNDMgF_FwBUBKADFZUB1AQWhAAARBgABVQIgwIQYGhmQC_i4AqAlABisqA6gILQgAAARBiTBQcZMg5MjC0A1zESQAlIFscO89BWqEAABEGABqvAiDDEEIGzMKJFO+ULwpJhooO9WgbKUKwOM9CdyMAABEGAHMXAH6oEQYCjMxMpht_o1G9KF4TSyYWxoksC6ABpBoLBTgAAIgwAEhoIU+BNpkAQ0qAH9JQASXKg_05AF3QgAAACQ0qmfBMQ4vkRlYlC8sJyJi_yiSxui8BKQOM9BG6EAAAWghPwGIcaC2koXha2KkkTXMdFC6VQOlXKFYXTjPQfSiS_eMQAAEI9AYnYHJoSE4UoXhSRPrmOigAZFOIGINM9A06BHcs9YYYgD_hEDs7Ok9+AEhoLUSCYg85GhsDKF4UkwiKSo4QayBUID8pKidZ6DTEqOAAABnrgN9EFwUAEIyDaAYJgB4qEABBAATAfAAAuCgA2LwpBQB16hozCgh5KF4Ekw0UBJZN8E0YDRmCU4z0mg2EqOAAFIKD8XYHgEWeQw2mqi4As8lZSLgDT5UBx_+fAoNCAAMEbA6EPA+hCfhtGBlC8qp1JiouUiIAFJ_UycQ2c56GjEYKiAV8WBkaoHgZ6eQw2i6SheVUMIREqODzFoJSZAimJ1noSYRhfxEAAKRCBIRYwfBtSE_DaM1KF5VTqDFRQAZQ0KQNv_T4MnIwUQC_RMAOowfBkSE_DaOTKF5VT_jFRQCfQ8l4qVkxOM9DmKNZhWKIBHQmA8B0Z0tAUPn4bWxKFdrBcrKqGGigvSpqWSuA8j4qVjmYnGeg+pKjlEAAgQDBxGaMYPgmZAflpHPFysKp5piooAGRSSZjaZ6BpUCOZUOKU8AGMQJwFIWCgNAMA+ADcVAAv0IADvFQAAUj4AABBHKMHwRYfPw2jJC5WVU6gxUUAjIpCqrVPQKugRwgNmsMICwUieAFIaBBBQW40HT_ykNXJtQk0qAAVowAAGkAHSkBBANovAAhGmiGuLDxJFcID8q2kd+ULwqgm1zHRQDIg8KQOM9D_KMBdAqcnA6gwMCBOmoKMYPg7BCfltDMFysqowZiooxADItJoANCRoZxKN6lYCvZMFoFSdcwwfPnKwNDh+XTSJCLlZtLJXS5I0ckgGaGC4ppoT0DOoEc2k0AGYQJxFnR0bMwQIbCaa4EQaDBEBBAaYTAAEj4A_8RAAEGDoAACIMU9_Ok4aAh9La24ELtgGAgQgwDAGgAAtg8XQAExMQgAAbHQAABgIAExMARDgRBgQgwABWi4Ac7OLgk0VEtACyAqFIAAABuTAQgwABWi4Ac7OLgk0VEtACyAqFIAACIMAAUqABkwIgwcQoAhFSsA05cAOdkFwHEloAQnTeYQo8nAAARBgA+HQAKqBEGDYFAuQ2AAQTAAFCYAAP_CwAtDoAACIMAYweBEGDYFA6Q2ASAVAFYjoASjkD_BEAtZaAAAiDABrJgCQ0BgFAxQ2AAAAAD+hEAkGIDy0AAAAhLgqJMjQcA_o+AAPWiwAJQAQgYWMKQABGg4A0ZMHIUBuQ+AAIqFTDr9ZkKQAQhmJmdKpAAA5CgDok4OBWiiIE4Gj8GoIoyAivdi4BiJR6RSQiE7+MGzCgROngAQaCgnJ50fLSUBAWwIgwIQYC4GQERS4AcpuRIYB_UIFmkAshZAgnAAARBgAQEwAEOBEGA0DBCQMpbDoABIVAAAf6WgBYrAAARBgBdH"
noncomputable def WL13_3 : ℕ := zfNat64 15289 "BMaAAAAAAAAAAAAASGgAAAAAAAAAAAAC0YBEVAAAAAAAAAAAAANlQBIWAAAAAAAAAAAAAPMgCQsAAAAAAAAAAAABgIAWYcAV0uADNhwACzDgAIDJQAABgIAAAAAAAAAAAAACQ0AWDAAAxLgACIUIuCgSAAAdZKAAAAAlYOC0+RYAAGJcAARCgQquEh4AAD5koACDgsAAxaD8KDUHAEQAxlQBGYSAAk4kAAI1CAAB+FAFIkAAAxLgACIVq8qDIAABAZKAAEGJABJJkaDg_cfEgHgATFwABQOOCJwAAUQM6nAAEaDgAQrwCQmCsKADIVAFIMgAF4cAAAOQm2lAAArCgG4OPmNA+E+DaIdKgABwUACkAALDQGpCAADcHAAErgeClHFwMHPj_TcGrKgALgcAAB9AB4pAAAeCgBIkwfhR9RoCyG0NaVAAHQ4JlGQAC0AYikAAD8KCUnv78xAEo8H4UJUOAuAcAAB4gv4AAAYQ+jwTgAAfhQAE2ID8OAGQcAPIyAEkEABW6RPABE5FpWmiSwADEhwCaaYBgIDwUApQ4BphMAAAE0ACDB0AADYKAaxYJuEwLQ4AjhcAABSo+U2lAAaXZIwAALQoAEK8AMKghDgAABRMAAAug6A4xAAAAANgoEaDhCA1D7NHOKid8YuANAKwAWiSgDSf+aqzIwAAPwov7+HAKiUAIKgiDgwhwANSuxkHvg4ygAUYqJQAAbUIAAH4UFaCPgCFSKAOAJcTAAxKgAVB0AA6xoAANSEAAKAOAAOtB+FDJEgAIrJy4BAqxfHoALRyjQAEBkoAAH4UAbBQbA4AO0MQCCYAJcZAAUoaAABsdAAA2CgRoSEqHAdpCAI4XACjD4AEKjwAAj0IADFhcARBQlQ4BdnkMC7iQuAQcvD0AHejiMIr_piB3CMAAYQ+AHgokhJiYviEAgAuAJMHwAQFHgAChoQH7FYB5jwAHl4LgoDlCEHkuzALgIh1I+AC3I8EVAPChAFUB6jwB+FCRHEYAUQn4apo5gtCiA9ABoo4jDjIsAc9CAKoD1Hi_uRcXvQBaVB+FBsDgACllQHkmIAOJVAAAWKwAAPwohQEOTB+FCVDgA7QxAGOmLuh8AD0AOoJOUgAAfhQABV4LgoBJCMEkWUXAA9ABwpcGDhIsgm9CAABcFAEQcRQeA8CEAREqAKkHwAJFLgP8KwF_QgLHCwABEFOWHgZQgRw0lGi4AWS8PQAOOWMwCJZCNCMBJ4yAAPwqsI8BBLSCReWiWLwCfxo7JiE0griMl5JQiVZye6Ro5LSo0EIiOIwXF78jK725AAyUAtKgMBgPBQAA5koA2g0AAAACbUAAAwGAcAJDQH4cABzMuAKoDzx+D9DgSAAAdZKAAAAJDQIocABzMuAKoDzx+H6QoAAA6yUAAA6AA14AaVAAFI0IuA_mpYHPgAB0JAAAHQk6JQAAAghwZWEgLvFwED1CuPQAl8NAG0DRIydEoAAAFY8CCHAAczLgCqA88fg4IKAEgAIwTrCqwABCgIIcBsCoC7xcApVQrj0AKTLQH9FoBzIydEoAAAMRIAC7xcC_CpTqhXHoFJMGqwAf4Um8Iyuk4AAhZ+_ACQ0CKHAAczLgCqA88fgnAIHgAAHWSgAAHR0ADrQliQhw4AB7LouAjsrU56AOoEgAAR6EAAEkSALhIBqTQMPKi4PIHdOTnMqFcegBeQ2AAIsjAAAuEgEkSCyHAh5KAlsXARwVqf_T4AAC8CcAPFIAAJIkABIaAkDgFchACaJgArB0AB5A_0nAKY6AAABtEggokTwMItEMIUOclEAxw_AHIhMIQkByZLGoPlZhKJLdUeQwACFIzkCMJwHYcGmjIOkEQASQWIwBVAISoRSAJKNY4+AAAAdNGALLoQgmQZAQMLgNpt0+AD+BcAAVVC_0nAAMAWATkSAYgsw4fnpKF4VTaUXRHD8CsgDSxeABQoylkAyiS3VHkMAAObcLAM5UA6mkSIg+CwAAECoABAdAAAAAeWgADiABsOKAaDYJAB2hiSoXAVGyZ8AAAYQB4pAABfVgAJDQGAkBZCVTV4QuAUYrUx6AOGHhiANQYcjAFUCGpQLgBIaAwEgIIF0cpQvCirSVqc9AGrHD8B6YsAmVGAqIIKTi9gZ0AAlQwkivZA8AsSxmALQAoK1NfB8_AAiKWZJQAbARraSQAlZIrAGwnAAT4BmVT8TEyGg_wRAAG1mysAAJQACsIX5nIAE_EwAoioACTBcRBAGgEIAAfheAA_kfAAEcXgAAXEQCxYABKoHJFfKh4GCkisAWk0NqpVJlB87AAU_+SgAOyKRjiAASSRWW87ekUkwEETIP9kV_y4B0yhXHpF9IVBRTeEwAAA0SWZQAbKTABXJgYxoEcpD0lMht6XAFUAp4_IoEtB6IQsg_JOllfYM4AMjJgBQEybkRdxoP+HQAAc5WPsfSoRgJaEUCyB_FL3i8AAFIB2NAWwWAFoBRJkeOwDKC0BDzp7R00ZzKyN7xeAAKMnABZUjpAngaNAfgwXgFb9lwBRJkeOwA_CNHEpFAAimUigBH"
noncomputable def WL13s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL13_0) (dpk j 1 WL13_1)
noncomputable def WL13s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL13_2) (dpk j 3 WL13_3)
noncomputable def WL13s0_4 (j : ℕ) : ℕ := dsel j 2 (WL13s0_2 j) (WL13s2_4 j)
noncomputable def WL13 (j : ℕ) : ℕ := (WL13s0_4 j)
noncomputable def WD13 : ℕ → ℕ := rdw WL13
noncomputable def ready13_cuts0 : List (ℕ × St × ℕ) := []

theorem ready13_cuts0_ok : CutsOk ready13_cuts0 := cutsOk_nil

noncomputable def ready13_0_state : St := ⟨26112, 203904, 28545, 39936, 52016, 92445, 53248, 93677, 29666, 44151, 52016, 79534, 28545, 171456, 26112, 203904, 54657, 243840, 106673, 324894, 159921, 378142, 189587, 407808, 241603, 485823, 270148, 532466, 296260, 558578, 80561, 120990, 133809, 174238, 163475, 203904, 215491, 281919, 244036, 453375, 270148, 532466, 105264, 145693, 134930, 175359, 186946, 241983, 215491, 413439, 241603, 503921, 82914, 123343, 134930, 189967, 163475, 361423, 189587, 451905, 81682, 109200, 110227, 280656, 136339, 398657, 80561, 250990, 106673, 368991, 54657, 316975, 0⟩

theorem ready13_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD13 ready13_cuts0 110 145) ready13_0_state = 46694 := by decide +kernel
#print axioms ready13_0_cursor

theorem ready13_0_covered : Covered (toCl ready13_0_state) :=
  ready_cover_cursor WD13 ready13_cuts0 ready13_cuts0_ok 110 145 46694 ready13_0_state ready13_0_cursor (by decide)
#print axioms ready13_0_covered

noncomputable def ready13_cuts1 : List (ℕ × St × ℕ) := (145, ready13_0_state, 46694) :: ready13_cuts0

theorem ready13_cuts1_ok : CutsOk ready13_cuts1 := cutsOk_cons ready13_0_covered ready13_cuts0_ok
#print axioms ready13_cuts1_ok

noncomputable def ready13_1_state : St := ⟨26112, 317920, 28545, 39936, 52016, 162091, 53248, 163323, 29666, 44151, 52016, 162091, 28545, 155038, 26112, 317920, 54657, 346465, 106673, 453518, 159921, 506766, 189587, 536432, 296640, 588448, 325185, 616993, 351297, 643105, 80561, 190636, 133809, 243884, 163475, 273550, 270528, 325566, 299073, 480604, 325185, 616993, 105264, 215339, 134930, 245005, 241983, 297021, 270528, 452059, 296640, 588448, 82914, 192989, 134930, 245005, 163475, 400043, 189587, 536432, 81682, 191757, 110227, 251205, 136339, 483184, 80561, 207054, 106673, 453518, 54657, 346465, 0⟩

theorem ready13_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD13 ready13_cuts1 113 52173) ready13_1_state = 96973 := by decide +kernel
#print axioms ready13_1_cursor

theorem ready13_1_covered : Covered (toCl ready13_1_state) :=
  ready_cover_cursor WD13 ready13_cuts1 ready13_cuts1_ok 113 52173 96973 ready13_1_state ready13_1_cursor (by decide)
#print axioms ready13_1_covered

noncomputable def ready13_cuts2 : List (ℕ × St × ℕ) := (52173, ready13_1_state, 96973) :: ready13_cuts1

theorem ready13_cuts2_ok : CutsOk ready13_cuts2 := cutsOk_cons ready13_1_covered ready13_cuts1_ok
#print axioms ready13_cuts2_ok

theorem ready13_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD13 ready13_cuts2 128 1) (ofCl (RC 0 0 1 1 0 1 0 0) 0) = 113674 := by decide +kernel
#print axioms ready13_parent_cursor

theorem rc13 : Covered (RC 0 0 1 1 0 1 0 0) :=
  rcOfC WD13 ready13_cuts2 ready13_cuts2_ok 113674 ready13_parent_cursor (by decide)
#print axioms rc13
noncomputable def WL14_0 : ℕ := zfNat64 33246 "4xLglIyBeHIEGknE28jAAFShgNAp6cNwMABc2BTpI6AAACjiw+AAgDjPhnwsAALCgAfpwmM+IkGAWobApAEcNwP8CRF44jABNAAMtOM90uhDPhYAAWFFuCEE4iQbNx0ABNumbACkC7YQcs0bwKpVUM5D1UIAADoUALZOAJGQA8uAAaNgAAA_s7A9JuAAAAAOhQA104EwYADR0AAAH9nYJFNwAAbEIAADoUAWhOCAlwJgw1PyEQBEjiPpc2AFIB1mUzBxAYz00gM0IAADoUBtSCKk4iQayBMABNuubACkCjYQVI2aywlUqv8bgIqBHAAcKhAI1TiJBshEwAK_SJ90zYAUgUbCB4GzWBVKoRlQikkUCtycAV1OAlCw3AwAC8k5HBsAATTqGTGzmFEq_0VgNChB1AFoBQAglFOIkGVkQJwYvVLgJo1AFMIS4KNhNgvWwylhKpVNtVYMjQwyz2khRDmMHwbgScABpwARKAFHwAI6AQlwAAAAAAAAAAAAAK8FqvhqZcNwMKQAgdBBg+AAA8gAHT_T0FBuqwtAAAdCgNjcMvgTcBCZwBIOGMGBExEtsqA_UbAH6jYP+lQWKMgIIBPUIAAAAEDESDA74mrMXADUL6DUJSF6jIKCU1KAsqEAAhAABZwBIaAPwiAcRABeLgALxcAATioAAChsAAAB1zgImIlXlQA1ABqH_SoMjGQEEAxKEAARoSAAeNANYTGRLF4UltJg3C8hFzBuEpBsJYzCg0m2z4RqKJQABeImASmRLF4UlQxszC8jKzBvZo2JSDnyxmFBpNtAcoEcAi5jACXhkADCy2oaCrRQzWkXADUAGvwNQlILfLGclCCUQbyhAAAuEgAAswMrODOnwByEw2AAPoTQBXChLFzDQAQ6jAEIAAUAsAAw+AHmQBIaAAAAAAAAAAAAIm2gWsKtKFQFZAAP+OwSdHpyxBoAAZIQAALhIALOcC3RUacmAgglABhD_TsEkAACCdAAAGAgNQm7ARALQDPKU8LqGUJJdAd6xfkpqpQriGWq4WIRmEKwAAKmSJw6BhyheGXkomgcR6DNjBoKhbAskJMgmlU2_6UmxoEcqgAeckVg6AAWYAVnAEjIAiKAhVOiVAFEANIHUNgLwE0AtaEAAC4SI0FB4kvj6kAc2RgiwACNF8MC4BWZg3A8k3zBuEpBKxkvHIQSqbQn6BHAAI0JFTOh46Jy4CoLgCQ0AomlKgAInAVNfhTxsAAPy4JyaTcgAAACVFxVZo7CiNcsXgTUcmjclt9Js1ZxqEpltdmIbZzIbjPRXJ0v3gMAAANQuASTQ2B0FHuBcFJGoLb7KBq9cbBKQT4Ze0JjaOZDcQAA_0xAFxLl4JvqHQUXwli8LSJ0sagtvppHGYNwySkLrRDINo5kNxHv6E4AJrCwWYEYLmTjoKuiU__lwUlmhw3BaeTSUcwbhKQu5wMg2jkPI9DkCwAAAyy4LQcygLgBqC3tz0DUBqACSxmH0ki0GMIwxIYNpZCRZcTIDnLigJi3nQUekFwcpSpqS2+sQapqEpBQBkG2cyE4gAAKAmAXIXBbZv_UIBRKQHCoAD5kAAfMgAAiAAJ1YshEA_6hA7OzI7OgBIWIkG6yNB4ouAeSYNz8acDyTBuFEcgjIyXhpKpVCvCMAAAA4zv6Eh_iwMPKgBqADUByERS4CqAeFCAABcFAAJGg_xg2TVi5QvAzCJLmJTTyC2NmYTYIHTcJaGkqlU20EC6BHAIAAAAhoNUYNk1YuULwsMlTEpp5AmGzMJo5ANhkvDSVSqbQqCNHQIAABwF4DBnAg6J8sqCKWQqDr_xGAAelRAe+bAAF_PiSDwAAPiLRUGq_SheGUaQeOym+geiYjOkaXNQloZTWKFcqmkIqgR3_MQADEGcxQ2f_Nl7lC8soiw+dlN809ExKS1M0dhLeWJRpKpVtIGlAjlBCknlTYAYecDkNA5sqA+yfAHqjYAE7lwE0AtiEVwmAAAERkDClC8ag1C7D52f7TgQwbMwmjkJaUUbiqVQ90jKkNikgKWHgZAT8AJDQXowbJqxcoXgZhElzEpp5BbGzMJrxDpuEtDSVSqbaCB9AjgABOzpAY4jdKKFyYvCLlZVnpFGJTTzVtiEAbMwizGgmpVhbQTCUSraR3yNDNpRKJBA25QvAFVFI0RUqGgalrLF4DUZ5g3A+g5EiOFEB1xYzDKUSicT1KMAESIY9ICYQAIucBWFgWFgFhlQH_DY_ujB_w2CiBuIyAogFTQg0zH+40ADMqAAc4A_XBcJGyFgWSVAf+NgD_xsAFEi4DCBEtCAakUADU1A0XA5ZQvASIbMwBIhszAAWgP9QrgJKRoZJGjmZSiARBKlgAhxnABoDllC8BIhszAEiGzMzAnDkBafQqgP5QgylECeqUWYDvYinxYEMlQFjjYASMbMyaAAHMGZlACGiEUczMxRApIlAFI4jQYLE56QHKF5tAAZgzKaExpJAMyL2qxHyhfXSmgHYRoZVMJRKphAYJ0swSmBG50dKZsIkGAij2Ll4Ul15g3A8hUzBuEpA5RYzAg_xSjaHcSo4AAHQYDScAn5wd4uIkGEINaGlwUlRRo7A8m0ahKQwgSRyMiaPY99+nAAAdBhDQzc9oQVNfAMBDEFgV8RAf+LgD_xcAAxAABcbAAAGAivJYEACrwASiHUGAiOXA0mhTxg+ABnMG5QaqBITR2Vmw1VAlFPaJHAAAMBAAJDReg0bJS7wuViCVzGSZiAL_GD5YaqFvR4tthqoHZRJYAAAAEyKgGjZKUElC8MI_8wbgDCxoMNVCVQ8NTLYQErIw6IyAACV8w0bJS5wuVhhsylTEAu0RFhqoewJioNxtsIURuiJLKwEwABSNDDQMhKF8EAYGzFfJiAWnGiwgCbGD4d5YgJIoQcbKAKcMJg2AxFJE8aJTvouHJhlqlDX_xcgQAWgeuTgml2ohpYgkRwAAVhQA+VJxguNEpo8XBhLaGwgQPbJwtADYkTwml2ognNCAADcFACFVgB6kigCLKhci8GUNhAgAhAhIrBFLIBNEIAANwUB4eAHOJvQaBEpQvHJhDVGzMuoSHKgsgKsHhb_piKIA70IAAchMABziAJCwd4wbJS5ouVjkwkxLrKBiK8lQWSaC8h4WmEogE8RgAAAAnEAC0gAUsAGKGwf4XKxydxYvgxAZuHcJSFkmhwoejwXGEogZmRgcgB4hYGwAkZAASIV1LKniwPyJgOtFwAJQA5qPAAPKNgAIkjQNjYADVg0WkABqgBwCICkCUADkABiFQAAFyIAAAwENGEQYkJ+DUKBcrC6IIMmYdQ7OVE2w1UDHlC8NthAY8jDKiYAAcIinoaUwbgiLlYXQo5gzDqH6SosNVBKZQvDbYQLGIwbQDBxMDYAvVgTE0OtKPgYeVFZl4GoA7EqACf58AApZChoAC0AOoN9hAfJAhPxdBszlIXQYy24mG0CcKQqVkmw1UEyFy8s2mu1UGuJEqGgB5lIAsVEwUEJ+F4MG8pCyDEuIBwJFYYQEwmjsNphAPmgRw24tYgNrhiRGSc7GlNyAAVYjrXA0HMODgbIPAdKJgASgAKQAHeFQAAFgYBBCcUmNABc2KzWVGNWHyBOILSWx0IhpQTkAlyEAABYGAOwpAaR1HZUVkB+cP9WHyBtsiVYJbWQUGkTwm2UBEKEAABYGDcDQaQByxME06YlAA5AAVREAAC42AAAMBAASVhfVcvgdAv4iA_8XAH_i4AAACHhsAAAYCAP4RAjnkMmpbi5WW0PKlOS+ID+6mViqhXCkzWUhFCiNYyeQ+6ZTAAAqDAaGeQz_xlOkoXhhCIGzPVh8dQGoWQJzHQYSyD0chB6EABr4aAbA+BzZUAQdWH30WKoj0C6FNXUoTwLoZRQCEAAKAOAa88hgxbwXKwwkx1YfXE1jEGEqtF_yfMBRJYBDDVaSZY6p9AjgADbKgAHCwhJ5DBjFQuVhhEGGzPVh9cQfMQYSqhTQCGGq__SjLHURoEcAACAkAAKWEEGLKi5WKMWMYcgyZ6sPgDCARXTgMIGUKjqRoYYS6XQWGMHwbACSsL7ll8joGAEQAtACyAAABD42AA88VE3NgAxWADGQAkqAJCwAAAAAAAAAAAEVcZ5DB6Ks4fkjFjGTEfi4dwMoaTCBxC6WTAzZzL4IwACOEoR4SmeQwej0MIAg2Z6sPhpO3MwhlADPt3MHIMJZKpxCKTkAKJNgBIyFtPIYPRCID8KIJI2Zw2wgL1gzhZKIHCbOZ9IJBoJhM2IxOQKpIFGBckSWPRQ5w_YycPwogxLCa+LgwsGcelUBITdvMM9IIBe0COVZyANdRI5UgPDGXULHQGONgF4FwAvBaABuTMAAC42AADybAPswBppAJhZkxCB6hI8hhRACmDcsIcaagsgNmcggkENINNCGgLE0A_0DAHeCi5kJ+D1eZw_C6DAOG5YQdY3BZJoA0cggkEgmUYenHEIhzLQAqDcCBihILTFJkHwATTgYhqw+OoKsZgACG3AAAABCyYAdossshE9GKePyQkx1Yfe+as4BEas4YaqAcHbmFBAJ+hAMaD6diAGQA+xJnnkMHr0Th+bSiDEM2E2oXGUZsYh_upAMvaN4PSCAtZGhhxMJbQFB03A9HoPUvHzspoMSwnkypsLBnAA6zdrJLDjqegAsRoatFS2ba6AI4wbmCABFYsJCfg9fEfOyiUQY2WwgtcGwZ4q0FQrgH4btYPSCAlZGhhxMJbaKjw2blnNyoASVhNVcmsdAnIuA36XAG_VoADKAA3g2AAA6JBOAElYPnlAPHQAaLgDCAGEABGMwAALjYAADokWsDFgoOA0IASVhM1cF5DAm4iAHoAPQA_shAANyNgAADARTgsbcg4AC6gaesAsMgAJP_C8pIaAlRMAOQDKOQAAAATqwAABgIBW9cDolWsWBZxEBLQCWgAAAPgNgAAKgwBS9YBWZAAh5JNsPAUQiAJoATQAAAATqwAAEwYAtple44jv+NEpTaUL6KYSTMTabazoxOH6SKyi02iiYSRWUUo0EKaAABMGA8CftQILKABUwcA0eQVpUGwXgDKBDNoFBHoB_c6moAK1QgAAKgwAAPMOs1gAVm35FZUyCtBkC0AAYgAHwyAABWZAAAbCg2c+3cZAVAHlJQAxomHoByw6moAIKQgAA3BwAAeINUROEUL1UDiMyjn+ahXDaFUUJYABoiHpNAJqURqAkFWAAFAHAAB6gMWsABskMToHfpwH_k44ge7Nh6ARlNpqABjD4AADYUAvtm95QthJD2LU5pIARKl2Wqn6lauNR6QQDbHDf65ovIJNLKJ9QI4AEHA4AAMNUIoWwgHD8yqMcqjOSaEmy1UIIqjhvNSCAsI4bi0g0H9J1ZSqqEAAGwiBJFauPdHMwIxSphNEeoksBDSENRqBxjYGopAADCFDtNNJoA50SWDo7JoYABQgCBkAMKgAY0ANFgAAAAAAAAAABeh5CFxMyilILUgniyNEQLzzFgh2TAdVLgBtI4jACOgATzOgAAXAwUnd3gjsCfk5OO04KAjobHh5PDxIa"
noncomputable def WL14_1 : ℕ := zfNat64 33234 "nVgNoCti4DZmpwxcEIWBEDAIMqAJ4RABPCIAF2CwAAjUIAAIQsAARmATTVFwCMCIP+JwjAiAAwwsAAD9COQTAAABlZgAM0mwsACUqAWsRAC1iIAF4D38k4AClIRdAAagsDoALZgAZ8IQsBhAB5EQR6TgeREANAAAEahAABCFgACMwAMrBoaAwuXLgIGEQE0gwMIgAIIIHj_BUgQAACDg0AAJmABlwhCwGGohcBugiAmm6CIDSDViBOEE4mEIPIwAAQhYpa_DAAhcABKVAB4IgAPBEAFMlIDIAHIJgAAAFFwBi5cAyoiAmkFlREDUAMCpfAAq90SjkEwAAAXS5XBmDiF0uAAcGhDUAAB6FUIo+k45BMAAAsKAd0JSCIC0PRqi4AxxEH_k4McRAAAAHHQh6ABSCIAA6cAQQgBZ0ASGgAAAAAAAAASGAAAGMaLIO4LgCVmjctNRNJKzRuB+NgsGX_CoFoABFkYAAMY0AxjQPXUkDFwHIzYKiaeRmxWw2AAABHoQAAYxojbUAE4QZ5sCjS4AxxEBNDHEQAQdOYAfQAFaNFYqAAACYXLCEQAAKiIP9JwCoiACRDMH0ALApRWKgAANAAhcAg0XAYUJgLP_E7ChMCqHIAyH0wgE7QorFQAAAAUIACfAGS4ACTAEhoAAAAAAAAAAAAHkuHqai4hlKgAJz_UqAAA+lhNiKwPFKKxUAAQsLX2JiH8VAFkLgDJEQAZIiAAohdABloUNAAfxUB_FRsW4BLlQBYiIALERAAUQu0EAVKFDQAH8VABpLlPKjyFwBkMgAKSAYQHlLQXQKTApOhoAFPKgNDQAkXEiVAMbLgDtEQE0O0RBhAakwZwugFm3iUAAJEqAaGXDIppFAAgTAA2HgAGw8AAAAAAEUHQFIXKeVByZMZcS+lwAE5lIABIFoLpYQ4qhXIaABTyohYWdHcMFN7eHiYGPnQCcrhuBtpHQMNKgP_FQB_4qCyATQAE0IQAAHQYACTEAiKgOzYAMGwAABGEgAB8RAAAAAHQYARxUDANVZ2AShsAH_UYAqIAB1joq1KLwpAAAdBgAJDQOJ0BISoBIJEAJBIgAg8dB_JiALuhAAAAZl4bgoB4xcG0ceRAVAlB87CCWQy2YOwwmUCNyMAAG4KAAkNIPHwfaLg0ijjx2fsFiaZIIggyOWgHIGUBnyMAAAAHGiIkJ+TEipQvHHsmsHJFabQfhkQQSqDVfpo7C6YS7QZ61pKjmEAAbIHv_nwbYLgH5nD8A4yRAA7DIY7IXgAlihHUugHIB4nZ2_nQPDpAwDf+OgW4TAVNMgCppkAA1CIAAGJsAAB0GDklAFhUAwEIE2AAA0LAAGhYAAAAAAAMBAKNQHB6NgB8TAABjA4AARaUAADY6AAA6DACCcP1eCBcb6XAAlAKgWRZp0VUNITRu6hTWolRwAAOgwAEgpGhKJh8BDi4AIgkAGQCFh0C6VLYAFFwCMAAAASEkaEstHwHfLgAAMgx5aP7HQLpUtgAUXuowAAAKtaADVyNCTjzoA_GwAAGgHEYXQKcKwbSmgXNCAAg4HAALrgGAhWmwBOJgB6EwASQAFalAAA8NgAALBQAnipGhLV7cBQC4DLf9OAAKoDGVYLp5Ep7JSAAAWhwBWnD8K0FwAM0SWAuIeEIXS6BVpAZBtBrac8JGAAg4HC1Isio+dggMsXgAzRJYD0Bg+IbDWQBRK1M4_6ajSFNDOiRwAIOBwU0oEqWkaEiunD8FJGwA5AfYQHzKF0BMixXAAowWRgAIOBwCunD8MtF2UCINLPk6WE+kYqoXQAvqlc_g3FNCjaRGAAg4HA3A0b84fhxwuKoaVmJksCKGiXK4XQNWKwBNCjFZGscLAACzw03Q+dgLSrPTSBhOlhGtCLwVVU_2sXwCqG0ppAxSn8dRi6AD5BIHUE9CYe9mZVFDwAjlAwDD3OgSCZAAEpAJoAfGKF_+GY8IpE6RgAAOgxawuDCgAo6G4GCALAEkmAA4HAAHA4D_x0AAAQToAAAiQZpw0SlOxcAB8OAAPhw9tSIo5AAAR6EABJBCAAkxGEDRKYflwAABLDgIo5APhwZQzKwFDkoACDg0AAo6BAFgCSTAAkEgADgcB_46AAAIJ0AAEIWCHTppg0SlOhcAB0OAAOhw+dSIo5AAARqEAAEIWABOvCkLHMGiUpKLgsgAOyMiEC0DkAsItAPQAAIQsAAZiEfGD4NXBlC8kmkqj0ABGMHwByATuWg3kTDVRgAAhCwPmQI1UjB+gjU2RcrPJpKr1Dh+AA9GD4A5AMsoloBKs5KAAg4NGDfgCFmADnQPiQAECYAAAD+ysBWZgAAbHQAAHRIBSFhZFjMrIgSxeAuoeAFrngwmewWgGIhDSWQGqowAEHBoBzJ0MgrhSFuJlQW1JgAAD_A8AFZmAAHoAAQhYSKXgCFjOg1m+xcAAAA+kYqmbi4ACSvBGAACELCMi8MSChFct3wLgAAAH0jFUPWbAAEURgAAhCxCiuEQxoogl63ywuAAOGFQAF6C4KqAiZGOIRAACchEcIsZ0UsiVKF4ABJQD+CkOIKF4VECqqMZQALoLA6ACjp_CIY0UFq5bsYXAAEdAIpVF1FwVEP+JSyEYAAIQsWpKBEPgsZ0UsgdKF4AAHSmpoWK4VQiJ5DDSWQnqrUSWABBwaAADlPQRFmLGZFrqZSxeAATEAilUQybB+dSAbolAAQcGi1hUWth0MfDw_BgQEAJDRZA0f7KjRFwANRYABqLA9A6AAACChAAAADeYFgYJSCUqOsGQAAIRYAwxYMgAANiEAABYGAFWXAASlRyJSFzlwACoWAMoLiEgnoGyVgAAihwA6i4ACLBWHB4GiSlALl4USCq0sZgANxYuNBMsxJCUSeg5ZOngAATBgPA2lw0SkJpQvCiGGMF4ADUWBBLQDEP_rxJAfAjAAQcDhBwOpcNEpCaULwohhjBeAA1FgQS0AxD_68SQHwIwAANAAk1MGDRKSplC8KILQDvnSshguFkDLBUV0kgPgRgAIOBwMEDRKSplC8qILQBNg0XKyBd0qHNsVJAMOhHsAgAAXwGiUlTKF5UQWgCbBoufAmrIwEoLulRYaSA25GE0EwAA3cNEpYOULyohESheA946iqQiIsgCkCeJUsDGCMFWggN_GgbHnFvxDRKW_lC8qIIcoXgfwOieDReslkAR5IrothJIEHkaVx0AAGYACmw9GhcihsHglC8KIVsoXgYMNgqACiCRWXQAc2gRzyXQCHo0To7igUtSB0KCU6qLgmkGnhcHkK2lxPSSB+EieFmkgILQgAAOhQA6FA5FgB8TACiKgCIgBNdUhAELEYAAAOhQCw4DdrgdCkFiwOCKgByADkKoWQ4gSQGIHwAAHQoACTU+oNEpmCULwokyyheXX_7EB4LlYWQJyV0kgPgRgAAOhQPoDRKW0lC8KIp0oXl1C_ZUFkDm50fbXiSA0RGPYBAAASgsGTqJU6MoXhRGHlC8OoI+LlYWQDxnDukhJAfkjAAEUAEM2Gid24aP+lS9SheFEQaULy6hY0qCyBls6AkgFTQgcgABmmwZJNlTvi5WVEcEXKw6gP4uVgANQj4jAdgRgy00AbIwfBsARMT6A0SlgRcrLJRHqFC5WXWw1ENxcrPfLVeig9fyaO5zXSSUaiHwSo8sjoAANqIkYWRQ3QZSiAuV3EqgtLifBixhli5WVWihgjR2OaTXSSUSes+So8rjoAAwSkBPpGD6MxQ2f1KgmFysKJKS4pyYiUgDZjBvAAodl0AHuI0M8l0igPKHjZOjuKA6FBsHgCSTAKLKgIALQADGIgABSPgAAOhRCwtyAh5OfgEXmABGLgAAYCVMMEiKGAPiqywuAnP8U4aQjAAASBgBFlwJSKIuAABgJUQ1iyMFVlxcBRaaH5TmPkQAAAgi4EgaJSAQuAACppUQ0qsvFm5BcSQotNErpwJG4LkLAAA1i5RCUl0LgAABqVENAAS0AAjRkApwUZSlkzFFAiATACJLhJUglMZS4AA6gZO0LlZDSKWTmKlsWmUKLTQYScABkaOATQaA8ZAPBcADFgSkmBcAAH6MqmlV8j6G_kRgs6KLgKLTQrqcF0AABmF1tFQSlH5cAAVWMmOFyv75QnhpFLpZ+oXAUWmhOUyedUSgADMBwFwJSY4uAAGkGVTSohpFCzwouAotNC7p1llo010AN7p7AEUXAqhoEpJgXAAB+jKppUVYb+pGCzoouNIUWmkF04ACqg8AIADZgIJcABIbAAc+LgP4hwAVi4AAXCsWRGAAABGVBEFQAaNgAAAsTH8goAgLwCBAHerFkRgAAC9lz6DIyK7BAuAABfpUQ0gn7FZlBczZyxhBENNEgKQAAbiIAZZdXCZTo8ZU2u+QLgOcmQANwuVkNIJBKotAgiGmhVk4nEtAAR5KhgTgu5MsZhKUglwAAzo0ZscLlZDSKXSz9YuAIUWmjxE6WNQCAOTLGYOzo2UjpiBMGYBlXAGaYHQaQgY02AAP_Gwf2YgIRmwABHT4AADoMAb04yKrv4uAABal8qDCAiliuLQSTcVQGgIwAEHA4QcDunGRVd_FwAALUvlQYQEUsVxaCSbiqA0BGAABoCJloNLXA6FXILgAwbAAB+MuAAYgWQK4nwAAHQoBXCxmFkfZQvKaEkB6xlKSwh2RWQAULy41X8i1RTQaMewCAAAFBQ2josZhZTmULymnkYiSA1GMpLDTQqtaKF9JuNVQosV6KDeSo4ABFAAFNC+FjMLJWSheAs1ElgHQyoMoAt_kpBZGmoxVRGDCARPVhTwetYXH_VZQZQvAooDGDLdxUZQBAhQvNIANrQiqAGplYKQADXA4w4PAsZlVWeULz_CcH4UJYBRwqDKVQq6wLg2lkigadOlcdAANQBCHixmFlZ5QvAYaiSwBjKQwgPCKF4cUQKlMoopdAjyuOi6STif7RmjDRLgJ9IwfPsYLyqrvKF4HuXLZJAycXCkLoB_CxWXTSBFD7I0M8l0igPKHjZOjoA_SgdCgWEwAsIgLUJQA9AD_yc1A6AABcbAAAdCgJvQEPQ6cAqFQOgwiBoFVGwAAVZKFQDkf4uWwEIdAnKnAAAdBg1Kx0twwWobCcqobgYIAUD8CYAmgAHBoAAP3CwFTToAADoMABMuBsDw3AwA3yoBjSEATcOG4ADQEIBjIZWDKQAAHQYAMiUAhLgIBENwMAW4qA7jEAGUAP8ByUkIACAAAAdBgAJlwc8iG4GAG+VAdRUgKlMQAJQaAhAIpDSt5WAAA6DFrPgBMuELkREgwBKyxeAsZElhUQlhIrA60CYJ4NAQkESgUQAAOgwXlYAGWgdVUAwEBYGADRsH_jYAFwFwAMJMgAC2GwAAHQYAF6cB3SgANUIBnhuBgfhQAH5D4AygBjZSsIAC6jYAADoMAP5OG4GAAe0nA2NgACUhw86Agn_HIYyhAAFShgBxpwAsuIkGATIXBBJs1AFOMS4JSMgXhyBBpJxNvIwABUoYDQKenDcDAAXNgU6SOgAAAo4sPgAIA4z4Z8LAACwoAH6cJjPiJBgFqGw"
noncomputable def WL14_2 : ℕ := zfNat64 9356 "CGQBcuAJCwAAAAAAAAAAAAAAAAAAAAAAAO8CAwCzRBhDlwAewoAD2FAAHUGAAgIlAAAGAgG4GACSTAB7CgAPYUAAbgYAAH50AAAYCAAmNAAAAAAAAAAAAAAAAAAAAAAAAACIQBAyADlwBIWAAAAAAAAAAAAATGgAAAAAAAAAAAABUIAUXADCYAkNAAAAAAAAAAAAAJDQBaIsuACSFAASQoAA9iRL4WACzJQAAAA9CACHwAgqADkwBIaAAAAAAAAAAAAAMNgB5cASGgABhYAFoUAAAAAAAAAAPLgCQ0AAgTAAtCgAEg0AH6YgAAAAAAOFwBIaAiZ6EOXAAAUUwbgFpWWcOwKgYQoKJLAAArq6vDnwAIzADS7nD4AABwJAAOBInIAAhIGIAC9OCLGc2AAAQlwJqS5w+AYeVAB0ADoAP8HgAGlIQf+egM5CwMgAw2AQl3NHwAECYAGwkAARCgAAAAAAEQkABQu5w+ABGVAC4DgARxEevOgBiCwMQADaEAAG4WAA6Xc4fAih+CQXAAAE5APWbAxAyAb04zgjAAYhYhStDACaMABLgAJSoASAkACQEjwZ0AC4SBiABrQgAMVMwMwAiXcUNACJLgIXCwABEKJyDEAIIoxABkJQAEJz4AChcIQsACMqADoHAAdCY+edAB+AgYgAG0IABzh8ABQuEIWAAGVAFEOAAIQ0TkABiBkAFKQADnD4ADhdxA0CEH4RJcAAATkAuCtXIoxAyFE6aJLAAhOfAKClaGAFy4QhYAEZUAKQAgAcAAOg4DIAAABCFgALlwhCwAIyoAgAsACkAAdBwGQAAACELAABTgBRcIQsAGYyAA_8TASEAGYcBkADcjAABCFgAFFwhCwNAoAAAOAXB_kiAAMgAGlIHBDQAABVmEIWAWgcNgAJWDQtAAEAJAABqQgAAhCwABDIACMqAAJWFwId7EQAIhIAAPqEAAEIWAACvACi4BsJcQNAJMMjFoYPAAIRcFYWJyAEUYgB+0oCWgAAqLgEQlxA0ASwyKKOkJgCllwAARRqeRLgHgnACkGVJwAEhIQhYcBcAAAHALgAAJnEQAJ1YAAACQXCELCwGiUjGLgAA4BcAABFPhlwBnTgBSC1iYw4G_BCFgCWFw3AWACYRsV8aAAagAEvQgrK3AHqHgEIWnIPAtYuCiPyKgItGwABrjIAARqEAAKAeACEXCELRkD5FwAB4I2AAGoXcaIwCVEYDaAyIqI0_AALcAHLgCQ0AA0bAAAAAisyBj3BKD_yMZRGAAAABlwAMxkAAAEEBFZkDniSUBFPWjWAQgAAAsFxhlQAEDoAAAAAODJQDaRgPLQVAAYZUDo6PgBISEIWcQfAhYuAABqABZ8yD1jUH_EaXiMAAABcLgCQkIQtAQPUXAAHajYDj_5WCr5kHUugRUPIwAABpLMghCy6kIEKFwAAMQAJVFwADVEYJ+OQVExA0ALUuAOSQhC3_B4AAAE0ZAAAAAJ1YDaArYuA2ZqcMXBCFgRAwCDKgCeEQATwiABdgsAAI1CAACELAAEZgE01RcAjAiD_icIwIgAMMLAA"
noncomputable def WL14s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL14_1) (dpk j 2 WL14_2)
noncomputable def WL14s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL14_0) (WL14s1_3 j)
noncomputable def WL14 (j : ℕ) : ℕ := (WL14s0_3 j)
noncomputable def WD14 : ℕ → ℕ := rdw WL14
noncomputable def ready14_cuts0 : List (ℕ × St × ℕ) := []

theorem ready14_cuts0_ok : CutsOk ready14_cuts0 := cutsOk_nil

noncomputable def ready14_0_state : St := ⟨26112, 220224, 28545, 39936, 52016, 179415, 53248, 180647, 53248, 180647, 29184, 45301, 28545, 155944, 26112, 285696, 54657, 260160, 106673, 428184, 159921, 481432, 213169, 534680, 242353, 563864, 334597, 592409, 360709, 741970, 80561, 207960, 133809, 261208, 187057, 314456, 216241, 343640, 308485, 372185, 334597, 657881, 105264, 232663, 158512, 285911, 187696, 315095, 268549, 343640, 294661, 629336, 106496, 233895, 135680, 263079, 164225, 291624, 190337, 577320, 82432, 209831, 110977, 238376, 137089, 524072, 57729, 185128, 83841, 470824, 54657, 441640, 0⟩

theorem ready14_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD14 ready14_cuts0 113 17284) ready14_0_state = 60281 := by decide +kernel
#print axioms ready14_0_cursor

theorem ready14_0_covered : Covered (toCl ready14_0_state) :=
  ready_cover_cursor WD14 ready14_cuts0 ready14_cuts0_ok 113 17284 60281 ready14_0_state ready14_0_cursor (by decide)
#print axioms ready14_0_covered

noncomputable def ready14_cuts1 : List (ℕ × St × ℕ) := (17284, ready14_0_state, 60281) :: ready14_cuts0

theorem ready14_cuts1_ok : CutsOk ready14_cuts1 := cutsOk_cons ready14_0_covered ready14_cuts0_ok
#print axioms ready14_cuts1_ok

noncomputable def ready14_1_state : St := ⟨26112, 1040384, 28545, 39936, 52016, 425984, 53248, 220224, 53248, 220224, 29184, 45301, 28545, 305088, 26112, 1040384, 54657, 1080320, 106673, 1506304, 159921, 1726528, 213169, 1946752, 242353, 1992053, 270898, 2297141, 297010, 3337525, 80561, 465920, 133809, 686144, 187057, 906368, 216241, 951669, 244786, 1256757, 270898, 2297141, 105264, 646208, 158512, 866432, 187696, 911733, 216241, 1216821, 242353, 2257205, 106496, 440448, 135680, 485749, 164225, 790837, 190337, 1831221, 82432, 265525, 110977, 570613, 137089, 1610997, 57729, 350389, 83841, 1390773, 54657, 1345472, 0⟩

theorem ready14_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD14 ready14_cuts1 125 25) ready14_1_state = 74904 := by decide +kernel
#print axioms ready14_1_cursor

theorem ready14_1_covered : Covered (toCl ready14_1_state) :=
  ready_cover_cursor WD14 ready14_cuts1 ready14_cuts1_ok 125 25 74904 ready14_1_state ready14_1_cursor (by decide)
#print axioms ready14_1_covered

noncomputable def ready14_cuts2 : List (ℕ × St × ℕ) := (25, ready14_1_state, 74904) :: ready14_cuts1

theorem ready14_cuts2_ok : CutsOk ready14_cuts2 := cutsOk_cons ready14_1_covered ready14_cuts1_ok
#print axioms ready14_cuts2_ok

theorem ready14_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD14 ready14_cuts2 128 1) (ofCl (RC 0 0 1 1 1 0 0 0) 0) = 75117 := by decide +kernel
#print axioms ready14_parent_cursor

theorem rc14 : Covered (RC 0 0 1 1 1 0 0 0) :=
  rcOfC WD14 ready14_cuts2 ready14_cuts2_ok 75117 ready14_parent_cursor (by decide)
#print axioms rc14
noncomputable def WL15_0 : ℕ := zfNat64 23883 "GAgA3AwAbAYAAADcDAAA2OgAADAQAAAAAAAAAAAAAYCBMDAG4GAAAAANwMAABIeAAAMBAAAAAAAAAAAAABgIEwMAbgYAAAAA3AwAAEh4AAAwEABIyANlwAAAAAAAAAAAAAAAAAAAAAAAAEQwBuBgAAAADcDAAAKhgAADAQAEzIBAGAIAMAboWADdCwABABgAALHQAABgIAAkNAIAwEeCgDkCwAAAR4KAAAkZAAAAAAAAAAAAAAAAWlQpBwAAAAAAAAB5aAACkFABBIg2CjogQC0M1qlu7BUAArFgAAEoA4k4AACQMAbBR0QIMJDQBiRYA4kXABdKiWMwEocSKQBKjgAASBihA29UAwEAJQNIEQBpAiAASgAKENgAADARS0sWABR8AOMgAZUASFgAAAAAAAAAAAACy4LgoAYA0AAf0HgABgDQAAAAEIOAAkFBmFAGCgEkJABMFgACwsZ2EgAAAAAAARMwDAQAAKIWABRCwADaEgAAOlQAAEwoACQkGYUAYKAAAsLAAFhYzoJAAAAAAAAYSgzCg_YhA0EgAAogbQSAEgJAABsQgAAihwAHC4MwoBgcAAANcUgAACaADlSAAFAPAGYUzk8hhxtOZAABRASg5A4jwAUYM4xCOSUAADYOCXDABhUGYUAAdxNgDb3E2J_CQAAAMVGAAg4PAGYUXouAeZMBn82AtM7TYAdQXAAAjUIAASIkAZhQASR4Bzx03ANJizBuOIID4ElVZIrACyMhRJYAARQ4AuCi9LQAEZjYBCDZrGoBSUsEwEkKoOJGAtBcAFQSA0hpbWZwxU1pYEAAtQAVmB_A2A0HAGEHgAwg8AAqh4AAKR8AAC4KAAMzJ0XANRXCQDJB4AZIPABcwiA_+xAX9CAAFAFAAJrgDUaIkA54eAHPDxZCqn4yI2SsMSwgiFElgAASBgBiMzCkQAQRICF5EAQvIi6MQKzExJAAcSEAAB0GDOzjwtBAJAABeFgALwsBkAJaTEsZgHGSgAAXhQAKa4Qg6GQkAhAiAPBhCIA8AGkioAAnaEAAB0GAAcFCKHAyEgIYRAFSFgALwsM8EgAAAH6EAeIGgAAotCEHEUEgBy5APQAU4RABEAmACiGHQgAIOBQAFDYQg5fwkEPiYKIpwiAAAHoO3IAAiiMAAC4OAALXAmFAsDgAMIJhoAFORAA41WAABobAAAiCgAB1wAGqBMKBUJAB+RiBINAAaDoAVkZAAAPDoAAAwEADQiBMKBMJAB0JiBINAAAAAAAAAGAgAxkQhBwrhIAPsMQJxoAAD8wER5WBiATTFJwAAIgoIauFACQsIQcH4SAA5BsCcaAF5FwAMGMgA2hY0IAAAAkNA_CQAHINgTjQBTguAC7YgyADaFjQgAABxh4BVoksBXhYzABaFNN_LyUyxmBVDb_hG7ijFMJgAAB6EgrkhAbnRgDmBcAF0YgVQ2lcRrmoxSiYAACwEGFgGTGpGgAeQYLwTjQB70uAP+r3yzIAOIfNCJIAAUwNQgEgUeVBFI6IoB+8uAD_5kAfKch4KEWQAQONBs41CASAAThg3foPAkwuBaABtyxmAf8bg16BHLIVk601640C8qOjs2ALtoBChCEHAAAJCIAugXABZxgZB_ZuK6HKRgAAohRe0IA9rhFDv1MQC_Ngmg6zIABONAFzkIAAJkhAAAaCgEIOJWJAOSq8GajYmDcABONAELEoAAIojAAOcQgD7EgjQdH_1YvcbAAJxoAOAjAAAP0I5AUAAAqYkDMTR2VU0xtMG4BHEuJbVQeaiSwnpTRfaMqIyAAAOUSAchReI5GIMG4BjwiJaAQQDdCsF_RJZoi4AAAJBIBBGwArDIAAAcucOgAASHxoi4AAhwUo8aTuJAl80dlVHcmDcA1AVGUy4AogARaRi6ACjxoKPGjwiQDknurBszBuAP6IE4APdPgAEcoRdABR40ARCwAjDIAO5UARUA6MbCUAAFxsAACIWIcfHZ2BPwAehAXSoABBhyAuXAAFyIsQcBFQDCAShaAABOFBWe1d7KgseC9FQUKPgJjDQBMYaAsglQaAwgJuRgAAXBQAxEoQg4vRUGBD4AAACaE5jIK6A3BGAAA6DACnJhCDqaFQZR5LF8AallRazG0ahQQAHIFsE4AADoMBpJUHrT4AatCEgBqTG_y0AsCZOBltoL5QgAAKAwAHDIqYqCxp8AN42b00Abxs3JiBZUmpIZTiCZUIAACQMFVkitC5IrK6Pc4fgODMG5hsIZXOGzOoi0ASm0koOZsdpqIrNEjgAAdBipO6O1jwBAhAAi4AWVAAAAAAAAAAACNJUMAeMwNnCBMGAIgpFggmYC4AmS0LQAGIgQAaaMAACEGAGfhAmDHUEgFoHeioAokVAAk6GABSDlUgAAQgwAT8IEwY1IgXB68UoXldpv_SYAAAitkNhAgKR9CdLAABCDEKAAeYDJhAmDRkFgAGoHhYAnYVABZqMXAAEWRgAAQgwDveYADhAmDEkM9HwAUB4ACgNAAEweAAAAAPAwA4EIgwyAAUC9bBIVAALib8AsAQQAKoWE+AABCDAaAATIB0XAmDBIfpnwE1SoA1STAB+y3BKQpoWRZR0AACEGAOUXAmDWvTgAQk0EhUAAkJgAyUK2gSwApJgVKAABCDEaYnpDhgQeuBkGO4NB_42AAAYgB_42AAK4ZAAAmBgCD1wMgx3BoP_GwAxAAAP_GwABXDIAAEwMEKCRjx4KIDQGpS4A1KXBNooUQGiq0UCMCMAAJEKAAkFFAHGRHgocNAajLgDGZcE3+qMEuBoqtFAPehAAAAEjIAkJCpjwRiGgLjlwBccuCb_9GCMQ0VWigGjQgAAFID+OIwsYNAdDLgDoZcE2ihYwaKrRQJnoktiQ0XcdgP+pQEKjwSeGgMJlwBhMuCiBJ4aP0q1FAU2hUQLiiAJQVgALjaSIkeBzg0BMkuAJklwTaKDnBoqtFAO0jEkADSmwAwIAB5gAVcDoJwaFn6EwAEUK4ALy4ABeXBNnoBVRqAlFSA34dAAFBJhuDjvkQOvUK4ALS4ABaXBR_OfABOQFMqQZQC1zkAAHmCekyjRMF_lIAFpcAAtLr7ExN_WfAFVGoB+1IIoxAysnECAgVReA3Vw2hMf+SgroAH8zIKIHnzYKLd9mBviEUwOAAGKk5J44jKK_owbltOUFwFBeyWLwmgCUqtFHmuUyCLrRI4AAoBYACYW4zMuUeB8Bg3LafmLgDzJcE0ASkH7atRa6D8UIAAAASFw8RNZHEZRUSGjMWk3b6yLQKCLaCwpOlgQQMkCcklGe00ggKUCOADUApAAwUysrHEc9oqLDRnWbbWRaBQXsli__CETQY4hCUglUgooUp5BFiI0cALoAArMh7R4HCGDctp7IuAP+FyFJNFASpAnKrRa6YlGLVIx+hIAAc9Lpuj1ZBiG0FoACcoX10KiUALkgTm1h6cPTEpQADRI4XQCW5sVJSpqxO5HgHwaMzmLUC0AKGULykgIBJFZZB6AodAjiUokE_q1EwSIFZWPv6MAHlw7OmAJDQAA6cTAHTiYABSABFoyAAAjAM00sjaGgWMNAIDKgBAZUACxhoAAbR0AAWQqADONcSbALYGgHcFwA7guQP90B3RQWwNFVooBAkYABLpcB4ASGmxIE7vxxGBJh42AE0oX10BaE0oX3Eo0EDGDxsq1UggHQSo4AAWYDZsyQLlLDQf2GgLLlQBZcqAD+w0AAw86_8XAAAGNCxBHogjwCkBVZQvABslwf1OAEMNC0+YgRwAWkUcgNsWg5giPtOIj4BkBHZQvAFpxyheMXOJEcchNFItJs5C6NU4dlmRoYtIo5LrURNJUsFYEdBMs3oxVBIaBvwobAFIAKQAb8KGwAIJHQAHRioHZ0dmZUPh4knBrFUDIMAIQNvDwBt4eAAQgAQUMgAATAwS2INtrg2BrdBwf_HgNWjQBq0aAD_48ABC4yAAAMBFPTho6AjtTHh5PDw8TEhsa"
noncomputable def WL15 (j : ℕ) : ℕ := (dpk j 0 WL15_0)
noncomputable def WD15 : ℕ → ℕ := rdw WL15
noncomputable def ready15_cuts0 : List (ℕ × St × ℕ) := []

theorem ready15_cuts0_ok : CutsOk ready15_cuts0 := cutsOk_nil

theorem ready15_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD15 ready15_cuts0 128 1) (ofCl (RC 0 0 1 1 1 1 0 0) 0) = 23963 := by decide +kernel
#print axioms ready15_parent_cursor

theorem rc15 : Covered (RC 0 0 1 1 1 1 0 0) :=
  rcOfC WD15 ready15_cuts0 ready15_cuts0_ok 23963 ready15_parent_cursor (by decide)
#print axioms rc15
noncomputable def WL16_0 : ℕ := zfNat64 590 "CUIAkZAEhIAAAAAAAAAAAACEqAYCAUBALpGAFElAAokoCKAukYAAAAAMBAGAMBAKAg5GVBS4qlIDUlIUUa0sKuulQENAAAAMBFK"
noncomputable def WL16 (j : ℕ) : ℕ := (dpk j 0 WL16_0)
noncomputable def WD16 : ℕ → ℕ := rdw WL16
noncomputable def ready16_cuts0 : List (ℕ × St × ℕ) := []

theorem ready16_cuts0_ok : CutsOk ready16_cuts0 := cutsOk_nil

theorem ready16_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD16 ready16_cuts0 128 1) (ofCl (RC 0 1 0 0 0 0 0 0) 0) = 601 := by decide +kernel
#print axioms ready16_parent_cursor

theorem rc16 : Covered (RC 0 1 0 0 0 0 0 0) :=
  rcOfC WD16 ready16_cuts0 ready16_cuts0_ok 601 ready16_parent_cursor (by decide)
#print axioms rc16
noncomputable def WL17_0 : ℕ := zfNat64 422 "DAQCgIA3AwAKR4ABSPAARg6AA2gAABgIAGAgFAQB1BgHIlwElRiULwCWkXLGYAQUAAAMBA+"
noncomputable def WL17 (j : ℕ) : ℕ := (dpk j 0 WL17_0)
noncomputable def WD17 : ℕ → ℕ := rdw WL17
noncomputable def ready17_cuts0 : List (ℕ × St × ℕ) := []

theorem ready17_cuts0_ok : CutsOk ready17_cuts0 := cutsOk_nil

theorem ready17_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD17 ready17_cuts0 128 1) (ofCl (RC 0 1 0 0 0 1 0 0) 0) = 431 := by decide +kernel
#print axioms ready17_parent_cursor

theorem rc17 : Covered (RC 0 1 0 0 0 1 0 0) :=
  rcOfC WD17 ready17_cuts0 ready17_cuts0_ok 431 ready17_parent_cursor (by decide)
#print axioms rc17
noncomputable def WL18_0 : ℕ := zfNat64 401 "YCAUBACwiADYDAAKR4ACMHQAG0AAAMBAAwEAoCAQZUAG8GAGzlQBokuGIAQUAAAMBA+"
noncomputable def WL18 (j : ℕ) : ℕ := (dpk j 0 WL18_0)
noncomputable def WD18 : ℕ → ℕ := rdw WL18
noncomputable def ready18_cuts0 : List (ℕ × St × ℕ) := []

theorem ready18_cuts0_ok : CutsOk ready18_cuts0 := cutsOk_nil

theorem ready18_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD18 ready18_cuts0 128 1) (ofCl (RC 0 1 0 0 1 0 0 0) 0) = 410 := by decide +kernel
#print axioms ready18_parent_cursor

theorem rc18 : Covered (RC 0 1 0 0 1 0 0 0) :=
  rcOfC WD18 ready18_cuts0 ready18_cuts0_ok 410 ready18_parent_cursor (by decide)
#print axioms rc18
noncomputable def WL19_0 : ℕ := zfNat64 413 "YCBMDAG4GADYDAABR4AAAK0VAAAAYCABgIFoMAdQYAN4MADqJgAHwTAH+g4AAADAQQxoa"
noncomputable def WL19 (j : ℕ) : ℕ := (dpk j 0 WL19_0)
noncomputable def WD19 : ℕ → ℕ := rdw WL19
noncomputable def ready19_cuts0 : List (ℕ × St × ℕ) := []

theorem ready19_cuts0_ok : CutsOk ready19_cuts0 := cutsOk_nil

theorem ready19_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD19 ready19_cuts0 128 1) (ofCl (RC 0 1 0 0 1 1 0 0) 0) = 564 := by decide +kernel
#print axioms ready19_parent_cursor

theorem rc19 : Covered (RC 0 1 0 0 1 1 0 0) :=
  rcOfC WD19 ready19_cuts0 ready19_cuts0_ok 564 ready19_parent_cursor (by decide)
#print axioms rc19
noncomputable def WL20_0 : ℕ := zfNat64 487 "BgIBQEALCIAFI8ABsBgAIwdAAbQAAAwEAAAAAAAAAAAAAGAgnSDNfLgkrES4ADeDAAaM0bgBBQAAAwEBo+"
noncomputable def WL20 (j : ℕ) : ℕ := (dpk j 0 WL20_0)
noncomputable def WD20 : ℕ → ℕ := rdw WL20
noncomputable def ready20_cuts0 : List (ℕ × St × ℕ) := []

theorem ready20_cuts0_ok : CutsOk ready20_cuts0 := cutsOk_nil

theorem ready20_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD20 ready20_cuts0 128 1) (ofCl (RC 0 1 0 1 0 0 0 0) 0) = 496 := by decide +kernel
#print axioms ready20_parent_cursor

theorem rc20 : Covered (RC 0 1 0 1 0 0 0 0) :=
  rcOfC WD20 ready20_cuts0 ready20_cuts0_ok 496 ready20_parent_cursor (by decide)
#print axioms rc20
noncomputable def WL21_0 : ℕ := zfNat64 397 "BgIBQEAbgYAEI0ABsBgAAAKU3AAABgIAGAgEQwB1BgAhEwAG8GAAyJUAH+wYAAAMBA+"
noncomputable def WL21 (j : ℕ) : ℕ := (dpk j 0 WL21_0)
noncomputable def WD21 : ℕ → ℕ := rdw WL21
noncomputable def ready21_cuts0 : List (ℕ × St × ℕ) := []

theorem ready21_cuts0_ok : CutsOk ready21_cuts0 := cutsOk_nil

theorem ready21_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD21 ready21_cuts0 128 1) (ofCl (RC 0 1 0 1 0 1 0 0) 0) = 406 := by decide +kernel
#print axioms ready21_parent_cursor

theorem rc21 : Covered (RC 0 1 0 1 0 1 0 0) :=
  rcOfC WD21 ready21_cuts0 ready21_cuts0_ok 406 ready21_parent_cursor (by decide)
#print axioms rc21
noncomputable def WL22_0 : ℕ := zfNat64 418 "IR4BgIBEMAPiYAN4MABvBgAAgLAAAAABgIAGAgEQwA+JgA3gwAG8GAAyJUAH+wYAAAMBA+"
noncomputable def WL22 (j : ℕ) : ℕ := (dpk j 0 WL22_0)
noncomputable def WD22 : ℕ → ℕ := rdw WL22
noncomputable def ready22_cuts0 : List (ℕ × St × ℕ) := []

theorem ready22_cuts0_ok : CutsOk ready22_cuts0 := cutsOk_nil

theorem ready22_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD22 ready22_cuts0 128 1) (ofCl (RC 0 1 0 1 1 0 0 0) 0) = 427 := by decide +kernel
#print axioms ready22_parent_cursor

theorem rc22 : Covered (RC 0 1 0 1 1 0 0 0) :=
  rcOfC WD22 ready22_cuts0 ready22_cuts0_ok 427 ready22_parent_cursor (by decide)
#print axioms rc22
noncomputable def WL23_0 : ℕ := zfNat64 165 "GAgEQwAAbAYADYDAAA4OAAAAADAQ"
noncomputable def WL23 (j : ℕ) : ℕ := (dpk j 0 WL23_0)
noncomputable def WD23 : ℕ → ℕ := rdw WL23
noncomputable def ready23_cuts0 : List (ℕ × St × ℕ) := []

theorem ready23_cuts0_ok : CutsOk ready23_cuts0 := cutsOk_nil

theorem ready23_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD23 ready23_cuts0 128 1) (ofCl (RC 0 1 0 1 1 1 0 0) 0) = 174 := by decide +kernel
#print axioms ready23_parent_cursor

theorem rc23 : Covered (RC 0 1 0 1 1 1 0 0) :=
  rcOfC WD23 ready23_cuts0 ready23_cuts0_ok 174 ready23_parent_cursor (by decide)
#print axioms rc23
noncomputable def WL24_0 : ℕ := zfNat64 2495 "bKgCQkAAAAAAAAAAAAAkNAAAAAAAAAAAAAAAAAAAAAAAAAENgFJMAAAAAAAAAAAABEGCAJcElmWXASVi5cABLxJ2w0bAAAAESFAADRgB5kATEgBIYABAwABIYAAJDAAAAAAAAQhwALCIAQZUACDKgAE0NAAAAAoAoAFpEFwcRQOBSxcEliQXASU+BcAAAAAAAuDgCIKIoHApYuCSxKLgJLTAuACEqEAUkAAAQhQAIhQArJgAZkwARQ+IQHAD2EYAFIAAAiCgFACRkD8HAiouCSvoLgJLVguABEh0ATUAABQBQQkIaMgBsqAJDQAAAAAAAAAAALgKkujwJ0LgkrVC4CSnwLgKIGBGoP_HwAAAMQYAwzRJgocDQyxeElOWULwJKXMoXhVaK+A+FoDUAAAFADFLU1NCGztK"
noncomputable def WL24 (j : ℕ) : ℕ := (dpk j 0 WL24_0)
noncomputable def WD24 : ℕ → ℕ := rdw WL24
noncomputable def ready24_cuts0 : List (ℕ × St × ℕ) := []

theorem ready24_cuts0_ok : CutsOk ready24_cuts0 := cutsOk_nil

theorem ready24_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD24 ready24_cuts0 128 1) (ofCl (RC 0 1 1 0 0 0 0 0) 0) = 2505 := by decide +kernel
#print axioms ready24_parent_cursor

theorem rc24 : Covered (RC 0 1 1 0 0 0 0 0) :=
  rcOfC WD24 ready24_cuts0 ready24_cuts0_ok 2505 ready24_parent_cursor (by decide)
#print axioms rc24
noncomputable def WL25_0 : ℕ := zfNat64 853 "BIaAAAAAAAAAAAAAAAAAAAAAAAAAIbAKSIAAAAAAAAAAAAC0iAIhgAAGQwAAKGAAAAAAAAiBgQgwDACgAnkwAAsmAAADqEQAAAiBgEIGBCDAAP4KAWTAA9SYAFMHQAMQAACEDBCQkMbOx4e"
noncomputable def WL25 (j : ℕ) : ℕ := (dpk j 0 WL25_0)
noncomputable def WD25 : ℕ → ℕ := rdw WL25
noncomputable def ready25_cuts0 : List (ℕ × St × ℕ) := []

theorem ready25_cuts0_ok : CutsOk ready25_cuts0 := cutsOk_nil

theorem ready25_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD25 ready25_cuts0 128 1) (ofCl (RC 0 1 1 0 0 1 0 0) 0) = 1005 := by decide +kernel
#print axioms ready25_parent_cursor

theorem rc25 : Covered (RC 0 1 1 0 0 1 0 0) :=
  rcOfC WD25 ready25_cuts0 ready25_cuts0_ok 1005 ready25_parent_cursor (by decide)
#print axioms rc25
noncomputable def WL26_0 : ℕ := zfNat64 992 "CGwCkiAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACQ0AAAAAAAAAAAAAkNACQwAmJgAAAoNAAAAAAAABgMAJiYAM4cAAqJgAB4HAAAqhoAADpDhWBQEYJgE6jQAQgmABqw8AAGEAB0hwOjs7Ex4eQxoa"
noncomputable def WL26 (j : ℕ) : ℕ := (dpk j 0 WL26_0)
noncomputable def WD26 : ℕ → ℕ := rdw WL26
noncomputable def ready26_cuts0 : List (ℕ × St × ℕ) := []

theorem ready26_cuts0_ok : CutsOk ready26_cuts0 := cutsOk_nil

theorem ready26_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD26 ready26_cuts0 128 1) (ofCl (RC 0 1 1 0 1 0 0 0) 0) = 1146 := by decide +kernel
#print axioms ready26_parent_cursor

theorem rc26 : Covered (RC 0 1 1 0 1 0 0 0) :=
  rcOfC WD26 ready26_cuts0 ready26_cuts0_ok 1146 ready26_parent_cursor (by decide)
#print axioms rc26
noncomputable def WL27_0 : ℕ := zfNat64 165 "GAgEQwBuBgA2AwAAyGAAAAAAADAQ"
noncomputable def WL27 (j : ℕ) : ℕ := (dpk j 0 WL27_0)
noncomputable def WD27 : ℕ → ℕ := rdw WL27
noncomputable def ready27_cuts0 : List (ℕ × St × ℕ) := []

theorem ready27_cuts0_ok : CutsOk ready27_cuts0 := cutsOk_nil

theorem ready27_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD27 ready27_cuts0 128 1) (ofCl (RC 0 1 1 0 1 1 0 0) 0) = 174 := by decide +kernel
#print axioms ready27_parent_cursor

theorem rc27 : Covered (RC 0 1 1 0 1 1 0 0) :=
  rcOfC WD27 ready27_cuts0 ready27_cuts0_ok 174 ready27_parent_cursor (by decide)
#print axioms rc27
noncomputable def WL28_0 : ℕ := zfNat64 539 "SFgAAAAAAAAAAAAEhoAAAAAAAAAAAABIaAEhgFEXAAUGgAAAAAAAABDCgPAwKWLgkqfi4AE6HABDASAAAAAhhQOzs2"
noncomputable def WL28 (j : ℕ) : ℕ := (dpk j 0 WL28_0)
noncomputable def WD28 : ℕ → ℕ := rdw WL28
noncomputable def ready28_cuts0 : List (ℕ × St × ℕ) := []

theorem ready28_cuts0_ok : CutsOk ready28_cuts0 := cutsOk_nil

theorem ready28_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD28 ready28_cuts0 128 1) (ofCl (RC 0 1 1 1 0 0 0 0) 0) = 549 := by decide +kernel
#print axioms ready28_parent_cursor

theorem rc28 : Covered (RC 0 1 1 1 0 0 0 0) :=
  rcOfC WD28 ready28_cuts0 ready28_cuts0_ok 549 ready28_parent_cursor (by decide)
#print axioms rc28
noncomputable def WL29_0 : ℕ := zfNat64 165 "GAgEQwBuBgAGQwAGwGAAAAAAADAQ"
noncomputable def WL29 (j : ℕ) : ℕ := (dpk j 0 WL29_0)
noncomputable def WD29 : ℕ → ℕ := rdw WL29
noncomputable def ready29_cuts0 : List (ℕ × St × ℕ) := []

theorem ready29_cuts0_ok : CutsOk ready29_cuts0 := cutsOk_nil

theorem ready29_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD29 ready29_cuts0 128 1) (ofCl (RC 0 1 1 1 0 1 0 0) 0) = 174 := by decide +kernel
#print axioms ready29_parent_cursor

theorem rc29 : Covered (RC 0 1 1 1 0 1 0 0) :=
  rcOfC WD29 ready29_cuts0 ready29_cuts0_ok 174 ready29_parent_cursor (by decide)
#print axioms rc29
noncomputable def WL30_0 : ℕ := zfNat64 165 "GAgEQwAODgA2AwAGwGAAAAAAADAQ"
noncomputable def WL30 (j : ℕ) : ℕ := (dpk j 0 WL30_0)
noncomputable def WD30 : ℕ → ℕ := rdw WL30
noncomputable def ready30_cuts0 : List (ℕ × St × ℕ) := []

theorem ready30_cuts0_ok : CutsOk ready30_cuts0 := cutsOk_nil

theorem ready30_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD30 ready30_cuts0 128 1) (ofCl (RC 0 1 1 1 1 0 0 0) 0) = 174 := by decide +kernel
#print axioms ready30_parent_cursor

theorem rc30 : Covered (RC 0 1 1 1 1 0 0 0) :=
  rcOfC WD30 ready30_cuts0 ready30_cuts0_ok 174 ready30_parent_cursor (by decide)
#print axioms rc30
noncomputable def WL31_0 : ℕ := zfNat64 131 "YCARDAAAAGwGAAAAAAADAQ"
noncomputable def WL31 (j : ℕ) : ℕ := (dpk j 0 WL31_0)
noncomputable def WD31 : ℕ → ℕ := rdw WL31
noncomputable def ready31_cuts0 : List (ℕ × St × ℕ) := []

theorem ready31_cuts0_ok : CutsOk ready31_cuts0 := cutsOk_nil

theorem ready31_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD31 ready31_cuts0 128 1) (ofCl (RC 0 1 1 1 1 1 0 0) 0) = 140 := by decide +kernel
#print axioms ready31_parent_cursor

theorem rc31 : Covered (RC 0 1 1 1 1 1 0 0) :=
  rcOfC WD31 ready31_cuts0 ready31_cuts0_ok 140 ready31_parent_cursor (by decide)
#print axioms rc31
noncomputable def WL32_0 : ℕ := zfNat64 33248 "D4UGIASRgIaEAZKULwCZFysjo1kpMi5WHWijUEqULwELDQAT6GAAGYAa0grDgI0FQEDioBqQORi40UETFQAKaJgAAUAcAI5eEIOASlKKlYC0PhcrAajDi5WHWijUpGVADGBoAAANBQfgYlCAClyNCSGiheE0WZQrDSQVWlCskI1koXSheX2Yh0EgWQAP6FQACoOAT4hCKHBj5OMmUKy00FppQrJCNTUBcExjoAxpOIzYPpI0cAADQUAS5DBoOi0VCDEieKQ0kF0ZQrA6NZKAcoXiBmIdBIH0EYahlBoAALQogye_m6mzACSM0oPBUMkVgSULvN0Ikodazw1CBSAAuwmAACEFAAOMgkxg+TGShFMIXOpJE4WSCFCJk4cSqQRaRUkVikACrkwAAXwoGkh4JUkisCShdyOhElDrWaCCZJFYABSiYfAcAADSQ8FQSRWBJQu85QiSh1rPD0IFIABSiZ1Q8AACNCQUhg+AZCpOEUcCSJwskEkocSqQSjFwpIOQRdD0A9OQAAbBwAES4AkNAhjB8mMlCKzIudSSJwskEEgTJw4lUgi0ZZIrCyABQAAAAMXAYNB0AcFSc68jDOSROFkggVipOHUskEA2SK6yWQAKFZAAGDQOj4FYkDMYPhJTiyMLhJE4WXTID8AITJw4lUghNyRWFJA58bAAD0A7Ei8jB8B_EycIoTUkThZHo_omThxKpBFrjyRWFGi78Nv6E01GoLQBLjFjAASLDkXB0B9FScdMlDkiZOF3YiESUOpZIIGUkVgADcNjCAAABYWJkeGCMHxmZgzkoRRH5InCyPReBMnDiVSCLXHkisKpJmolMGaOxqAtAAdDbHkNjB8BtEycIojskThZNMgPyShxKpBC9kisABQGQ1AWN28ASYTA8IsvEYPgxGCSJwiglCyPRahMnLaVTdID8WnPJFYTSDfwujoxGtFNpdpI9JLtCRWTs3NwJOOzdSZmJyOgNOiG4GE4HBLYqAu0VANTyxUFF_2bGlioAA8gABCBgAGlwI4eG4GA4SVB3QqlITUtyVALRqNOKgOnUASgABRBgDAxBERIMSciBBpQvAPwXKwDMlFoS0a9FJsBFwHU8hJIIAAUQYAxBERIMAlkoXhJTcFysqoZkvBi4JaNZLiYuA6nkJJBAACiDEaPglEqIkGAwGYMyoJMLQLgiMllISkagCOH8pA8x08tbVL4Xjh+AAFEGKEIkGKaTAJgqVhJVbkisBrJW9FScKKNZKHUkVgbS7TSCjEsZifwYAAAJDQmhMHAyoD_pUA1I7FSsCKNSUhaSTykYEMgAAAxJ8ASGgexoAJKLQkslWCULwJL_0m2gXAVXdLF8oiM2TOAAAAYRg5h8DkNAKM2AMCVBJQwJUYQkoAVXFLQGkszkfpQgCiAe8+B3GgAkqtSoJKJFKriHQSUHKVAVSyRhSLKE9AWcRAyBxz5NSKygBJcXFwSUuZMLXmNwSUTCVAVSyUQ67JnAADuHAHVPlNE4_wfASXHBcElkpOSheb9CCSyWbRcSmLiqWSiGUAAF4cAhY_hI6iIjA9AktaC4JLJeUFwFCSyVLRcBNqpNBjOGsACDgcGcbZzoAPQgCQ0AFIVAOg8FScKj_o2JMVJwNtRBakisLTWSae4MgAAACLUAOQgQQh5IrAcyUCit42koW0oxGOnVkisLTWSaQUVljMCqhBLeLA6JYLOeOgFICPipOABFamI+Kk4qsyONREkkisLbXQOYjQwAAahQAEkYAehAFPFSsBQpIrCokCSRWBtqII8kVhaaz0pOBiAACIKAB4hU0SLwB7kisBzJQMlHpBtJYKG0oviOm5_SRWFprJNlchDEAANwUGdiAEUcxAMZLwbSSKycj7NHclJKUSSlmcm0orqOm7+yRWXm01kmlEbpw_AACiFDzKULQICSKwDVFScCiSU45rNraURmxUnBAbRvLpNHPnD8AAKIUWYB4VjAC4BSA3skVn0AMrUxvZIrIknRxqIrEkV0kNoAH0SWAAFEKAO_fCEXATeLgLkFQAKQMI1CoAAJBOAABqFAAhUhAF8IRcAAFRSA1LjFQGEKFJQAAgjoAAIQUAeKupgyAfMnSyUiaiZOXSChlSJKVQ26nUgmgADkAAJ4UMSmRlBtChPIcJzTDqSlkqI0kkTlUym2mjSE6X_5WCySRqAUAAFIUErDIygNhOngSUKiSUuhxqIr1Mn30Zg4+nYgUm6ewh41AAZUZM0atYG3TJ4AVCZOBRAqEyeuhtKIbdMngcQDqEWbjyBHkaJkZAw0LBbspAImkNwkH9HYUhYY6JYVJwqIfoqTgbaiExJFYGksk0_wZAAEaCgChLw3CQdBjfAqA4EVAA9StkCSRWBpJJzoqAygNWNgACNBQhggxCG4SDIQRaGVcChXYcVJwU1Eaw3JFYGUejFHDcpAylEJCBLByAARoKL85j8WvHRUYAEkisBvZIrDaNRnxUnDqRRqADKFYGks4oTjuxkAAB4KBRQE6SKwuj8ipOG4bNY1H5FScOpFGoAMkV6TPg0lkmnejIAAFIUBZD3OUYBSCeZhuZIrDaNRnhUnDqRRqCkDSWf7Jx3gyKwDQAAeRdRQFCSKwukEyRWG0ajoSRWBFGop0oVgaSzd5OByVkAfabBIQ9RQPeSKwko7ipOUEahrJZKKTqRRrJWNkisDSWZAJwQwsZlZAH2mwZgGUKLIeooJHJFYRBmEkFScNo1HKFScOpFGv9SYZJQrA0lkKlGQAEABRQJWSKynTEDAKk4DX3JMUAqTh1Io1GAkisDSWSiJCNGY7hog1Gqm0V8PBURUnooK1JFYSUKRUnAapBJpKGDcO9FGo+skVhaazhpSoIxKpBqNVtpTEeB2VGRupABmMb0lRwBuUKwkqvipOGkayVORUnFJ1Io1BT+Y8hhlKq7EqOR5JgAIOBQAmkYQA8hgPEkVhBJKFUa1QLivFScPJFIICMkV0UNJZA+ChbAAg4FAAMPgEJcAAAAAAAAAAAAGjru4VbAWglWbAVhJgCSnEBIhCIAAHpKAAAiDAAo7gCOMLkPu8LvSOnsABbOYqDCCmBhUcS6BkAJP7E4KNNQAAEQYABh8AhLgAAAAAAAAAAAADrmMJqB7Y2b1EvQdGKyRWgQgjOSimkkMIHVFIAACIMCwkUhiZByOm4CmDJmXQajoSRPNJs1lUYkEc6kTyqTHRx8AdgoAS+GgDazTCXokng0M0dgADNG4U6Og0hUnAa0UOAoTwAA6AALQdHZN3BqJoM_NHYFoOgDmjcug5JKS9yLI1otHDp5qhTvIAZQACDgUAYfEgAw+AQlwpEwAAAgiAAEEQAAAAAABEGI2vBYsJLX8yEU5j4BKApAkR_wYgFPEiM6iBAFHwlA0lkLjGQAEHAoL7MAFlwbDwGxyoDRhUA1P_FQEUajGCpWEkon_E4+UZAAARBjDKbMPMR2bJaEB91w3AwEaCoJpZwqDCNTkRUFFGpy4qJSAYpRgAAhAwClVIAkjGEEwOV3FRPRUxUA1APJF_8bENioAAcCUAAEIGAVMpAAUIEQZhBMDldxUT0VMVANQDyRRqVxKgABwJQAAAftSAJDQCRMDmspUT0fUVANQohUHkijUp+VAABmSgAABTykASRiyCYHMpJ7MboFQDUDwVB5Io1L_lRKQiBGxOAABsHAIxUgCSMFgTA5XyUKyezEfBYrAayUWh5Io1kotC5WSkInvUCGiBaJoAAMwoA9amQgOXiFisnota0ULwGpWIucMnHkijUYcULyUhEII65IpgABuCgEvqaGHwDl4RYrBqLWtFC__YMDU7sXQEIo1EvFislIRCCOuSKYAAbgoMzMzHYEzBOCEASMgENCo_yvFZioOJNIrFQTmU_8GgAAMyUAAEIGAUEhAiDAQ0Kj_K8VmKg4k0isVBOZT_waAABwJQAAAnBCAJDQCGhUf5XisxUHEmkVioJzKf+DQAAGZKAAAFZIQDfI0TCxWV1Xh0KQ4k0armLFYTmUhkJSEQERJQnhIAABWSHjw8JQxR5HDCSKyujl1JIrDiTRqqosVhOZSGQlIRANAkUyUJUcCof6MgBBaEEo+5EfikrqoDp4RUnDiTRqKQnMpDNCBIlIRAYIkUy9GwJQCQEQB0UMfh41BMDLiheAmYsVhVJo1FIf_OgM9sEpjKQiAKQwl1GYgF9CIHZkdnYEpuQIChEx6obgYDXBMEk5+TAF8SYAIfEwAf+ThiAAEIGCU_ACQcNwMHQBgVJyyiMNkJk4XSCASKk4dSyQQJ5IrD+wkAY4mAAAAJMQOgDAqTnOEYfwTJwukEkpatw7lkggYyRWH+BIBBBMAABEGAAnhKlDN3GgwOTACkLoCkOtZDQhUARAOIAAbgoJaEhPjiMBGEycoosckTgAly2QSShxKNBCKkismsVH6bBWtWAAg4FEGACDO8zIOhJQii2LnekicmEuWyCJCJk5cSyQRahUkVlmUhEAkRIrAAg0FEeVoNBvGD4ECJk4RRfJInHmLF8gklLiWSCC1JFZKQiAp4mAA18ZAzABxUy8dBBckVgbDJFYXSCbDJFYdSyQTzhUAACghgAAAAjQOgJYmThFGlkicGsuWyCOfJE5cSqQR35IrJSNTlikDES0MAAEoGiMHwKITJyiixyROFkgklDi5ZUtkEIqSKz+5UEQIbkxlhakgDBDIG4EAHFyNDRPi5eElG+Iksd6SJwukEJ4VJw6lkggoixWAABQB4AAAKFxkExPi5eElB9Iksd6SJwukEkpcSyQcwFwYyRWAAH90IACkNAASMgB5cJ8XLwkpvxKHekicLpBCgFScOpZIJ5wqAAAAAciwAIS68DpSBcvAoRMnCKLJJE4XSCSX_6UdSyQQQJIrAAAACNDRU1ICAuyooBb+q0DnyRWSsSiShdIIUAqTh1LJBPNFQEpGIAAAAuyoKw7+q0DnyRWSsSiShdIIUAqTh1LJBPNFQEpGIAADKWgB3FQahwy1i2TWShJFpvyROF0gykohMnHPO3MskEWj9JFYFSUjECIgErSoG4EnAMs3+ihXDoSUIoickThZg8hA0iZOHEqkEdqSKwIrAF4BqABmwuBmCfC4DZKEWTCp15IrCCACJk4VaaEeKk4dR+NG+mgpA2l0i30KgAAjQsAD7CApTQ3pg3B1xMnCKCULJBF8Eyf+yMcSqQRd5IrLCRTlLwDUACbyUBCJg3A2BMnKKCULJiEJ+SYJk6Bjq4lUgi1CpOGUilX_KkRhMG4OQBgpEDZKhcrJEbM_5IQJSaRUYlRpiBOWSzPRSJbKcSqQRmFw5CpOWEilUXStTIo1AAOGLBnTgCyyB0CfEycooJSq3hYvkEWQTJ7LcSqQRp5IrkITdKLQPuOH4ABGhYAh6MwCPA2gqT1EJKUS6n5GDwFScOpZoJ4gmkIWQL9HwAALRIAAOMD44jaQPGwEpVuMjDdiBOZSyb8+BLdTaVSCBCKk8xCL_5WTwrA1AAI0LFmd1IDSztTgy4ANwiZFUNwMEsaCSgeDJgDwZMAGjyYACaMQAAhAwSmJOT09KOgMCOmMeHhpe"
noncomputable def WL32_1 : ℕ := zfNat64 33245 "ayVtxcrABJAMAAAGAgAQoQL8+IkGAGIXBJbcFwSWS24LgJLJQAEkAwAAAYCABChESDAf4KlYcaOm7kisKiPdJFYHmojkUZQrABJAMAAAGAivACY0AAAAAAAAAAAAATRgFgYD4kwB2yYAO2TBRQN6TAAkgGAAAGYATGgFgYD4kwB2yYAO2TBRQO2TAAPgGAAAAEJUIQMDQGA7ZMAcUmADikwUUDtkwAAAAEIGABCXDcDARoKgLOFQDUs4VBRf+GxGgqAAAAAhAwAE1YASVACQwQ8KgHzFQf6Nh8xUFFBWRUAdAAAARAwADi4BX8qAWkXK1RAQNRaBcrCijUm8XKwJpFQAAAUQYAAJcD2LA5wuVgSlUQEDXupNKQoo1GaFysCSAj8mAACiDBKSgA4uANuLlYSUXRUrAayUXRUrCijWStuLlaLIYAAAAGwMAA8uAJDQCNBUBZwqAalnCoKL_w2I0FQAAAAAAiKULwymTSkBrJZSFFGuUyZ3hcrJYBQAE8CgAAApnwBpBcElFoSWSi0CSyVpBcUcEgAJ4FAAAAFIDlvZIrCojeyRWB82z3URyKSjgkABPAoAArwAlXBKByi5WUCSv_kz5ipWA11mTSkKKNZK24uVgBlAngUAAA_AsDHC5WEl0AVKwGv_SZvJIrCijUUjJKFYBRNocREhk8CgAChAYx8APLhxDIAP_k1Bi4JLJaDFwXSS__JgAAJ4FAAADVPgAhcAAktBi4JLJaDFxCRaJLJQCiAE8CgAAB3Hx+CEDUv5UA6YuCSyWhBcBJZKAAJmPieBQABG2IAOrgAAipWAKQDioWwUn+n421E3KVAAFkngUAAAA4uM2Ng6AVAHTJFYVEOmSKws22onQCoAAJ4FAABiADy50IWAUgOQyFScKjNQyFScHttqI5FIAATwKAADGvDaenGkCv5UBqsqAaiei5WFFGpX8qAABSno0dgAkSoAKZ8AQrk3mx8Ggy4JKLQkslFoElkuFy77RkAAQQUgobFoABPz__kJihkAEloQXBJZLQguAkslAAK+GzwkoGIB4h4mQF6fAPK5BAJ+bA9A6lQSUMCVASUAr0VAGV5yUAAgxYAf58ACLyOQk_jQKWLj+pdJevFxLZLJdwFwElkoAARQAAliwcgGNCAHlziBsAAUIqCShQioQJJQTAXAAAABCFgDOH5IIXzmYAAwJUEmShgSoGpJQmBsAAew+AACWLBjBhoCTLgGkCoAUhUQUgefGqRm4qAAAWgBiDoACNdAgXgKgBSF7FYFIHEqmoCqthsAAFYqDwAAAhFucYgM3FQApDx6kCkDzUTRxUAAAADOMgBcFzCAKQ_+dNOKk4cRUK5GIqTgcSrec6FIAAhJWIoBLFWBsbj6+nAOh8IQsAoIuFhE0l6YXBJZKLQJLJVBFwAVsJgAAJIsAhC0dCYBSFqDpvJIrCog9SRWB5qIK4qVgBWwmAAAkixXgFM+AFlQCIpcE2GpLxwuCSyUWgSWS4XLk1FwTT5p0AAASxYAth8AAnA1oUmgYXBJQv5UBJQTQXB1emxBcQAAliwAICoAO4+AAAA_6TADD6KBcFkCGhUAAB0SAMCpnxzOwAvjYAv5UElC_lQElCKBcDn_KMGllIAAJYsEtKACAlCsByNQqThUZqGQqThCls91EcilNBcB+tGEqGQhIuAAHiwAJljMAykisMnHUlCozWSgcajk46DKSK4JGQAF5LGYZQAtIsDYASqjmdgBMFSsA1JIrAqhqSRWBxKoQQqV_sLik0EDuyUOoKgACQegPpFQDFSRWH6lamMVJFYHGonRiqKBcAC5yYLCAhwWBklr6EADTQsDQEAyheNkOv2kwNi5WA1kspCijXKJM7wuVneLgAAFoAAhCwBri5WSGOpKx8oVgNZKWUoVhRRrJTbFysAKsDQRCsgNYGgZPuWk2CwCyLlZLRaBUrJyNSgRUrCijWSoQLlYAB9AgeSQAGCLAQhsTIWAsBcrCSplKFYORrJUylCsKKNZK3AuVxQLgAAAAhCwHnIDzTiQegAIHQR0AAAw2XGeMooFwAAAAQhYAxJ8SD0AAXTKgMPFkaUgSWOgeJooFwAAAASxYNwA9pEg9AaeKgIhpyRWQ0qhNyRWGE4lUwIVRQLgAAAAhCwKAHwCkBvJIrK7JVRG8kis_i8YTbURq5QrigXAAAABCFgxryrHYoQsCtC5WfrLgmhUrJyNbek0pCijUUCULxaABJCAjAAEkWDmDuY8AAlwBsWE5WpnBDCYDqLlYSUppQrAayUppQrJJRRrJR1FysogAvEeEppAAAHKEBhLgDYvJSkEQkCVAXRKgGpdEqCaORqSBKv_JwAAlNIAABhLgDYt6ChXQijAp4uVhJVTFSsBrJVTFSs_qZUUayVTxcrJoAAlNIABiAMS4A2LecoV_lCwIGLlYSV+ZQrAayV+ZQrJzRRrJUyFysmgAtEv_iY0gAWMaANV4hUoB6hUD0jwVB_42LOFQUUakaCoHrB05AP8NwA9peAJWXdYpTyiCri5WR_ZhKBUrCKNfSk0pCijUZCULyaAATTKAGOZMYfgPcu6xSniJEgF0XKw_6TK8KlYDUV8VKyc0UayUXRcrJoACUmmFPTZrALpYgHAusRSnyEDVFSsJKQ8kVgNZKQ8kVlEoo1kpqipWTQASAVJyaZQAyDJjKUAF2QAKuARoKgIHFQDUgcVBRQVgVD0AAy++YgCCgCARS4CCPzelARoKgIHFQMRqOsKgooKwKv7KQE9JIUQAOGPADoLhgTp+gxoEyFSsmoNkoVlFGolYqVhRRqMlKF5NAAKIASeIg5ABxcA+Fy4bgFYFQEDioAgcVBRf+GxGgqAABKcQAAAChAdC4hUoMgxYqAjUVANSNRUEWcjUYsVAAALTDCwBUToA6JcMCdPAd4XKwyiTSkBrJRCFysWEiS6KNRIxcrJoE5KoURaADHPIYYgVsuGBOngKKLlYSVbRUrAayVbRUrCijWSqKLlZNAAspEURbTQF+nkMmRsfHZtF0uLoDiLlYSUnJQrAayUXBUrCijWStuLlZNHI+koGIAAArDgBJLQLkqCIqAAwbAAAOseD_wsA1B4ACIAAAiDgBjFRnl05VCuEUapQvCSq+LlYDWSykKKNZKj4uVgBJHqbioAAFYcEpCDEbADULlYf_JjClCsBqBXJFYUUaj6ipWhAeDiYSqA6MG4AAyDIFNMgDxFSsJKrEkVgNZK9EkVhRRqT0mFI1DiYSqPwMG4nh4qoEnRYGaUC1n4UFzSlquAWi4JLVgu_8nElktWC4FpJZKOUTKYADEAAFYcAKJeBOnwxGxZAyBxEMtC4JLJefFwElFKci6IxsAAgYeAAA0BSHwDueGI2AAktCi4JLJaFFwElkpZC75xsEUAFkPAAB0OAAYZU2dfocgABBFQSUEEVEkGGkwB0AJJTG4dw0AAAc+AlkbWDZmFxetgtFJMRyrAqTlBqI1ZEVJzz5VAhm2ojk+BUrGpJAAMA8AAIw4OyLl5ZHodJ2SKya8soXjmSl0KNpjaS22mm0op5NHaCyRWRSaADDKFYAAKw4swAXzQcZSEDJByhWXEcrSKk4VEanYKk4HebPdRHIpGoAASBoAAPhxh16R5dJS_6ELUkVldnLDipOUUayU5pIrCijWSlgLlZBoIApOcWKwAB3iQBsMfljYOgKQFVkisA+HQq0kVnkJP_jofQVJxzDwAA7hoAAMwOToBOhUA9YqAHrFQCX_hsQqKh1DwAA7hoAADX3jIUgKQyv4PHb0SRWEUayVzhUrCijWSurKF6QBxuAFJHcNAAAAPMg7OgIVFQD1ioBqPWKgEoJyKgAAdw0AABsGCWMIBCZBydFkDgDwBbBoALYNAAcAeAAAAATBwBqWIADf8+dPKNgAYfAFFBqIYJgooGeJh1DwAA7hoAADQALhU8XBkihZCpWURqP0mFIDWSyn7zEKaKNZK8ouVjUAAIw0AAHw4PaKocCwYJJgBSeaRgFJ5rNFCd5MABDwmAABWHBmg2N_Gh4AAeoUKhADi4L1NChA_zC4CLhUAANQAWxUM8dAABpHoAA6AO7IAkHi0XAEtKF4DTC5WEUa_7JmmFysKKNRuJQviIEeHFwE0AAAAEXAQQ7BS4ei7koiJIrCzJX3kisLo1kqRSRWK0bPdFGsllMRAAA+mkDKUoABLqzLg0DxsGIrCpOUE2hVJQojmSvPJFYNaKNZKgwuVxEAjIpJINDUFoAAQS4BsHn0XA6HjZJGMlCCoYqkoURyeAqTuzJFYNaKNZKx4uVhEAD+pEAATpzYgIAhLgTcgDskwBxSYAOKTB_1GA7JMAAAAA2DgAalkhxkA3AuVhJRaFSsBrJRaFSsKKNZK3AuVgAABLoAAwADgCADzIAkNQYZAMjKF4A8C5WA1ko8C5WFFGoyMoXgAAAAAN8yDo+AjQVAWcKgGpZwqCi_8NiNBUAABEAF1LwOzo7TgAXiAA3wBiyAFmJgCnEwAekKiEG0tABh9_5GAAJDQAAbCQBNFN+lYCv5VOQqJ4LlYDUd4XK4qUUanYyoigGDE4ogAA9EgzARJcACKkFWLYDOyheC2SjcLlZNHI1kq3ShXWaLRRrJSsFysihFJjKQAAKIcAJNGAHFwAtRcrAHqUKwGoKQoo1GRFSsiltrpoU4Iw1ZwAAOhQB4y5VA5iVAClQbMDUFCSK8DWaKNRwhUrIpaXjLF85KUAAAHQosyWhAJwuOhYrkUgq6NmZISRWUSbJRmFSeumUazFzxUnKDRRrJSGFysigJQlMlAB85EDoB8LgC5NjCsGQimVAVvKgGpMguVgBEyHRRqQPKh6AAAADYeAEmXaspfKGgFIApCLvY2BSTSrRXFGxbQqHoAAAANh4McO5KZcpKR0dqbsAJDQBtxcrCNplOSi4KlYDWSm+KlYUUayVtxcrDiBBVElgAAABIaCuFgSIXKwkrfCpWTUayVWhUrCijWStuLlYAWgSAAADkJNJFYBfJFYCfSRWEUaifSRWVmijUZMVKwKoHCyI_gUAALwk0lPXnTrSRWU0UmiJk4QRrJTVFScOMqW6KNZKKQ6lGcg1bkOI6CAAPRQ2BkihsSn3TpUZIrCa5IqkoQRrJSjFScKtFGslDGSK6z49yKM5BqHe2IQAAUgyromRn9jpnhUnBv5VJQgjUScVJ56VaKNQCZIrLpSQQpAnFoZSM6czpL1uggBknZ0B4GYUSLwauUKwqjEnpIrAayUkxcrAaiGGoNKF4fyRhqGUGgAAeBiDACykALLgAREACHgCQUAAAAAAAAAAAAOEpAISIHgYMhYo2AAA6AEJjIcJcAAAAAeBgNjQCqhAIilC8Mgk0pI6NZKFguVtECjrRRrJTOlC8AYwJAAACYKAB7pADiIBGwqAtAVAPSwRUGEe_+LhUAl14yAAAACkFAB1QgDbi5WElFwVKyOjWSgELlYUUayVAJQv5YVAFeEgAAC+FBiAEkYCGhAGSlC8AmRcrI6NZKTIuVh1oo1BKlC8BCw0AE+hgABmAGtIKw4CNBUBA4qAakDkYuNFBEx"
noncomputable def WL32_2 : ℕ := zfNat64 1249 "BWz4BgIBEMA1CSyOOgJLI46AWklBsiNwASQDAAABgIAGAgANDQAEQoAA8NAABoaAAAAADAQAEQwAaGgAIhQABEKAADQ0AAAAAGAhmYADhIYGbcXKwkqcCpWA1kqcCpWFFGslbcXKwASQDAAABgIAEKEC_PiJBgBiFwSW3BcElktuC4CSyUABJAMAAAGAgAQoREgwH+CpWHGjpu5Ir"
noncomputable def WL32s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL32_1) (dpk j 2 WL32_2)
noncomputable def WL32s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL32_0) (WL32s1_3 j)
noncomputable def WL32 (j : ℕ) : ℕ := (WL32s0_3 j)
noncomputable def WD32 : ℕ → ℕ := rdw WL32
noncomputable def ready32_cuts0 : List (ℕ × St × ℕ) := []

theorem ready32_cuts0_ok : CutsOk ready32_cuts0 := cutsOk_nil

noncomputable def ready32_0_state : St := ⟨26112, 271072, 51168, 255035, 29184, 45301, 29666, 44151, 29666, 44151, 29184, 45301, 28545, 182117, 26112, 285696, 77280, 526107, 106464, 555291, 136130, 584957, 165796, 614623, 194980, 643807, 223525, 672352, 249637, 739110, 80352, 284219, 110018, 313885, 139684, 343551, 168868, 372735, 197413, 401280, 223525, 686976, 58850, 89452, 88516, 119118, 117700, 148302, 146245, 299817, 172357, 585513, 59332, 88302, 88516, 119118, 117061, 270633, 143173, 556329, 58850, 89452, 87395, 240967, 113507, 526663, 57729, 211301, 83841, 496997, 54657, 467813, 0⟩

theorem ready32_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD32 ready32_cuts0 117 89) ready32_0_state = 64419 := by decide +kernel
#print axioms ready32_0_cursor

theorem ready32_0_covered : Covered (toCl ready32_0_state) :=
  ready_cover_cursor WD32 ready32_cuts0 ready32_cuts0_ok 117 89 64419 ready32_0_state ready32_0_cursor (by decide)
#print axioms ready32_0_covered

noncomputable def ready32_cuts1 : List (ℕ × St × ℕ) := (89, ready32_0_state, 64419) :: ready32_cuts0

theorem ready32_cuts1_ok : CutsOk ready32_cuts1 := cutsOk_cons ready32_0_covered ready32_cuts0_ok
#print axioms ready32_cuts1_ok

theorem ready32_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD32 ready32_cuts1 128 1) (ofCl (RC 0 2 0 0 0 0 0 0) 0) = 66791 := by decide +kernel
#print axioms ready32_parent_cursor

theorem rc32 : Covered (RC 0 2 0 0 0 0 0 0) :=
  rcOfC WD32 ready32_cuts1 ready32_cuts1_ok 66791 ready32_parent_cursor (by decide)
#print axioms rc32
noncomputable def WL33_0 : ℕ := zfNat64 33240 "wFCS4eCJRQTJkstLiWDOKQBRUrLsxFIG0gvaFDbhSheMS6dSyRQ3Jx5AAg4FFTT05nOk9_GgBFGAQlxn4sETzR2BnoqLKGeioPJxJp3UqAAAAA3BQAHi5DxaU4sUWalVf0lR1hkisMpZmJVipOHm2k2akHKFYOQAAAA+DAITxgAN0AhLiFOAsA9AR8RACPiIADcjwAAAAAYCAAPLgCQ0UhE_sWCagCksp6F5nZkKaaeTiTQUxUrAAAAAABxdXRNQUWAahVnejLFJFYZf+LUxIYVJ6bdTaTZqFsoVgABAh4AAALZdbZM_sWCagCksquFoXRsKaaeTiURYBUrPpOQACUADqkwOjs7H2ZmDHMIUgYAggTzJgCFxMAElCYAAAACkDAASViYD4CNmjsC3xUAW+Kg8nEmmcCoABPAkAAG4KAAIrCOoEMJqFWmaMnkkVjEylmYlCKk5dTaTQPGzcUh1AIGCQAAHQYAAHCQVPgr2aOwNfFRZQ18VJSQjycSafTKgAE7CQABeCIAAYsS+gQwmoVZxoyeSRWGUszErxUnSkhXW2k2akZKFYdQBWAkEEAACpPIYRZqFWisDJFYZSzMQmFSdKCFdTaTTlmjcUhtAxcRBEOr_2YBWAsTYDAv_jT1TyGChTBuAKbL3tiAU3E6m0mjHyhWABAIWAAESDBnd3cbTgBJGSnFgGoVRXJIrDK3xa_SZT3JFZdTaTZqckoVgAHlHgAAJgwAiDPVFgmoApLKoJeZ2ZCkPJxJoBIqVgAHlHgAAACQ0mmLFFmpVWHJUdYZIrDKWZiQoqTh5tpNmoWShWABwsmAAAAHjSaYsUWalVYolR1hkisMpZmJDCpOHm2k2ahdKFYAG5yYOgAAeAmYBSwgCQ0jcLBNQq9AShSGUszEUhxOLZlIYv6LlYBV_4bAAAACZLgCQ0LyLAOQK_FR_hSL8vGoioOJxJp5kqABCAAAEMGAAcIAzXBmFQYFgGoVfiJTlyRWGUszF0ZIrDicSaMZSAYb4HQAAAzCgCeEQXBQKxoA3JwB1C4AAJKAMPgA2glAABcFAGAVKIMworIsBBAy+HAGDioOrOWznRTTxUAcQAIuCwAAFi4EATAEhpHMWCamlkYAgWKz+yxfJiKQ4nEmiyOvrlQAKQ6AAAAkSZPMWAahFg0lRwMFisLJZmK5ipOHE2k2apXKFYgQFIdEvFwAAA8yZpiaO4sArjZuBugqCydvMhSHE4k0fx1KQAU_wHgSgAaYmB0dIyECtlwBIaF9FgYUdNwrBQzBSE0umoQhSG04mUbiVKQDaURqAAABpy9yEYDbh0BKSTSlE1eB3lCsOtxNIogqVgHX_SsBRABlg8AZsulweKWLAYc0dgp_0lHBJFcxJpZIJ3ipOPTacTKRSHlCsA2lEaxEACDQsGY7RieIsA1CrzVGWKSKwylmYjkKk5dTaTS9mjcUhx9gzACFUSEAAAEEyUTFgmp7JWBSWUZyZCkuoDnDeTXsmyfCpWAAtkeAJNAErGwOgBJWEvYQDC+AEECeZMATzJj_TkBKwmAAAAA3BwACwo5IIxFsjR5qFUGCVHY2SKwylmYyXRCFdTaTRqOUkVltsJOpGIxjyMAJIAcgfPIYTUKvo0ZkZIrDKWZjJV6oR1NpN+MbDlJFYAAHhxGEko03_jcP9JiVAKfEcxpPgIoApIlsxPcyFJdTiTTbHTACpWAAeUeAACEHABuYgFIk9BCakAESGAlGTySKwqlmYlCKk4cTaTVlmjcUltBZyMSEAAOYcB4A_VnvkIDqHTco__VgUhlD9GQlDzbSbVQ2U6UKwABrjwBKQeAAOSsZ+gQyiTUo1UFIYaKLReDIMJAnLqbSbXY2FIcSjMwAhFoADjHidQcGNqQAkxCjsIAQQJ5kwBQ8mDiBK4mAAAAATBQG4nkMBzXUJNQKTaeQzRkj8kV0W6m0m63NhSAANceAtYTAALUhPySURzXTKTWUkis2nkoC5jGJPCpPRTqaSaNQgkistoBB8cT0X6aUADiFgdP6XM7CzyGA1CT_9GBOSKzKWedLQs0kVl04m0ms8NhTpJmAkhHQACEEQAaQpNky20BCfg1GoSaK_ckVl0shHVLYxK8VJy6cTSTRqWskVmW2hJAIfG9Rw3LQAAXUDIT8Go1CTRVtkisyllpKpbGMlLpxNLd0ieNUOkistoA1DtOGKohVfg9CTShWCo6AD2o1M+ASgaKKiaTZyKRBFIbTaEXUpUAAs0qAABMFEeHgNrqPaSHwNCWK4FvCoAt4VF1OJNPnlQABOhoAAFoUACTqAEQoYTUGLsD44JIrLJNKsxmQVJ0CbTSTR6aoqVgYRsCsSUAAFoUB+LGgAVGTlFoyTUYlWlqMjMkVhlLMxSEVJzjdTaTZqycoVltACMDCcAAGIUIICDM0RBthiwDUqjrUK5FWCSKzDYT+5kkwqTmk6mkm4ONhSfT6ZQAAAE4UAOHqABcwA6uBZE5TKQLob8RrnFQEx3wVHE6hNOUlRlB6AAABuCgAA6QG2yABU6uDychoCSBPEmAJ4kxtDaMQAAx8ZAAARBgNt4QAG+B8mfQNAAdaNgDrRsABFAAAAADAQAAcYPLhAlrIADTX0RAEUCepMAT1Jg4gSWSgAP9EQAAEQYAEJcAAAAAAAAAAAAY7hDKjYBCRAiLU6NgLoDdEIAAAAAAAAAwEFUB4ASE_AsSJPbstVGimCOG9hMJMUlFSc4nU0k0H8mU7SE5HIBCFlATIbACgwfSmcPwpIiVSorOTRuZbCFxamMluJxAI2ayazFOptpADbmwdLpFAOziwOjdXExsWC0dSZ3dOg4FTRFgGoVQUhlUQtKlMkfkisNptJs1dKUKwAMoABBwKAMOXACsmjsWcrEpDCXSBGwpDTcajEg62KVS6KiegBEAAE4cAP8iFoGBYLAIxCAPwTAACiYDeSMAAgQIgAAnCgEYlwTBwExDoGJYcqCiFuSoNtxKJOoqLoA5DoNAABOFBCBDiIJxoKA0AlUIBNZMAANJgAHIkMABAgRAAAiDAADwhIRcKQ8AOQYnzyoKOn14nJtKQ23GomTyoAHIdBoAAEQYIQ8pA4OdACQU_AkjEWAiZo7At4VAFmCoupxJphoqAACERAAADwEUTLUEwE0AUwIDrKf7MhSXU4k07eVFplIYgAABGgoE3xYBqFWisqKk8CA4ylmYyUOqlGjeTRTGxQyRWW0wmCcN5dByAABIGKMHi7wCEiBEGRcNBaQIREwAAYOAAAgkAAAAA2CgHi1w+YmBEGyQZBaQAKEQABQiAACBMAAAABuCgCEEQBIaMaHgIIB+SxeAVwKi6_iciaXwKgooRAAAACyEQBIaehHiP61PS21EUhlFuqW5i2IqTl1NpNmrcShWF2ihEkstAAADQkT+o8E9Lb_dSDgWKwy5kWpiwskVjW6m0mzU3hUrC7RQiSUpM5ABPIaALCRMkKGwEjB8B6B3FJgxYrroKRMgClCu0nU2k2GZsKQu0UIklAACNCQZzo6RkIAQVk3xYBqFWisuKk4tMpZmMlDqpho3k0UxsUMkVltMNVXI4bwigAa+KgTfFgGoVaK0IqThlLIcjJnJQ6qWaN5NB8kistphqpomzmEX3hMAAD8B2DxYBqFWinZJFYOBgz1UYyUOppAYnSxqv8kVltMJVNpZL4gRyygCchIACSsHewgANEAIJ_5GJ5kwA+8mDiBEcmAAEohAABCDgATKxHaBDKLNQq0U+ZIrJplLIxkodVhNG+khBMG7AyRWW0w1U2lcWiK9pyAAwgemvPIYDUKtFaYVJywhDVLcxkodTSTSnGxoSRWWkulU2imUCO0puKIGwZgEqxbABmrCCEWahVoqFSRWYTssGcsjGSh1aY2a6Sdcwbr7JFctNpdKptLLIUCOFEF5MGcslkKQAkrBIRIAk8hgk00dhVCfkissJZmKNCpOHU0k2a+aKiujkqnENclAeSSk1AEADQIYDUKpFVUVJyy8YWvQmUlDqaSaE_JFZjluMJVNoshAjgcaiBqBYACSsAWphSUkAQPBOQHDEwA4YmAB+RMAB+86AAKIrqozyGEUalU1CuRWakisMNVGMlootHU00lcBszeuSKwymEqhvaN5ZIJUTTUQgpmMF4Ax4ASVi8zyGA1CqRWmFScMKAVS3MZKHU0k0tBsl8kVltMJVNpFhAjn_2oATcNAFeVgA00BBhid0CGE1CqI9JFZZUzLXjTIUh1NpNF8kisggARf_wQAXqKidnZmBjY8dgQO9hACCEUnmTHkQgH2kwcQIjkwAAkEIAACQMD7iEBIDR2AKTqAd0kVkk684biaHhJFddANMVVvc5FFAAK6JAPBYVELedA9Q6AUEVHmQgBhkisOo1JOBSAF1LIAAKCQQmoVSKYskVhIQrKWRjJQ6g0bNdJE6YN0lkis5m3GEquObOYRQAAAQQXrMJnQEkC7qoqABSRQ4onEBiougApRGAACELCewwQn5o1CGpUSK7AqTmGw_9VhjJURK1M4mlD6RPGgkisumkskk2zmWqCU2ex0GnKlsAYMdpx81A+B4Zo7A_gVAH8Cr9qkdTiTQxJIrAAqAjAAFEFwK2JnJ0zx+VSLNTCVT0oktXpIrMNhLIxkpPVCudTakJOljVSpIrLJdItVuNdJIH0lIZKkdNwBHIUIJqFX9yU6QqTlGm0WVqY6DJnJTqbbSTRqrEkVhlLtVRw2cwihs9CACPACSsABqgCNMI_kgCB4CCAxgmAGMEwAD+EgAN7nQABRAtTh+B5Cfk0cjEEcnS5yu4qTmEu00Ym8Jk9ROJlpMxZKSKwZLVs010o2mqkEm1UyjWikUOhQvAAKjADjIAmJAAAAAAAAAAACLAQADfDno4Qh4D5UAWC4BgY8AMDHgAYmPAADUACQA8C4NQfQwmoVSK9ckVlEo__UpjJTqbbSTUQmy3SRWDBmK0yscQglhG06ewAyR4zHwMrGgx3WUcrDwEECGBMAQwJgAB8TAABfOgAAJgwCH0YRAHJHhSJTJTKaVeOFlQcbjUShJUFd10lBf1GAAAgDAFeMkaRYBqFaSWdGIaSKxqBpevgm0kVlU4m0mgPyheVWs0U2mOh4AACIMGYHIR3qGlEiwTUUlUDuSK5rYfzLQt0kVlptpNmq9ShWcQ4l1hDcHkAACYMABFrAAdIEBRWiVHwGgJoFfioA44bDkMIxCagFE_8nAABuDgAA4wBGye8mQMNA65GAABCAMkTnUCCQ7SgABdkwAAFgoTnKuNEwBMRCCaBJHikitAnU2hyNOOIAQcLgAAehwPdKF6SBYuFlCu00mmEAobEaKk5tOJpJoGVMnjkwixV27bMSmmrqRgAig6AO8YBJZBiI6+ypSAsEs24AogApOoE0+mnFUAP_FxBAAwhDBcrfiKFyg2UK6vBOnk0whJTacTSTQmzULUxV2PDNwBKawVK5qQQDOJcDouFhILM2dSHnYMpsxTEC5YRAuTzPpiBFaYVJwABxUnsNtCaEiKk4AVEhB87AAAkDBTdkJ2Kk8HYgdfY2I6N2dDAgJSOx4eGl5a"
noncomputable def WL33_1 : ℕ := zfNat64 33245 "YdBUA9AVYVACPCoASiZioAU_0YgAACEPAHHgY2ZzZ2CkFAxFgAIIAGJJgJjqwWQmAEMHwAABCCiLIwCLTDWFHkGgoIEpA44jf+KlZ8RyCay460KVAAfQAAKQUAVYiGsKUMNBQQ_yXDSKlZQlCDKmDcUhlVAvE0cykACCGQAA3BQPgAEyColwCgmQiIlJRShBsKRCZXnMF8mjOVvpGQA5MIAAAmDgDTl58GQD2ggdJSEU4SU_w2Zq0JFYZS6TSqdAwX_xDgHJhBUmOwAADwUAXouAAs8h0EiiUlJhopBEpdxszciSK1pPx1rpRKotAnNd2UdAAAJQojwAmxBmjIBXR6sdACdQj6BUcHKiikSTaUiBKiTQLgJyaQAAB6FAHGL12VgDYIwEpIIfkNjGlCsqmUJp1wyEIDkqvUTgAANwUFNTU0NHOlIqAEhogIYPg1DoSWSGS89BUrKzQZi08kVhxqpNGopDqZSbQVonDsoZQvAAAlsPchHgDoDACpWZOXiYunJFdFOLLVYmzUUhDJmJtBBaAAd06AeswCVHE6THwGgDoCHipWAaI2FIcbeLxNAClCsA686Yhox47AADoAGhJgirWA8CBBg+AeIqVlZJizkkVhx_yrE2ainKFYFUm0E14XAcQA6QIAC4wAwabcHgDofDLhlFSsLpMX8kiv+5UcaqTUlmjcUkkLpNoJ9QuBIcQA6QIdsxeBACQ0AAAAAAAAAAAAIwroJsAdCHZcF0kVlZJjsUkVhxqpN_8bN3JFYBlKodAwbhNMo5Hs1APegmwB0D3lwKyRWVkmLgSRWHGqk2ARsKQCDQRkRcrCzsBiHIFkdWWlbGzcA6FyyxeCskVlmskxI0VJy6caqTRqrckVhpCDQRYBcrCzdRcxjkihZAfHgCOuTUBaApSxnKQO6xfGtGzNSJIrDjVSbNQ2FSsspFBSEHw4MohJJRABAQAFhABq4I1HAWFwESHgFVFQAqoqABcBUAAAI0dkMCgAIIAAQ4Hw6bhOMoXn9UqWpAKlYXSYvzJFYcaqTRamjcUh1MpNoIRkoXwdDgAAgNgBIaDkRwCBMAAXQeAC6DwAFiHgAP_NQAAADEOUIiWwbBHQHGFSsCeRsKS46cWiiAeKlYFBoJsguAI6AABK4CQuAeg8ArwqAFeFQH_k4XoVAABuOiGBwAABGg8ZDJoRkF2iRWBKQMkG0pDiVEsGVABEAlsFARIrACZwIvLgK8SQcNgAI0BCAElCvQQ8VSYmAKk4ZSiTRqvkkVhpsJhKIII0ZjwCgNJVHIJIEUZDYACDB8EAFyUyhWVkmLgSRWGkJtJjYUgFUkgtBqYTieJiDzDB8FVkxkAdAlIBKZjy1yKiM3KFYHK1oMwFxNQ4gqwaABlVBD6ZhGYdJcEZAuQVAFyCoAMoFQAA9JqgTaAHuLmMYRw3AOQ4bAWhhJFZWV6HkOYyUsmkok0auDJFbFkouhVJI5FvqyoemE2l0o0kgY+zmQASNB65Yr4qAMhPwiLYRACLCIAEAEQAAxAAdcNA2LhsyAGVYtIaAOgDIKlZBrJMTFkisonFh6sTecGwpAJtBEMGzMYlUAwxfHgCCTWaDR_RYAyAcomADlEwAHwJgAOOFQ9AAKgABwgk9cFxMB_YqAIQPABCB4ACKjwAFGjYAACYsABoHFMe9OhBGQGVlCsyhMXskisOITZqo8oVn7HZIrFRZqD3LF4xAsk0egAuN4IgRDcPLjPgGIApAscbSkCo5EOvLlQEUBSAB+JSLcXABMrguGh6nQM2JgG9FQAKQBjEQA_8xEnlYAAGxEAGAadgekwhABcYPgFWKlYCoDYUj04hRA2qFMWhUQcN2soIQQO8IQFMDTBToAyAeCapxUAVqKgCaVHTgACTgZXMQAB3BEnc6DaxEAAREUgD0runAAU8PsCAC0UoAF80eKdAJQncVSeUgDDxUATS+6dRQAHuBACMCcAwxK0BGRWdALQAAEnKwCkyGnAFkCTUZrBgAsROBJMWeQwYhn+CURRa3tMp1mqj2yzGs2kok9WL89eAnT56FWumUohfOH4nmrOHNYvlWsl2srqVqYax4SAzoI2s68HmJmQB0P_ERUCIAUIRAAr5GAA_8dAAAoHgpBaETjYE7nZ0FIGACdSEQQWlQA2UqAJo9kqAAFcVAABuBiLp4MAXbQ3AwUBYAAIxUB5AAYKsCFJgABBBwAAbgYBLacAwECYSAmgAFCBIAAExMAAIIOAAAMBAWCiz4BCXBaDALuLgnu9yoB7NZSBURyS8qAAAAAWgwCmT4D8WBdRcE93yVAPZrKSjAQVH_h0S8qAAEeLAAAWBgEEHwBIWG4KBgLABPbwFQDka7AKgCaOURlQAAPBYAAAP+fAKCwAT1vBYrAcjVBRYrDKE0cxqLgAAdCxXAoAABhJ8EwUgQAnt4ioNI5GuJioNITc8HQAAOAeAACkFAMKzipSEEwUQQA_+fAHHgHoADOEKPCMAAEYWAAAMBAaDVEIAifCEFDkP9FwT0eBUA9EQFQBVvofAAAxBoAAUAUAow+G4KropAA9LxFRPRyNf2FQDQmjlTJUAAIQWAAAiDBiYjs2Z05uegYD4MCIKAcgCkLwL15jYUgcSaYVKgAAAAD4MABIaPQHg98dAVmKgCsxUf6djiTS8hUAAAAAHwjwIgOm4DSipWH_l4aUVKw63FcahTJSAAWgOisVAAAdAlHQmoApOINRZZ2ZQbJFYdRVOW8m9XNhSABe4ONIADoEgdnQEwYtREfAsB03AKuSKw0lmYowKk4dbaTZqksoVgAEsHgE0AQAAEmIA6XG8ER8DeHTcAUhpLNFzJlRUnDqcSbNSJlCsGIAAACgCgRoKMIRHwmoApPlNRZZyZDPJFYdTiTYZm0pACiAAAdw4AXhEjQUWoiPgWA6bgGXJFYaSzMUmkisOttJs1N4VKwD6C0YgAEaDgfAA4sjQUigiPgYY6bgKtJFYaSzMSYFScOttJomzRuKQmtVbc3BNBiAAEUER8DDHTcBVpIrDSWZiTIqTh1tpNEiaNxT1IqJrVW4NwTQACNCQEVER8EGHTcBMZIrDSWZiTIqTh1tpNEiaNxSBVazNwTZwmQAAAK0YyUmBp5o7AFIF0IRszTqSKz6aTaTYxm0pAAOvNmYAC0EwHMdADx03Aa6SKx6TMWZjXkkVmU420my6NhSB0tWAmpkdgAPWLBmABBqcRYO0UwaJLDsdN6aVSS4EkVlWwlmYgyKk9dONtJo1M6SKwgzWq2kJphAAAADNBCg9aSIDBMjAagCkCfxsKbCytutpRJSBU1GBeZUdSqG0AYxGjOjB8Is1IhqRJX2SKyqYSyAswZyWum02k0apjJFZZAHQrD0SnEDjYQlxAnBcTgenoZB_46Ar8VAFfiqrCcbS6TS_xUBxAAAApDRBzpnOlM2AAcICmXAEhoXIWD7x0BXIqAK5FR_52OJNL5FQEkCygAAAPy4CArNw0CgDpuARckVhlLMxTgVJw620mzVBZQrENBJIFlBCAAICidJaHBAHRENYMGwqVgV00dgCkCzkMyDaSKy420my5NpSF2Wnm0gAAFkKAjAiPgF46bgArJFYaSyKtJFYEJw720mgpCq1E0g5kSGOiGAAAkYiPgHI6bgPAKk4aSzMZKUTjbSa9I2JmSKw01WovfZNYQQAHOGQMwATNIXER8ESHTcBqJIrDSWZiTAqThxtpNRsbCnhg0VWomkVgiQwqgAAAQyOmIj4DUCWpIrEJcZamJ_CpOHE2k0RKSKwqpR2OzA9DrZQCrjB8mwANZEnER8A8HTcB4hUnDSWZjJQGMV8420mz2NiZkisOmmq1GyhBAAg4JAupYzjoSZqQaqCdElm9JFdRsJZGMlsokWzmbaSCEwbtTJFclNNVqJy2TXVSCTxNgAAxjoRZqRQoCVHTySKwwlkYyWygYcN5tpLJjZm3UkVodJrLVSi7dkzlUeh1soCvxQuTZnUgTLSAJDS_hEBJAnaTAHLyYP_NwxCIAAEhWAAADF2QAGuGVrDxsFbmjsDDhUAYcKgP_JxfdOAAHoACtjYAN1kACQdAAqKgAFRUXQeNwAG04ABSikTvNgAADor9uPFzHEYRCOm4CCSRWF0sgQMmclDjbSaNXKJ08tNVKI8WTWEEnebAAGYAE61hlCtEhYzBhBg3AAgcKTKC0MYSK66ZaqTRUilPFJKRyUQAmSNjiAQkgQABWieJFZ5jBeDxDRmANa8VJzSC3WZlJTCZaqTRkCdPLoaa731mDyFhlYmgZQBAwTttaWRfBHgroAyCpOACk0_8bgm0nNjZKU+whUTSC2PIZxiYAAPbuPBQIPZAApYx_EPB_46Ar8VAFfioEfORNL_FQAH4kIAAFgkTZTJgHgLGQaDoTWyh20Z4xUnqIWR9GTOSi1HDebSaNVpkisZzEZaqUTSEGogEkABBKxM44jA2R03ACuSKyyFkCuSKy420mieyRWHhVYogPSTWSzVQnuPAIEomoGlxDwb6OgKOFQA7YqT_6Vg4k0QMVJwACaAGkB4EaYeMHyyRZrZajRVEkis4hZGMlKtpFs0b6SIA2ZqDJFZhMtVpthKKJTh_ZS6WaqbS6wBKlkDdyo7O0JPLwYKQMBVA6Aj4VAEfCoDaTScRUAAIIOAADcDANUXhSBiCAG1CZPRUBFOsFQGEmlkC4AAQocAAG4GI0CjIQCEuC4GC0JASS0gpJSXYeGwpA2kG3A1ZcqAAAAAXAwBVUIAkNAtCQEktIKSUl2HhsKQNpBtwNWXKgAA7DQAAAAFGELoRmgkUWNSZLLSCklJdAKYNzpkisWhtIIZIeULwABRjQAAJg4A1KEAOLgmDgsCR_NGJJaQUkpLuKDY6pIrA2kEMsjKF4OQAAACeHAGqQgB5cASGgWBI_+jEktIKSUl3FRsdMkVgbSCGZwFysAAAAAEEIQA8uM0EiixsTJZaQUkpLo1OqSKwNpBDJDyheAADQPgAACdIQLEu8guAJJaTGhUSnuC8RSKgNpBGRlQAANQAeQXA7Ok4LXQwaEgiUVJiRPLTYRSDEunjMG4RyRWBtIIZFoVTaURTxUPGA9gAAxCgD7oQGyeCYONEJFFQAmSy0geixWBkujUBZIrA2kEMlvKF4BNMoAAAxCgfpwK2hA1CIJg4AklpBSSnty9Do2jAVAbSCC_KgAAyAAG4KAQShABDIA8XHWCRRXJJE8tIKSUl0atmKk4G0ghl9RcrEp6U2AqEEAAEwcAv1CmVCziJFFJpaSUkpMJcTBuhckVgcR6GRvlC8Sn3TYjIexCfgAAnCgpAN3EJXQgBpcsQJFFcwkTy02EUkpLo1G6SK4cFk8NpBDItMIAVCCAAFIKAYshAIS_3DoIjGik0tIUmbGTgsV_7LpSXRqS8kVgUNpBDItAAqEEAANwUGeCQgltCQouiEJHMUYklpBSSkuu+NnjkisDaQQzKQunUs_8Rimzx_AABOFAMBQkuHgiUUEyZLLS4lgzikAUVKy7MRSBtIL2hQ24UoXjEunUskUNyceQAIOBRU09OZzpPfxoARRgEJc"
noncomputable def WL33_2 : ℕ := zfNat64 33247 "BFYUEo9ZNpSd4KCom0G0jQwAAVhwBaEIBCXRwXEKKk4AEGUn+RImmtMG7dSRWFBKM1I4XK4aS2om0oIAAHgoABh8ARMgB5cABGgAAAAAAAAAAAGAgBDsQKEyADVwSvYqAD_B8AsmAB+kwUECBkwBZQAABKFAfHgKlHeQmYYVAAClJgJoKUmGpQUDqwAACEWgAApBQBfkIASXU4cPwaFCcB6BBlIpCa_I2ZqvJFYJAJH0MozUEBcrCW1E0lmggACDCgzqamdMaEBHIQAGuAJDR6BMABKQBr_4qVgPSiy46x+VAYQXgPoAAARtCQwW4aTAASkDMRsKQoNRG0dcxKgMth9ipF9AADGJAFvQuUMhKABKT3A09xOFyYN3RkisB6UZqHguVi00mUulERpAfwAAPBQBFkIDHZADq4uAqAAlIGYjYUkUoNRZcdcxKg_czWEL6AADsKAOohAG67uDrQBMABKfrGQekNhSDQelFlx1i8qIIZS6B9AAFAFBmU1I6ThpeTk4ALvgtBgUFQABDi5WAVGoPSRWE0KM1agXKwRwBAASAgAAXAwAAkIIgYA2xw3AlIFUXRsG8oVhNIJRYEdSkAA9xEAACIGK8AJKwBWhMBKQCEmDcs5IrHwJwFKM1HMXKwDoELBoAAKQUABJWAAC3CoAW4VD4k4CgCTKY0AqCfxEAAAAQBgAJKwEm+CsKgAPulQE1+6VAFEgeVAQQFpmwAAEwYAwMBaXwghQKCoAECQ4uVgDWsZIrCaFEgykIJkQAAAHcGAIGfCCFAKJgGoGPSoA6NRSE0Jvmi6qJUAYgNgAADcDB6AFCYoA4kgpg0dgLPKFYFGYpTJFZ9JGGv_kynhU2lIBtAAABMDAASGgtkYO3GwHySoP_Kx8kqAglE0SVAADgQgAAAAw00klAK44bgCkCiYg2FIRSCUQQxUrAOIWqQhSAABnCQCkiOEEagJRGSGSKwYk2Yl4Kk4RZiTV9GzcUhLTifcTiC6ZqAAZwkDs7RgTjSAQjwTBRVCISEAuYqAFzFR_5KEJKQAAAAAIwYARSEAJLiwhQmA5AlIFEQhszLOSKwIJRmpTi5Wd4OHIAAAAjBgNAkWkAtPgmCiaDFzoAmxEAE2IgAAADJLQAALgYAWq8FYUGQJkaOwPdlQFVhhsAkoVgQSia9KgAD2IQAAQgYDQL0hCCFREIIeEiOGUlJJSqyw2ZjbJFYEGah1PJQvD_pcBcBGAACEDF_T3NedgJAiB4GLoSKwnIUqTmyFSsJMtmIpByBSi1s0dj2LlYSUNoMQAAggwADLoBkXALyILQaAgqI+AlIS0aikJoFKPATR3EwuVn_gIEhtBiRUCgAI0AdnwTAwEUDwGjMlIAMzBuroqThJCjNVmlCsEsRpppD6JlMAAIIMAXUqCYGAAan3yoBT2A2ASUKwFJRMulQBBLvOlYCeBQAC8GAANVAEg4EAYyB8DAyxmBv0qAN+lQCkogAipWBtAbArAAAEJNzoP_GQGaSoAzSVAKSiXiKgbQ3AIAVgAApBQLsRGQPgEwZLwBkFSsKCCkBKTREpQrA2zHTjSFgWK4AAEAYACQcZA8ZA+AEhkvAIcVKw_6hAoyhWApKIq8oVgbTbLUFkAAAyB4yR8AmDJeAMoqVhQQUgJSaIjKFYG2ZKcaTUSpbAAFkZAnRFgpCANpYvAFIUFZ5kmEkVhJEJNC+bCkDLTVRNWcKoUUAnQ0DIuBRHwIBLGYEpAPqbSk4RcCkon6yoDaBNRaAAAgDAeBBcYBCX_ovFUIKlwCNioARsVQkogJgKgAAAAAwEALwzFY6IoEqMl4BhyRWEmgzECRUnhJREJNGprSRWfFKjbTbSMhWL4AEHAoDwA3fAtrIMBVKcTffOgAG9EwA3omAUg84qAAJoAABgIBG9mJxcBshGAYcTADDiYAGqEwABVAAAMBACNsg1BwicBAQqAICFQBJIvFQADtVYAAjQUAAIDk3Fho7BSQQbAbGvJFbpE4IMmDJnJRz_42DJJGruSRWWJwzhZJphCKAfQBWBOHITUPIYC3ipOBBmJgCpOOdDGwZJIbMkViUcgqlEuhBAknECRkCcl5mZABzMABTgCSMAUJgBokAAAAAAAAAAAIsAGHwBIyAHlwAAAAAAAAAAAg4+NBCLgGpcAIGpGAqAJ6FQf6KiaVmKgABYKQAAUgojYsAF9xLtmJYYwAE+AQFwAEWPQACehEAT0IgAkwRAAAAABgIswIHzCSXFkCaF06CVAY3NpSAlClpUH6Gr_wsGilYAAGwUYZSZh8eL0peQgBJGACIQBIOAIAJgPvlQA1AKUKw0gUot0OsflQAAdj4AAAeAFi75goBhRMBKQOkGwpDSBSiy461WVB_k2AKwfAAEaDgACFwBIOAMGJgJSB6I2FIaQKUWYHWdyo50Mf1NgBkHwAAAAQuAGeFgJSBnQ2_0VKw0gUossOuSlRzoYAFTHwB1ByBkAARCABhwDsJcBKQlJyTBuWckViU0gUozUnhcrL0JE1CaxKQgDCAixYGQAIXAD9EwEpAdMbGGKlYaf5AxROwlRzIYK6mZOB6AeQgIPEvLx4C_rgEkMBMA_EqCqD8SoFIUR9xUABQN2LADAAAAPQgDtiYCUhKUhmDcs5IrAClGaj2LlYTUJrDJCBgCCwAAxAMRCBaEQhBQCl1Jw_CDTXHlCsBaNUgFSsQIFKI5JeULwD_0ED0AAFYcAC1OEIKHAdAASkDlBti4qVgFEFoFR8o1GtEYAAFYcAARCCaFQA2kLDAB6UgMfsGwSyhWGkClEjGVADkygAACsOAAIhBsCoACw2noRAdlIDESZg3OCSKw0gUozVDhcrAHJlJIAACsOAAkZABC4MIVAAP8D0pAY_YNhSGkKNgzazZUAOTLphKAAAVhwAgEIA8XBgirEFoAD9Q9AsqGoMSB5UHUKIjEqCofyOjKAAAKw4KampN6EAAoQAgyB1FwIgMsmAlIHSDYUhphJRZcdarKiaDEmgDFaFGNwAgQUgZSqB8KAALpFQBdIqCEhGEmA+gE0AAPJsAPguB8KiJGWyrF8CKwgqVhMZisMkVhpCNBmopCSxma8GRkhL1sJjHQHklRwLARSEAOLguCvfBwFkCUgMTEGzMtJIrDaDSTNZSANBv_y4_4tAPEGiCBAwICuTgCBcABnhJCgACUhdBFmDdWJIrDSE0TZo3FIH2q1kQIxXwKSBuBYAdxcBQjguCoiCYEICUgZX+GyNShWGkIlExyVADn_xUHyWgAECAO4uA_FQhBQCg4mABBqR0V4yXgwBgtlkWhpCJNGopAAmkggKlS2AxJJBlr50ieABpCBWlwhBQNBKDqA_gCkDL4syQqSKw8iUUlJNpSANBCf4UgGIDh0oC4E3F6UABlwAUgMKKlYR5NjXGwBShWGmKlEYeUKwQJV_mlBpHRDAAAArLvEHgCNkisAA5QrCa2HMj0kisNMVJo4coVgfSzSRwTVnEIADTIidAxlcWh8RQvEVAKgKgA7pMC0A+ZMAAaQAAVhwABUZMkYAZRIrAFITX2ZlI8kVi00xUmy3NgClCsLyVaSA6ZNYAAKw4DQEIX+4tAFYJFYAAyhWSSa7nMj1kisYkVJoeoqVjEQJVpIi5o3gAArDgBh19_GwOQUkEvGbC7KFc9PymjeYpgKk4VNMVJo1DmSKy6HkqkkqyRHMoAAKw4AEJkZxsALQIklCsCCCkB6DicmjGShWF9qP8EIfguYwAATBwAti6plS2AKQCOlCsBrMV5FScAkRJo1E2SK4qO4gP5VpIzpo3gAAmDgpsw8zjyWbnakAdIQbk+DjVwWgxRAAAWTAACyYAAAC2gAAGAgEbJwMyuC0GsERAAJ8KgBPhUAB_8nH0EICKAdQAADAQXgA9CAJDQB4SE_AlIGUKhtE4qVgDSieHKgC7_ZONEPQAAAHhCZoakidALk8hgAKKlYGFwZkKQBpRUGbSkMM1LpNFlOnsAAMYkAG5CUsyaKdBaJCfgE2KlYWFh5kKQhpRJSLTDNS6utMph1LIHAAADKQlxMG85BSp5DAqpPKFYWGYu6Kk4Q0mzV+hUrFphmpdG4pTw6jkABXjROgCpCAx2QBdZ5DAOYVKwsJhjYUkUhpROKbSk+sxBddgpB1AAB2FADVQ68PgEkIT8A6hUrGIZQ1GwpBoDSiUk2lI9JqXSaEOeO4AAoAoMympHbcnF6clpQmpfBaDYINgCYcPw1apCkANgVJwAkoAA4BIAANwMF9eY04GAoDBsFgAPtlQH_zb7ZUHpFYoj2SoAAAAAoDADQMeQaCggSkDA5tKT4TkFEqWVAOMCgAAANAwAEhoeYaCko8BKQKTm0pDqVEu2VAAEgEgAAAA40NoMHwDoCLLpSVkBwbMzDkisONVKM1ZkVKwAAHCBv8xkAAJoCzghoGpjB8CUgTEs5IrpJxH+JlOatFKFYAJGHgj_Z2AB4gsTs6BcDAxFgAHIArw+N0TAAD4mAAKZDAAAuBiLIwAkFAiDHkGgoIEpAwIbCkJU2cwo4nNuzlQABnD4AAAA2XAEgsGgpGw0FBD55dKSsjaDZmt8kVhxqpRmqfipWF0lIAAAUYOEMHwoIZJKlspKyQX7mDdmZIrDjVSjNWQFStXAEABmz4AAJ4UABsuH6GgoIY5LpSf_WhtBszW2SKw41UozVPBUrV0BF0lIAAAawoowbIaCggSkB+5g3LOSKw4nLVijNRiFSsAAyB8Q6GAAAA2XDbDQUEI6l0pP6rQ2g2ZpxJFZbaqUZqYYqVhdJSAWAGAAKMC4KPcNBQQryXSkAaqvJFYcSqZNUnzUPRcrAKoAUAADwUBAQwfBqHQkjE3RUrzMPF0mKdyRWHERi1XJs1aaUKwJ6SXdow9AABiHAASFiShoA6AMIqVmxl4mJsSRXGo2ONVJs1aUVKwCQIT8J6AAAAHFuVGmiDQEZGD4BDipWVQfYbCkunEJsxzaUgZwQgnoOQADMzw2WENBFUYPgK0Klf5l6skxTiSKw41UmzV7pQrAKchPwnpXCIAAAJIvXqstAaCaYwfAbYVKz_K0TFW5IrnpxqpNmpzyhWAq08hgPSKAADoXeMHwDI9Fdlz7yhWUSyTFmpIrDjVSbNXulCsAKLPSebZzKCF4CIHF3gwfAyA8bCWqWKlZWSYvcKk7SlqunVs51UmzUUgBkEaij0OJQQ2wRAeNreDT7Bg+EZ_wjEtbAVKybWSYvqKk9dis2c6qTTMGzcUgKfPHYT0AAnh8ABoXbwacMMHwaIPGyKS195QrJtZJi+oqT1041UmvyNm4pAKYhPwnoaT6ZcAC6HQ03waAMgyAuSoVKwGhmQpru1GoJoKQCSLQDqZR6C+h4AF8s4qwGg3IPARSKv7HQEUiokgTSIxUAB+96AAHUPCkqyHDfLTqYxmi0UWimolkezFRBUnMJtU8qUyaNTEkiuql0ijkgj0sqcYM9tiotUGihaRxGACbCEJGHQVAPQFWFQAjwqAEomYqAFP9GIAAAhDwBx4GNmc2dgpBQMRYACCABiSYCY6sFkJgBDB8AAAQgoiyMAi"
noncomputable def WL33_3 : ℕ := zfNat64 28437 "EaHQDAQCgIA3AwA1ABt_jYA0_+BpfHQAJIBgAAAwEAC0+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAWnwAAAAAAAAAAAaQAgWgwQwFgJSANSykisAwSlTmp4i5WAAHgOAAAMBFfBwcaAExoAAAAAAAAAAAACEyAAAAAAAAAAAAAAAAAAAAAAAAAURgBqEAAAAAAAAAAAAAkjAJgwBZCgFaFQArQqA_4nC6ioAATwMAAAzMw0AQkQAAAAAAAAAAAAEJkAAAAAAAAAAAAACkKAEYXK_qBQDUZpIrUpDBUZqkIuVgACCDgABEgwBgCEWAAAAAAAAAAAAATGgKwCgUhQASi5WANSKkisCozVRRcrAAjIUAAAADypGgoIIMABKQP9m0pB4ARUSA5UAAAcIKAAAJDQATAcBKQPAm0pAqJFcqAAFYHAAAACBIYxYAMIkB90qAGpGyRWBUZrt8qAAEgLAxAAADUkDAUAJQMBlQBgMqAqJt8qAygZxJgPICqBYGZ0RoKAABiFysAaiNJFYoYCF0HVGa6PKgABCCwAAGwYANWcjQUAASkD_ptKRQwEVaiLVKgABuiwAAGwYJ3ColFwD0EsWkaUhSVWmDdFJIrAglGaiyKlYAA3RIAADYMF4AMPkaCgACUgf7NpSKGAiojqSoAJbCQAABgGBGgqHicH_joDfJUF2l43yVAbSiabKgACCBwAAGAYr6+3jaUAQoRQBQAUA4CUgfFNpSBUSFZUABmgKAAFAFAASMgB5cACkHAKWKgBSxUATRZRUAAAAAuDgAHlwBIaABSDgJSB8U2lIFRIVlQAAAAAANLgAYQ4ARhcrAGoyyRWBUZqoouVgtADJQ0AAADougcmADCHACMLlYA1GaSKwKjNVFFysAA+UPAAgcmJ2dj2vhYAMIcB7UqAGopGzFRUdKm2PyoAAVw0AARoKAACHFAHABhDgBJFysAahtJFZNQuKjNV5FysAAJg0Ae6DgAoA62hk5CAlIG1TaUgVKiTFKgAC9EQAAUgoAEJUgYcKI2bgF0oXhNZSE9MOYNyCkisAozVcRcrAAAADPiBcCiDtNGwHnKgJSE984bFjJFYBR_6baDKgAADiAQCK1YgQBCfIGHE0AAYxcrAMjURpIrHBGRtqM1eYXKwHIAgB4ACDgsAAgqKAO0wbALU0dgSkC6ag2B2UKwuJRYwdSkByAAAAvEivmQoA6khjgyA0+VAGnyoFpdKJhQqA8gQjKgAApBQFAHZtVgakVKwE5FSsJ67Y2FIEkovVNpSB5AdaVAH+CgAQMO_2rAgsoVgK_KFYT2YuJJFYUkmzUR5QrLyLR5JIMmLlYFFnoKcKAoA4sgRIkVgCkJ74MycKSKxbBUSSbk02FIXUkgJQsVgfSqC5RYGZcNpbcAKsxQBwXUAihN+MqA5ibSkCokiyoAAghEAAFIKABQzFAHBdSZIQEpA8kbAFKFZDSosuOs_lQABCSIAAKQUAFZmQMOJ44az9bp7AJSAdMaYNyzkishspKM1KAXKwACEkQAAUgorz0KAODtR8H8aAlIHCDYUgFGwZts8qAooZKHgAA3BwFAHB2o+D+NAGILlYA1FIFRFwdN21FysAshBQABEhxBgBo+KIOcQxAASkDShsKQKNROKlQBd8MpAxAACkFAUAcYQA8cPwJSBMU5kissglJ3YNZNr4bCkAuksTKYMQAApBQXhQBypFoI_HQEpAfuYN3DFScAozUEpQrALpLEymDEAAKQUAApmKAOB8VA9AJSBbY2FIFRPKlQBd8EpH_jIAAKQUBsaRgLfmKMOAAukgIoAFyvwQ8WQaikLISVbHTdDRcrAAiYPAABJCgAtoRQBwgn4gIR09GVATXaJUGEIIqUqAAFcNAABCCg_Q8ONFw8RoKAFQRAf1KgJr_UqJeJxUR+pUaqHgAATQBAAAQLgAqCICUgJ6Nm8pAqJCsqPkDwAAAAnCgOVdDwf+NgJSBxg2LOSKwmsjKijNfIlRqoeAAl4LAAByRkaAD_hcMYuVgDVBZIrPeLRUZqSwuVmqh4ACXgsAAACzIAIXHJMx4EtJQHaSoAaikJpUY4HWPyoDoAAABjCgLDVRlIb40EUch+1CAsXKwBqeckVjWu6MVGalULlYHQAH8CwAC4KABGjADi8FPyPAAJ8KgBPhUSRjC42JoqwqAcJAAEvBYAAPAeK0tY9GceAQgdJSORaBpMG6fipORSKKSjNVmFSs1UPAAS8FgAGYB5jo0C0kgdZbTSSIeNmanyRWTenJ0uclGaqeKlZqgeAAl4LAAACEuDYaAALelQGH_5tb0qAeikPCVAAAAAbgoCz0zABicIQsAASkAHRs3lIFRG9lRqgeAAl4LAAAVY+AHlwhCwABJcEXKwKI1daUKwCbOR7FSsAAH9CwAAQKDcABIQhCwCkUSWBKQFVmDcs5IrCbZSjNQvFysCiA0H_joAAGwcCeiMBFAlIAbDZmKTGFRNDkxZyjYM2O4VKwJ6ErjYAAFwUCujB8igZIoKQEhUrJI5JimckVvoWKZNWyqYybNTplCsCejEVUcNwAAXBQZgCMuEIWk0dARQJSY4Lg9BszFIRf7MWco2BNgLFSsHIAVCXgsABPgAPnBwaAIjERJYEpAY6YN0bkisNJhKM1NAVKwcgp08hH+jYDoABAKMMjLy+PD5cAAqQHOuCsGAEkVAf7Kgsk1_2VB9CiUDKgAOAKQAANwYA12kI1QglBgA_HQERQZUAPoKgJqHQAAnjcAADEGAJYhBaDBJTcHD8nJKScg7TBuKQFpRI8dN14lC8GvREaih_xKAABsDBicgAIuAyEQWgwAzSoAvBcrAGopCaFEMJo7bQXKwMDdQWgABCBgD1kwWgwAzyoGoJMULgCkUlqFYJJBWMXKwggWbvrQ1AACEDFCBgBISBEGAkHDZjIAlIGBjYDpQrAKJ2EqAuJhOJnQAAAIPGQpiICUgWsNvxFSsAonkyoC4mE7+dAABuCgAdAyFQRASkCmBsCUkVgVE_yVAHWwgJD52cgCAAAMQpdA8ABKQWh3DZERUrCKKSiSkC4ooYicZ0AACYKAAkNFXjQNS6C1BQ4jlIPRSD42ZtSKk4TZyTRqVckVhBLpxGyuYycgAANyLMFGgLIFMIpSANw2ZrnJFYSQCihPymbCkB3DZzroOTaAG8j4AAg0TONAIZktgIQXFSsHpMW_FScJI5Jo1HuSKz+R8R0bOddByYQo1UmhjRYF3cyKio0I+MG5ZAMykCYrcKk4SQmjUu5IrKIG0u_5So0HTc4lEZCsB6ciJ2dAQG0GIUCQaByASkDLuI2KSSKwFpJpgZSkA4l0QwgPwAAXBQehYASGgDHj5sT0eykMIkTx6Wo2ZvmKk5VZSTRqBEkVg9LiYQox87AAAPAIj_xsNQJSKGTgyRszcCSKwkykmjiNm4pAONdHgHD8rhMAAABIaJ8HgGoBPipWBP42FISYllRRFybSkA410eMcPwAAHQA3fABxo1ceBiH8z4qiVAFqyoJSUTPJUAcQbQdGEAADZ0BqFQjiVclIADzJUEknMbSkLMpqJaUqBAnVAzEAAARxIAExcKsVBBAJSFUO4KNgakisJSUTuZUH_mI4mE3EdTUMgAANAIlUDvmp3Fr6HwAHSCoA6QVBVDpRP8FQG0AggAf8MgRMWnoNTKFdk5jhUrDiJxMXaFScLIxJo1NeSKwDjXQ3B87NID0AHIEcAb+NZw4jHAkRwgmUCaMwqVgPZi5skV30CaNV7kisA410HmcPwACeHwZhYABwgk9UAMm_XRjfHwAHSioA6UVBVDpRP9FQG0AggABsGhRXOHz8GoFmjOBNZMVKwmkxZ8VJwCqpbGJNGpkSRWD0ONdENHzslzcFVJoMUYPgWAPxpoU+BqNQJSNSbOQEGzNnpIroJZPwVKyaNRokisHthONdJpQTh+YQptFARiwZgCuqDbTahD3_EIECAx0mAGOkwANJJgACKABUIeGvyJwqJLBiVSekULpQrCaPZiYAqTx2qi0mjVK5IrKI1GkxG0s0kTpo7UM4b6aTmighANZjAuT4AkJsIVf+XgolUA55MAHPJgCAHjJgAAkFQAAWYE5kmuIgGNZAK2UKwHsxFIUiHiiO82Z+UKwDaAQEB+npuCqh_0mBmLnRclnS8djxmjATNcCYM_wiAAG8XKwBqHMkVhH+DJrIpRmq7C5WBUIoSdTKYAAiQYAPx8HhrgrBv_HwDkCCS0mADXkwCEDgkwAH_kYAANwMAOdCCYEQ7hUAOUSiUgfvNo_lQUGogAASSwAwAAB30IEeRPokwLQJIWwuVhTZqi4qVhQSiOdrFx2AoloBBAABWHAAuQgAJsCuIgJioAAuZUAAAlAHHQAZQCgAAiCgCVoQNkiHcKgAkn3SoCaymNhkUEo9YOpklQACEggAAlCghBBKEAHMgTREfxd88mP7FwSSSFqLlYU2agCKlYUEojm7hcEtAIIAANgoBE6ECFsg05HTCsdwqAAsGVUUJrSkqgpQR6MQQgASQAA3BQU1NTOgFSuCIGAAE+FQAnwqBqf+ThVhUAAf56AACkDAA8QgOhcO8VAAf_KgMZm3_yoKDUSlpUBUQCwAwAABF0J3UmAAlIfxTuVG0USRWFBKPWTaUneCgqJtBtI0MAAFYcAWhCAQl0cFxCipOABBlJ_kSJprTBu3UkVhQSjNSOFyuGktqJtKCAA"
noncomputable def WL33s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL33_0) (dpk j 1 WL33_1)
noncomputable def WL33s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL33_2) (dpk j 3 WL33_3)
noncomputable def WL33s0_4 (j : ℕ) : ℕ := dsel j 2 (WL33s0_2 j) (WL33s2_4 j)
noncomputable def WL33 (j : ℕ) : ℕ := (WL33s0_4 j)
noncomputable def WD33 : ℕ → ℕ := rdw WL33
noncomputable def ready33_cuts0 : List (ℕ × St × ℕ) := []

theorem ready33_cuts0_ok : CutsOk ready33_cuts0 := cutsOk_nil

noncomputable def ready33_0_state : St := ⟨26112, 285696, 51168, 188607, 29184, 45301, 29666, 44151, 29666, 44151, 52016, 82940, 28545, 95948, 26112, 285696, 77280, 412706, 106464, 441890, 136130, 471556, 165796, 501222, 217812, 553238, 246357, 581783, 272469, 607895, 80352, 233908, 110018, 270000, 139684, 299666, 191700, 360063, 220245, 425087, 246357, 581783, 58850, 81393, 88516, 111059, 140532, 171456, 169077, 236480, 195189, 483264, 59332, 81875, 111348, 142272, 139893, 207296, 166005, 454080, 81682, 112606, 110227, 177630, 136339, 424414, 80561, 147964, 106673, 394748, 54657, 342732, 0⟩

theorem ready33_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD33 ready33_cuts0 111 137) ready33_0_state = 50281 := by decide +kernel
#print axioms ready33_0_cursor

theorem ready33_0_covered : Covered (toCl ready33_0_state) :=
  ready_cover_cursor WD33 ready33_cuts0 ready33_cuts0_ok 111 137 50281 ready33_0_state ready33_0_cursor (by decide)
#print axioms ready33_0_covered

noncomputable def ready33_cuts1 : List (ℕ × St × ℕ) := (137, ready33_0_state, 50281) :: ready33_cuts0

theorem ready33_cuts1_ok : CutsOk ready33_cuts1 := cutsOk_cons ready33_0_covered ready33_cuts0_ok
#print axioms ready33_cuts1_ok

noncomputable def ready33_1_state : St := ⟨26112, 285696, 51168, 164800, 29184, 45301, 29666, 44151, 29666, 44151, 52016, 160411, 28545, 136940, 26112, 246784, 77280, 345303, 106464, 390604, 136130, 426696, 165796, 456362, 217812, 553238, 313760, 581783, 339872, 607895, 80352, 210101, 110018, 246193, 139684, 275859, 191700, 372735, 287648, 401280, 313760, 581783, 58850, 81393, 88516, 111059, 140532, 248927, 236480, 277472, 262592, 483264, 59332, 81875, 111348, 219743, 191179, 248288, 217291, 454080, 81682, 190077, 155087, 218622, 181199, 424414, 125421, 188956, 151533, 394748, 54657, 342732, 0⟩

theorem ready33_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD33 ready33_cuts1 110 73337) ready33_1_state = 115166 := by decide +kernel
#print axioms ready33_1_cursor

theorem ready33_1_covered : Covered (toCl ready33_1_state) :=
  ready_cover_cursor WD33 ready33_cuts1 ready33_cuts1_ok 110 73337 115166 ready33_1_state ready33_1_cursor (by decide)
#print axioms ready33_1_covered

noncomputable def ready33_cuts2 : List (ℕ × St × ℕ) := (73337, ready33_1_state, 115166) :: ready33_cuts1

theorem ready33_cuts2_ok : CutsOk ready33_cuts2 := cutsOk_cons ready33_1_covered ready33_cuts1_ok
#print axioms ready33_cuts2_ok

noncomputable def ready33_2_state : St := ⟨26112, 1040384, 51168, 581632, 29184, 45301, 29666, 44151, 29666, 44151, 52016, 250271, 28545, 305088, 26112, 533248, 77280, 1622016, 106464, 1667317, 136130, 1703409, 165796, 1733075, 217812, 1960803, 246357, 2265891, 272469, 2799139, 80352, 626933, 110018, 663025, 139684, 692691, 191700, 920419, 220245, 1225507, 246357, 1758755, 58850, 81393, 88516, 111059, 140532, 338787, 169077, 643875, 195189, 1177123, 59332, 81875, 111348, 309603, 139893, 614691, 166005, 1147939, 81682, 279937, 110227, 585025, 136339, 1118273, 80561, 555359, 106673, 1088607, 54657, 838336, 0⟩

theorem ready33_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD33 ready33_cuts2 124 33) ready33_2_state = 126263 := by decide +kernel
#print axioms ready33_2_cursor

theorem ready33_2_covered : Covered (toCl ready33_2_state) :=
  ready_cover_cursor WD33 ready33_cuts2 ready33_cuts2_ok 124 33 126263 ready33_2_state ready33_2_cursor (by decide)
#print axioms ready33_2_covered

noncomputable def ready33_cuts3 : List (ℕ × St × ℕ) := (33, ready33_2_state, 126263) :: ready33_cuts2

theorem ready33_cuts3_ok : CutsOk ready33_cuts3 := cutsOk_cons ready33_2_covered ready33_cuts2_ok
#print axioms ready33_cuts3_ok

theorem ready33_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD33 ready33_cuts3 128 1) (ofCl (RC 0 2 0 0 0 1 0 0) 0) = 126746 := by decide +kernel
#print axioms ready33_parent_cursor

theorem rc33 : Covered (RC 0 2 0 0 0 1 0 0) :=
  rcOfC WD33 ready33_cuts3 ready33_cuts3_ok 126746 ready33_parent_cursor (by decide)
#print axioms rc33
noncomputable def WL34_0 : ℕ := zfNat64 33248 "C4GIcRBLsqAdwaOwKIDQSmlLypTGZlQRQOJKQAA3AwBKy4iQZfpEUV9pQvANUYNz+osWQnZQvBKbSzJQflC8IoEtloAAiQYIQW6XAVqIiQYUjZ0YvBcBFGIFkMUXKwOJZnr5C5WAGkk_+SgABEgwQj6GAEhowkSBtBcrAiteMl5QSzQRvFyspptLMlFMXKy0lkogU0gTgAAD99IBCPBMDCEI6kQBFAc4pPuJgAAaRAAAAAJgYA3xEecPBx8qAmpUaqbmLimm3BasKPKgozGOkxoKkAoAAA6JFzQtsAeBqoYqVgA1NG5Ud8KwFcoXlNNtVkvhi4KMxjpMaCAAG4WAG+IgdCfmDcXRUrDTTUdHTcqNV72hC0pptLMlGGULwozGOkxoMHyoAABAZG0iEHRYBs3aoVKwJsnDUqJVPvFxTbTVZLpYuCjMY6TGgj0ADfjwOgcwiH0a2yPFCzaUgTUqLPlauf8Lim2mq_9JtJFwUZjHSY0EAixMBJAPGRI0NCaGD4NSnFisommmvaNHYUSqQb9FxTTaVZKPcsXhNmMdJiQQmoDLB4mQStxA5bITIRAGQI4yCwSRWFZUqYgBUQAe5VgQaha0yAAA3CRU1MDHzo+ABMId9XAMBDEEkDQFei4ASoNAAkgaAAFoAABgIBbDMK2rgANMAwEAAUkASaPAAlceAAsEXAAAGAgFcMwbA0pAcx0AL8wZgXScRUfxMjiDKCoAATx8AADYGEMNB+iEFYNJQ6TBfP2dBSZqfTFiyQUHlC8C6JZSaQuB6VaCc1o3lZAABWDAYuWMyqikKKm0IFxkvCqVSCKfvD1FMqukSXKRSFWqhpRgtdGQgAAahQBsFPBLGZVRSFFKKFLQqlUgikoqq1zOeJElykDxYrCrVQ0nEEIADXA0ABJWNgYQAu+CUP2GQAAc2LgAGIAATzIAAGwUBhJYzKqbQqVhRoLSUSXqwqKpVIIjyhWUUr65nIspFITZqS9OpmkIIHZCIAACSsAPLgCQkAAAAAAAAAAAA7AyXlVZsVKwo0FOaJLCyVSCOo6busYL9FTKuZyKLRSE2a6vUp5pBYtEEAegUDIDhzx2TAyXlVFIUUHoSCEqOFUqkE3h03MtFFAzXyKLRSE0pppM1IQAkADhTx2DIyXlVFIUb7oSCEqOFUqkEdhs3MtFrpFFpmSRWE2a000lUyh5DByBdAzJFMAEWMAorgJdEFEEuSOpElwLIKgCaFkByUUy__SiZxUARDKAAANAGBALKuO7MMhEC1KSmh7kqOcabVSahVsJg0aWgzKFYTUtoThGhgk4mAAPM4cAJCxpwsGNDoAk6sKiyF9CooplyalFeioANI7hCAAAAxiwXpYzKqFQsVhRZyhUXVhUWSqQRSUUba5nIspAqSKwmzWmmks_8QgkMJABsAJKwWKuMvLgYATAd2SgBoJMADGCYAAumBAAAAvMAGVgBiMAPKgCQsAAAAAAAAAAAAAejCyGS8KopLBplOgiWSo5VSqQUkGzcwk2ukUWnlJFYTZiGXQ6kPQ4lksl0O8nTw6I4fy05UrCkptBooVVcK1MgmsNm5hpNdIotbeSKwmJQRmB6uhaOJZrJh14poAbFcd0oZBKQBaJUc6u7TJ4M6Om5UbCO9LhSA1BdNQPRafS6B4ZOA+zhwGbGRmJACSsAPQhQ9UAQaPADUAP0PAAfAeAAyajAAAMBilACTEbAwgBd8EofsMgAA6QXAAMQAAnmQAANgoACTEAD0h0y4IYFQBA0SWAXOKiim0kgA1CyU4XgAAbBQZwXK5aRWVhSU2nqFRSzQf_KxBPWSK6STa7IxGGrn0ymLbSKU1DSEEDzBwABJFRQCoHMkwBJCzSkB_9GNoFaUJwAAkFIAAEwcACBeUr2w8lQACh4ADRUAEUAPaJQAAAACIOAIm1BiVW6hUObMIQTaKvZMjkfm4ojGi10OgoTyiLSahpHQKlMAAEwcAA1CAJGQAEuAGlQAEWAAAAAAAAAAAAYCAACpADUIACZADiYAkNAAAAAAAAAAAAAbix0ljMCp4_OpKw5B70s6XIfO+ULRFppBppJJpZIpNFMnTxaURyGkUYpUwAoACPljMk5w_MNRJEeOwezlDR87KpBJpBNIpTyTRUSLFcik2mi0mzWimUaM_9FYohZKIHEYJtJJsAT1wQ6WI8uhKdBGY6A7AhAEDFI_+jAPtTgAP5KQABtAKiHUwdLwUID8rSpDkHoPSqQSaD1TKZJopVpJRQkqUxaTZiV0sosYj_IUAS6QgBTkqo9E8hPycrrPH85KpBqM9AsnT_8okuil0kk2AKZPFo5HoURjFe8JxJKJlBYpAAiZOBv9KLkYQAWGEIiwotARQAAAJIeFQgAAAAFiMA6DCOGnQUiOI8u8c1AcQAACWiUAGNwAEZC6AVmZgdg+d1Adu4QQtqjDEehBGJBDpNopFB6ZZOnhLRP6MOMGi5BJJNALYTJxI8uZw7BDByAIoA9oeGCIwDvU4ABURAbGMtIIAATkB7LIFp45gD0Y1EjehIQJD4dopFOGHxRDoAk0oEJBDCBjRaFZXU7dw2lUmoASiOQyCUBjBcq0Wgz2eyaTp4OfkmQRR7pUUNr+PI5VLpZCyxharhqC1XcU8gwKo2YwDyB25aMYSHyjRSiRQAPrHxFSKVS6A5NUtgBzBbLC6ewMIbSvuHM81EolWsxko0UkoOUhCTkyXgTQW9uIoyOR6TSSJQDcDB_7xyAnjZjAgC1aQqgEGei0AKdSxWAOiQgSj0ikkDbqsG4GC84bdrDKVJivlhrp4WrORSyTaChZyQRzGQqZIqXzUloIcoTyUOj0iz2ajEdWqWwLRCt2sMogmK+WFLS9frtJMNZKtZoMeR6SQRCQ48NgGaktJDXQijI9Is9moxHVqlsAKp3NiFQpyCizBvA8ilUwCAbNrJpV_8nBXQGIFQBaKR6OQ+qlXAC8NHYeMzut2sMoGmK+GGs0fSqYxrJRHogWK+NSqRZKWWUq1sA_+Qh6D2cjX_gFKRyLR6DEAMhEphcrGMzaxizNjrpXSqy9Olm0slEenfZsZpKpFktdZ+tXziVRqQEAxUYDx3Lo1jsNJSJSQ9OpuoViqJhark5loWRI_WSDOR7XayNThljeUjGAmUgkEsstnNtJM1nNBFqVypeADuaATaJU+qlVCSKYjXSzMRi29KplkqjEQz2VptLLoRSsj0QqE_LqBLoQSUgS1EeCEPTVlysKefOwCkSeO1Wiy0Ys5VqdRIMplM9pJpLM5K6PZ6YSrMZSNR9DwBBVpspHolyZWTmQx2ciJRI8tmqx1anPaKSgqVymeo9NpdRLM5KyPZ6ZbaRaLWfXoxrVK2J6uVOpz0eymgzkf5EnZ2RH9zKU8gy2audVqZNoIpltFQ+bSyjQRbKaLEYCAhmxlWajmkzEla1TAACbnMBI6O8qTkZEMZmslloxAKrU5jJRTKZ6bc2lz2ez0rppuq00iHSSFqU+i10rIBw8S5iXCPgCQ2Gw0Ux2QjEpatTkoRjIhOchP6TOZrLSw20zbt_IJBHNJsI8VaviesRMn9FItRmsxmJDx5GOZyyw+dzV_qtTms1mspnoaTaWQaDRaCdNexmm+sTPnc9oM9qNRRaRLxRSpmT+ikUDa1TJrNZDLRyPRi3dSriEYjFwxErFKYQ6TLRrRS0mm6nWQF5BINVNP6GsHfQBCw0BXTQCOXEVnkAP_5kKUQkysnopkNJJtFGI60qvSSSQRCsEwh0kPJhCibhA11ktN5rNVpoiShuDpnJ1HvpFpqXy5WD2WyEekWajEu6VXIo9FIFThGQaSaSTPRcSlrNN1MKflyuOR6+dgr2mugaBh4COASPybMV8DyVkoi0KJJPsuM6qRSSTZ6sswh0k0hC2CmWkekU0l0ijEmivDJeBbAgFVqZVQcLVcnpQTJfHSjQRzNWZq1Ooz2YykCCE_pJdopBLLRaCaaSPR7RXiHQTDJeB4eClEki9BCVTKJVqpPRSt0qRkkgzUS0Eqj2rBpDFNFvNlII5FlKWsslKRn5xJI1GJNop1jJWAoeZIvqJJIrNEJ+EUi4Em1UilFkLFrKpBcKZRxyMarZSiSS0kWe1YcNZJIJBJrijae3MkZgSbWSM6ikJGKpoVC2T0U1Ug0Uaj0l61rJI1GstGLbVbP7pyKJNBA4E2k0kkmkg0EhmAYF7t07JGZqEqmRSqrNQtk9HkiK5SQaKNR6SSaTS6OQi6FHOpVKocS67ZWjnEsk0i2EEqSMwrAG9Ee3UEXNFsCqgNV7HmM2nkVMZlJMtLIQWq2BVAFqiVzqZTCAYhIZgaCwdoAvVABaM1EW5dwNIYEJxEnDySVjb+DLtxuI7pu110ijsBgQkoieP5tNoaQYh6Qjp9xknWg4ZyKZTwrGMLpVCE1V6KXSaPTbJWuelUmy2ouqTtZBKI5ByOVjHS8ilEkkGok3AgCBgoODhRGQDjYGgMQB5AIuEwEEJcJQAD5CoCSAlRSA0EReNpAew6mENNqGpgbh7CiORyHQii0GxiLhTFTc_4lC0FIHQikkk6dNRzDJbA8CyXQ+qls0z13DbYQ01m0geYr9psp5YuNFzDbbiO5HD8lHI0c4fgtEIdHtJJJNRPK5bC0MI7QBIaAQWg1KdAF0AAAAAAbiQAAHoCJgsY3pPIME5NmMA+hRKxLQdKJFJJ6guZ8VNxyF0BEnAlCyAXUAQUCydgGIxAH0AGAPf+agAYg8AA5gmBKAGeUiPIIXradHjuHVvipjA6n0JMbVoquiJD5ZJtVDAj0ihQbmHwZHpVLpTQaSpbAUJCiXj9PQAuGgNqIwA0oeAKo5BSAAcwRBhAE7KwFh4CFpbTJ09lRHoeOzl5sMR6EEJqBJJFItVANKlNDBcPQLTGwZIJFJoUR7hMnAcFezQAGWMV6LQNaMgP+nQAxJCABrSMAAAAVMdidrbUNJ0Ol43EB+VE5Bw_BIJQ5HpZINBH6KE8ckUk0EouiUK4AW0CiAHVIgDlxuLAAPUAPQgCZkABKgBgkABDgAAAAAAAAAABExuLBg4yC27IxcEVAvIiA2AhADLiIAF5IQAH_lIAAGwUVIAPYlIjII2FQBNCSf+Qn9FQRTLPdKMUKwAA4EIAAGwUAyhiAWL7CGwGJGxURUAehWYqCz_5qB+qcLQALAfAAA2CgPDwWJACTEAPQhQ9UAQaPADUAQ2PAAiUeAAyajAAAMBilAKSM1YZFR1cVGUG8nUMLNRBSeSKZTvwdwYqEJVronRqCyAADYKAdAyZtFLF__jptakKVhL1NoMtqtRqJBUSSKyrRS7QZSr0kVjWolUso5RAfjsUp4AFEnQAkN0WZNTLGYGqKlYAEDJeWQFzlCsq1GwgoMoVjUzyrBpCCAABqBkvM8ULwCCSKwIMtqof+QhSVSLXQ0JUsUkV0EAEQHzs2l29K0AdsoXk7OjoOcsx+MnsEQMDHgOwFQAwEeABiI8AAWQAAGAxUmaCdgNmYhC7CAYCjcRBDoiAGoA3MeABw48AAE8yAAAMBBjh0I6TkJiGl5fSxsCOx9PQk4CHhpe"
noncomputable def WL34_1 : ℕ := zfNat64 33248 "CykYy0khBDEiNURKKRyLRaAmoB8wXE5Ccy2cg1HKSK3ElzMaykagRKFYxlolCKDmi6PVLYlFJFCKbmWrYjiRVTOgnIAGwiImItBrf4iByABUM6EoKQI4hwAEEIOCfbKbO46AN1CWATRCCGYtLNHYZgMBDI5nIZP6hxMfUl0dEoRCIZAmpcrC5zZ3ME6fi2SoUk00qxKVq9JJtVqq+y5mTaQrl+0mmWy2ak0q1VFpUvlIDSZXIZqSaaLZSycqXgSh87WafOwGO9fwumWo1UMLVkyWhSiYTiXRQjCMUjktIuYwQymSyEckkgiUloA3DZzzZ3PSTVRRvX8pNVANJ6UpFWW2n_iBHpJRMsAGwCJsSLjknJEQ6VEmRyE1Zo7GohDsdlIJOjP5SFdAFIVUaurWybXbjVSg8sOiugS0U_mOiaBMQAA24C98+dr4PI9VvsxoNFjs5JJJHJw2K+3pEn1Wwkm6z0chRKbMZTIZqSWrHjegy1ypUvBjW7nPS7Vb6UVWClLjtRJpVYSRKx3p18o02qyUAwEgugQh6SkOmtIk8llI5FMpEqxy5WFduW9CJ0_KM9GebVx7MZLHZ6MZDHYCRZrMZSAV8pVsezEUgAypfLZLJZSLQVFyeUylBZUvFxlEjUyqTYCS0SyGS_9MpaMVBv2sYzWgzkNDVjrICkHs1GIRBueiRfs0oVzEYrLKk4Z+xVwLnT8ijmAvRRIc1jsdppBlstPa_ayrRZzObCItKt22ba5jnM5mstktFoI1a6bM5iBUqXtZLlYUryRSjlhOgIQRLIaKS2Wnbav5RoNBnNhrJBJOGDsnMxlohEoxGI5sgZS5LGYHmsuW8pZ0_po9tM9mMhCeRH6CNZTJTCu1MizmczGsjBSrc9mItJjLVdlSeSykWymWy1rJUvBeXLe4M0jlEe2kei0UyGijkWglLk4BJI5Io1tKp2q2QRyMQVxk3GMlkotGIpGMtamVLwHCwcz9y3kUqkW6kEYjUfgEjos1GMpfebQySPXqHUuc12so4PIY5GpNRjKZKbIsTvEMlYxFstloFi_tW8i90XijeQci0EQAzIoPRS81Cbk2kkGWv3XM9ZIIOSajGUjEWnAPlYtFooEqXgWOpFC+hJoIxJpQXXHCuglUm00emUFrVbIIRT8x9NZaV4yTi0ijUBbnDMCwUS1u5kUu1UKTd_CCSS3GAMiyuUqSKTnpUMslEsz2y30ghJCCUBIdy13w4zFpFmI5GspAUv9y3kUu19Vr6EEkiQAGZRCrOcCWSq0Rezkm0jFRoZBCiEmaylFg4zFpFGpBGelysBw8JK05IpRsAxYEON9wJdLyeSQsWcmmE01l9qA_lo5C6DkApYvlLFCg2OSvnk8gjUPAZLwJBwsvCXJTh+RR6HeOoYORqIYsVjEFolVSZL_9ECcUjWUjGWhUGIMZZGy8Yx0Sy0az0voAqLfQwheSoYPQU_oOgYxIIE4izZnJRqNZSMWqmS8SgxBjLWqlyuO8oHE4hEo9CyBpmJs7Ea0ZyaWQwHUMejUaikYzkWiVFJkvEopGqbSheMT6lzMSg1CLTcDHRKJZaTaqaFctgGGgLBx8OQoIA9ixWAOiOoYhNEMO1EGkcPAdDkQhVOsKQcQAAHKQA0qRKMRQJIAtKktFjjITeaOx6SSK4QyGKKkqGAA9AABQKwBgyuisIqooVdQgMzmDcAlJF4YlEEJCAAbQAAqJQQh4HUmlVEB4pBPR1DB7_42FIC0SkxNmY9NsdDWUjFGZczBmiUBhOIGEBzChXB1DBxfChGhIcNg0Y6hgCEAQoEkj0anALiJB1DJJSQFlPHcqkkegeKWgHDwMLAe6UPgkgdRIJhgwAxAH3JQATDCgABKABpRGBkFJaeiWEB8CQDyMFIHz8avoRgARgvEtNHoxGspnJUBY2UQklVHLMD52YSiUSq9RWthZA9nhKD0OIwwIElopYvACiQQkiWUx8bQeNjkCxC8D0wlkwgZOWgLEeTJauhg+BflKmCtE4U0knIhZcpUy6SSr_Y6MCOQsldJrEkB+YSyV0wjOFy2AoCAB0oAYfAITIAAAAAAAAAAAQYYtygAM01qMzgmACvjETQBJyBLAAwqkABHBWMIAKALg1nRsAJtQ+CmAAWPgF2FD8AZudAA2Q+AAHoAAHg4qZUj4+voWdyLQUSLR5DAolNmMpBdJpNLWmUyyGkNIOZUpgACgCgNj72DCwcDxdTMmDcsgEkoVgB0GDKRzcqAwlE7apAbTazcEEAAUAUIsaCh92B4+IAChB4AIySEyCoABJYzAA2FQABmKgABPHwAAoAowbuns6ElIZUxHakAPsxEgwGUg5QvAijEkJZtShMgLlZMTaWZK_UoXh0BSJaAAAiQYBx6kAhIiJBh6GVwhcHO07_xsA9DKUC4DKPZKuouVgAAAAiQYBFCENwMETF5JhsF0HoYQJaVAVRSCoGgC1ZcAAAbgYACSsf+XBckqA6EZH_G4J+lQXTKEUSoAtWXAAAG4GC_BYYlVT4VKwfS8FuMl4ZRvKlslIXTKSf8kyxi5WAWrLgAAESDAASGiSS4HNFQFZDIAeaVBdMoN2KgBS5cAAAAJw4YlKVZPBUrOELRLQyjqVLZKQumUkyVYhcrALVlwAAOcNgABYwAcaAGATBBkFxyoBRJYzDaGnyoLplJJf8qe8XAAAAACeljM_+rRwKlYWQKhkvDKOZUtkpC6ZSTJViFysAUCXAqQ6AAJ0ACjxlJYzKqxYqVhZIpjyxmG0skExhcrC6ZSTJViFysP2lQZSyKQUgAAEiDwU2bZ0eskXBWAqAGIBO4qAACpNRQADD_FGALOjwOgCRGMKMl5VVRlCsLJFLmWMw2lkgmCLlYXTKSZKkwuVgDkCiWhmLIAugiBVZiWMwgMVKzeC0S06i5PMpVpohSk4l0ykl75NKQAK2KQAAbhYMwAKjOgGQxBalIA4jJeDTb3JaJSdS6ZSSSQLlYAFbFIAAOAsJhGUtKqFcoVhZIr3jJeUTKuZYrkGUnGQKZNMpJkqBCpWEUA70pAABuFgzOwDQRCOJGVLGZvpalIAxDTV1WF4FysLNhJP_yZZ5QvJrIQwg9AIQRAYQBIEQThx0SxmVWUgipGGIaaqVxCW8XKws2EkyVaJQvJrIQwg9Jz+AqAGuNA2Tz46AgI6ZnZiGMsIBCRAMBaAIgoiPACkAnePABQ0eAAAAADAQY3OGAdsIbgYCagQqAZYjQwCL5URk2hPkqAAJoJAABuBgAJIwfhCMgGivR0ACdMgAKhUBpJIAAcgyAAA3AwAEkYPwhGjCwOXqlQE1AuhGSsEFwGkkgAByDIAADcDAMFQq0FvrCwOZaFwUkakVLpJzwXAaSTJUuGwANqQiqAAIkGATuhK8CwOQPli8alJTgYNyKl2ZCULQNJJkofwaCCAyYgogACJBgPBIqEA7skxBYHLHyoCalULp6krtRc2AeDaTZKREAHIAAG4GASajAAUJBWANA5REVASgNg_+tB7SoDaTQL5sACCjYAADcDAGLQw2XgFskyoCXBg3IIWSOJVCQwkEOqVAAcgyAAA3AwZ2dTZ2YASChuBhCEpMKKRLQs3rVgzpQrCzaYKq06zBvKQACKlQAAABIyCEJSc6UgAhkvCzelWDOlCsLNpgarTtMG8pAAIyVAAARBgduIglJSlSEPGS8LP1VYFIWbScMNpSAAPQqhQHAAAEdKyQJoxEQT1KgBiEUelWipWFmuvaWr1I0pADKRQAAEQcAWUqYQyEIP44fmMLlYJY6MSgj25qEyQqVhZrtVIqYipWAGUiiEAAEIUAALGB4lSthED6C5WCEUiWMwijkAGUKyol2XKsRViFSsogGUegAAIgoADZcEkKrKNhCfwOhMFysEIpMsZhFHIKZTUS6htWIqxipWCQDKPQAAKQUFNmdgVovJAmI+DBXEqBCDEIpZBSVE07AWt6I0pA4kkwt4PgAAEQcABJGDClxSYMSlFRcrEiECsGIRSyCkqJpLP5EZAhUrA4kkwj0AABsHAGFL+oQkcgwaVKgQgx0GnEWsgpINRNJbFreyNKQOJJMI9AAAPBQZgALGC4lxSYMSncZULKKEYMQilkFJUTSWe0IyAipWUQ4kkwj0AABEFAG_L8uOgSSk0hcrACFCMGIRSzSRGFMpqJpLKXkCOxwqVgkOJJMI9AAApBQU2Z2Sg3o4jByDcoVhRbOgR5aFWqkEQpQrKibaqMSolCsNJpKyO+OFfvEoAAToA7Ch_xxGDkUhVb6hS0KpVIKzipWVECDJvbArVxiwoqVhpsc1ADkgAVPZCGEAA3BVnDTXRxGDkU1Uq0GWhVKpBUaUKyomYZN7VFauMVPlCsMJpKyP4KHY9nvjyIMIE6ELsIAkBBMFAOmKgBqANzHgAcOPAAAAABbvCAO3wPOuAJAQGAwxAYgAB0guAAYgAf+JgAAAAInFhczpAfg5JmUKwogPEqOFV2CtXIMpKiWaqMQlFSsNNZCOrQOQIIAAErqEEPvlRMpSKKFlUqsKAKlZVqJhIox9+VAAdQOgkgDTiYPGRIY9ByHsoVmO05FKFRQqlUgpBKFZJqJZKoxS2UKwLGtADkJIBy4qDMAPGQySA_ByHsoVhRPGhUUKpVIJqCpWDaiWSqMUCFSs8mksgDkJIBy4qBTZgAGuCYOhQfBjMqAqokTwshW0qKiYQlqVAAEwKgAAAw4kEwduhCDhZUEU5SiSws6kTgUlRMvQ1YYykBqGUAGhNTBikQMDixIbKgmvCBw1wDAQE1jICcgDpCIAHekQAH_iYAAAwEBerCBiVwB2SAYCGIDEAAOkFwADEAD_xMAAGYmABgIvR0C5yYAkgAVE0yKUgjUMmAAJ4XAABuIgA4VQpBRIDoDZkwDuEoANClAAbMmAAFJ_4qAAAQFcAwEnQ6B2ZMASQCoicVE0gNAAJ+FQAAIjYEMEhBID8HIpCCxFCooQSbmhKKJUSyVWMJlNyaZTAAFIVW4tHMBjyBHAAfjFjID8qgdCkIJRTyQSb6ZKAWoUyolnnisUf9plMAAUhVbe0cwKCIQAYWoUhAfg5FI5_kgP0CoRJFpBJtJPWoUyoll_isUWiplMAAUhVbm0cwKCIQgjwGjtpJw_MkyaxyKQe0FZCVHIpBJpJCSmUx6pFSjlkqk0ohhAHIpaMtFUATlrCSPWRIYAy2MtKoeQwcnsKlZt_ogP8PoEckhJKJJUYpTyolkqo2UJ5RDCAORSFUv7RzCSPWRIYHhSzE4fj0BOUKzSQaCNpGjm2WK5BJpJHamU57RSzUSaPdMpkkqgGOOhSE20hJBZIEcwcUzBQEHiQ2ZGycdqRUIkGFyQIwlJ_5SXWhC0LJVYQhEeLlZRTbVZLsguVgBVIoAAIkGAiQaQgqAuVim14HIcTTBBSlIXKwamEogAFEAABEgwBwZiED8IBgJ4YsDbR4CagDWx4AG2jwAA7jIAAAwEGIA_nhuBiHEQS7KgHcGjsCiA0EppS8qUxmZUEUDiSkAANwMASsuIkGX6RFFfaULwDVGDc_qLFkJ2ULwSm0syUH"
noncomputable def WL34_2 : ℕ := zfNat64 33246 "gTBLhcrAloFklJxrJpLuqW5Kr4uVgDWkoggc+TgCcixZgc6OmIAgngSBidBQRVKgACGjMCaSVKgMuQFoayVAbQ8kFAAAsDAIoKgSBidBQAiNgIdGwEUdiVAaf9LQmIqAB7KYaAABYGCEfAAe0D5IgWBlthwOhKF4BNCqh0yheBd2jfVQWgVZqAAABoGA7gqCjJUAMQkYtEpA2tQWs7lUpC2htByIkNUgUAAAAouAGzKF4AuyxmFVFWFSsLTVZST4qVhZtobQcyNDVIFAABiLhiQLtKF4AxCq0EYhUrP_JxWG7XVZS40oVhba6vBo3hBVIFAAFOLIJD0F3lC8CKMT+ZsLZar0EgRUrA21WUrZKFYW2umkIYeQ9HkwAFkEgAIIQdDwF1SoAYgWSUkkYm0PC1ncq46VBbQ2iYDyGKQAEsPE6AbpodxkHBDgqAUYaMwCTpUBtCHBUABmxCD_zUAoUSADbNLSJYoDgq6VAIoNGYBLUqA2hV0qD_7cBqxCAADoAAppKESBbpQvAFSWMwqv+0IUhUriMTVW01WUutKFYW27zFaQgg9AAVpHgiC5i5WIkOh7pYzKpVaCbcoV12o2mqykDJQrCul00hXjyGMQAlObADvkj3FohiQEaLlYA1AA6pXHWlCvBi0WklLNCpWFpLFNQPQACCDIAgFqNGgaCRC5X6w+B9pYzJI5qtBGKUKyqSbSqVUrykUhba6vBo3hBCqFikIagKmYD_Cg1EudkQbdKgKCCGFo3+VAbT_ZV3kqC2htByIkMMpFEoAMIhREFmFysBPxkvCqrkQhSc_UrSVd_lQpC2i1WTWD0NJlLv724cePAApRmSRIGeFysBXxkvCqgDyhWRS01WUoXKFYW0NIB5AfgX+7sZQMBEwAehoIgOCkZUBQYwbgEgyoShtCkZUH_W4BsiEBdAAgPC+YsDSMmcLla_CIckU_RkvmJVSCXskVkUomkqyk5JIrKJaTMLxlqI9DJZSybaypAiPg6ZzsrNgSWa4EQLgkDI2CpWDkAIZLwKpBFPu1INJVlIWyRWBpAog_OH4GloK8DfhYmDoCHmM7Qko6UkIABMgCQ0CodACsmAEAZAAMyYAAVkwAB1BIAAAAkZADxYAgQqAbgZAB4ioDaCBCoAAAAAoFAASGgWjoETFQDqDIAQEVB_xuBExUAAfYSAAAAJDQMJ0EvyoBzBg3AskLSoDaCryoAA+gkAAAATMgBwsAkqVADECyU3KgNtUlofGVAAAAADBYACRkFyfAYcoXgI7LGYFkV8XKwNpZkq9yheAAooeDKAJ0GgAJGQSGWeHOgmMVAACNGYBTcqA2hMYqAAyUZAAcqHgbmx0dG4EAJDQtZ8BDyheBFGIFlyaE3guVgbSzJWQlC8ABRYkAAACwMA5B4XLyXA43_4PDEII9F3FSsMpdLJFG0VKwABsiQAAHgYAQG8DIMBBFuULwCqBZH3FysNplqslMSULwACaCQAAIgYvwFShACBlShUBPY2CsiESouplAEhUAAGISHRDAAACvQgPCgCBkWgp5KmIVn1SM0soXyG6mkiyUkJYvAAEyJAAAnCidQwAcFFZHzsHp1i5WFkipoMl4WSzQScFysmBIrqptLMlVYXKwAEviQAMQAAmFE8LExyA2C5WWQijiMl5ZqoilqvQZSWXBqFc2lmSgKLlYACYRIAAAAIjADQsFhofOwREXKwAlGS8LJZJT_hWqptdstV5K4guVgAH0EgAQgB4AOCvvIE4iTR2EpAOiMFQyX1kq1Wgyku1E2slVLclBcXKwADzCQBxYaAMzMBAGAlJQSLLSoplVLdBKkXKyqm0z6pbkq0C5WHQFIloAAISEiYFAFHUGWFysAcBkvM7LTgFquSkqplLMlUEXKwAEyCwJCNgAAAO0AuNgGAg8tQAWFgAjHwAAMSAAAAAAAIiQG6FOlcO5VTwFysCKyUsZlVqp7UCGKQq2GqlFThcrAih2CYOhELJhLIOXGgrGQEAayzsFjyoBhJYzD_qsW1KiqmWqlEyoApIAAAlDgB8kQLAx1A8BcrAHpZRaKq1EI8JQvKqZaKDtKF5TRqFQKmEAAEocQcGGgPkuDcKAkmVADE_wdFklIUTbVJakwfb5KgAy8CTgwQZAAAQwuAAiSNBQBFSheAMQclkTuUKwom0cC1XHpSipWDtToMpNAEIAAUAuRoKHILPKF4HQYg5LOF0IyBUrCibaqPSCFSsJyGX3iRPAJNJBqg0DMCg4FJuPnYMgLlYB+yxmFmq0EUlVtNVGo8ShWfwbgLJHckVgASQRgKMSUcfOwZoXKwC4ljMLNV+YhCkqtpqo1CuUKwAsgxCpOF0P7qxDRaA8s6C+ZUAMQ04tByCpWVU2g1+2VAAHqJgAA3FwEqHzsHrri5WVEikdLGYWarQQnlCsqtpqo1DWUK3WFC82z0LNBJAVJyigGrDIDwGBAiBUXA_AxMqAX0aMwHJ70qDCXSy7JKlIAZSKHILgAAACKFysoJFTQZLwo1UyKBDFJVbTVRqOcoVh1uJlB1xIrlcZAAAihwcO4K6LlYD4SxmVWqucQhSVGwlUanpKFYGkAyw4rCaADIFgAAiZDKR1BZRcrATcZLzjatVQUkmo2Eq6wNnpFSsDaB3QqAkgABAzOVBIAvJQvM5pwfksZlVqoTsoVlRMtVGqdipWGk2mGugBouCSAAeAIlRytO3MJSASoyXmt1aq3EQhTRSrYSq+UwbikAAUw4jIoaQBNjB8AARkBnGgUPDkDsSoAagDUyoqJlCYtDxSoAAOQ8ZSKWQAjxkPIcRnEBjFysCKxQyXlEq1VaSFDFJRASpT7CVVOmDcU+UbjKaQFuDisbyEABpKkPDYGlAciMeQfOwTcXKwIQGS8LNVj8hCkqtpKo1WoVKwiADUOkk30tAZLMgBGiVxFSukgi4uVgQgMl9lKrT5CFJqnDfTbSVRqGMoVk0AJRFRVHoAAFnqg2JhPFwNHJgP8HwAgsmABEpMAf8OgMgbQABMuOUhEAsUiAHIArQiABYpEAAQYaAAA4XAEFahMN0MhkABwqAJoGDmrARUaQAUgASoHi6ABaTYHdKFY9MpBQgVKy7SSKRgyX2WolUggDJFZtptlKqGDZmKchJwE1xycOQ6YSycWdMxFB6YoASRgB6EALPgAIsAAAAAAAAAAAI2NARmzHR2nAaBlzHD8H8lC8BFBkvKqWSAhcrKiZSzJQjlC8DaACTHZBQAANhQBgJwqBoGZUdA70qAEYaMwJpKSomUswFNvIlQG0FIZAAAbBQQgAPOGkVQ2keAYCDybBNQmAqIBGomAACBMAAAAAiCgFAkQRAzKjoN7lQBNCqh5i4qJtKarAHSoCrNQYlEAAEQUD6xQsuY4fgtAuVgRWsljMqtVoJUShWVG01WUi5KFYf_btdd2A0bwggABJCgCmswRBQAtIqEEFtKlYcS0KQm2k_YhLdKFYV0XUuYwQgABSCgCsF3OHQW1Xo2FwAlBb7xQrkpCaaSqLBGzqVASQygAAFIKANcXOcvBXY0FweMWBKC0AipTB4lCsck00lHASFKQJPPiYygAAFIKAByZAZi4lAZkXAccKiYg8IqCbaQZMVGkJpC5mAAAKQUAf4uvNCCuxoLgBKC0og8yhXOSaaUWKlNhyNKQaEnAZMaQAACkFBSUx+GAElYQhXAEaIA5QmAHIA_smP5qQDxCYACcgACgCgE0Yr4TVQFysCKdUsZlVqtBVeUKyo2Wqyk95QrDraa6oJo3hBiwDAAAU_vgz1cASGhZAYgAB0guAAYgAEEAAACJXDFLQABJAojfyYDaCNSYAAxR8_8yAABOi5tjFfAnqpXAAKiSyq1XdSEzcoVlRspVlKbShWHW0gkGjeEEAAigAGmj1+DFfBBKpXAJIVUXUVKyo2U4KtKS7FSsK6GkIJ6xiALyMQfUdF0CqGNUoqqJLCrVSCKQEGzum2UqykCZIrDbXaS2JqzlUaR5DOQMQ1CSA_XMYZgAJWAIDQj+OBIWgA+hAYeRgBPREACiyIACvpkAB_42AOADG9rwaMVgCSF1VYlJUbKCjKmHlQG3pDEbQf+ZAAKQBlxXS2S8VSq_XSiSPaqVSCKSo2UqykQJIrCUtnO011gzVnKrHEB+9Eypo1mNNNsNSIACTcLtkgSFoEjHQBFAEwDwAJGHgAOfmQACIhIGZOBC4kA_BxyNNYvgKQuV0AMgK+WMwq1WgudKFY1ptlqspPSUKw6mkNoRpEhlUDKSkBOi4x60AB_hChgUSdhUSzTjaDNCoAATx8AADYWAAmrADkIOHTCHo4AAg2AnkVACUhoAF3DwAA1AAHoAjVZIBeBp6hXAloVU9mVFNsvz1YfkVKxqGkD41A9KJVNoGdC4ACSsABrgT1oH_JwAA5CIpAsjkrsVAAKiPgMoBcioDlZaxfAOClTAsl3I6UVSrQRLkiuaoNTJ9lKspPqSKw0mkMv2VCmPWIrmMqm241GisfLF4E3YCFy46OxoHh18iCv_IwI3IgKtFwAioiAAGJEAAE8yAADcFAAj1jZD52A4i5WBLQo1UZCEhskVlVtJVlJdShWcTabSygekaGAAG4KA8BF1zbuA6CWRUBMQCKRUBtCWRUVQA3ApAACgCgDAq8sLQFVyoBM5YzJCWQSBcrKCAhu11Vd5UKSqG0NI25SngACgCiPKQQTrAA9J5JIFnGgGAEQAWMaAAAACIXAAAOBgAY1wbGR6DoEakwH_kIAnmTAbSiCQAAxCsAAFIKAPBVJ2XAOUJgB6APhJi6AOUSgAOLnQAAoAoAKfElhkipaBNZMAVQAA2zyUhKTQABIKQAAUgoAAOsA3rnNMoSLQAH+TyGBRK2pxdDaD_U4AA0h8AAKIKAAk1BncJF1bP9JwFCOgJWHQARQA9olAAAAABgIB1a0AH1gAN8LWthL1cGBd_9SABT0AAFFAmh2hKAA+SjAAAOBgCmaz_6sDMUoC958AMFSiKAEfSgABPJwAAogoADiNTGjCUOJqQDKkJ+AeSVi7_dOsocTUiKGkBGChXATKQAADusBVsu4RhCEJlID55cARqUgAkUpAATkmkEk_6VgBtsODoHPHkYExAGkpk8eg1R4TDUIoBwl4HphiM3FkCl6sAiHQAByApktRItvzIagjk5dB07kAjDZkYBapw_KsgF4ggFkAWFCYZCmZ87AejUBbIaaQSCNcVlUBEoX5YrSMUOyShBACVSSPRyTQUy1XBIQoIA1jspAclUh6EUPaoRVAA+kUbstAOuVh2UeEIF9On4A5AagTRjCM3AaG8sVuSWgCyBndO5VB6BjRaAU2z+uNADtQgJ6ANeSoYpGLzDoGkoT8qgA3x4_kEogExFYAAyheCnTp+UeRhqKZ6C0SuhMm5FIM1lMtB8VL5qUkA6iUikEjyERtGAvLlsAERUASGgAAAAAAAAAAAnoBDReAETp+GjjIUvDRgWyGqZk3Io9mspGMtJIQQxIjVESikci0WgJqAfMFxOQnMtnINRykitxJczGspGoEShWMZaJQig5ouj1S2JRSRQim5lq2"
noncomputable def WL34_3 : ℕ := zfNat64 33248 "DiE_AItZ+cPxjWR6AssZkrZjoAPGg5ByipAfkDkomj0Lp0AqlJVONhBaZ0oVhhKpRcs0bxTh5DJaPQB8jwAExsCiYc9SRhyPRAfgD0LJqoqBQXKzScbCS0ypQrIIAmK7SsG0IIAAGYCXFllnpo7ByOhAfgTR6WSyCkNxUrguwZzjGNgvgtEOUKyyWSrTR8NmsIPyhQWAAAKlGHbNHYOR2ID8CaERAfhZBTKQ4m8aL5LUHlCsYk0mhlKLMjh+CbiYQokke5w7AAONDp+0iWXSKBNIuHoSQayku0kBDmjcQ5IrAFvsmsov+gI0_qLFYOQxZw7AAEdFIIFxvHTc_8tJ7dPYRiKhKAKSaFysyl0JqKQAOTUILQI4JPJNByACLMINfbGfJYQQzwpAAARQA9olAAAABNADxrAoZb8A5TZkCPG4AagHVS4AEoAGU_8bAAISZgHxrQM7GCfS97CWxzIAAAPKmQZSqFNAAAEVKw+gGnmoAES8ohtgCQ0AIAAAfKRgApIAAIBIAABgBjMEzoAcZAExoSQ+gnAAAAAAAAAAAMYeAMDQ7QE0bmUsgvcu5UaiPeSpVdIyao+dmEJS9bHIFIoKUynDaaPQeglAJpotniKix0ugAOQgAp0ATGgBwcAAAAAAAAAAAAADPABBodQpZIpUXLuFRHoPQdA4bU0VKyyRSSD1pSlPK6BdnU_T3+QFZWDNGcKpOQATjY6IZ69mUkbp7uoYSvqFcexWejkMm8KlZVLo9Ao9YqmU4iXSCJazfZ6AbKM9Ejx0q20Qp87A2NAAqsAGMgAc8SrrNHeaGos1DdPYAIVh6AFSsFysu1kehFAOoVwAugGCxuGUigXUAR+PvwBCNCRmQFacgIInQAUgq_89ABNU4AAAAQIAnoLBgIWADFoAOlADDYAcXAExoAAAAAAAAAAAAES6AAjQiAlcqcPwCaATZSBR05mkGOK1MKx03ALSC2Qn8phI8gFHDoAUd0A+Gg0nLdrHtNHpPVUFisml0qkUmqxKFdxtIwGK_gSjNRiTR7QUTsmuoj0A3Es0UciVHB07A2rLQMptAAS4AkNALlwHuMgAAQqMPgAA6RAABKPgAAvTMbHZuLnQ0nBB6MGQmi2B4GelQBWEB+AYpKg4_9ZiW8LKh6ABukieAAOQANzZKJ0cR_dQpiM4uVkkYhka1kmgpICUKzjYSrQSCREkVk0QgaQLKlMeoEuzUYgsiJDhuAzHaABTQuEwHhSoNkZB5D_yEIQAlt4yoA1U3FREIAAYxsHtmAMBYqi6KQ8DUXZQvAIIWQLUXKw4kQXNYLR4FysAOJkJGOpJABaAIAMTgA50ASMgB5cAAAAAAAAAAAAA0lCENE5MgQ4VAEEAOEVAAhwqAAkcfAZGIAAWiV4jYioAUQDXmR9Co_43AKBKgAF_nxTQA4SMAOneJWGwUCROCoCgIwH_GYA5sfAAOQAAhLQAAHjoA_pcLI0CQ6CDblWAVQcNwelEHcXKwymkLJ3CxmERDSAIRaEnlh8TQAaJSou2CgSA8TACI6AAAigB9pKAAAAALmQGT2YFxXAA6YLRIMg5h03gDEAT4VH+oIBTpsAA2w6AABchAAtrgoEjcmQHJTgMsFwAAZOlhtAmgAZS9iMAAEJGAPo1B4poCEyAGCcAIQFgDSNSYAHdqQAA5AA38jAAlmwEallwapbUcrUxqQRqHSKVSKPwqVk6KlZBspda0jQyiVSCTaaOayPR6gUDaSokEbqRLAZdhAgr4HlXA75v_nqWgSQAA6QVAATQAP_HQACKj4ACc08jW2DMWWQK1MCCNT9ScBUehUrMtZHJTWAqFcKoU0AKBLJBCb_Y6HWiSwADKQBs6AJmQAAAAAAAAAAAAGU06j0gotKZUKYABBKDgTBvWR6RQghaKk4AWS6oEummVqYAS0iWAKuaefzIQUwVgbkvGUAAegEguFyUAKp9p27hZANpJQAHJqSHjuhSyPQZK1MCyZSOhJF0xYyrLSSCFf5IrCiBVUuvHlAlkuhRuIrUkAQx0Ens0m9j0F9UoAugBlAMelXIy4AA4hpc8hAAAJ5ttuJ+pCoSIFwO8VEUAgnEPn49EISEAKqERdO59LI5ATcRIwADnQLebZdZtGcLIAOQP9DyhEqODEB7MQAAOvHsKo1AjIAAppxtphKsJAekUjoKSwo0NTCFHGIQhoDYeN46VSSgLpdT6URiD0A4RIwAbnQEuzZR8OXMNNFCklECUk7RoZBjv3hoGqSRY2AFkOJ5Jo9CKABYjbGHD27Nw5m000UApHksighBSKSLHQyAGYhFAu1+bkWO3c+lEehJ_+vUETFqbJnnrfEqHRSezmai0Uh4Om81OWbO07FjeWyUM00To0fEJAezrUSyYaqabycSqVaiUYCJio1Ijz2iifPo_9Uaezma0EYqzNHc1P+bOyVo0ucyUM00To0fps9koVGkZM4qAbq5dgz00c0kc3kTFRqRHntFJKfRyezmazEU7UOpqrU2dzn_xkvksdqIGAI+8dYr02ekG003A3m01kONdfa_ewDABx0AbJfwNRmaqk0B6OTbZMDEE587IMxmJU9YlxkAUSoSwmn02lEKpfQNL9at9pKaxZOlhOZqVsMhHp03A2jQ6LPZiXEUJkvACy4E8mUsgX0AwFgX9s2sskkUp9HPEHQ9HM9FINTNmzskyUUhlk6xLjqo2Iok0omEsmk+mEmlWUiqUZ6B4AR6hZvM4oEIaHVj4kgE5MLXzYK7JQA0hpPrBGCmTQqj40aGIYAImkucMbqG7mZS6ixOjhQSSSuOgc30gyUtxQfCjJQCwiMWzWfTCSQslBAcAYTSbJt2CFicB8RKADSSSqF9L8jPwACqAAWM2AMAEncDdS20HSJ4enQqCTUntd2SrT2YlpR8BHwA2gynruFEolhEqo0sDysBCwscSotnMokErwsTA+xQvKP_jYKgBSuhPx7LQaASLgZ1NRFA03k4Lx7PpRGoQSq4oiRgKCgWQ6BizbbTd2CWgsADBeAMCAAAAgQogHZR4BwQSdAOJtxvJJZHjQC0ANIPQAAKqHkJoDkw+RASADVIAOnAEDIASNACA4AAAAAAAAAAABoABOgAM08sfeu8+Hq6oEC6XQQgxbCpTyDLRaCFeJIrADPpEsPJ9KJBBySECwPDZpO03oN5JwBdA1MhIvYM4AKb6FS8AA4gABrHgpAR5AdBe18LRFSukTwHJpGCjhcJJAmbGSZaKQQmbJFYARQ+oEsj0b+hCFHoAQT4dD2I9lDY9AIVKALoA0VgzgEpB0bLwAAQOD8ACiguNKBCWicAppk1gBgmbGS0BS90sVgBdDxvn8Is1AqIlAeEAVIAodD4Jo1AAcdAAAABJASAAHoAFTmonQ0HCY0BUJQNiaAp47ghNHYXmVgCCALLKiggYEABBUF_CyAfgSgFBBGkEHOgAM1AjkH9KVMlsxEUagB0UmkygOZSnl0ALIl569oEqlEpoY5OlhyBgASuGwNgKgpARAQgAvpUABUFZCjMADFD4IIAhNGA8JAUd0+zUyoxVLYY1CuEkkkGw2EwnE+Bw3MtltP2YIijuKk5QFKeTQm1kejwPn6BJpNKiQVPJUsAU00+ppNHYWVWK1cAagHCi4J8xAYEAAghNAOkpQClofigDiyMpNHYWSqDkjZPQ4jPJZP_FUpOJtLo6BUplUKoU8XLe4D4ehNJoVSCjxOllSAuzI3E0dhZcKoVwA6PSyfKKpSJTaXQVSpTKQuVwugYQ4SBHCaTQqkU3idLAe8wbikKoW+MgyUQr0UJw1Fyum1SZgqJVNIAAbOH5VKoB6FKCmWzedMwbl0q1Gkj0ah0stwUK9BFKLCpWZTCXaCURjqFc0kUSgfOyzOT8nD+sgIRJbVkieFEgkkDyk7ABKkASMgA5MASFgAAAAAAAAAABPguGAB0oAChACj4AkZADy4ACLAAAAAAAAAAACDgwKBIGZcAQEoAA_8VJsLgAB8ZAACQQgAAUHxE09WFwIaNjs6CVq4NgZcwsDgCYAggf+FiHEwAOAJgADqFj8AAGwME9jhho7Q0I2UgTTKG4GA8DA2oiAsgkBKDcKgADQVAACJFgAA3AwAy84bgYDwMBWiYAAAD_xMG6JgABCCwAAbgYALJ8ASMgB5cAI8dAAE5A_01AR46AAAAAhAwABUYCcfADy4AOo2AAiofQEg0xUHUbAACoFgAA3AwAWT4BCXDcFAEeOgACcgf8agI8dAAAAAAE4+AQlyGBQA6DYACKgBp_yLA6DYAAAADcFABOPgEJcNwkAOg2AA_yLABpioOg2AAAACGBQAEEIGyfTuNIUG+mDMACKzk2pcEE0xWS8iMgACqiwAAiRIAJx8AhKhuEtMPwDqNgAIqAGmKg6jYAAAADcJADPPhuEtMPwKuNgAIrOQDTFRVxsG_EoAAADcJACkPhuEpOPQDoNgAP1iwAcYqDmNgBoCnEoAANwkEtKGgAhOAFnwAEyAPlwAEWBoOAEYdAAAAaYqAAAAABoOALUfAIS4bhIAdRsAATQAio_oqAAAAA3CQbgQ0+AClxEiRVDAZkABFZybcuBqaYrJX_mQAFdU4AARIkWMaAh4CZh4ACQgbh8ASGgCwYG8mDMACKzk25cBpisl48ZAACbFgAAAGaUABPgGAgMAwAgHgAAAABAPAAE0FgAADAQC3U4BkfCCDAYBgEoGoE4AkogOgNsVAAAmgsAAEEGDUAGnwAY6AQlwAAAAAAAAAAABux8AhLgYBgFqGwDUAmsQVnYlQEVLIAAAAAYBgrBn58DwMGwmBBhsH_lbUx0BNKoBFQvhYrAYgR0TgAAPAwA+D4CiVBKDBAGgAANGwE0CYfAAyguACygQ6AACUGAMABHxEU6EEGCGHAUwuVgVQCar08hsUNGYAHRaEdjoOVSJ4AAQQYCBx8IIMEMOBrAsFRAJoJkqAOMpUCVB_8eAPQjAABBBitJSc3HSett7UIkGW2HAk0oXgNhLGYFkQ0XKwNpZkrvSheHt0oBDgUAAIkGAiQZbYcBcyheBFGIFmdqE8EoXgbSzJVIlC8ApJ1AABEgwBDjYD8RDcDE6CgT2TAbmTgABZMBpAAigAAAbgYA4MAJGQSAUCryoBzBg3AIWlQG0skvyoAAKA8AADYGAAkNCnhwEPKF4EUYgWXJoTeC5WBtLMlZCULwAFGkQAACNBWmj4EKlC8Bh5YzAsiSC5WBtLMlcKULwAF2JwAAEwYACQ0zqJAv8oXgOYMl4FkBQXKyqm0syU9RcrAOXrx_5OAAAADoQAE+ACmwAEuAHFQBIaAAAAAAAAAAAAFMLEwaKULwBifvRizxNCAKUKyqm2qhcUK4tCehZoL8kyXY5WAAKs_sWBoO2LlZAo6NxGS8Kr_9C3eUKyyWmqj1pJQrAAYIMCzqE0BsYsAGVGS_EgVuULwH+ljMCyMGLlZl_4pGksn7C4ACkjDENoAKBIg4wePmIEwS4XKwJaBZJScayaS7qluSq+LlYA1pKIIHPk4AnIsWYHOjpiAIJ4EgYnQUEVSoAAhozAmklSoDLkBa"
noncomputable def WL34_4 : ℕ := zfNat64 33247 "BWqUL_WDwD0AWgXKwu1pYiasCSo4ABJDC4JGAQuXBmAElYAOlAAiIA2JADBQAAAAAAIEgAAAAA1EASKyzSXHFysCCPSqYQAxQvHwXK1MnDem2EKK8SheRSyEW1h0EEBS0YSCGUGaWMwru7kzlZtDMUMAJKwUaSALBgTKTAVUCQAsAAZsmAPyDQPQBoETiYmZWZACSsABvgCwYAPkQA_lYAI4hAAUw+AP_ARFQAAJhQBwcCAwNdXi4CaCUqAIIBBfBUcUqAAEpUAE+CgAAAyDAClbgWCMc0aGgLxkAAADY+KobQCsdABQAoAAALAwCllKBjqmA0DEAP5AQXRsHwTjoEhtKJIUqACgBQAAAZBgzAE2sGSQgDFCZYvK6EUNImlzGUTLiqG0mhlRQ8AJaFhaAAAWBgEiIZGHzXhYGNvyxfRa6EWcmku_pPprlwJDaTQy7IeAEtCwtAAANAwZ3IDc1lFKY8ClioAggEC4CxfCoAAOFQAUAKAAADIMAfJrORPkR9ILsS4LJNIIBrOHEoUrfLF8ROplmajSUWgCWhYWgAAGQYNvLhCZf8Hz+i5WAPQDwxcTTjadiLTkwtCQgdTCAABYGAAD1A6d4AabAISIDhYWIkAohoD_jMAAAAAAAAB4GAOArFqCSYs0VYJQvOFLQMQqj0bWULw2mkKqZSxeBZAtapAAAWBgHIZLxCZVQHzsUl0egBOJVQUeQweJIrpptMJBKK3SxeE0ik4DoAInUwACNBwAmpS5TI4jMo9CQXK9kNQRTbaQJLFcGspLJxsIWdQrmvLF5NKiDkcAsTwjDwDUFoAKQKLR+jiPszMOjKF4BptIYyNn7FyssnEHTEFWWgAH4Wij9guAAC19Y4jMoTjh_KQkNGcIJttJVBrKSyJZy1mEX2oVz8li8olUZwiSwik0y1EogHmDOHXLGZKjs2AAeoBqlAAbYGiIDgsAIh4AAAAARFwABFkoAADwMBITd1cGih9ih3Z2OgB4uF8KAp0XAbePIYU09MXBaabJdhFwJQAAAC+FAAPIgCQ0CqFArwuXgD0KaITLF4Wk_ydPkqxyxeAAAAAA06IHgYGgUAMSIArh8AESIgAF4PAAHkAADwMAYceCEGB6FAeAqAIIAcIqD5TcB4jYAAYgAAhBgDAZZUACngaBgRBQAAMj4AAgVATQMYhAAKQAADQMAd8iBYGIIVAiMqCTC8UQA4xsFdJKE0qAGzkIP8zIAACwMAEPCAS3wP4iBYGPII8KgPeKQAAAQ4qAGh_pCAAALAwAJyoIMRAYEwIjKgCiAAZnYgIcVADZyf0Qg9QUAAAd0iACjRTRUBkC5eFdKJMRrxckwyBrYSSrbLgIg2chBmPuEIAAA95EuWVAZAuXhXSiRZidMLmZGQNbD_9KksNS4Ch0EQbOQgzEAAjhUAncjBwqoIVBoguAAyxfKJMS7pU9w2JqYSShaLhSEQbOQkjUAAjQsFM7Ok9iSgATaCJVQt0iCYGE4FAKUoXgHkCSMRqH4l6gyVApkCBMIQeeJwAAJgYJR8dpwAkNAHgwNwLl4A9Amivi5WBpZ6kT5SZ4uVhTaCcayFhGhgAADOFSaNgQ6VAfRQgCg5UBpJTbsqALaY6RoYAAZwoAGiUABIgGAgAAAAAAAAAAAMBAASGjLxIKoFwBxjyGACALlZRTSFVnJYvD+6cW0SOgRwAAEaGksiBcNXFwBWEB+H+E4lJRTSHzUK7vi5eFNLaJBQI4YMQgAA2BIFZlQCsDyGAfJKvwFx_5mCqw8sXgBtHIoEMDiAUMWFshr3wkAtAHoCYiqUlmzKNYRS6hXHyWLwG8vBtCCBxA4ANBmMztWYrFAzuz4HUli8AegTQZly_C5WBppMpPEXKwptBWa2c6zQQAAQhQBCFO7PgdSWLwB6BNBmXL8LlYGmkyk8RcrCm0FZrZzrNBAAsUDAAYVDQJOVBNIKIQBlsqC0n_y7opUhoSANpk5CEeCQAABeZgaNcDwUAhAgPAf6QgAw5MABYiYAB4iUAAB4KAB2zAEhpDQI2VAYgQgBmZUHU0g58qAP+NxoJGAAAAdsyGgkIuA_+hACjSheHU0kpdmULwHfMVtCKcgSAAADOzJsNQ0HCFwA9DUKcSTKF4dTSSlhRcrBKF22ixECPPQAJsNE7OgPhCAJDRvhMGFMp0AAGxi4K6SlxZUH7EItoRQAAAoSEz0TBhYCdAXPQgM1EMeULwrollP+C4CCW0IpyBIAAAxSEmw0JQw2yPg4orUEDNRCklC8K6JZT54uBKQf2GVtFcIEeegATYaJ2dw8MnCdz4LcFwDODyGABuLlZbTSS12BUrALaWlQkdBwAAACBMkD4_Z5DDUBcAYhAfjSloJSHE0gtccVKwA4iukaGAlABJA+QmeQw9QXAD0_8rDPi4PBcrDbYQWrMKlYAbQbyFDAugMYFgZHQNvXNkHQKiJgB6A1QWMMTAAqImAAHoAAHgoJwAQrFOnkMfsZC0AelVDVFyvi5WUTaaSUmaLlYU0OIYxGhgASQPgd9QrvmQn4eyLgB6AZwqTEXKy6bbCSmUh+9OF2tnMA4jQwAsldkoAL4VoStTnokQyXiLKF4E0ek0qkkWtOLlZdNouGrGSZSYwuVlRpobayJNAjgGBPlhg8gQMarACQopfwjAxHIXLxoqpfCCFmmhQSheG00k2UykJtNBlOW+spORoYATQA8IAUQhGwejoAYkQBXD4AaePABH8iAAIoAAAAPaB94QSo2AAywhG0GDoBXDQH8mIAAAAAAhKwAAFCYDzUK89DwljMtJQvKqTR6TUdK1Mki0GhcrrNpsIrhari0qNNoNpqqYjyGFmo0k6mUsSE_CsBAxqv_xUAxuAXG3F4oIWb2qQbsoXhtNJKQjFysANoQQqlE7E5CQR4D5WBAELMA0SgFpsDA0AAYaAAAJB8AAAAEBaAAA8FAFc1mdlICQDwABxAeAABMRAABPMgAAPBQIMQlwpQABRAREbJTKiyV0FTFwAA4EIAAIQsAwoEeWkkqoL_Th7afxqQgYuVyksmmwjHlamH0sXkkporxu1hBAKiTjZgBngobUCOQ4yXk0CorVwB6Bs0qRqULyzabCFUbhcvJJTQ2_+XiDo01AAKgCBZaJKD5VRcBCU4BvB8AQKKgAjIXAAFH+RsAAAG_CQ86AN8nAFEAMOTEkAN8VAACePgAAUHwBihLH0LkqZTAaysAvgaAORlRZOJZCqsAuX_+RgDaAJQNpvhaADvJBPJQFVTgJmFwBydIngBNAD_zkFUAA9iMEPBQcdiRPmo5TsrVyaTT6HDeOmGukpGEVKy6ZTCRSiDVQrkRLGctJtFMtNHpFJJtMI+2znXaSArAk0mjIFauEF_Rw3Dpp+8pApAwVKwuN2sy2EKIfyheC5EhhNLKVR6VSSbVxMRxMNJA8Cg6D0jAEBKAAP_FSbC4AAfGQAAhEIAAFB8RMzGwMrOgbeuB42FoIsRgB6A1QWMMTAAiwmAA6whAAAaEinC4EPq7uPsQEPAiBgHmFy8AegTRfRcrDiaVcJ0uUnoLlYU2grHbOdZoIAAIgYA2ZcDYMmY6JSOMqAAGhSkqAq_+ViLoMqADSUWNGwAAGwYAvyENgdEpSKVABKQYmVATT_pUqkqAuhtCNM2c9gUAAAn9CAJDQgJo3JTt8uJzUaCSmojUY5QvAm1GUy0ppdLJtoctB9YMYAAAn9CEJNG5KdslxOajQSU1EajFKF4E2oymWlNLpZNtMFoPrBjWK6ewAAGRoQM+b4ImTgfAhiYAAUgL8qAgkDyoKIAFk0lEA8ETA6OzpPGgV4uAvc2QGVAVZQgigLQ4_obtYWRuljMANPEkIPYFAAAASGl5B4_0bVVKgB6DaXgBQXKw4mklr9CpWAG0r8hAAAAE2opAeBmpUAPQAFBcrDiAZqxktc+UKwA2nTEIMpLQDVDIACTU_cPA1d8XKwB6f8WicRVKQ42ElqkShWAomYMo4bwgg1AB6DwNzoAHSgBh8APLgCQ0AAAAAAAAAAAAAQjDsmwNPKgOYHkMA+mVDU4mklr8CpWAG0wYhAAS2HgZgAdKAGHwA8uAJDQAAAAAAAAAAAA1jx2DkoCA_AhCcPQunLiqUhxsJLTUlCsMJVDaFfPIZ7AoEoBhAAaFPsRc6OgcmiQH4A9CyZwKg9FysONhJapEoVnKmKqgBHDeEEAJIBD5cOQclQQH4A9CycOKgUFyuknGwktKKUKwwwSVg2hBDbKQBLhKADA8dg5WsgPyaSV_pOHsdLpfQqlIpONhBarkoVhhKv+lIwhBQkMHwAABs4GLABisyIdA1WqULwB6CKWglJNONhJauEoVhBlWDLOG8IILQBOhkAbpo7BqjQuVgD0LJ_QqBQXKw42ElokShWFn_ysG0YKeQ_fDQ1ABwDwNgcg1VIXKx6pJKYAnD0LIKQSFSsONhBaKQwlWOytaReyE_aIPDX_qEGkSkOIwASjQ7JsCVyoAgkUDmpUHFkTUS3yZUAG0ishfqKgD9zkESBOxWZDUUnAy5cI4sZ4eJqLQO8oQRYvqQREoXh1NoWR+ljMJyGkggADnEIA1BcHoPE1FoHd0IIvTVIO+ULw6m0LI+yxmE5DSQQ5AMBVRKisAd0uN0aSiPE1FpGQghBWIpTwVJQvDjaV5JxZHeWMwnMpNNBACq0lJKpbB0DN4QMeiAJDQWkWABgQLxEBWNgAAEZkwAJSKgA0gEUAEoBgC4mx5EQ8DX4hcB_tCCC5hSERlC8MppC7rFsYgOQ0gQUJ6POOgbAQEAGJwAc6AHlwBIaAAAAAAAAAAAAAhEptRJZ1zR2DVcBcrAhCcPQsmJiqUjU42ElplShWGFtitXDaEGShNAAeU9GwHgKgCCMQELlRJL05AHbKgAA5IRyBoAAR5mAD0YOQap8LlYA9CycyKgUFyumnGwktJSUKyzy0BtFcIT+SkUcjdrAEoF3HTeUjlFRcrAHpVDPRVKTTdQNgaOwClCsQgGk_+cP5KXwbgLiEwOpmDpvRRqcwuVgh9Elj0KIKQrFysy2kuhMDhuKVtNRV_8pFpB8IT+TxlPbCAJQPAfHE2t4OgbWVAE0Ar+VCl2oJbkcqADaV6Qv8CVREI4gBg2YB4En1joGqgyheAPQuhKQ42EFotipWGEssiVmsNnMd8gR2CDwbQBCQIE7FyOTgPCwJV7lQBFAE3FysNppJb6kqADiKqQgKpVCZAkO3E0CDpuDVGBcrCxycPQByxXBTKQ4l0FoXyRWAGksIfP5KaTSaCTgIxg3JuZmQAmlADy4AkNAAAAAAAAAAAAB3zeqOxpS4DGGwHiD4ANmTAAYwmAAfQdAAf8OgHgAdKAGIwA4uAJiwAAAAAAAAAAAAgCNZgksI6B_x8APQ7lxeD9ZUG00ktAIVKwA2h2EJ+FUmIwBOQzABMaJRrQRydE4fikgk0e0UUCtTIopDAVK7LaS7QS+nkMUjWm00tJVI4hPwCLWfnD8Y1kegLLGZK2Y6ADxoOQcoqQH5A5KJo9C6dAKpSVTjYQWmdKFYYSqUXLNG8U4eQyWj0AfI"
noncomputable def WL34_5 : ℕ := zfNat64 33246 "wDAfi2IAL5gAisCUhKNgDiFwxCcocLj5hcElCAbAXYGAALOFAAABFYIsUNhtIuVns0IFIxKIeKLiu00F6lQbiCgAPsBwAGNqO2OGAEwoDAOACpMADcWAABFSTEIAAYdARICAAAAAAOsEnQ8IOrpDQKcHFxppJ_geNo5IorYuBIElQYbBtoKAAbwFAAv2RZ9GiCLXRlC8ynmy4MnUugtZQXKySdSyCldxcrAAgAJAAAuBixBrHgL0mQEpCT_w2fiVDaNSUBJUsF2OBIBIAAACIGAkEaHQBAqA1DgFaULwIoA9FKRjZKCECBkvnjYASAAAAaBgAQlTRjVPB4IhlQB9jx3_52CiHTKFZJKSaRj6sqAAAAANAwAVl4BCVA6BdyoKpgQ+Aon5ypJSEUk0_+Mt_lQAAAABoGA0ECjB8_gaMxSFysNIOSmlF4CcHQqVpSQiDSTSMTXFysAqMJAZAAI0HADf1pvKgAHGAIFdtDVQRIMolQB+CBOZSaDZyhecSySQkGVACQAAANwMGd3dxtmAE0YAKfAHgwAOOgAAAGIAOOgABXDwAAJgYAAKcAFSgBh8ABOgB5kABGgCIsAAAAAAAAAAAAAeZAEhYABA6AAACxRkAEDoAAAAAU1IASGgAZjIDoChBIDxlwDEkrLy4JYKQEByIAAAAehAEhoABA6AAACxRkAEDoAAKA8AAAASGiJRID5lwAWhg+AMPLiihJZklwU0Ac5EAAAABPgCQ0A6HAKAyACcpABmS4B6SVLJcAAo0iAAAJsTEBY1QMAwIQYEZFQCakYAOhAKgARkVBCQCiAABgGAIkRA6DAhBgB8TAK6QgBER8ACGj4ALJ_5SAAA6DAGDuFLbDgIcXACUAGwll4uAP9k28i4ALofw0dgABzCgALHwBIaE2PgAwbAABXYuA0n+ya7hcAV0y8fAAAAHz4TRZUx8AOTIAANalwGkku5C4I6V2oCcAJAfgj4SAAApnwyR8AGDYAADnlQGkEBlRRA_IvH_j4AAGo0AFE+i9mNsdABo2AAA6pUBpBBJV5JiALoPQAAajQAHz4BjoyZ8AZjIAANalwGkkqZyxeEdK62tInj0qlWS4AA8PmQIifYMLXkOgA0bAAABMqAAzozABQXgenUygDQBYnR0AkswJA0dDKR4uAIIFRiqxxcH9mYPYFwAXQ_ho7AAAkDAFBLkaCppLQZTZFwAAP0LgcnH9CkaMLgAs58TgAAjQUABIaGsVgdEXAEEDHBVY4uKrJRlACkwtAC6EeNHYAACVysFWhxcCyE4ggC3whcEkyklPGULwCuhXDR3HdWAAD8RbM6sFdC4CgJQ9AFIQSheFhP8kzYyheAElWL4NTyAD8RYnR2nw68As1QJAwCXKgEGwAC0khjyoC6C0yoAibQXj_iMAABIGABoXAlJeC4AC06MV0LgD_pNKwu5UJC0K6V6OjlQkAAbgAI+BsGG4PA0yoAAB+hcdmei6CCSoFoRC6LmSo4AAGwYABIsDQUzoaJTZguAHIGMCZBZYvCsklO6ULwe_1Jiui6jR2CEAAAEmRnQ0SmlRcAOQJWEyDSxeFZJKXcoXiEehXRBBo7AAg0HAAJGjOholLxi5eCgkYcgQQwFCcWhWSSm_KF4PZKF0VQaO_eEwAAOEPHzGiU7yLgByAeYkR+CLgKpJWBlC8ALoSI4bhRHoDoyIR0iA0Sl7xcAOR6ADCbzxcSSsklDKULySSFJiug5AAEiRAeAVVYzwaJS5YuXgDk8kikKSqrLF4VkkrlSheTR6JQujbkqOAAD0SCkADpQAxGAKlwAwqAAAAAAAAAAAAD6QhQjhuSmG5cAOQootQCWL8LIwTaLJSyli8FslK6nJOl0UAAUAcBo3uPE1CmULwIo5KyCUd5QvwcjHUlqxXJKoUoXn+j4C6HENHZywWAAAEAM7+PE1JeULwIo5CyFWJEY4yhfgxGuJVJKo0oXg9_aTBdFWGjskoE0wgI6TUzJQvAijkUUsVwQibKF+DEY41G951JXoFysHslHNZFJmjsJo1KibarEQJzZiAzTIxYaIJGIuAHJVCsxM+soXmUslUoKai5WAEEAAAVhwBCsf1CacY0EpAADfpUbSqVQlNpABHBsAABgKAQIzAY8aUDYQghI6AAP9ER_xqADTkwAAnjYAADAUJhk0PixmQSyKkoXgTTiAMSTlC86zNVgkrxyhfaQC6L8OG4ACtCoAAQ1vZNVguCyA0oXh_ZOOIAx_kXHWny0AlUoX2kAuj2jhuUZaAAxmTFEMF9BLLSSheBNNoApH6UL7q1NWCSq0LlYAWQU5g3NpRAJNjwOzaGE1NndztTNl5PhhpCA58oGgYEIMDRCIKyAKQbpUC4CYAAAcpMAABoGADBnAAcoGgYEIMA4yYAAAD_RUDcJgABXEQAAGgYALB8O4UtsOBuhkExAjM5MqXAafjjUlPkZAAomGoAAAcwoAEJUAwEAiGAAwsAAACRIAADCwAAAAAYCAFylA0DDZDgBcXAEEAVgbAAZs1klHgXAf6NgAAANAwEhIzKJQHwCEqBoGA8FBJQAAAAkoAAAABoGAPIfAsDDdOge4bBOQJL2pqzgZNgJLJY0GwH+jYAAACwMABfmDTHwNAwExCck2Xg6yVxzJjAJLJZiA2hbKRsAAABoGAXUfA0DRZJgcUbBZskjAURyZWFGwElkv_jYINCwAAABoGDnDL7UNrbe1BEZ8EOHgnBgQgwNtMGYFEAakXrxkACVpRw3AK6f2OGYAAJwYAAKED9Pg0pEFwMCEGAepkBRADP5zJRwgXAygVYCYNwjs1CrWQAAXAxPgOeqCYGBCDADouAsgDUs19Lg_snElE+ULwAIZSJaRPAABMDAEnPgDwYDAGwT0CUj1yxcCBP9kweDYANozxCfqkCgAACqn8xC2lBIGumQT0CUj2NpcCBJKQEyCOhtA8tT0igANsWAIIfAApqjlYAnBsE9P+JRKR6p4uEIgQHobABtGcIT8DgxMAAS0+oxWAz8ZBPQUkpHrdy55wwXECSUcBkEdmppHUrVx6EpAdwPHwZjwFOfABRICcOAMxsE9AlJuD4m5U54WECAAG01yffeSgYgAswOSfAuHBZDgi6ZBPQBSPU0FwIE_0TKzMgkIaRhyE_Aul0DbGzMAMR8C4cFkOACB0AAKQaRUCBAAIGNQ4Y+AAAAHnwAWiBziQLhwWQ4ByHQREAU_0Pi8lQIEA1HQAYQA+g1HaLwAgIGqPgJw4HpmQT0AUj1NBcCBBKe8yCQhpG8IT90BUEmmn+0505MAh0+28aMOJA10yCegCkekoLgQISFMgkIm5ozg9KISQMEkwOjIyZzpuQ0o6N2YATMgDwYFYFy8AehTQLpYvC0iWTp8lV2WLwAkuXAAAOwYAAN8ATMgBxEAYDABQeADAfABeFgAAFDwAAAADYGAAmZAHgwIrKgKCAUTKgCO0byU3JKgC2lI0IAAGwMUNCAExYGgYB4ME0i4Aggn5SL0FwG0ktri4EHGQAAAAATFg7BgHgwYCLgHfID8A34XBaSS+KLgMoEZi4AACUAJDQB4MCqi5eAPQP8nTwLpYvC002Sq3LF4ATrLgAAAAYjAHgwYCLgABID8KafuLh6G2xKdJcmFwAQ8LgAAUAsAAZWAPBgmgXAfmQoYtCeKReYuA2kltcXABNwuAAB6AANWAKqLl4A9EpTQLpYvBFrRvpslQKWLwAwqXBAIKABzDQAA1YBcKBDZUBzpCEoB4yoDSCUSoJCAYQAAhCwAA1YBpLJ6BBSoB0SEJQB5lQAE7KgAH8oR_5CACSCwAAlY7lWDhxcAPRKB+4uC6Zdo1klHiULwrIBNAACELAADVhxiYEQli8Ae_oJjqicBdLF4GkGidJRaBZBOh8SQKoDYFoACSsCLFipioHPFwDrjyGFNDgFy8GNppsl5QXAWSaT0ABJEcAqsbACGxoAJRh6BIOHFwA9AO0FxhBXMmsnuTC0AAiltAYwZwEUCwBrhwF_LF4A9scjAWQuC6WLwspJSZlC8AAwKBDDRMGcygS0BYxxGTlDZQvAHtjkYDRhcH287EHfC4AAkhxLwzAGAFgxMxsAJKwO8iALBgAuPAD4VgAZiUAA1kYACKgAAaEgDgxuBswfY2BoHBHwuADshQwCwxcFpJLT4uAAZCX8joAAMIDxmBACSsAFzgT1UABHgCwYDwlQHZFIAMKVAAHoqAP+Hw9MIAAQg4AA9UACngCwYEFlQH8FIAe6VGaEi0n+ip7JUAH0AAAhBwAFgwHnKgNJIQAtsqMwJBpB4RcABUAAAhBwQj4EZIgCwYLUFwDQkyXPASADUbBaQHQXATRygY6ZQACFGQAC2YaxYByc8qADshQwCHhcrC0gx0WVAAIqSgACFGQAAhYEw4CcRcAD48hvCEgF8FysDSDEgBcrAslC1oAQmSwWgAAXqkFOi4Aux5DAHUFysDSDFERcrwQfBZAk0lAAERMgJsWKJ0xOESULwB6DWk0HLioFyv+JcQTLSRiQAqVgVQ0SZXKKGUAcKZBmACFYAMlABkIACdACjIAEXAASIAOLADBIAAAAAAAAAAAAXNCbaIgAIXoU8BIqIgkoXgZf_qQxK+ULwKIGrEoAAhRkBo2ZEHQCpo3eQXKys00elZJItBIXKw4iZYM4MV7FSsrpVCqNlRJYABDzIscMbQ6EAJKwCUiBxyQBYMBvyYAwgBdSYADQkwAA9AAgcaJgABbQBJWBOSQVgKALBgNyTAfmYgASx0AAcDoKqBFBmAAgCkAQuRqHw0HDi4Ae66YgP3FwGkkv2C4CyAVJMlhJQFmDwAPWYUhYMhlGeVAdCQgA8pUH_moEOlQABkkYAAGw0RoFTQg1EvWEQSXHmQFBCokMC4DTMRGxcBRAOaiSwkoCzB4ABacAHSgByEALNgAJcASGgAIkAAAAAAAAAAAAVQHmWLwB6GEWEXJmLlY8Zs1mUKJGyheBVBqIhRJfvB4kp_s2EbDwVgC9GFUPHFwA9K_sQrQuC6WLzKaTKSULpQvCvSsAAZKjjGoykCeJEAzkCdvqhTpolUoXk0po9ItdWclSkr5QvsthMpJkr8yhfVQqkUDvI0coklJqMSHj5ZjtiAiWYBEguJSEmcgkErjbNBcR0yklGeULwlstAE0BKApgeAAQJGPFisJq1SheAPZ4CQ9A_pQvKaWZozgpYWULwKoOKPiaGkAABVCxL4sEHWJcAPZ4CQ5D9xcEk0n_Sb8xcCcVoBDCUBVHIAMgCaWCABRukX_ioJrJSheBl1wrWz_ylQRS5UuKaXSSmfLF4XdIKwT0mhhJpFAyAgiGLFYTWjFys_MhVwQh6D0FpTSheU0yklW6UL2NGxdKJFjodBBDCQQygySxmAd9SAVywB2GAVT3FQAAoQuCIDQcQewZAAfpPjAgCUSoACSMv0VBNpYXKwB6AaMLimubYM4NrKgACSGFwSMAhcuABErNgFQTVqlC_1g8A9AFoFysLtaWImrAkqOAASQwuCRgELlwZgBJWADpQAIiANiQAwUAAAAAACBIAAAAANRAEiss"
noncomputable def WL34_6 : ℕ := zfNat64 20600 "CnAEkYBCVAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACEuAAAAAAAAAAAAAhIgGAgEQwAWFgBZBQAAkSAAAwsAAAAAGAgAQlwDAQABhYAIQUAAJEgAAMLAAAAABgIAAAAAAAAAAAAAAAAAAAAAAAAAQlwAAAAAAAAAAAAGicAUBAAhGAAAAABwcAAEQWAAAMBDSAECEGADRsAABYi4IwFxJSuFwAAqRYAARIMAEIMEISoBXpIrAik9SoCqRSEJUABEoSAADcDBeb0sbAgBMaAAAAAAAAAAAAAaHxEgylBQmAXjIAADclwBJVGlwAAQyBOAAIkGAiQbO4cCcC4DpIwASUJFwV0ksui4AAcA0AAIkGABYdESDFWAB4IcLgABKG1LgLDJQnFwABBBYAARIMW4NwM2AOAeJUBRo+AMllQUk0jHmZUEHhIAAADcDANwN6YKBSZUB_Y+CentSoKSaRj_sqCogMUIgAA3AwS1teAE0YAeVAASYAcLAAw4AAAAAAAAAAAAIAwASC4AIQkAHMLhsxMElOgXAAXGNgABEgwA0DF+EC4fVLgimTyYqIZBLgAq1foJJexlwA7omEIdAAESDBiAE1oIgoigcAAAAKCoAAOFQHIiIAAANwMAAxiACqQAI6AFmwAYyANlQAAAAAAAAAAAATBj1CQCDKgBpFQBJcqACrhwuA5ARAAABuBgrAIe0CQMhkSAOJcExAAOBkBFJKDMyDOQ0MT8hcAACJBi9vQMAJmQH4cAiS4AIQUAI1LgCStfLg00FAAAAHQYACaMAOLgAJUASEgAAAAAAAAAAAAEkYEUOAOxcAIQA+hcAf5Jj+FwN+CgCSCQAAiQoAAysANRgB5UASEgAAAAAAAAAAAAEkYACNAGBQAaIgAAbAkAABoiAAAAANBwAghwHHLhKUASiy3gUNgLV8lwBJZmlwADwUieAAIkSAAmjAnCoACJAGBQEUOgACagAEUOgAGUKQAAGg4AwMAcnwIIcCXDIAdgKGw_4dG1LgCSjnLgIxDQAA0AFYkWoCCHABwyEoAZCiHVLhFgwdJozklwuXACUDrECcAARIkABNGAQlQFwcCeSoCpxsH_F4RqVAABg2AAAAA3CQb14DEgIATVgB5UAOFgAgcAAAAAAAAAAAAAIpADkIACdADioAmNAAAAAAAAAAAAAHFQBMaAAEOgAMCQ4wuABhUAAHCoAAAAAAJDQ3AkAkSoAhZEACPKikgCRKgLIDAAAAGJiAgAxWANFQAgSBBDgA0bAHWjYAAAEZUAAIHoAAAABJQAvGAPGQFwcAKyYAAEIAAKyYAAAAAwFAA0PgEJEAwEAoCABCMAAAIEoAAWIwAAAAAYCAAYfAeiQAQOgAG1EwAAAAtAuAAANhQAND4iHoNgcAGDYAAAABGGwAAQKmcXAAAGAoAEKsMSEAEouAAPcHRYi4AARVJToFwATeLgAAjQcB4eAElYAJfAGhwBwLgAA4liLgSnWIL_pMXouACbxcAAEaDgAJKwCJKAQkQBgUAEB4AAAaHwAAGHgAAAADAUF5fXgBJWACFQB0iAwDgBsVAAH4iIIh0AAHCoAAAAAwFAALVgQw4BRFwC6CYagIfTFwBKSrlC8AOI2RGhgAEaDihoakAJqwAE2AQlQAAAAAAAAAAAABasnwhAS8uA68LDUA+JQvACy+AyXgALGGD4ACDQ4ACaMEIfABcqAAB45UAEiIKsvy4CAw8ACPg4AAAIrJoIQD3LgAqgFVKF9lALLCSxmC9A4eHRqMQAAMXDizAwAmrAICoACHACQwAAAAAAEEgAAAAAwEABIaAwLgCeVAH2KgCDpUAFWlpcAAHQAAOiFlKFx_xaTaVAEaKgA1ZQvACzcsuA_oPAAAEaDgAAqwBIb8lauQZBZjQXACkKv_GwBhSheAFlnZYzAhAPAAAAHgYALVgNqEARKhZjILI4i4AGoDEp5QvCqBZ+8ZH0g4AAACNBwAElYAcVEwFwNOKgM6lwAw4qDqYQbwXAAAGeEgAMbUYIMgswgLgAJQIwVEoXgBZZ6WM3sDwOCHgAABBjQAC1YlouCy2UqA9mhE0B6JQvAohZ4uXABvIyAAApDQAAeYAmrAmioEPDEtFwWQBhCMAKVKgJqVa_lwADkAWhUUXDQE24FkygCSMGHKgFCYEPnwAAAAH8RgACiAAB0OAAUrBiF27BcAFUeasBUShfZQCywksZnKSgbwkOQAABBhxZlM6h4dXagI6ZlIAaZgCakAhKguEgKF0bR0AAAAAFSYAAAADcDAAOZgCCsADQgBJsAhKgAAAAAAAAAAAjkLUcSgCoXBhImABVpQvrIBZaIZLwIsDfuGgAABEgwAGb4BnEYL5UE0AAzpQvlojfgTgiFm4JcBYAaAAs4MAAJIFXKgOeDhspObA5coXnmMiaBZ06XAwoGAAAA3AwQcPNxRJYI1KgPJDQBNsoXlEmhxpYr_9LgKwDAAF6BgAMwAYpAISoLhIKiEAAFQDaABPGIQxMAAAABuBiJMS+rQwG3pAISoEgqWSEA+SIA2gA+CIAAGkQAAAAG4GANIfAISoGgoTyECrEYD_zEAMGQgFoKsRgAAAAAwEBIEQfAkEqAweVBQRYJU9o+CjQRIJUDCgYAAADcDAEefBrAuD_R13sqJpQTrBcBRoMl04XAo4KDIAAAiQYMy+5ABzMjQkAEo2AAAsRcJqDg_6TFcLg3EFAAGeBgAAAysAKRgASEABOgAJkAOLgCQkAAAAAAAAAAABERr8hkFmnxcHEj4YgC9yheWQCytgyXgADgDgABEgwAf0IAeVBsLBELjgy0ATEATKVB1Aqr5LgAADLAwAAAVWGILGYWf_FwEEg_gXqSCF3BcrEPKE+kgQFS3LQBIABaAYACYMDskCdvRYzIpZMKULwIMKECOaSSB13pQvnulkqORQsy2DgkAkAAAESDB2AnsoBCVFAJFWLisS0BlAAhiVAQTKVWmlwAAAAG4GLUxCatDACQ0WUNEpcmXACtFgBGpcASVrpcHEgoAAAAB+YQCEqCIOKKPAQAiAAP_KwABACIAAAAA0DAEWTgEJUFwcGkiB0hsAASkAADhUAAAAAaBg1AIakIAlBSKtALgCKMSsyePqiFwDkkqsC4AIiLBUAAAyDAAEVgeCEp0PA14IXFRCKMSTWRzH8uAckleyZACQQcJACA4AYFAAZBg5NwAQ1PgD32U6av6LlYH_RhyF0x+TC0OJZJKOMsXgAFQAEBwAEwYZ2OurjxtHJ7i5WAOQsndCbtxcSTiWSSgXKF4ABUAEwcABIGAHIrAECohcEPE1HeULwByeSzZdGO3FwcS7Rf9kyVSheAJAAAAMAwH4tiAC+YAIrAlISjYA4hcMQnKHC4+YXBJQgGwF2BgACzhQAAARWCLFDYbSLlZ7NCBSMSiHii4rtNB"
noncomputable def WL34s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL34_1) (dpk j 2 WL34_2)
noncomputable def WL34s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL34_0) (WL34s1_3 j)
noncomputable def WL34s3_5 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL34_3) (dpk j 4 WL34_4)
noncomputable def WL34s5_7 (j : ℕ) : ℕ := dsel j 6 (dpk j 5 WL34_5) (dpk j 6 WL34_6)
noncomputable def WL34s3_7 (j : ℕ) : ℕ := dsel j 5 (WL34s3_5 j) (WL34s5_7 j)
noncomputable def WL34s0_7 (j : ℕ) : ℕ := dsel j 3 (WL34s0_3 j) (WL34s3_7 j)
noncomputable def WL34 (j : ℕ) : ℕ := (WL34s0_7 j)
noncomputable def WD34 : ℕ → ℕ := rdw WL34
noncomputable def ready34_cuts0 : List (ℕ × St × ℕ) := []

theorem ready34_cuts0_ok : CutsOk ready34_cuts0 := cutsOk_nil

noncomputable def ready34_0_state : St := ⟨26112, 285696, 51168, 114175, 29184, 45301, 29666, 44151, 53248, 84751, 29184, 45301, 28545, 75944, 26112, 285696, 77280, 399871, 106464, 429055, 136130, 458721, 189378, 543472, 218562, 572656, 247107, 617097, 273219, 779489, 80352, 143359, 110018, 173025, 163266, 257776, 192450, 286960, 220995, 331401, 247107, 617097, 58850, 89452, 112098, 143601, 141282, 172785, 169827, 217226, 195939, 502922, 82914, 114417, 112098, 143601, 140643, 188042, 166755, 473738, 82432, 113935, 110977, 158376, 137089, 444072, 57729, 105128, 83841, 390824, 54657, 361640, 0⟩

theorem ready34_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD34 ready34_cuts0 111 137) ready34_0_state = 46761 := by decide +kernel
#print axioms ready34_0_cursor

theorem ready34_0_covered : Covered (toCl ready34_0_state) :=
  ready_cover_cursor WD34 ready34_cuts0 ready34_cuts0_ok 111 137 46761 ready34_0_state ready34_0_cursor (by decide)
#print axioms ready34_0_covered

noncomputable def ready34_cuts1 : List (ℕ × St × ℕ) := (137, ready34_0_state, 46761) :: ready34_cuts0

theorem ready34_cuts1_ok : CutsOk ready34_cuts1 := cutsOk_cons ready34_0_covered ready34_cuts0_ok
#print axioms ready34_cuts1_ok

noncomputable def ready34_1_state : St := ⟨26112, 285696, 51168, 177182, 29184, 45301, 29666, 44151, 53248, 84751, 29184, 45301, 44441, 91840, 26112, 285696, 77280, 462878, 106464, 492062, 136130, 521728, 189378, 574976, 218562, 604160, 294506, 696000, 320618, 779489, 80352, 206366, 110018, 236032, 163266, 289280, 192450, 318464, 268394, 410304, 294506, 696000, 58850, 89452, 112098, 143601, 141282, 172785, 217226, 264625, 243338, 550321, 82914, 114417, 112098, 143601, 171925, 235441, 198037, 521137, 82432, 113935, 127774, 205775, 153886, 491471, 73625, 137141, 99737, 422837, 70553, 377536, 0⟩

theorem ready34_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD34 ready34_cuts1 112 52066) ready34_1_state = 92311 := by decide +kernel
#print axioms ready34_1_cursor

theorem ready34_1_covered : Covered (toCl ready34_1_state) :=
  ready_cover_cursor WD34 ready34_cuts1 ready34_cuts1_ok 112 52066 92311 ready34_1_state ready34_1_cursor (by decide)
#print axioms ready34_1_covered

noncomputable def ready34_cuts2 : List (ℕ × St × ℕ) := (52066, ready34_1_state, 92311) :: ready34_cuts1

theorem ready34_cuts2_ok : CutsOk ready34_cuts2 := cutsOk_cons ready34_1_covered ready34_cuts1_ok
#print axioms ready34_cuts2_ok

noncomputable def ready34_2_state : St := ⟨26112, 259119, 51168, 79646, 29184, 45301, 29666, 44151, 78153, 116255, 29184, 45301, 28545, 91840, 26112, 259119, 77280, 310287, 106464, 339471, 136130, 383622, 228768, 461775, 257952, 490959, 286497, 519504, 312609, 545616, 80352, 108830, 110018, 138496, 202656, 254751, 231840, 283935, 260385, 375775, 286497, 519504, 58850, 87328, 151488, 175105, 180672, 204289, 209217, 296129, 235329, 468336, 122304, 145921, 151488, 175105, 180033, 266945, 206145, 439152, 107337, 145439, 135882, 237279, 161994, 409486, 57729, 137141, 83841, 316848, 54657, 287664, 0⟩

theorem ready34_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD34 ready34_cuts2 107 107273) ready34_2_state = 153295 := by decide +kernel
#print axioms ready34_2_cursor

theorem ready34_2_covered : Covered (toCl ready34_2_state) :=
  ready_cover_cursor WD34 ready34_cuts2 ready34_cuts2_ok 107 107273 153295 ready34_2_state ready34_2_cursor (by decide)
#print axioms ready34_2_covered

noncomputable def ready34_cuts3 : List (ℕ × St × ℕ) := (107273, ready34_2_state, 153295) :: ready34_cuts2

theorem ready34_cuts3_ok : CutsOk ready34_cuts3 := cutsOk_cons ready34_2_covered ready34_cuts2_ok
#print axioms ready34_cuts3_ok

noncomputable def ready34_3_state : St := ⟨26112, 285696, 51168, 177182, 29184, 45301, 29666, 44151, 53248, 116255, 29184, 45301, 28545, 155136, 26112, 285696, 77280, 462878, 106464, 492062, 136130, 521728, 189378, 574976, 218562, 604160, 247107, 752512, 273219, 779489, 80352, 206366, 110018, 236032, 163266, 289280, 192450, 318464, 220995, 466816, 247107, 752512, 58850, 89452, 112098, 175105, 141282, 204289, 169827, 359425, 195939, 645121, 82914, 145921, 112098, 175105, 140643, 330241, 166755, 615937, 82432, 145439, 110977, 300575, 137089, 586271, 57729, 200437, 83841, 486133, 54657, 440832, 0⟩

theorem ready34_3_cursor : U (walkCut TOP BK TOPD BKD PT REG WD34 ready34_cuts3 115 105) ready34_3_state = 177037 := by decide +kernel
#print axioms ready34_3_cursor

theorem ready34_3_covered : Covered (toCl ready34_3_state) :=
  ready_cover_cursor WD34 ready34_cuts3 ready34_cuts3_ok 115 105 177037 ready34_3_state ready34_3_cursor (by decide)
#print axioms ready34_3_covered

noncomputable def ready34_cuts4 : List (ℕ × St × ℕ) := (105, ready34_3_state, 177037) :: ready34_cuts3

theorem ready34_cuts4_ok : CutsOk ready34_cuts4 := cutsOk_cons ready34_3_covered ready34_cuts3_ok
#print axioms ready34_cuts4_ok

noncomputable def ready34_4_state : St := ⟨26112, 285696, 51168, 292894, 29184, 45301, 29666, 44151, 53248, 238399, 29184, 45301, 28545, 155136, 26112, 285696, 77280, 578590, 106464, 607774, 136130, 637440, 189378, 694783, 218562, 723967, 247107, 752512, 273219, 779489, 80352, 322078, 110018, 351744, 163266, 409087, 192450, 438271, 220995, 466816, 247107, 752512, 58850, 89452, 112098, 297249, 141282, 326433, 169827, 415648, 195939, 701344, 82914, 268065, 112098, 297249, 140643, 386464, 166755, 672160, 82432, 267583, 110977, 356798, 137089, 642494, 57729, 200437, 83841, 486133, 54657, 440832, 0⟩

theorem ready34_4_cursor : U (walkCut TOP BK TOPD BKD PT REG WD34 ready34_cuts4 117 89) ready34_4_state = 214201 := by decide +kernel
#print axioms ready34_4_cursor

theorem ready34_4_covered : Covered (toCl ready34_4_state) :=
  ready_cover_cursor WD34 ready34_cuts4 ready34_cuts4_ok 117 89 214201 ready34_4_state ready34_4_cursor (by decide)
#print axioms ready34_4_covered

noncomputable def ready34_cuts5 : List (ℕ × St × ℕ) := (89, ready34_4_state, 214201) :: ready34_cuts4

theorem ready34_cuts5_ok : CutsOk ready34_cuts5 := cutsOk_cons ready34_4_covered ready34_cuts4_ok
#print axioms ready34_cuts5_ok

theorem ready34_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD34 ready34_cuts5 128 1) (ofCl (RC 0 2 0 0 1 0 0 0) 0) = 217222 := by decide +kernel
#print axioms ready34_parent_cursor

theorem rc34 : Covered (RC 0 2 0 0 1 0 0 0) :=
  rcOfC WD34 ready34_cuts5 ready34_cuts5_ok 217222 ready34_parent_cursor (by decide)
#print axioms rc34
noncomputable def WL35_0 : ℕ := zfNat64 33247 "BGhhU06ABRcmMojQwFoVEux47tPyFYBScaaVVasmuWgfJFZVCbUWHtG8oIS0OgAs7Mxr52hJQEeRAkDBDoiqYZAD0AvKVANZaN4x16VBRSqgFhAXoPADVPgQBiKvkIgBTPQDtRlIBtSOWM1_FSsJaVX_NWcqkECyaSKUQMkisBNCoLilwCcjh+ASkDDaYKGUyCpWAe6bgghZQEjDQAIUIADfBOqoL1JAMBAVALgKxGQAjEeABAg8AAVQACyAcsKEUOJoVB586AKYeOwDe5UH_2K0jH_JUBhDSAV0DWQ0AIACFhFDgFtGS8BTh47AE3FSsDCaZaKQJtRJg3ZxeSA_CDZaqcf1MTZR4BFLGYfCxmEtAqjkEYrF8SqUKwNksX21NWeWikLNJqNlKo9D2NnMy1U4mFfxEfACAjO_GQFSMl4DLjx2AFEKlZdLCaZahkoVgBpCPID8e3GygKEHEYxGTKJPIYC0AcmUBd5Qr4s3byo2WWiBJFZVCWylZVaKw9LqAG7WYaqcTCuAiPlmOjcrHl9CMjNTM1oGDkr4BgIAegbkNgBfI8ACvh4AAAAAMBFeXgEtCIkGdEdH_V6E6EDECIgMIuAOMlECZAABcCgABEgwBGT4HadESDGvbN5eaqU2chRZSKmMgEhJQpGzMAANAUAAIkGDEEpnREg1DB4DqUliy0BFLodAc_sbKZJR+GjMAARIUAAIkGC8AQkQpAxDQ4GckQACEB+VES0rCKLlZWS2zEBRcrAAAAApAwAEhoQkOBsZEUkHpURBCtTDQXKys002qUMmcpAATeNAAAAIS7nDopw0B9yIDGx8AbXKielt_8ZfVKgAAAAKQsACEuOZKPQNA+ciAC8gPwkgKwuVk9FNtGJlCpWAAAAAQCgAIXQA4uIo2OINA7ciAHoRQEMXK_5NQ5FNtGJ9CpWAAKkDgAAAHl1PFSkBoI2kQCcjh+Ab9KjiTS000MpSAAFICgAAzDw8AYIQA4uAF3IgAHID8EJxZWEUXKwFNtGJ1i5WAAKkDgAAOXJg+0VAVSOH4ZQlIbaSab0GQVCpWADEjIVIHAAFiAjkJiQeAAGkgPwQz0qjeLlYCm2jFehcrA_ipBkVGVIHAAABCrkoyYEIHjcAchlCUhtpJpdKWMyAFSsApgRAqQOAAC_AZrJIrByKQmjBjx2BSYL4SktJFNKKjJevwqVhLScs7JFcRAAYuJAaySKwcikJowY8dgRlzGEpZiwY7SRTSioyXpAKlZJJaTlOZIriIADFw4R4MqDkwGrJFYA5PnMQSkgm2imkfxkvIwVKwADHCypA4AAMw9xpxJIrABZIrASweOwwhKZ6baKaRuGS8gBUrAOOnDc_8LKkDgACzDyGxJ6cHZ3wA8uAJDQAegbkNgBfI8ACvh4AAAACvAEJcgZMRkOBx5EEEHoSQvysN4uVn81am20YykAAAAIGTAJkLguU2ggBGIgHzHwAe0qAtIbgqCIABNCIBQQdAmxYDCAbQ6ABfkxQRaAwSZNBUAAHgKgACQsABCaatKHwLBCFSAHoBv0qKz2NeNucDKUgAAFKIAE42AAqjIkbCVDgwSqVwkg9KKUQhxcrNIxLtpGIui5WcYuAAE0FQAAfFngCyEwwmCWiRGixiAcm0qgDwqVnUwlU0l6Ml8pPQVAABfY2AAzACyMAPEhdRoFgkQHKT4A5WVGGgy22jEbRUrAAHgZB0NIAAA4T+AmjiNBGUiAK8cPwCU3Gwlp_MZM3KFYAAsRr9w8GkALMACiQ6IkOArZEA108hhFDdJV_JGmpbZj3UqAAHCVAOQAjwAuZAJ6590SASgDkLoSkwmkwmkfxkvUsVKwAJJHD8YgAEQeAAcZv8TJVDg0iRAHuOH9dKISm0ln5acaRkljMlRUrAAAvsbAAqQAKJq2TFrGD4e_IqqD+Dh_XaiEptNZDSiUsZjaKlYZACTQ8FQ4gBO1JmTgHcWAyyQpCwCKioA0B0AC3JgMgC5JgAA0FQAAAQ4KRoSlsNA_JAjgMwNH5_pSAhhcrJ6LTSMRAFysCyAA5NIhPInpCAJGhOCJB0EfkRLQeghnryVCvKQlJtC4ZMzUFysKqD5SKJBHIPTjYTaXWPmjsBtmEEQdyEiAAHoAtseABdI8AAAAAiLgCa4QRBwBNA0cdAC3SYLIDBSYAAl4cAACIuADQXDKcP6aD8kymfPQq2nw5CyAGShWG2i2UYikMqEB8AKwsTFITjh_WaCaQegBbVgOpeMkIUp4USiEWetcOH5lrNNGyFSs6m2i2UYikA6EGUh+EiYpHJZoIzWTXURCnD8AdheSqATp4JaUJ5dIIOTaXQUGUKyKZZ6WBozjFKRUrumNAEEDJBGJdLKE+OH5djoaF2MqNhQC+AQlwHBQA1A_kZADHxoAHZDwAAAABgOK+Zp50dACSMABLhVBoIdFQCgEB+AcnKie_+KraMRiFSsMoRQAAAMAwATa4AkNFkESMHVFScKpFHJWQVydKSszk0j2Ml6MipWYGw0kJSAAABlrg9DmwESMGZFScAclZCUlZnKAWTWP4yXm4KlZ9mCAJSAAvwWAB3XnGNLKIkYOqKk4VSKOSsgsE6UlZnJpHwZL0aFSswNhpISkAAHYcAAIyAVVwAEaHcIkYN6Kk4PcRhyVkJSVmcmkMBkvNwVKyTgbCAKQmu2PgIKAGKubaKEQDpJFYCuDh+Ab9KislpogZSkggAKbIJQAAAe6_pG6lBEjBLBUnAHJWQlOgV4qjmyj8Ml5uCpWYEAFPvmIAADwFUgBLqAuVwAaaA+BybnwiBhBQvAHoBv0qCqWnNxlKQALJFRxAAAARNPKqR4IjkwGCj4AUEVAArQqKIAB3AgArYmBhd2QIwbUVJw44jDkrIDeKlYIFq2WZzZZan4qVmlIIAFKLmjeBtoo60eI8XNEjzDSBGCWipOAOQjK0EpItZnNlH8ZL3RlCs0gAPIqTuQcN4AG0AQDTXNUEQK8JFYGODh+Ab9KhKVS0tOMpSVQA_0TAABuHgD0NQAGvfhaAh+VADbNHZUQlM9Lo9AJGS8lxUrNIAI0IE5VABSA8GOJUsfo4juM9U4cgRRyXaqRcDJwWCpWXSrNbLLWplCsygH+iaSlky8IVqYFOR4RY8bKZ0pG51BwKYANBxoqIhLwPQCqt4uVk5FJpFr+yheAgRicYaAAIkGAFOXHsFS4HgAOg9BSFFchcrNOnDcUiucNYxVoXKwyZRAjEOgDQAEIMEIHZgLouCEGl0PAAhB6C0lkrAWKlZPRTbU0ljOUg0yhxnIQgaAaAAhBijB2d8AhLgGAgB6BuQ2AF8jwAK+HgAAAAAwEV4ARIhuBluDQM8NgB6Z4YgUkXKwslpGPEyoppFCiAAAbgYAYBi2hwUTIj5p8TqPn4RQlJUS0t2Ml7oipWU2whhHiHzsADXAkNcCRVw4JqkRBk+J6EUJSVEAs3a25GS90RUrKbYQwjxD52ABBwKARUOCEJEBPQihKSohI2jevgyXuiKlamA6m2EMI0E4fgADUFINkPAGEcRgN7PH4BKSah20qYMl7NyhWFNDCMzOH8KA4AAB2d8AOLgCY0AGoHTjIAXyPAAwkeAAAAAL4ECEYQoquCEBqB04yAF8jwAK+HgABiAABAKAAPNKKwh4JjERPQehFAsxcrKjTTJtmuWoMKlZTayGEo8zOg6zw+AAWILnhDwbBIgEhHD8AlJUQ0n2Ml7OShWDBVorpOQolkBhpEDYDZrr8NqeDwGEAegxB+ZUAtBpxUBVA9SdAAAQCgAHTS6eQeBhalXAMAcPwAKhcrKiXTTLX6FSsptZDCYtOh1x0AAX4bWPHgKICZjx2AMIKlZUa6aZaIkoVn9k4060P+Yr5OQq1kBxhAnBsAn2Qsg8GJFYCegEpKjXU+N2uwxkzkoVhkBCtARWDGD0UgBtUiIEBWGQNiaTQqjQEgUgLInwAqMqA_03CYioUgAPU6BIAIEAroccqsHgluoVwHinwB8cqKjXbaMXcFSsCSGUH7I33CYNIZdRgBAGguSDEBKVSAHoMQ6eVAXWEtmvqpdKSmgYSuZ0F0ggAiBgNdvjwLlTKYA5ADklCsqMBVi_ZZaP8kVgBdC6HTd+yMXTDcaiKiKk4Ni47F1IaBCMIUVXBCA1A6cZAC+R4AFfDwAAxAAAMBAADRixB4JjERPQ6xw_CKBcC5WYaTTXQNW+WymO03_a0Va6GERJYAAIQoAeGMAsrhkOgYQNyHQBD4qLoBJ4qAqgNKOgAADAQAAi4AFhCADEZAADIYAALiwAAAAAYCASuTgaNNKPgKIAAItKi7YTArRlITlQTEqI9bURAAAxCgHY7IQVEAAR47AHRFSsu1EummkZcKboIQExO8w3GE52dAADqGgBG0wtCwSzoBbpwH+FYAyIVAG0EgBUT2ScAAAYCCCiRXrNCCogD0AFNZJIrE79DdLRONkpTxyU02k0AAFbKQAUhsvCqmaEFRAHJN1mbAKSbNQCKUs0zVHKZTIoTfONyVVzGG5cO4AApAlTKgQwDUpTwByTUQUnG_KFZZmpJMs1gamU6qBXSHjlzdCyayK+xGAjJOgBILQwmYWfBUQFZHjsAlJdmuRFI03pNplKVMAKJLh2AAABAwCANFJtkKGElbSlPGI9Io5Is1EVJwpHasX5rSbKMY2bpeUp5BpNJNq2GK+Tk8gT2SgBfA4prKfAthSngD3NHYBPUqDAzTktJadSADCRdOjyOZCf2OgBNChOQQJoEUck1CaKSzNU6oktpbJnScbNzbJ0+wScQQLpJSQdNyQNmsk1E4ln9ycISXnRUAA6Q+rCAOlwAEaQKLgIIHwDIAZOPAAtM2AAAAADARYgoDRxsWZhoACIRATQPgBMJUeoyD_7cIkKgABiHQAAUgoANiMDVriEAIhEBnA8hgf8VqylC8whbZa5guVgBdAoJFcAAKQUB8eAAdYSDjB48IACZAHi4ACLEsRBIBSBxEuAGaDwAMSHgAAAABgMAPwzUAiARSRQmek9DJFKDKy7ipWNaj89ONoxWiUKzrTTCF0k6YLgAAihQHgW6yN8cVn4EgMIGzjoAhgVABI4qLoAfZNHYAAEQYAoOMABuhRdmiY8IQIIHwDIAZOPAAuoeAAGIAAEQYAANcDI8AF5CADQZAAKx4AARDwAAZjIAACIMAXtWMQM4pTyqAPSY6MSg+RcrCKVVntGuWmrKF5hppJzwtF0qoAEHAoApaMxhku5CBhqhX_oxBRTiXQuKUKwe1GyyFIYYTLICSFy2G0AAjQUAAPqA4WQswnK4mdidB09MpgAAdQqNIeAZhY5UWT_ZkVEegAADgYAq+MoqdAxVIngDkAnYVV0AjuVDkAC6EwAAoAoBA6ZTQchPwAOkTwoo5otsj4gk0UpIrrtJptlloIi5WXQC7hJKmtRntBLtV_+lC8SpZAjo2H0dndg8zXRMegUXAQQPfGQAyUeAAEo8AAGQyAAAiDB3GhsWUmZTOlI2Qk4N3rgGAnKhwbwIgONGQAuMeABxBEAAIQAADARTk5DWmNiOk42GhsCAlMeHkpa"
noncomputable def WL35_1 : ℕ := zfNat64 33247 "BhFgAAACQ0NiTABVJIH_kYSCXHUGID8PSW3ZcAAGEWAAALACy0ASGgGRIAKoPkWADmlC8AnqyyheAAGEWAAAvAgOEIQUjYaA4gEkAOeTAAeMmAAGILAABSCgB2nQhBQLRoDiB_JKADTnwigyDaJUOgABiCwAAUgoCRGg4GYkLUMhyAAY4fgFKSoA0_8LrxlQABJiIAADQUAihQMxIWoZDkAAxw_AJrlQBp_4XWFKgA4gAAFsKATwoLokDEcgSUeHD8CQClKRpSpTLLLTJFSsCm20ROgRwAA1hRQ0ZaAB1oAkjAD0IAMdAASIAMJAAAAAAAAAAAAKAOMIPABXQWBwNAEQyhecEWgLItAAXUTAAEaDgAQkQShQnB4AGgDQPRoAbKVAH_VKPhcAAAAArCgAaHQnhQ6h4DaAAEySoM8zBx_4pZeLgC2lq0IAAKQUAnhShB4FvLF8BSRQqgfguVhddspG0ooBKF4SQtpZjygRwAA1hQWgnhSGh4JmqwApAoEbPhKF4ZQKIMyheAW0OOgRwAA1hRF0NCCvloUVhCEFFEAAAG7EwAMeJgABiCwAAUgoAN+0J4UKQDY7BBAKIeqLl47Q8Zn0b4sUzpGS8AAaosAAGsKA29K4sBRYQ3BSfG4APhOwGRID6BNKgOIC3KgABqiwAAoAoAFp8jQUFs2AADELAD2SoA_8hRfKgABqiwAAEAYLwFotAgDCcHgAARCwBZkuCKn_mLvBsAANUWAAAgDBfYzpSBXToiQYJokCZxxGFhIoDUJaeMwCyWSNgABqiwAAiQYASBgkhwGwJgLkHQBNkqAMIpsOVAABfFgu0HAAAEkYCEOAkBEBco6AJtlQBhFNiSoAAaosAABAGAoAovRkFJyIAcgFxSoMGnxhFOlyoAAqRMAACIKAoAovRkGMyIDnB0AWvKgnphFOfyoAOIAACgCgM0KbIbMwayECS6s0dhhCSLgqVinWjeOa7KUfFSsqpVpptPAtUEAACQMUNGArEIoAqqZEH0i4LCdA4fgQTohcFEMIp1UXAADVFgAAJAwGgCEiBMGSsPBw8iAHIBEsqCyjM+LslnGVAAAAAKQ4ACZECYNe0eAQmlEKivWOm4UQkkYLlYWRyYRSXYuVgBtAAAEIUEICQMlYeCQgJhNHYBm0qCzBg+MIp62VAAHoIgAJKABIaWRHgEIQWcJUd6x03CiEkaxcrCyOTCKSTFysAAjZEAAAW1FHgEIIXRJakTR2FECqFysLI5MIpGAXKwADzEQAEGhIDhx4BCCGEpSZo7JbKQSkKo5MI5YMVKwABhFVjh4AACBEC99R4ASjiMKK1E0dlNCTKQqjTNHddmonipWEg0ai10FJZAAQIgXB0ADEQihyBh4KVkQA5AJ9lRoxaDCKbXlQAVQQgABNDiDArxcIocqIiDWZMS0HIQaCOZOUMVKwsz2wjFdJQrLz9Y2KaPQAAJocEIAB3gBdcE1IhFDhrFwUcJgCCANfKgDD_4qeiVARRCE9AACaHBzjElYeCQgOuOm4AYIuVhZgsfGEUj2KlYBVtoiJGhgABNDgORcx8JHgMkOIwIrizR2U0JSLSqvQ6bl0Uq0KldVxu5BVNoQQAAmhwAAzJAceAQgSV3mjspoCkIlVQJo7LotGOSKzLhRuLpVeK0bwgiUAAbhwAX0ZEceAQhQJKZ0dNwogIouVhVHJhFIbipWUQMJtBkNmsAAJocKpk1Th4BCHiEYfpo7AHRFSsq_9Ugu+sMmY9MoBtH7oEcAAWRMAAFWAHDWREzRB4JCAN80dgEpMIV33pksA+fq6agLaf0Rir+M2AAfpJmPjh8AjEB8CK_U0dgDvipWVQLoxAmcP56MwFlCCcTCAZ7IidG7MpArOseBUnDo1QqYEKHwIqqTRuACksgXRSeguVgFW2iIkaGAAE0ODuzj6Gnjx0BoTGzly0ACkQbAxejIIInwFEx4AJaVB_8+Ao5UADUAAAbAwESDE2NGYFIQn4MQTg6AMYM4CmLl4cZ6SXBBcALMXMYAACJBgAA4QBIaBgLgF4fAEvHgA+ZUACLSoAMpX4+AAAQ+Mg5GfAAfGD4Ai8oXhxHpJWglC8CiWUNUgPyuBwAAABUZRYyDjp8AHQBFZQvLKtGjmPSSs9KF4ToUiyg9P9LQAMoeB6h4Yh2c+AklLGD96mYB25QvNJpHpJW9FysCiWUDkgPwAAThwZjo6Q0IAjQgCQ0PyRADpKAA_ghAFEAPR0AAFoWAAAAJIwGVCPVIgB0lBRNiAIIBRCSjMNgAFTDwAAJw4APyEEIdAciAHaUEKmYCggFEJKOQ2AALcJAAAfCgB7oRL5ciAwyRHCwy0CCakMszMxRCSjWNGYAETDYAAFIUAKNCFEit2RADtKD_jMBQQapsFEJKbg2A6AAAAQQoABiEAPMgCQsAAAAAAAAAAAADqhAEhoclacpEAOkoP+sQBBDxGVNKISUqBsAAHhiAAABcIRiKWzSIAcJQG0Cgh7DamlEJKM42ACmwPYjAFQAAAvkKEkZ7JEAHfF4bBMBBAKISUACRicYJgz0EAKqEQOjoeBx8HZzoaAmDI+Hg0KfAAEIj4XtSCjBcVmegn8qAAC+LCHIYAAI+Hg0KfAAEIj4XtSCjBcVmegn8qQ5DAAF8WAAAmDAASGltR4BkIT8IJJDpUZ7qwiEeWLysz0kq1yxeAAGEWAAAAwKnmPAUhCfg7RKDoUQ5oXBZHpJchFwBio2AWgAAwKAAkNJjjwflPgG7jB8KIDTKF4WR6SUF5QvAC6D8SJ4AAC2o8ADEJ+EEkn3GD5UR6IS8lC8LI9JKWUoX0kikiVKZXSCSQDLwABrGgADDYCDXiR4B6SQIIRJLYPGyyUQNGULwqj0koNShf252Aqo25InlkAAqR0AWzwAcaRDHgPcgPwawkTw6FEgmni4Ko9JLdYuADaET9BcAAT4DgLgCQ0AloeQwOgyCY+C3_iERpKF4TR6TlwpQvAihZBPEwAAAdwKPAPQgkloQ8bOQPFEELlyheFVlRw_JK+soXn7XIwhlB6HD8AAGwcDWDVNx4B6FMEotg8bCiEBShfQSqPSSwLKF4coYiyg9AAPkTAAIlngHq_jwBWQH4QSSpIeNhRB5pQv_uhFUeklfsXKwMJZTFqw9HIAANgA4+AElwAMqAJjQAAAAAAAAAAAB8eZwNOQ0IADRirB4OVnwEdIUqQQELiDWZ6BqSoAALZNVVuAaiUAhMcRm9HD4EtOH9JHpFfMPGyyTRyITAlC+wlUcklBOULwijUQtsFhKHEuk0BPIwbAAeRACAoIBxHEweAegjZGTaOGwAW2Eq_KPiSifKF4AAAMQA3EezUPBPQqyjPzGD4AoYuV2GqhKRjFysANoEg8h3UAK6FysoSEzAIpEmCPB98+Aa2MHz+ikGyC4LI9JLkQuAAD+JwENmJ3D4AU5E5A1AYeAegeUGgB1hcFXPR8B4yoAAHoAJFYHQOgXqaAAyyy4MaDIB0AGQBQpMACpyYAD1x8ABY4eA5wUPBPQ3yjPxGD4AiIuV8KMqqEpCYXKwA2gSkB+dTD_1SAniNAAINADY6AEINAAISaHyUAAXJgABPHwAAIhYDw8AHxRAQ8EZT4D_xEAO5KpbWUJnwQ5KgC2lJ0LDiUC0nIAB_RifB4MqHwGCBoAUaULwqj0FNySoANowI8hj0qgCrSIfpJhcjh8A+nD8CLGQAqhcrOtRCUlsKlZVAtJT48hkHracFNCYihssx0zoRUApLQAE+FHTacDViBoByH_EYAFykwAdFUEwAAtFIAU4GidnR2pmzEG4GCSHAA0JGADiBUmAAJJMAAMQWAADcDANwMEkOAAk50RgANxUAAaCoAAYgsAAG4GAkJiwBHtDcDAARkC5EH_oIJIfCXhoSgPk6AAGILAABuBg9PQMAQkQAwpEASkeAAwlSEg41A9_0qALZUAAAAAeBgAIHQWgwA5j4AAAeAPfyHjiAQOgAAAAFoMAWgwBhSIAG5w_AFolC8eAPSk0i1_hcrAA9QbAAAtBgtoQHnfDcDABTfQYAAZQeAPA5ALlQAA1RYAANwMAEtKG4GAJAfAAADwB6QgJ4qAAGILAABuBgGGHREgwC_0IDlSsH9z47TJjB4A9ISOyEAAaosAAIkGLUtACQkC4MEPCIxZEAPQnqvVCvKQlJtH4ZMwFFysAAMIsAAAA7xEfkiAnof5PnpKweC5WEptrYjJnKUPQwABfFgAAJgwAEhoB7iI_JEAPQnqvVCvKQlJtH4ZMwFFysAAMIsAAAAGvhuCghoRAFwkJ+AZbKgLaMR7lC8AAL4sCFg4AANifDcFAAAgUK8DT4CqHPKhMg0G2v5cAABfFgKMFAAbg+hxVCAZcBPQCIxAzi5WMoUjKbRipIqVgABfFgQsHAACqHDJQggCXAfqPgDfpUBdtuiDKUgAEmHgACWAwBmFCJQI4S0Byx47Kq9FYvgECpWFWumlpJYzlIAAGSBOF9RIAyACAEqYMwo2aBHDwpcBFA4fn5loJSVUwmk7pYzMwVKwA2gCFg4AAMwo3qBHCWgIMPHYWQaaUKyqmE0y1JJQrDnqNUTaQzQI4IWDgAoSMxrx0BN4qUmRAFWQH4B2sqCU20YoIKlYADGBYP_oQBGhoADN8CHBEAIOPIYAnguVhHbbMRaFysNVEwH5BoAAKQ0QYIocEPCIexAnAHoBlFYQhcrAWm0YpaKlYAFpCSgIaJgAUHwihwQ8IgAegUUVg6FysA2jXMGcpAqoAIXrYUPQqaBDhoAAiEGCvgA5UCQUAiGAagMMPgAqI8ABVR4AAAABELAAIQgXp8IocAFQAAyy0L0oXghDLMZNlQOgLEYCUAACkNAXPgihwEGy4AegAhC5WVQUi7bRi3oqVhd5GA8MvAABSGgAVhQih2vkYJaA0Y8dglFoJSVUumkxZYzbmUKwopIWIC6A9CaAABVY19EjB10uAaccPz_isEpKiXTSjMsZz5KFYaQRgC6AAFIaAAQjP_IwS0Byx47KTLQSk21UumlpxkvVoVKwfWjAVkKCbPdg4Y0JLkyeEaGAt+wzFb1JMx47NJVCUmmolk0l8Ml5ECpWDjUIAugBxBkDQZ3cqY18HHiNBQQ6IppGQH_j4AcGVB+BKNo_sqCIlVAKmnQAAT0iBIGAwRMhA0ZgXQyKE8KCh5WFoIZSZQqKEoXhRRiSEwhU06AADAHgIlkkQAqEB+ASkJSbVZGS9nJQrAm1G2g2kaGQ6GAAABetCSFBDoiAJ_HwBIcqANpScqAWhtBjIksKmnQAAAhCEMHwkhQAVAwgCUX6VAhDKGValQDF2S8aTrSkFTToAD0DYOAYiWMwB6A3mIlI8xQtl20oMMl7xyhWBNqNtBuI0MKmnQADCEX7kYOolwEwjh+FUGYFSsqJdNMtTCUKwJv_VI2hTkaGFSzoAAAkjMYIwaZLgD+HD8t0rBKSol00gEMl7XipWBNLaOkRoYVNOgAUXJjKI0MBaFRLseO7T8hWAUnGmlVWrJrloHyRWVQm1Fh7RvKCEtDoALOzMa+doSUBHkQJAwQ"
noncomputable def WL35_2 : ℕ := zfNat64 18082 "MlAEkYACdADSoAcLAAAAAAAAAAAAAQlwAwqAAAAAAAAAAAAAAAAAAAAAAAABafABzoAAAAAAAAAAAADQ6AKAgDcDAAAAAAo+AAAAADAQ0gBAKAgDcDAEcJFYA_8uAnMlnWXAAgYGAAADAQWloAPMgCQ0AAAAAAAAAAAAADVgAakAMRgAKEAaPgA5MAAAAAAAAAAAABodAMBAKAgDcDAAAAAAo+AAAAACJBgFAQBuBgCOEisAf+XAf7OpLOsuABAwMAAAWloAAAAAAAAAAAABcdAAAAAAAAAAAAG4GADcDACVCgCwZUAFndRcACBgYAADcDBWAIRYAAAAAAAAAAAACEuAAAAAAAAAAAAATGgEQYDUhQAXwoAUmXAElf2XAACCCgAAAEKH1IUAMUKABuFACNS4AkrXS4AB3IkAAGcKAAQjABkIACXACxoAOLAAAAAAAAAAAAAQo8ykwAsgoCFAsAI1LgCStdLgAFSCQAAbgoAEKMAFoFAA3EgAChEAADCIAAMQkAAG4KA8AJowBdCABnwAAAAAQcAAAAGIaAAAMBAeEh4ASRgB6EAhIgAtA4AEgUAAVPgABAfAAAAAEAYAByEAGIhuEgBWBwAJAoANQXExD_pMQYuAAQgAAIgYMwACUKABuFQwBgDmFxtwmD_5Mj4uAAQyNAAATBgAJKwA9CAPEQAABuFAAlT4ABDHwAOT_xMAAAYCIMACowA5CAAAEAoADKICChmZMBg2AGMFwAAAiBgKAmHqRAAAAOhICTQsAAAeoaAABEDAAbQwaHkwjwABiA4ACEQncuKaEleWXAE1O3DwAAKQYDQBChADD4A8RBCLAAADAoAFOfAALQ+AByf+JgAApAxB2YAFRgByEAEETACaJgAGZUZQAEpUAAW4KAAAuDAALQv3HD4Kx4DHkwFfSoAdaXFNHJJbnlwBLQh4YTAABODFmAIUIAydBSHAAAB_caAU8bG0FEdAADiAgAATgwAGkIKQ4AA1sfAFZyo_AXKUNjSLcVlQACKg4AAE4MFtqACD4NhIAAAmJAAKT4P2GwBGOgBYxkAAAKQYAB6EFIcAAAWEgAgZcfrNlMGxJSvlwBQw2AAAFwMRoABRgECEAMPikREABCgGAgAABwkAfRPgAHoAAAAAYCAMDADSEFIcAzZSnhehOEoFUF8XLz7xcTSSh+Ll4ABYsZgAAFIGABChBSHAVCKgCeIksCyEmLlYGE+zkchcrAGMFwAABCBgtLy87ANCgBXBQANwoArWXAElZGWL1bCQRCmkUohszGiBQAAASRgCZ0ACILAAABAqOKGQAAB3TgYBcAABoGAAkjAEzoAEEWAACARcYxMgksQi4AppXUyAABcDAATOqXJgAiEQAAQCLlTMQEliAXAFNK6mQAAQwYAOaEAUOlzPgAclwAAE1KgiAFRKgD_6cTOMgAA3AwZmZmDcFAvCgEoC+BYAa4XAxAcUXAFNK6mQAAbgYACJkABGgARxYAAfQXKcLjihkAIFgxJUAU0mqZAAAVBgAFIQAI4sAZoqAK1lw5HoSVnZYvFIFNCKgR5iAABUGAAcZAAjiwBoCoArWXG0DIJKx8sX9yPgKaRRIGzMAACgMB4EKugCRkACOLAEkAuOVHFDIQJpsqAP9pxD4yAAAoDBaWgBIWKAOACOLAGgFgAs5UcUMgDElQBTSIRkAAAASRgB6EASDgASRYAEAsAQILgCS4kLgCm_8RvNmQAADMAIIQAkOKAOACOLAABAIuBiElw4XAFN_wjeRMgBSAFlYgQAkNAAjiwAA_wunWXHEjIJKx8sXgFNIoijZmAAAANQgAY0QwcAEcWAFIBgYuBiElz0XAFWmkxA347BKgeAAkNBXhwISCgBLEwBLouAP9k1DC4AppNUyAAAAJDQAALQVAFWy44kZE5krQSxeAU0ikeNmYLJMgGglCsACQ0AYeVAJqJgBS5UcUMgF1lQRAaimgxD_zp7AZEPAyASxoASIuATgVAFrS5Iy1tgyJzJVRli82gU0ijyNmYAANAELAQAkNAAAThUAQoLgYicFiS5GLgCm_8RvNmQAARpaADBaDx6IgK8aANgVAF0y4AkqVyxeFEKaRRDGzMKIAAACQgDItB48AEkWASQaMwB2RcvAJKJ8oXgGmm0WAZg3CiXUe1F94YTAAELI0PAAJFgA1FQBC4uBiElycXA5Cm_6RulmQUVtCwAAMaAIkIAVLFAJAEiGgEeFQBWguDiEluYXHhi4KaCASo4BxD9x8BQCQBIBoAAIAFwOQkuHC4AppF4CZDGFImspAKkuAEN0SACOLAKPKF4AIIuXn8DoJLx4uAqNNHhGTMZApFdBg40C4BdQkKKgAViwA8ioALOVBxAMWVAFNOWIwWQA3pMAHJCcgaAXENADwKgCtZcHEJKvwuXktCm0FU6BHnpZApqFyhWTo3NgAzKAIIRQBwARxYAAjpNSoGJbQXJUAU0h8ZAKGHgAAIIQ3CQARxYB1iE_ArUrSkGJbRiOwqVgFNJomQChh4ArbUAIIQDU6KAOACOLAAABMqBiGkAP6Dwe04XchAUEChEwAAjiwCsjh+AHALlZuwyLKLQsFSsAppqsyK0HBYQB+HAAbQnIGgAkiwA5AaImUzNFSsIpZRahwqVgU2m0EOJgznoWGglHBonS0XnZcbqQstpyGhMwAYfAISIHgYAAAsJAAKT4eMPABGOgAAAADwMAC1aCIGCgJAAAQDgAJ5MAASSYAD1BsAACIGALQYJIcC2DIBWxsAJ+LgCSqWLgAPTGwAALQYAtBgkhwA6QgAPvIwWIuB8w0SU3hcAB6g2AABaDAWe0IBmJAOQGiEQAjYuBguQSVIxdiQGAAL4sAABAGABkSAMDsfCViSAUQ6RcASVFBdiQGAAL4sAABAGAsAJDQ7ZMEUchVJLUCIB0IksaOXFhHpJc3lwAAYRYAAAAkNDYkwAVSSB_5GEglx1BiA_D0lt2XAABhFgAACwAstAEhoBkSACqD5FgA5pQvAJ6ssoXgABhF"
noncomputable def WL35s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL35_1) (dpk j 2 WL35_2)
noncomputable def WL35s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL35_0) (WL35s1_3 j)
noncomputable def WL35 (j : ℕ) : ℕ := (WL35s0_3 j)
noncomputable def WD35 : ℕ → ℕ := rdw WL35
noncomputable def ready35_cuts0 : List (ℕ × St × ℕ) := []

theorem ready35_cuts0_ok : CutsOk ready35_cuts0 := cutsOk_nil

noncomputable def ready35_0_state : St := ⟨26112, 285696, 51168, 230629, 29184, 45301, 29666, 44151, 53248, 162477, 52016, 161245, 28545, 137774, 26112, 285696, 77280, 386533, 106464, 431834, 136130, 475985, 189378, 553245, 241394, 605261, 324553, 633806, 350665, 659918, 80352, 275930, 110018, 320081, 163266, 397341, 215282, 449357, 298441, 477902, 324553, 633806, 58850, 89452, 112098, 221327, 164114, 273343, 247273, 301888, 273385, 582638, 82914, 192143, 134930, 244159, 201972, 272704, 228084, 553454, 105264, 214493, 157821, 243038, 183933, 523788, 80561, 189790, 106673, 470540, 54657, 418524, 0⟩

theorem ready35_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD35 ready35_cuts0 114 29789) ready35_0_state = 67586 := by decide +kernel
#print axioms ready35_0_cursor

theorem ready35_0_covered : Covered (toCl ready35_0_state) :=
  ready_cover_cursor WD35 ready35_cuts0 ready35_cuts0_ok 114 29789 67586 ready35_0_state ready35_0_cursor (by decide)
#print axioms ready35_0_covered

noncomputable def ready35_cuts1 : List (ℕ × St × ℕ) := (29789, ready35_0_state, 67586) :: ready35_cuts0

theorem ready35_cuts1_ok : CutsOk ready35_cuts1 := cutsOk_cons ready35_0_covered ready35_cuts0_ok
#print axioms ready35_cuts1_ok

noncomputable def ready35_1_state : St := ⟨26112, 285696, 51168, 285243, 29184, 45301, 29666, 44151, 53248, 230341, 52016, 286091, 28545, 166816, 26112, 285696, 77280, 441147, 106464, 470331, 136130, 499997, 189378, 553245, 241394, 605261, 269939, 633806, 296051, 659918, 80352, 314427, 110018, 344093, 163266, 397341, 215282, 449357, 243827, 477902, 269939, 633806, 58850, 89452, 112098, 289191, 164114, 398189, 192659, 426734, 218771, 582638, 82914, 260007, 134930, 369005, 163475, 397550, 189587, 553454, 105264, 339339, 133809, 367884, 159921, 523788, 80561, 314636, 106673, 470540, 54657, 418524, 0⟩

theorem ready35_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD35 ready35_cuts1 116 97) ready35_1_state = 81292 := by decide +kernel
#print axioms ready35_1_cursor

theorem ready35_1_covered : Covered (toCl ready35_1_state) :=
  ready_cover_cursor WD35 ready35_cuts1 ready35_cuts1_ok 116 97 81292 ready35_1_state ready35_1_cursor (by decide)
#print axioms ready35_1_covered

noncomputable def ready35_cuts2 : List (ℕ × St × ℕ) := (97, ready35_1_state, 81292) :: ready35_cuts1

theorem ready35_cuts2_ok : CutsOk ready35_cuts2 := cutsOk_cons ready35_1_covered ready35_cuts1_ok
#print axioms ready35_cuts2_ok

theorem ready35_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD35 ready35_cuts2 128 1) (ofCl (RC 0 2 0 0 1 1 0 0) 0) = 83630 := by decide +kernel
#print axioms ready35_parent_cursor

theorem rc35 : Covered (RC 0 2 0 0 1 1 0 0) :=
  rcOfC WD35 ready35_cuts2 ready35_cuts2_ok 83630 ready35_parent_cursor (by decide)
#print axioms rc35
noncomputable def WL36_0 : ℕ := zfNat64 33248 "DAwhK5HQpBfSMKQmctE2agXTKaIKlYACJihuAAoAYRgAmlgGAgMqgyoCVZUAMCOH4GW0lUSoABFxsAAP4eA0bl5cDPx2pr5kKu3wCBxEA7IeACaAEDiIAAAACvAP68NwMAZ0qL6MZKgOgXRElk1JppKhlQAAxAoAANwMBEgwXSBOApCz_46MiSKymz0OAeOysk00heyheCIAIKgAACJBgAJDTsRMHLSoLp8j6UgBkjh+Vkm2knWVAAAsDgAAKMKkIkCcughCkLNJDoCZIrKbPQlB47KyTTSHNKF4AB5hIFdBwAB0JAnApBdGSKw6WRyqkkVlNnoOSsk005yVk1lC8ABO4kBbkejoACYVgAwnHC8n0gTxn+SEKRiXRy6koVgZCwh47BrSTKDtKF4ABJBIAaAAuZ5DNgTI56QSLFSeilkcs1JFZxqpFJo5qNZJp_WTWJlKF4ACdRoHYhg8MgApuwAkxH5kQToKgqlWyoAqMfBVJoJaKgAAWBwjwOAAD48Arqxo5AnEJBLaSK_lmC8sjkX5IrPpNA6Rw3KzSTSUWjlC8AAlgkAoAYKgBmo8ZQmRn+EJ7JIrCyp46FJxLJJJp2TR2VayTbKLpKF4AA2hoCuAwACm7QUEAQj1DBxLSBODuCpWF2jR0KSmgs48dlZJtpJglQAAAACIOChA5K5AnNjIQpCzCI6FJTZ6DkrJNAKzaxqpQvADYyULQAINBwALiKhg4LpAnAUhZ9gdG9JFZTZ6QIPHZWSbaQIZQvAQJxP_jQFCCgAgwHKVUMHG4LGZQZSFFTxIjDUVKwCejf1Yim2qqVKF4AlLpFAKEFAAUIHMXIE4QWyFScLI5VOSKymz0mjkrJNsp21JdBcrCDWTKDyjZmAAMgaCUHDVQBASBQIgVUPALIHgCohUACqh4AD_xkAAFLQj4AIMpuZkBkCcIKHSRWFkcmVJFZTZ6BMPHZWSaaSqkMoXiEAAAAJIcAFqqBbyQpB0wAoMpFQVS5RUAD0KpploHNFQAAtBaACkBfDk_kCcIKrSRWFkcptJFZTZ6JBOHJWSbaRTZQvAGoGvIgwyEAAERoSVqQJwgqGKk4WRym0kVlNIpNHJWSqf1m1jpSheEtAKoSEAaA0AAaSCUBSFnuR0d0kVlNnoEg8dhZJNpEilC+2isALxSAZknAAB9pAnCC+skVhZHKbSRWU2evCThyFkk2kdaUL7aKwACOIH5_5KAEoDwNhCeImRhBcaSKwswiOhSTabPeCJw5PipVyySbKPMLlYTQBPiA_AAFENBSGTkCcIJEyRWFkcivJFYTZyK4PHYQRKaSqLEoX1gLiKLUCdSEgygeBqBBgYAwLj4BguUANhSFlqCEKQIoOQslUqrVnFBlC+iZUQUADBQ8AAAhDhVDiWkCcJSF00R8hYqVlNB7Bw_KyTbSTBKgAAAAgi8AJEWFUOE+QJwWobJFYTRyiEkVhJnoMk4chVJtpDzlC8AtBAAEItDoy5crguAAd4AeXAARoAiJAACCQABgoAA4VAAAgeAAAAAAEJcKQc5Q6ACiFa8lQAeY6JqANkmAAAAAzGQAIS4Ug4eB0CXE4BmpMAaeUialkwgAAAABmMgBUKUqbBmZKCqKQAFEnAAEBKAAGURAABaLgEfIQvhwQ6JvlqQUcaKwBFamApHJGQC0qgABedGDSAVKQgAJKwehFH6kTwsk0UCdPCaTSaOE0dhZKplKJsliuAUUi0IhDhcNk1S3EHEcACiNHBNBucPwXEnTxHqRZJpLlKeE0mk09Zo7LJZDKFuWK5+wGFIGFhYL01SyKARQZ3diEgoXGhA_CAQlwpBwhBgQ8AyIeAB6ADAh4AAAACYTBiNgpBw_yICDFQA_CoATAfH_1oAgxUAACoDYAAFK1wcISDYOi0bABMmAA6TAAQjoAAJkwAAFEUgAkAYEnJYEADFwD+SEISEp+BCCeSKws0uOhSU2ehWDx2Vkm2kNmULwOgAEH_wEADouAFjJJVBQQsKlYVS1pQpKSHJKByVUsmksKVAAFKIiPCQBA6gABIOF8OMmQJwgo5JFYWRyikkVlNnoOSsk20sSVk1lC89wBAFfiIAAADYJC+HD1IE4EcKlZTdIHQpCSCFDx2FUm2koOVAAD2JgCT9wqAAdosL4c8sGBxhUrCixxOFISXrJQOQq1myh7SheAAPYmAykn9BUAMi5zi03kgTgKQsocOgBkisJIixOTyaOyak0yiii5WAAmAuZhRoIGmkYGEAxMjCDJayWVWmjt_RUnCTPSaNE0dkmak0ylFgxcrABCTFMF9YkYo_5QJ4ADECOAJdqADlxupAnMo80oVhdQIdCkJIEbNHZNSaF6yqMgALSD_JOAPRIwAHy7JjBeIbKNBJFZFqoKckVlsEr_58TVzHTckzUmmUlIAISihcQSiAdORjFHY8H3YQpBwhBgQ8AyIeAB6ADAh4AAAABQdBiNzdOMlIEcrnDyIOvFRWSUgBHDx2HV5TEFICoAAI+8JgAAAEMQZmuCEHEfAWKk85qo5RwVJyu0kmr4Om4ca6ZSiVIuViBNphKolCIAMZKAkSAJ7XpohBCZIreS7VUCWSKysa8E1OB03spxrplDFFSsAKol_4KEwAAVhwBXK_IyJaRUnBCxUnrJpHvFSeogTZqXTjXTKKxKFf9moAOiUDwoTAABuHAIVok7FpzkQSYKgulBSoAqJdcw5AWEKgAGqFAAFAHBDUoM6AEhMGg4SZAnAUhZ64dHdJFZTZ6BWPHYVSLaQhZQvAAygAAAg4eBsKMORAeIqAfYVAAAkSGT2OpFaQAksVCSBQgoAAMD+lwDMqBsKAD_q8H5JgBSKwQ1y5ccQZZcAH+k4WgOICAACzlYOBxAjpuUFkRUrC6OWolCsmMVJ6UWWm0EqULwAkh+WRGVFyZLAxxUAAHZKwcDgiHTcoMpC6OT0FSsmMVqImD5+UWWm2qiDKF4ASQyEykKSJ4IQKiD5MpgAPKgFS4AIEwAGCYABibAABAmAACCCwAAAvboLVXC5BIGwpo6EBMj4AAAnoAAAamImgABkAQGBJx+DBv1UASGgFx4KBEwElCYAHoAUCJgAAAAAwcgThBV0VJwsjleZIrKbPSaOQok2yyxUjTFysLiYabsZGKvvCYAAAwAUNBKApeOlOMWrbxjoApIrKbPfBJw5KyTbKMSLlYXH_zFfAd5QvJIOQADwM2XC8CQ8mJcyRWFU7SVHFJSRloksmjkqpZNItcoXr4Sg602Wy0KpJQFelC8DoEwLgKskr4HA1HCSKwqkkZJIrCSBKDx2FUs2kXeULwLJJGIQdFv+IlOCgABxS5awOBqBkkVhKDyuSRSEkCUHjsKpZtIu8oXgWSSMQg+LAGMH41AX0oWwbmQnSE_ccTIwKCSKwsgbyRWU2ek1bh03KyTTKlpSlNJsrBnLeXQAEXKzTHNCABSCkRoSkoSkLsujokZIrKaA5KzTTSPrKF4_52NOcD4JRFQGkggECAgAiOHxIE4QYgkisLP_jpIZIrKbPSaOSsk2yi6C5WGm4jwYr4FBKF7lBY8ghgoASvWJEYQR4FScqo5YqSKymz0mjxNHZWSaZSimAuVhdNoDUixWm9qLI5AXAcPwANmf0hwaiBOBySRWVWzR0KSmz0mhHNHZWSaZRYBcrwJdNoBpCheFkcgFOOH5HgAayBADTPRMEpKqFQ+1EVAA5KyTYStRrEqMIbQKpFQPSSABBSJDEISIwPp5DkpVWKHTd9BUnKbPSafw6b1msk0ylEhRUrO62cy6bSkgpWEmSyyOQByDtSNi9OAA5oe8gTgKRyXW1HQpP8pwHVNHZWSbW1mGGFysLiArEoXyWcgHzDIAKZkAYGnWIm7kCcUkFX5IrHpZVUdCkps9Jo5HtZJo1GrOLoLlYG0q+3OgWgIQAFIEsMglBtIQpHNVcodCkps98snDkrJNMowwuVgVSqEUCr_TcQZPMQFymjmKmdQZ2dpQU7XAEhJr4iA_w8AhYeAKoGQAH+HgABiAAFOTh4CCkgESBOEFvpIrCyOVHkisps9ApHjsrJNNJVR+UL6rBwlLqZQCbFQBJFSsAHskDoM1ciDyZUF0lIBXI4flZJub2ov6VAOQHxkwTQAACXXADJIHQYSgAkaIpQrKrK46FIdQHJWSbaQ2JQvCIh8BKA8xUAWqcAZMWB0GHATBqcqC70Y+lJOQemfBNpNtFLlQRECyi9Elh5ioBRB8BAjpUEoMuwoXk9KSUKyqgIPHYuSRWU2ehWDx2Vkm2kNmULwAAHMRmIFEPIYFkr4IgYGgcAlAuwTAPRThyAAlAAAAAUIQBPS4IgZyIkApKiE0LlZLZKBKSCXSYgZaaH80YlNJ_ihBcJKANqXOYHJ7Eg9OVFVNXlQ5ZeA8kpIoPHKgMoASmkgTqSgDolyOwsEpKqMeKlYXQOJKSLZ5mKNlQGUAMsZSmk+1QgrQlAJhLh9FvliwOUrkisqtBBCSKws1UmnElJFsJrkpvRcrAukmWyUmkppNBmIApIng6Og8GAaq4Iga9xsGiioqpfwqAOUHQE0JmFQf0UgP_FRKQAAIXXBaDZlMgAohWUgHsjomoDjyYADYCEf1VgApCEAEmuFFgwVgwIDZuANUymVkKySKwBlpo7JqAYcqAy_oUgAm0mYhXQC0GGpGk+eOkTyqjqCpWDkakBJqSaiHNLGYYSiXZIfgQSq0mggllMngAcrgmBnzGwXdTgAP7IQbQclUKtFQAHfEYqtJAnUlAASYiLDR2BRKqHOVKYddaAAjhvByVSGMx_0qAogP0MG5VaSBoROC_B4agTQ8KpbfSkT1lJ08rJZsJtJyVTKUVZFSsMI9E6nQao2ZlVotNLKmFMngAGUgDZ8ATKgAAAAAAAAAAAIifAKRSJUsKIexSnhdKksRtJySZ8JRKQ_8vADUItaVCuB3VOCfB4BSdpKlhRD1KU8LpYTaTmi0UWIVKws1kA2xszGJFBKoUzWpwP9TJ5OgATSAGGw86uH4DwAGGA4KlIRA1g+AYcdAFhAAAAAAAILQAIq4DgpdiUE9lIDAikAG0HJBqIAAW+VikkUCAyUABhiJBUKYDpTJ5tKOWU6mhNKNVN4xYz7PaLRbVlwAlKnDSegGFMG5TaLTQPwnTwSaSBNASKU8mKcKxOnlJptVMJ21CvZg+dkWiy1+ClT7AhE5CKTEc00ik0F4JE8QQA4rCiBRHqpl8Gi0Uf_JRNBlKxrByRRoqQfhQrlVlYAGsdpJFKoEISJ4lCQJxTkksCmKE8e00KN7lYCrJ9Y10EckVK6kFGYgAO4ob0GklMRoYBNDsdBZ8CYOwIE6TKYakWiiAAMdOYUE5qkVeKgccpADUqtJA0InAaG3oV6tgmDppGweiUgolV3SkBWTCABVyZeAAGQqAADcnBXU4IAEPgF5UABDgAAAAAAAAAABBhIPJhYQRwgEJUgeTBpUmAxeTAA9ADSpMAAAABUSgxASelGycI11QpAwUCILzkisAdJIrAaajTEACBkisAP9HQpAABCHBLMzI7Sn5iY1tfXxsCOx9PSk4CHhpe"
noncomputable def WL36_1 : ℕ := zfNat64 33244 "KyvhOHIGUyjjSheC2ol0FkKlMAAC4MAA5CAu2QCOpUBdsqBl60DkihlNJhkqAygZ8agAANAwAl0MKD4ASRcrAWmSKlYVmyycOQSGUykbSheMRb_1SLoaCUK4AAIgYMykpJz+nu8MCTrwLAwFVyoBTg8qKSABFiuW0y66ajFZUAA4giAAAsDAEnXgBNsASAgiCgFBlQCPSopIAIXLZbTKEryoAAOwMAAAEsXgC+EAEtgCRkAUGVAI9KikgAhctltMoSvKgAA7AwAAoA4Ahq8AIMgBBcAquVAKcolRSQKpbTL_xqMWlRBAAHAMAAKAOANovKaE3SoBS1MoXlJrI1BWpltsNlJUFys8x8AAgQYAAUAcAe5eAHlzaG1NCbpUApr6VFJrJUS22GymQyqCgAocGAAFAHBTU1M2B7V4CJRBiDU0jJ6SheApRmULyk1kmq5UK5bbDZbyYYuVmBLLgSqPQAAYgxT05iTg3BVVDDZUW6djipUEbVoHJSTLaS7pUAAAABuCgAJIz_qsHIyo0I7HQSoC6DkpJllm1EoSoAAeg8BjBIAAAQjKqEpFyOnN8BUlYqVhzVaByXaSZTSVXKgAB6DwCaAIAMXIqqBHCpWJ4chS5YqVglVaBzaSaYTSNkLlYAA9h4BNAEAGZmEGFVUGqlCsAY6cxSAskVhWQclJLYxYzSKNKF4f6bgyAAlQCAAgwqqjW14N5IrDiKRlkisppZJo5KSXbLUUyFysqJxNKYl4coYQn4AFaxIpaNW0KqocNeRGUKw4ikE5IrKbWUKJw5KTYTSLpKF4AEExYAIowHg6DFiFVQ4a8iMoVhxFICyRWU2ssgThyUmwmkaiULwAEWDwAAKw4ABpchSdVQlIchw7vuKnBFSsCyDkJJlb60ayrpUBkAAABQCwBHWIAaXhoNUbl1FysMopS0XKz0KUWQchJsJpE7lC8DIAAACgFgPACTEADvgCVcOoAIKlYbRTCsoVgWQIx47CqZbSK9KF5MZdHQAAxAAKJAqoCbKFY_Z05ikRZIrAsg5CSK1cx2UXGULwIoERDJUhMAAALGaBViTsJks0hdzCVAKZSBZCdHjsDL_to3lByoGJJQCoDIBiAAAaZTqpXQekisqymcN4pFmSKwmln3icOQkmE0iui5WA9ByDG4zUGyNHYOQMQ8fBkdAjqOGgmxmeuVBlKBlQFk_6fAtMppF8lQAB7DIAAEwcAbBjDQKWlQZRTi0qEpUlYHNHkMelWw_+ajgZUAAewyAABMHBmHkpOcMJhiXaiJE8UnEyj8Om5JShXUSaWSaOaiSTCaQsqTwi5WAAHWIgBiBAgEAS6MmGIHZKFY8hozsnNHYpDVi0Dmokmu2UaeULwAEAEQxDiAAORAnGJZJISSRWbSXMGeagLJFdRDuqlsmjmokku2UorILlYUEHoRo0Z1ELJJKJeIqJkdAALMABUgCSMANLgARMASDgAAAAAAAAAABG4MeAZKYHwqqhi0qMAOzGCqUgE+kieEky_yaiz5UABJMIE8DgAAC18DyJgfCqqBMShWHEUykuInE0M0cPwkmUygsyheAAdAsCCwKEHAAPgRAqB8KrIZbIjhTkIUNFysCyDNNHZSbCaSm5UAXS6AIQEgAApBUD4VWQ0ORFBWzmITzFysKyHZNHZSTKaRdZQvKKF0ugApAU2jEyRsWIVVAUhBnTn7wqFIFm9ycOQk12yjIi5WANnTfVpqAggAHyGgAAd4AFLABop3lLj6sApKJtFIpAs+WThyEmu2UUoXKwfw6bzSBpDyH8tmADoEqD2mUySCcSRXRUktG8Ul5JFYVUmpDNHYJHpdMoAouVgbTKAxzh+35gz02egTkAd+ML6JH0erBdVIVKwFIpAQi0M0Om4DFXL5lJSB1KI1AQQACdEwZzoEeRw0E9MzPCoMpQUqAJ6C0y9yahuhUB1AjYfAAEIGgCnsaLhwALi5Wf6YhSCwuViULKME4ej0mmGyhFC5WB1KI1AQQAD5DQZh4ATRZdDBeMS6CBInlxJFZtMs1IqSK6iVUms3NHdRJJdMpRA0XK2ZqxRNtlAeyEbMeUxqHQWgyA2TIBxLDrGDcJJFyv9y8aRXK0pAByOSSYUBNRrEqAygWAOh6FkAkhCRAnMYZLyySTdkiu0mGanLJFdRKqTXdHTeokmsmUokQKlZhLtpLNFEwnD8ovIeqaNSajUKQU7ZAEg8eB7DQ8CtiIBCw8AWHMgAVIRAADUAAKkbHQAkjADy4AYJABg4AAAAAAAAAAARuDH0tGHgB2+BbxwMgxRCUidmDWKRekispJZdInDkJPa2DGaRiZQvAogAYTCATwiAEnHAyDbcUgYsVKw0ikhpIrDNy0TRyEmu2UPgXKwNJlAcR87DCYQAJQBoHA+DG0CkFSsEk5ClBRUrAsg5CqqBmxmkXCULwABTEwJf9MQADYC_EgfBi6HrSJ5TBguGUOkKKlYFWrycOQkmU0jsi5WAWQOwTEVPbIDMigC4DVFgbBu+EQSUNlCsMpJaKUKwLJNHIAY6fwAYsZpE4FysCiUQ1AZATRiEQOgF2rgGAtNnQNLJgGOkwByA6ABpZMAB_5CAugIECDjyGEpMptxv0qTQBADkvQlWENzlQFEDw5cEkwgPhRgMqQH4I9KFYbQwJQrAsyETpqEkumUPYVKzIBwUQEwli8JJhJIcWSgCyywvYGCIOnIApKFYMFNpSBNNaIIF0H+FwUkACSVSKLQazUAE6WCIOSYfAuEmArwVABRAymEAAI4JQGEBFyEARBzZDyGBfSRWGkAIXKwIsDC4CCZSyJhTKYFEBhZo7CSYSSHFkoAA28BJlgiDqvKwAaQT1gqAon_nYDKCPk4AA35sAAORCAJw5RR8_AXClPK6NTpkisKrJxNtpTSzWbWsRRCTMZqCkC6YSaGVaKJLAIg4SCkFrk4AyBLRWDiBlMozJOAAE83AAAuQgADLQAc+ADHQBIaAHiwAAAAAAAAAAAD+liuDFkieGEOz5TKYDnlx47opRSCPWHGwAh5GBAkCeAZQkk0mgopMlgKiVHQkrUwWomSwux0nylPCajmiz0ikH+h87wwbNlHkYEUAyLBjIo9ptJBA6RLABAxOAjepAGHmDWTesoRRCBg8QQqgZcagkk0BuqMB8eAY2IbhUtgTQw9MIgUqFMAXYjRyikGwh8SGGkpkCeAAJgzhFJoFBkoA2_EOoQuSgHrJwAmZSGIAS4WAAEgvAAAuQgSRCEfho+ACRSpgaYOpyNWMGw9HIaYHhiicB_pevh3TSETQAiHInQ3jBeBwiY+B1CqQgH_kaOPQihQb3FwAS2WL4SZ6RQAAG8QBoksYgBBDoIhUAoM9CCDxT6GAAVhetimBSUSQO8jQUeGEwGdmS8FoW8gPgFBGo5AUhA8M+hi0AEYqlcalEAjoCiE9A36RXGRgCbNT_yMGwT4SgAYYSdePgILCw5iPUUHOjiMfObBEAJyOQc7SMh1p87KAVAAXRi4xGoIEdEdnv4DYcphJEY1MOYMw7ARyDGclGRH4xHI5HJFBihP1MFA8Hv_z4mkWqyEajmeg9GONHwIRya4NgCNRqJSxq1sck9IpFmM5DocP6CRRtHT9GRQPB6AFlUryEaj0ggF0cRh1hQjJyiQwCupTwklk97FnCk0mihEms9qAjCqOn4hP8li8+WdEhCIhFIxAEdnsxIJCUqeOaLVSHsV8OhJpJpUSPDYLNZ6OULGQzPwyZjWYyGUssIkYnyBOMZrMRSk02dhGI0fgIZCqMU6WJRTVQOrV8KhBpLDkaOjcQJg2e0Wm32Mhkaj0lp1DHMpkIlHI5_4fDlHps7EdQI1Bu700gmmquRXsaqBoKmIE5CAMsVhUAMhlMeG72FQAgAGGh0IhUGMxAAQrACUYAChL6Da0qfQSs2UP+i0lloBIjIcmlV5DJJSyhkUEQymU__MgHonP_30GW2baVPFmpXjYqanNOrykkMdgMlisZlIn9m1y0FoZyVqSMZaUEsZjUJyGmmzu60Wqn3Sp45oNNJqxX5KSGgoZVrYlFiIA47PaiHd6_zUnJJqIBWDHURiKZbOT6oVJgIgJ13LuNaibMSNyWeylAKE3hJIaCMFWtwkAx0AaE_qN9iJHd+G1BqMlEstGNBCy6Fy3hwLdzKG9d67VV_iRuo0EAwGakhIpB1quNYjHaDUb7LQzHRrPdxJ1MM5EnnMtGNBppZlq3cxcR8NXcjLEUQDWaiATIrWuck1ptRHMZFs9C2lTxCwX+aktJ7UXnFyOezUg0ErpNXLeHAuW9BbtzstdDqRM7DWaadF+10GOy03KFHoo9islns9GC9f5rHZLLZiw5OpyGgzUc0Gilk_LlvAsJDykzR+lJtBkksxkcz2UljLm8lDhlh+mhYaKctioloJZbe_g6KPSaZa7gcCQai9ZarmE44E6gGABEK+zR+fabbUCRarYR8m0MUgplJc1B_MQDKZSRVwvX+ckEgkGmmF5ahbCEfQwBpUcm00omVzrR3AsTg+dhJfvZUWOqVcg1Gs4GYgpqtVlsZkowk6XTWkvX8ehBKabVeqIDkaHSSbVSw3ECQEHDwMNBQEABoWbkyOghUSk1227NrkoUYBKU+kxkKz0kiLU6WAFk0n2QimMiCBKQDAIWE7Y4jHIxnqJUqfNaCVtSr10ohJpJFKOBrJRIYjQy_oT8S_QViiTaLUhGjlUnxAnGs5nI9HMdDELCQkPDR9OoQJwYggNlZNQEEiOMgMSCGDsijEWkEckUHKE_CoQRSicVUWjUiz0AMCiMDwsBIETJYlJCpIaPlFMRsHkeg9LJNHI5HpR1wlBRQn4hCCAA9UthBopFCCjYQLgSCgqoksQgdis5FYagYID9NIoNR6RRa5YuZkF1xxDGpBB5HGQggCiYM45FJJAPoAg3JR5DKJQVYUI35KVMAKIE1FyRDPoEwUkC2gGRzIQLuSgNBQdlaCNDJpNW_ihsJVERRAlwdEUCCCzx5GADGh5UVQJICm0oKRJM6iSwknmYjMEpLoDltyZHKJBHo5_8bNKHkdNCCAXR6dZAVk0ggPBMlgXH4JSBOHVkKiF3vhUW02AHKBAHsrwAAyJuKJJwAV9GAcADcwApaAFnQAEqAUCwAiGAAAAAAAAAAAGGADFor9lAIRYIg4AAhgdABVAAAAAAAUNQahu_aCIO8mfARQB5JD8AOoSSmysYWJgAAVtm8JJdmwpBbxKD29Ae88ASFgiDv_IQV1UiwjEXDUgA6hFMsg1okIAB5AAAfGCLk+HkMFXKU8rpNFeoUwJoYSqlkfgzH0DSAQZ05hJLIEzEoACQ0IIVEz41CyVk8qFcCiGkIqLwH0IPNQB1CSWQIxJQII9AJylPHZLxNKGmU__owTQcC5jJIWQyn3iCRTDCBt5w300glkCvSUDs6CgAFaK+2wCEWCIOAAQdAAMNgAygBA46AAAAAKwkDCwcFkym7gZsZBCEsFwMISuR0KQX0jCkJnLRNmoF0ymiCpWAAiYobgAKAGEYAJpYBgIDKoMqAlWVADAjh+BltJVEqAARcbAAD+"
noncomputable def WL36_2 : ℕ := zfNat64 33247 "BQgGxkAyyVKSCaSCNouVh1JOAQNBlMRLEbAADuTgABQBwCC0MOloCUlE0kH9pUHUE4BA0GU5VEixGwdACeyUAAKAOCmpQbOpmwT+hBKDASZSGldiE_DEXKwMk0D54_loUGUxFCZkIGy1UFKMIEAAEoMU5eAEhp6UmH7IwBShWGEASA_lIz9WAclpJIYKLgACaFQAAAAViBuJk5QRJkiv_pcYR6LYuVlVLLkw5LSSQSWWLwAImFQAXQZIkDoAuVwvhUlA6IwpDCPSpFysD8xcRQ0_ERgqwXAASTyAEVAuFAABwgqJUL4VhUmCUhheIeQ9+lQVQiwfFpJoETKgAloVAALwRAABwgqJWRxFhUmB1JQrDCQQWFysKoRYPi0k0CJlQAS0KgAAxEgCflQbBUnCKIMoVhhPggP5SFUghRD52WkmkUgkXc4agCWhUACDgsAGnuAB2QYwqdewkwSkMJxjyHv0qABqnRptJNA0ZUWQCWhUAAGIkARHCBdGQAEqJQAJkwIhiAOkwAAAKsmGoBz0uCpNB4AADwMQVTMbSUnIjMHKFYYScID+UhV2khABj53QbSTSKTGLoKAS0KgAAxEgpqSkBAupcJIUmISAGBUrCyPtMnykccrAQS210GglQHUmktAAC8EQBbi4nISAGBUrw0VFkCydPlIUQLWeQwy10MXFwGUmpmJhaAAAxEgD1l32FXDxIHKVShWfuYLZNlIUQ64hPwy12mkZyxeBQykkSi3OQsABBoWABiZBFi8FTMJFUlIWQ+J08+xUrCiBdzyGGWugwEqAyk0FoTQWAAA8CKGQCIuNTghwSkLPZU7+5UAEGKmWug1cqAyk0tsXAAAMRIA4JekCsvEOCUk0s3DTv7lQAQSqZb7rwO9Kg6GUmgtAAAYiQU1NSA0o+CKFSUoJbyRWM6Yr49MkVKyqj2SjkNJFLohP6KD0oXllMKU1CmT0cjQkieAAJ0NSUW2hFZJFYYR7KQBKOQ0neQo4AZGIaULwymEAL5w7DKALUOG4NiSlBLmSKxQzFfHpYCpWVUko5DTRQzIT+ig1KF4ZSArmMok9HPvA6egAcDoElKCWUkVhDmK+PR7FSsqpJRyWmiiuQqKDUoXhlQOuYyiT0cuSEv+lwAZQqAEBAqGEAGrgCQ0gQbABNCsqyoA_sfAAgImAACQZAAAAB0oAYfADy4AkNAAAAAAAAAAAAARQolAmTk2g00yyA_MI9bCUKyqj2SjkSW0a6KMc8h0UVJ5DDTYRgKU+ez2cyUDKWSWkCAB40ghFqkmCZClTKJhv0fSkAGUeOw0k0HDHwNOYgAOgALQAqBbYEShiZORQZCdPKNdHp9ShWBJQmHIaSSBBDKYb_pwSkOkKBlCWk7AoIAXmmGShjkY+6hTDCAJAfykAHIaWtJQaCQgAJdHQSQCjw8AAWuAthR6SAmTlBpr5l4wj1GZQrAV0TDkNJJAghlMJRJ7KA6AC6WrJgBGET5AnKJBKknTy7XR68gqVlRnIlHNdMtBCKrBCfmmSpddrtNNaeQ560o6bg9IpFBYhszABeF_gvXxykCcokFtCdPLtdHppyhWVEEo5i4xWzLFRAlhFMQeQyaZa6USelZNHYFQOoA2AA64Q0iAgCcAOUmAIjHQADxNhCACEjIAAOhUI8pj3+DIyZInKDTQjTFfHovipWVGGp0JRyGUghFQ4eQwy12mk9JcdN9Ak1JJoaSUZEAAtGSUB4jN1TKYYR6AIuVgCUck00gISIYF0PIYZa6A_46boWkk0COZEBqWEgTkEgwSTp4pro9GaUK_tJVRnIlDphMJBBq8hAfhZrtNIozkKaoWo6VHHpJMpF3CRAASGgGCYEgJQTwPgAWgAAmNgAAeGQAAQ5nOyorChYDamj1FJAnBopIrK6PXklCsByzQmRjkmmEghFWSULwsgPQ7po3_DBUGkgLsIj4AM+IAFXvsliKxEYl5IrjphHr9CpWAAImHJaSKGgi4qmmsgLhOvsPwAA3JgBzMVUDwpipOEUUhhHq9C5WFEEo5DSyxIhhFJ6ULyqZa7TSeuqOm8H3oAAAdzE7STAggqVhhHtrSoCQjk78zAUrKiaAASDBvZS6AVsKgdABfiADYQAKuB5B4KFQdSBOAAipWcTCVBKgB8B0GkAvpUVQs_5RgAOoElAECVowEU2aYKg76VHU2miyoA_sXBx_4jAg0qJIAAjXMY5noAeMeAhyRWkImR1kgkSKk5xro9CWUKy6URzIRyU9o3mEgzkitVKF5VLNZB6IY+fzWkjUkmUqlFFw8fLMXwSnBHZ2ngQBWlCia4Ugp0RECoiIAfBEAFR6ACoiIAD_isAADYGKdBABmUGwNMcmD0ZUGEYR5DlIARAFoXT9GwAAxCYAAGwMWtiOn5+Tk4GAyr4bgYDwMA8CIAAPIAA8CIAAPAUAAG4GAOofDcDANxOgAAih9YWAbidAACDCgAA3AwagQ06AJDQBgMBbjoAAAP9hQAPOgAAkBQAAAo06AMBgbifAATn_ZMBCQXidAABGCi_AwAADzzoRQoD4MBQTyGE1beXBOZLNQhJIRUmDcAAzokAAEUKB0dLwBCVDcDAiYiGsVAFLKgBUB8ExAkRUAAAABuBgAQlQ3AwIKFiFlQDXSoA42fBMTaPPKgAAAANwMABAqG4GCL4seUqAGCULwnoKQ4fhMTaPPKgPoAAAG4GCWlACZkAZQkSQqAcCVAHZT4Jj_5uGYFQAAoBYAAFYMABIaANgSJIVAODKgDtJ8Ex_43DMioAAVgsAAAE9nwNgwRhFkdDB8IyeUuCMlmggGku0+MgMEFQAAAMQoARBsEDwJELlYCmUhWQnx47AykfaN4eMoXhepOAAAAXBQBWjQc7Kg4QVSkC6DkDK7pq1koSoAAYhkQ6GAAAbhJBBUHLSoP0FUpCshIDx2BltJOMqAANwZAABuEhBwaKIULwlICkyRUrCsz8ThySEmbBnNI8guVgQSSBpDRmUgKgAAs4oXhKQFJkipWFZn0nDkIDsGc0jyC5WH_jyGSQGNjj6TS8Ab8GgbsQDexCRFQGmLlYCkuBcrCsxkTgImjsLCaR+RcrDh5sAMTaACPRoVVIjjljOszlTpQrNoKVAlCuklZJo5oMhMIRWTXUV7FysII5ooFRLGZtAAYoobMEdnSWvAAaEBJqgaBgNgJDYLlYC1aJQrABDJjByExNp8wuAANiZHAAAXBQB2yYGAYDuCQlSYAAUkjAWzMiyAACkCgAAuCgEpnwQgwDMEsEjwBk4xcBkLJBAKpZAByUTMJRoDBuAAC4KALwVAEhoKYaAEJUAtUqC0yUD0DLaSQpUAOaiPQAAALwVAEhoKYaDxhcApacXKwJI_44fgZTaIDKF4A5qI9AAAA+ZXYw0_oqB1JYvAUvmLlYEkVUcPwNptBzlC8Cg1EcxUegBsQaB2dryMfACSMWAVABcsZhYIulIUEHIDk0lvSoDKrY+DlJsAACIKAAYhBcJAFnLGYC1aJQrCgkaThyfvWhyaR_ZQvAwjUDtGzcAAFwUAAIaH+LgOuWMwFq0ShWFBVwnDkByaRvhcrAyjUABHTcQgAAQQjAdMsZh_wupQVKwoIOQHJpLelQGV0RsGhTZUi0AAAAkSLsmLoR8MgKDlQBIQ4fgOTSW7KgMoFmjZPycACBAtRr_CMC9yxmAtWiUKwAcgOWWNGcUYXKwLoC9TBunhOCiAuUmBkdYOMqCHMMklljMBatEoVhQaLJw5AcmkVgXKwBgwXxqA1907AAZUWBcRagh1jJJJYzAWrRKFYUGiycOQHJpFYFysIJdGoC0YGusnYAGSGjMAAFSxmFgi6UhQQcgOTSW9KgMqwD4NCmzBB4AAAWiE_ktAREQaMwFspCaj6Dh+AZMIe0oXgpMsbjxuDuUiewQeAAA61KIx8D_SxmAtFIEUQyaOx2C0PTKOOLlYGE1RsE1AcgPwUgAiix1qS+kIF3ljMBaKQusjCGTR2f8Wh6ZRexcrAwjUPRmwAkAFcFIegqoyXgLRSH_kbPychk0dgPTKFgLlYVUAKBszHpvmoijEAeECcmxkAZmQeg8AyXmDjoWlDKFYEUmjkWlUeu4aM4g4uV_2diaZRqDDDpuwQeAAEkiYagmgyXgLRSSQik0cj0mj0yseUqaWC5WaSb6pflIGBMG4Lj4poA_FCuVJnYgC6uIyAlaVADDDh+ARLJVMqAygPwUmCDwAAGxoCHk4DZhW1DxBKgFXejIIzGQByhWBoUIHoTk2kSyoECRWRpwEUAJiAINwtgg6CCgEVolCsJqDkBzvJqK9lQV0DQZsAAG4mADCxDilQNmYr5dBybAqVgUSaU80dgUS6UTEFyuOlVFNBmKGDJnPQazWy0lThUnACSJ0+RTkosdDuYr4SkgpQrCkk1Zpo7oIUS7UxSlP+1ILMpA2RszLIQUGoZAExxAj5IXQn4vASSKgAeh_RWBzRUAA6QyAAWsdBtiNDGpORfrF+0g5CeSK_6pRTSaX80d0GQ02slEKhcrpITZCQRiMVeLmMPJVvozElJBw_A8ZwQuVHR2xs6UAQoRCamCIGABKVACkBdiUlQ2ZgAFskVgARRaAAC4KCOlgR0ppQBAhGUb4BgIBqg0AwgWACKADVBoAAAAAMBFeCODAHHKgHllQVRPieigCqY20d6VAAA5CgSxDAAC8E4iQYCOgGQAyqBPBQBUFXTS16YuAADwFAAA9BgChsw20+G4GGoUBHgkqHSoDKABl_ktOpHgAAsBQAAPQYBVp8NwNQRQrhFoSCKJaulR_xWKp2BKByFUugAAaAoAAHoMAAFmApZwvNCBmXQ3A3_y4ABLCUqAqnEkoLIVS6AAB4CgAAegwG4duAEzIKI6CFZUBWcqD_60HoPHYGW0kqyoAAGgUAAC4GAAkNBWHQcDKgFP2yoKyHaPHYGW0kryoAAGwUAAAABLhnCgEiFys_IxCmUhWQcgZTBtG8UeULwAD8BwAAZwoA1DMKlwgAV0EQMdQMjxJgMCFQASQAkOTAAF6GgAARAwAI14AkrA_sFbXKg6inwJUFZCBHjsDKaSj5UAAXoaAABEFAAPXgAqEAPLgCQ0D+gVAMqDqUPKgrIdQ8dgZTSSxKgAAAAAAovACi4AkNABO1yoOopHgXKwrIaI8dgZTSS_Kjya8AAAAADtCQkBK6i5WHUUl6LlYVkdYeOwMppBLlC8roAPguUgnAAAB0LnmLg_4FcRKg6in2ZUFZDQHjsDKaSX5UAAC0s2jAJcLgdnR0BHYQShUJA3hUD0NEVABRD_jMDmioAAghUAACMGAACvA2UIC5XABKIOwoDbJUAt_WVExrIhRIjgZTSPBKgAD6AABgGABKXAeFACZSEtVcVKwLoOw8dg1JozmkNCULwyPQJj1gmAAAwDE+ABV4BohABPtSoBaVAqVhWQcmIGgymkpiVBUQGwKQABGgoAAS8BXQxkQg_oFCSLlYC0vBUrCsr4ThyBlMo40oXgtqJdBZCpTAAAuDAAOQgLtkAjqVAXbKgZetA5IoZTSYZKgMoGfGoAADQMAJdDCg+A"
noncomputable def WL36_3 : ℕ := zfNat64 33246 "syAABEDEOPgBJiKVKFY4ROFoaSqZ4uVgXZOiSBlBehcAAOAaAAFAFADAVdQqCWhpz4rZTKgBLhEAATyoAAMQ0ciGgABGg5SJQrFiJwtDSVQnFysAdhkIQMoL2LgAFTEQABXyIApCSLQ0tpUK5TC5WBSQ6EJoRCNINCLsFCwABiGgAAYiQAERZGhIUi9UiWLQ0tjUK5Si5WA3w6EJQTSFnS4AACCAFqXgALJFYSRaGlwqhXKoXKwK3HQhCCaQaYXAABiGveGwAA6ubCtJFYC0NLBVCuHwuVgDUOhp5mC1hcAAN0kVnkAEpjQAFkisJItDS+RWpj6LlYE0cgEJEYQTSUeWHzvMJcAAGIeYIhAAAASGl1ioHoFy8NJVIQXKwASgyJqAY5UAAFomAAAdIdKF6FyRWYQZJQvPJpqIQC5WBBI2EJJ_yhGkHWFwAAYhoA9IXAABIalsqFLKGIMWWLziaUlqFeUgAlCBDMBmC4AAKY0AAA7g4KiJE6MkVgLQ0iCVqZoC5WAMQ6AC0NuRFxRAAQnHtykAT1IidHZspARkBgKxYVBLQ0+AVqVlQHWygFVkYAABwDQAAIgYh0G_HTO_AIh8AhLhuBgAFlLRIyYAYgEkOpeToAAAADcDBqAEmIBLQEMqWzsFysJ6BkCCQUHFzLi5ePMEC4ASkWAAESDAA4MVkKCWg_ZUtoMLlYHWQn5GQIJBE2Fy87QUGQAAnADA0AAJCYMBwZwoJaBqFS2dguVgdhCfkZAgkETUXLx5ggXAAAABuAoOokHHS4CraEqAA6D8jyGCDyoAAkgABJFgAQlzcBQG3S4CrMYuVgHKB4CCB1yoAAAAc4dAALZm4EgIusy4CraEqAA6D8jyGCDyoAAXpEAAEIWATRAuB9QrhpZIXLyclUchcrCejZBo2T0ekEYAXLwAGMkwAEGhoAHSEAPLgHrS4GpZc0XKwB1g8FkggdwupgLAAAABCFgbgKkETBLQe1IVsolQAIS0kOTgQeVAAE6TgAAhCxYn+HAwcyBCEIGAoB7LQkllWxcrBUaEFsHgykEeksKgAjgNAAABEGBQx5IydLBX5YvCS_lQrykLM91GVRkOI9IIucsXllBeREfAACDQUABqyIYTpYNcLl4STbK1OUhdNufAZBYeOziPSCLcLl4ACAgNgABBoKEliJkcmL2WL5yPW+K1OUlmVLYDEsQwfMJdJpJYOYNxaBVy0dCkJoAEHAoKcGgsIAjJeQQsoaLlYUZ6_kqDqMWTGEGeiiC5eF0GARCEAAIOBQGmdTYgSRCAQkQMBQSXb5cDUq09KgAAgjGBI8Bo2AAAAAIgwg0HDLGD4LRaT2okiLlZN1InhGShWGSmj2ei1G5YvAAikkAAroUAAZGWYHgtgXLye_AVpSANwHDZxJI9BV5UAA4hiAAAiDAAIVgjxg+C0Wk9qI2i5WVSaflKFYZCSaY4fz0WmbLF4LZqWWGv1JxhAAg4FFmUMcN0NjB+mi1WJQvLM9qMpMsoESeClyAobDpJHP6z4EiWLwWzUDsrEABBwKAKZjJKyh4FKFQCPyYA9cLAAg4mAAPYtAAARBgB0KxrbEeBauUsXk9Kodi5WgRyBehg+EkgkEHOULwWzUDsrEABBwKA8zAv2sAhIiNiYD1EwCJCYAFIAAQJgAAAACIMBeLWAQkRbi4iCupEBlYiAAAAGEQAAAABEGAAYjAFS4AYVAAAAAAAAAAABAWanD+Y__Ng1Fysik0osNKFdptI9o4bjGak0cjty4WiGWzULRG09AAg4FBsb6DcmcPyD5MylJRD8iSyiKbbiFSBbMSqSRyC0AZQvCagNUdID8ACDgUB8aAIjZqD7XA8E5i4JpVkqAP+HX+DIWgFgKgALoAABEGAOHDzu7gzE_BdVEDYUGwOBi5cF3lYA_4XDUAOzHwGECiKQAAJgwAP6I3A4AXBkvAspULlYStPgEBUnAgkES4XLymBwfQPoGMCgAAMAQlwJ4mBgKA26XAVXjlQAALY+hwAG0Eo5ACoAEBgEJD38hg9_ocEtBOipbQwXKwnrXkqWKQHLlkJ+LRiANYyEUAACoMAhIfBwOD_y8PQyXlAW4slCLlYB8koUgOQtCZADWMhFAAAqDAaABWYACpACC4IiVAA6YIRPAwFAAElix0AIQAAJHwAAF2CgAAAmXBnioGAoDaxkBZNaULwCIHQFpB_oZUILgog1DJxqUnAAAUBgC5FQAGeBgK6QnBrkuKaWUfFysAiB0BbiZCKHFwKQahk4gAAFAYADScBXKgG08DAUB5ALItCkKj_yEAH4C4CwFQAAAABQGA0nJR8jAwAkLfuGDw4jwS0CqpguVhPfhlQZAez0WiZKF4FWct5lKpBcohPwAAAGbMGMpgYCgONqy4CeKluUgTyLgySUBZZQvAA_8eQwAAPBQB7JwBELl4FVfRcrACEDxsCCC9SoDiAt8+LgBAAABcLgCQ0AloJQXLFdcRcrAA6BBBB5UG04lsXgEqfAAAfh2kxNBOBcvH8GjsqmaLlYGtyoMhFHv+z4IqULwtphCCz08hgABfFgLsWHakTwVMXLyalU1hcrAlIZCKPf_nj+oRcVMoXlktthCC65CfsINgAApAQodTBE8ZMlhGguXgVcglQBUoYPgQQWSVB_1uATefGGghhACfxZCCVLC6_0sXg1Koli5WDUQ4VKwyEUcj2UktKF5VMpprpPSxnD82l2o3EylH6Y0S46ACV4AkNAJaALFiuyAuVgBgBw2BBBeZUG04gLbPgAAABK8AloA8WK7IC5WAEcHjYEEMKFwbTiBaRCOQlAAABzXnmLgNulwFWt5UAAkHDYEEGRlQADVT4W_2AgBKxcDs6BUy4AkNA3UfBCMl4ZSzKQCOgQeboRXguA60Wlw9QQAAAKUXA8sfDKMl4YSyJ4uVgB9CA6BBoJaguAwkEO0EUgnAAAFfLpYLgPJlwYSz9cqAOUDwEEDqlQBDCQW6kQC0AgCWC4HZ0_Px3DASi8B_rgYCgJ+lxef_Kz9yoAEoHQEslQAF1EoABHAkABteADVwMBQEtLyfBUtsgLlYAIQOj0GTlQf_bgH4JQABOiIAbK8DnrgANEDAUAA4mP_vQBgmAP6EQAGCJgAGnHwAAAEpeAA14NBwEtLyWhUtvmLlYBR8xUIQOkcOH4C0MNtAXImSwigFU3qEAIDAi_aUE8i5eG0q_JKgDZAwfAggv0qD_LcAvU+AAc4TAPAJcc4KlAzYuXhxQeoV5SAAuHjYEEMoFwHEDHyEhwKDKBXQUkCgli8OKkVCvKQBSGSkjkBClC8PwxG2z60CQEJ+cQKCT_BODQJUDJfRcPZOlgc0sXhtKoJC5WBdoqDIST+HD8BaGG21kGNnkMCSAhMWABgNYufRPSgcwXLw2lUEhcrAAyGvDyGGgi4Lb3ZeAggKQAD5kAHmQAEuAIiwAEOAAAAAAAAAAAACxIQAI2ABVwoiQf6XvOlwaSrYUqAAJz_oiAMJwXEA+g9pGAAABsQkgY0sXjk2lULBcrKWIxKQyD0eitSYmp5DDDbayEkU6ZT_gdDkEYcgABKVhJJorUsXl02odUK8pMsPEYHuBA88kEegoM8hhhttZCSKdMpg9xGABaAuTkkRyyAlLF5lNtRJUVKzKApQYMFxzNRySUsyE_KqaSyEl0SdPAmzUJo61zGAEqLuUuAElR5jLwLbSbScqFeUgSyKozChsgzUcg4pCfhbayMATqiB1LIBK3aDYgjbCCIOKoVgLgGlFQA7h5OFQAs2dAABbKge0jAAYwMKAVxYtFInzkSgXLwym1UK8pABYVBkB6H_C4MNtrJQX4nkMtA8ExhoACIFoJLlHJ0sHdFy8MptVCvKQIClQZCCPQFs5MttrJEBCbieQ0KExhoE6AAdINsDCaHIvRJYOoLl4bXzqFeUgNuRhSAASC4DqYT+ZkGBjs1CahsAA8uAJDQAAAAAAAAAAAAEG8BargJc8EQcSQloeWVtYlQAGQAlYfAAfUXMYZQmgAJpqgA8sIQcHgmBgBMA1YmAAAGAGQAFBAABgjAHyQgKBsBvlgA8EGwcB8suC7_5WxSVAdACcgUBOD7jkAfQ4gEQlIArl8VMhhCDgxGQFhIgDQEQAKQA1EbAAAABRBUJtALT4BgID2iUARQAAAAACUfAAAWOgAAmQA4uAIjQAEWAAAAAAAAAAAAJocQQAQdOwymyUhSA9VhqAbSDLRO5w_A2gDjTKYbTD6JeAaitXCFxYkhOR8y1XU4TI5SVmgj0ui+GbGORqQSXIT8qplqpZprC1CmWWulkynpbOdVAGXxUScPzUoEcByVEQuiKlYAXQX6cNw8whA35qAKpZS6BZ9WAAJvASFcNJoEaPnYXRKLQqVgBdAQNGecg2E8hgaQCrgTKWUXLwRbVgCGKwAWaAQw_9DWGE4DiHzsLop+mVABtNutU5Dgx8AAAJUpmmymUD2CsTseBRtZdVGBMpsAjUmACqAASzYAATycAAC5KCcUieRSKBRKoxL4hPwCaNBUvl0nIm4+npTkoMoDoFCuWUuhbdNqwMgLE6DQaaM1s50GoiFxA8fMoQRqZtYv1EujUY0hP56PSaYfdKVVCiYJYrmEu1UZ20b2rK1cH09aJHBbbZzMpVEpaCA+ANRoKl80g1IaH09AygAGVKZlspd5MtFtUcsVwPC487QQ5ltCaHEvRgooAjjyGAWocgAPMfAATKVgNoCRVIPQAafAIS4AAAAAAAAAAAVYPFxsHYw4AMPgEJcAAAAAAAAAAAI0BhZObF52Xv6ebpaEPl8EBGZwCEuG4GAIUVAAH9moAP_KxpzoAAAADcDAABzhQx8AhLgGAgANHQFEAAaACvCYAAAAAMBAPDl96BdV4StXABaIbgYNEEQECYAAGpBABwxMAAEI8dgABuBgAAsQCBeENnwDAQCRkYBBCUAE0AERIwAARiIAAAwEA4Lm3gAJ8CRrgGAiSDiCIB6BEAAB_oyAQjAAJgPgAADAQBaWYBofAMBAUOKlkYAAAAAEIwAAQB4AAAwEBoAhXjiy0A0PgGAgCCBzhKAAAAEIwAAcCIAAAwEA8xeIkGyeKEwYgF2nBsAAAsEsZg7MggkUCaBcAAIkGD1DACQ0HYVJyitiKlYZZ6youVgAAWiKgyGQABNCoAAADelBDa4IgYexMnCUhh3+fVHKgqg9AJIJpKgACSAACIGAEGfBEDN4JgD0VFdD8FQE1AJIIvNgABwJQAAIgYNQH0hAfkwVZKgwz20ZUAAgaDKQDBsAAIhCVEJAAAD6QgPyYKslQYZ7aMqAAQNBlIBg2AAEQhKkEgAADnoQANIkuUhhDmeQ2EFysCao0+B+ASBoMpiKBjYAAmiEAAKAOAQ4hhonCZJgkykNKdzyGZQuVgTZ7_AyGKBoMpiNsTIACJiMAAO8OABvxAk0IACZDnkwaFKhiYZ7qUqAAQNBlIBg2CIAJuUgABQBwBfUIBsZAMslSkgmkgjaLlYdSTgEDQZTESxGwAA7k4AAUAcAgtDDpaAlJRNJB_aVB1BOAQNBlOVRIsRsHQA"
noncomputable def WL36_4 : ℕ := zfNat64 32675 "QoQAYmAGiQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAhLgAAAAAAAAAAAAISoBgIBEMAECYAChEABCCgAAgTAAAAABgIAEJcAwEAAYWAASJAAQgoAADCwAAAAAYCAAAAAAAAAAAAAA8uAJCwAAAAAAAAAAAAEKEAOYXB_smLEXAAAAGjYAQgMgiABgMAIUGABChAKaoABc2AAAD9LEAFzYAAsR0AAG4GAMQKBDBUAfQqAJbGwG0EMFQAAnB4AANwMF5KAonBoFDlwSU2pcAADB22uxAGYyAAIILAACJBgCcDgiiVAVHKgLJZgwbgbSyRRKgADzCQAAbgYLzEngQAmNAAAAAAAAAAAAAND4iQZSgoTBRpcElNyXAAAAXjIAAIZAnAAESDARINcYOCXRcElQkXAEkD_68HSRk4FwAA9RoAARIMACFOIkGBpfIOB+ZBJSyFwWEAOIlDuFwABBBYAARIMVoNwN6YSB1ZUAz0qA2m1T4CSA5SoAETCwAAG4GAiQb1AUEpAYhMLlYWkD8cPwJM9EwFy8PqqRJBuhEAAIkGCW3rwbgYAAATUXASEDgtRcAAAaBIAANwMACFeAMnw3AwATzoAJx0AAEEAHnQAAaBIAANwMACFCIkGAUOXBJTalwAB5dCAMxkABZUaAAESDAAkwhuBuLoQLnKgkilSoADoADrKgADzBQAAbgYAEJcRIMXsaJbDIuCSnMLgA4gsAASi4AAAAESDCGAIS4bgYADhUAIA6A_01AUAMIxAAAAAG4GABefAGi4iQYAFJcElFmXATWkgbQyLgMgAgAAAIkGK2HAA58ASMgDgoAHnQAAAEEAHnQAAZhoAAGwMACI+AJDQABCMAAAAACEYAAAAAAQoQBM+FIOAAedAAAAAA86AAEgXAAOgHgAJNQAo+AA1wAJpsAAAeiaiCAFzYAAShcAAFIOAAkZAAq4ABc2AAADTbZCAC5sAAEouAACkHAAEQgBhkDgkABc2AAADbbhCAK5sABtAAApBwAAq4AdAuCSo1LgA4QsGkBWBdeImAP_NWfcycAAGsOAAufAAq4AKQuCSi8LgD9CUfOaiCAqC7BBMAWWYScAAGsOIefAWtk1g0ABwqP9FwAGmHg6ACDioAB_xkAAFIOABGhCkPKpGgRuVA9D+lQABpAAwbAAEENgAApBwfgBBCFIeAA4VACAOgP8NQFDSBgGIAAIIbAABSDgADoQEmyAF4iA+dAAAE0NoAPOgAD9MQAAUg4AKiEAwPs2PgQIXAexJhYFwxA+YlAkNoDENgACKmwAAaw4M62HKalFAQALhBHj4EAY+gBJQJlQZQBAg_hOHsbAACuIgAAMAwCUV4nEtANT4FAYQh_xGA5slAAAACEYAATw0AAB4GA0BgSHALAMkqJiC_KgAwkHBVADRsAAOAaAABeFAHALAMkqJiDBKgAD6ysAGjYAAMQ0g4SAAAAKZBwCwMkLiY_7JmAFwAB+BWADRsKQADINAAArCgDgFgGSVExBglQAB9ZWADRsAAGIahQPAAAC+PiVBIsAySomIMEqAADKAGjbBzkAGgT42j0ANGNABDY8mPgCBFxR_yXSUp5dNwyAAKoBALgAFTIQABHB4DwBqxAhT85EiLAFUYvAJgJlQAAaT+isBc2AAE8PAAAiDizACa8ASPgaGgA8mxZAJx0AAFUALmwAA4BoAADwUAAFiAFnwUi_UiW4oqVlk0kVVRcrAAW2UqgFwyAAHANAAIQDh5fgBI+28qaERHzCB_KFZxKJojBvKQAAqgBo2AAHANAAAeCjBQR2pm7M_sR2pJzG_rwbgYTgUAaCoANxUAbCSgADQVAARUAANwMAHM+G4GBoFAUs6AAP9mQBJApZ0AAAABuBgAJGQBQMAGiIADQ8AEVVgAA0RAAAAALgYBxgoLUFwSXZhcAf9VLYEHHh8V2LsIBwA6IWAABEgwAahwdWLgkuzC4MYHxVS6EEISFwAEpDoAARIMDykTYRoGClQCgSoAchFVTKRQGClQAEpB4AANwMGdTUl4BFPhuBgLAwD_OgAAIgCEB_nQAAAAG4GLWHACSMAPLgCiS4JKbUuBARUAACJLgACViwAAPQYACR8ABOgB5cASGgAAAAAAAAAAAADy4AkLBcDAR8Lg_6pNlKgAABQDwGjYAAAAA9ABp8AGOgB5cASGgAAAAAAAAAAAAEz4AeZAEhYAAAAAAAAAAAAbBQAQuHgB5MAADKSi8qkA86AAIILAABSCgAQlRQBQBjy4hYPBSSoAGIfEQgOSVAAAAAbg4ABJUjQUOQ22XANB4q1tKgALBYzAggdcqAugAAAOwoEaChyAyi5eA2Hiro0qABaBBBk5UH7G4CHx8AAG4KCWlAs2UjQUOQsSXANh4smgLlYGEACyPYlGwAB5hYAANwUGpfegBVCRoKAV4XAHiLgF3JxBBr_xyBXhcAAZseAABcFABRQkaCgDoFxQf_kxei4BvqUAAxCwbAfyIgAAAXBQDiNBQZLOkLFy8JLp0uALa0RRiBxrP8UbpZcBRAiQRAACZCgAkoSNBUJBJJQvAdESMUjTKF4FkinMLG4aTiVaLHMuAggMSIgABMhQfgB1OAFoQAEuRoKABGbB_MmAUdAUQelFABGVAACqHgAA3BQDgDNCAQlyNBQCzSheEkcnPKF4FEhoLBJEoBINgAAAADQUAERCAQFwAEWA4GAA4VAVAUFQAAAG06AAAAANBQDgARGAIIQA0yAGlQAUmABBwAAAAAAAAAAAAOKEjQVBQ+J68AyXlJLKGSheDrV4AEoAATCWjyAADYKAD2VAnB4DgYixcAAGWIBRMH_1YAAPwfAPQP9IwAAbgoA70AVLyNBQBVfZQvAcmdKF4W6TgKhJEoLiLgw00DuhkAAJkKADQhI0FAFToFwf5JiyFwMQAD_aMrA2AAHAXAACZCgHAX6EjQUFZdIXKw0zF5JQvAw6NShqGUQgZ8yAYhkIkGQAAmQovyWnN6U_AAN8ASGgHQoAhFQASioAkklAAEIqAAqolAAAADy4AkNAFoFwSVqZcAEkHnOQJ0LgA_ufbGTgAAAMZcASGgAnyoApxcAf0Sg2u_cgE+VAASIFgAAAwMAJDSHikALSYAGpMADHTgABaTAAPYSgAAACQ0KISbLgkuLS4AklUWM2awAUlR6ClwAT03ylTAAABOFwBIaAHQLgksbS4MpYBKLIcQRslAAHnBYAAAODAAK0AMPgB5cASGgAAAAAAAAAAAADy4AkNAJ6Fy8Cq1koXgUTLy0AASi4AAAAA9jQDUfADy4AkNAC8nQAANQCSBeToAAAAAAHFwBIaAMzLF4SVu5YvCkkUogQaSSRGNYXLwUgAAAAAOLgCQ0C6Z028sXhJUNli8CSDrTKZbSCSRYhcvCiAAAAAH4uAJDQchFL6WLykyUWhSaKTJUpgQSgpE8isKLl4URyFF843AAAfgZfOgeU+AHlwBIaAIKRgDpJQAUQAQUjAAAAAA8OAARYCBYADhUACgqAFAJQAAcKv6oQABQQAAAEZANhQLOLg_2TKyLgAkgnhyApBdQQAqUlAABPGgABGQERFydi4JK1MuACSCenIEoF1BAOAn3+E4AAJ40AAIyAelwJKOouXktks5y4AJIKect5dKsjy6glUqkUYz0pClPAAg0PF+AAjIE2XAFoFwSVWhcfaZgJIcXoOQAuLqCAHkBYAAJ40AYHNgAJaAFpwA8uAJDQAAAAAAAAAAAAB5cACFhPGgD6Fy8CqnEoXgH+koHguQCfKgAAoIAB6CeNAWpKgGKWShebwTgI8OIwtIGpKgAE+EwAATxoAExcJ41NQlJOZivQuVhQl4GohLiHFo31HH50LouXlRnIAAAE8aKUAPFwxI0C2C5WDUYvDKF4AIVsDwuRq3goguPuqQAAABPGgAPFxSjB9w40CkBBcrBqMWZFysCiNQKDiOoltqM57CXHqVIAAAIODwZn4AhLhCGgAKkwBSjoAsgAAVJgAAAAIQ0ACEuBISAAIJAAIEgAAAAgkAAAAASEg1h5upCgDg10bNdLgeyXZpcASSqHEAxJTkS4AAkgACgDgBFHwAEqBYKANydA6BoBElADUAkgXk6AAAAALBQAAU4AYfAEDIAiXAAAAAAAAAAAAKAOgsnALQuXkxKuhyoA8orAQQRqVAAEkAAUAcXpeAH0IBCXAsFA8gqAqTAhAAAghJQHnQAAAABYKAAeXAAhorMaBzZUDUZeVAHNlYIv+i4EMlQAATQAAAHFyIo0f8KoFlC8GslLWULymgyZUphFFoRYLgABUicAAAIsumYuXeNA9cqBqNlKhTKcBVCKLQQ2VAkAAYgkATMXA7OmJ+hgAFOAAoQAs+AHlwBEaAAiQAAAAAAAAAAABCDhSAtAjStTd8XKwA_ipTNZNRFDCxcAA4hiAACEHB6AG74GpVAsFEGGgMYTAFwJgDFScABjCYAAygAAWCgKAOLcRAk0qAQeVAH4FYCKCTSoAAAAFAHAGAbC4AENAJRFwEWi4AGwsVwukUF9lQCkPokQTQAABjlwojiMYgWUsXhJWTli8LIX0ieFELpFpIUQuXgKZyOZCZsoVmmkiELlY9AAGgXBqB5SxeElPqWLws0kKIXSLSTBoTtC5eApnI5kK9CRGzdQrk9JICnHEYA8S60C4BqBcAyguAB8KlsQlGchJouBIAIQYgkegOaLgdGZ2DpQBCXFAHQUKoxjYJMldUXAfOSiyAASC4AAAAFAHAaAaj4BCXAsFAF5OgAAagEkC8nQAAAABYKACehAIS4FgqIA8BoOgAAALIlAB50AAAAAWCgAglwAIaKgQgrsXE9KNFxDY6AqghIIWELgAHITQAABKlwilVBmULzOZ9JREli8HJJCiCEg0EXoXLwFIDldypbVInAAADMLsjLiJIQZYLg_2TXmLiFh0BVBCQQsIXAkFIDkGIJAGRlwOzpiXocGB5T4BCXAsFAIKRgDpJQAUQAQUjAAAAAFgoB4cdsR2bswaktAEz4BCXDcDAf_NgGpJQAAAA86AAAAA3AwAmF4FTXDcDAT9LiolVNJUANSSACayoADrBkAAG4GAAkjAMhwUtLg_8rPHKgDeGwAATyoAAcA0AAG4GAAkNAMBwAgJgAA3hsAACYmAAA4JAAAAFl4EgYC5ZcGEsglKF4PTaJ0AAHcqAALhMRQAAOgwI0FPvMG4O1LF4aSqYguVgDUQhJNP9VL7p0iMsXgWSiUkUZo3AAA8DADtXgCQ0CIAgXFLwECoAJcLAAEAqAAC0ZAAAA_14IgoIgA8sZiBLLyi5eBRHLDhxGFpqM5TgXLwApO7zYAAEQUDsaAkDAECLjIjE3RWAOtlAKqIwAADLMgAARAxDj4ASYilShWOEThaGkqmeLlYF2TokgZQXoXAADgGgABQBQAwFXUKgloac+K2UyoAS4RAAE8q"
noncomputable def WL36s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL36_0) (dpk j 1 WL36_1)
noncomputable def WL36s3_5 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL36_3) (dpk j 4 WL36_4)
noncomputable def WL36s2_5 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL36_2) (WL36s3_5 j)
noncomputable def WL36s0_5 (j : ℕ) : ℕ := dsel j 2 (WL36s0_2 j) (WL36s2_5 j)
noncomputable def WL36 (j : ℕ) : ℕ := (WL36s0_5 j)
noncomputable def WD36 : ℕ → ℕ := rdw WL36
noncomputable def ready36_cuts0 : List (ℕ × St × ℕ) := []

theorem ready36_cuts0_ok : CutsOk ready36_cuts0 := cutsOk_nil

noncomputable def ready36_0_state : St := ⟨26112, 285696, 51168, 292766, 29184, 45301, 53248, 79646, 29666, 44151, 29184, 45301, 28545, 113098, 26112, 285696, 77280, 578462, 106464, 607646, 159712, 660894, 189378, 690560, 218562, 719744, 247107, 752512, 273219, 779489, 80352, 321950, 133600, 375198, 163266, 404864, 192450, 434048, 220995, 466816, 247107, 752512, 82432, 108830, 112098, 138496, 141282, 183797, 169827, 254380, 195939, 540076, 82914, 109312, 112098, 154613, 140643, 225196, 166755, 510892, 58850, 89452, 87395, 171948, 113507, 457644, 57729, 142282, 83841, 427978, 54657, 398794, 0⟩

theorem ready36_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD36 ready36_cuts0 113 121) ready36_0_state = 71003 := by decide +kernel
#print axioms ready36_0_cursor

theorem ready36_0_covered : Covered (toCl ready36_0_state) :=
  ready_cover_cursor WD36 ready36_cuts0 ready36_cuts0_ok 113 121 71003 ready36_0_state ready36_0_cursor (by decide)
#print axioms ready36_0_covered

noncomputable def ready36_cuts1 : List (ℕ × St × ℕ) := (121, ready36_0_state, 71003) :: ready36_cuts0

theorem ready36_cuts1_ok : CutsOk ready36_cuts1 := cutsOk_cons ready36_0_covered ready36_cuts0_ok
#print axioms ready36_cuts1_ok

noncomputable def ready36_1_state : St := ⟨26112, 285696, 51168, 148720, 29184, 45301, 53248, 148446, 29666, 44151, 29184, 45301, 28545, 128208, 26112, 285696, 77280, 434416, 106464, 479717, 175604, 565453, 219755, 595119, 265056, 624303, 293601, 652848, 319713, 779489, 80352, 194021, 149492, 279757, 193643, 309423, 238944, 338607, 267489, 367152, 293601, 652848, 98324, 177630, 142475, 207296, 187776, 236480, 216321, 315984, 242433, 601680, 97174, 178112, 142475, 207296, 171020, 286800, 197132, 572496, 58850, 89452, 87395, 217660, 113507, 503356, 57729, 173509, 83841, 459205, 54657, 413904, 0⟩

theorem ready36_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD36 ready36_cuts1 113 84447) ready36_1_state = 133674 := by decide +kernel
#print axioms ready36_1_cursor

theorem ready36_1_covered : Covered (toCl ready36_1_state) :=
  ready_cover_cursor WD36 ready36_cuts1 ready36_cuts1_ok 113 84447 133674 ready36_1_state ready36_1_cursor (by decide)
#print axioms ready36_1_covered

noncomputable def ready36_cuts2 : List (ℕ × St × ℕ) := (84447, ready36_1_state, 133674) :: ready36_cuts1

theorem ready36_cuts2_ok : CutsOk ready36_cuts2 := cutsOk_cons ready36_1_covered ready36_cuts1_ok
#print axioms ready36_cuts2_ok

noncomputable def ready36_2_state : St := ⟨26112, 285696, 51168, 292766, 29184, 45301, 53248, 238399, 29666, 44151, 29184, 45301, 28545, 155136, 26112, 285696, 77280, 578462, 106464, 607646, 159712, 660894, 189378, 690560, 218562, 719744, 247107, 752512, 273219, 779489, 80352, 321950, 133600, 375198, 163266, 404864, 192450, 434048, 220995, 466816, 247107, 752512, 82432, 267583, 112098, 297249, 141282, 326433, 169827, 415648, 195939, 701344, 82914, 268065, 112098, 297249, 140643, 386464, 166755, 672160, 58850, 89452, 87395, 244588, 113507, 530284, 57729, 200437, 83841, 486133, 54657, 440832, 0⟩

theorem ready36_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD36 ready36_cuts2 117 89) ready36_2_state = 160296 := by decide +kernel
#print axioms ready36_2_cursor

theorem ready36_2_covered : Covered (toCl ready36_2_state) :=
  ready_cover_cursor WD36 ready36_cuts2 ready36_cuts2_ok 117 89 160296 ready36_2_state ready36_2_cursor (by decide)
#print axioms ready36_2_covered

noncomputable def ready36_cuts3 : List (ℕ × St × ℕ) := (89, ready36_2_state, 160296) :: ready36_cuts2

theorem ready36_cuts3_ok : CutsOk ready36_cuts3 := cutsOk_cons ready36_2_covered ready36_cuts2_ok
#print axioms ready36_cuts3_ok

theorem ready36_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD36 ready36_cuts3 128 1) (ofCl (RC 0 2 0 1 0 0 0 0) 0) = 163756 := by decide +kernel
#print axioms ready36_parent_cursor

theorem rc36 : Covered (RC 0 2 0 1 0 0 0 0) :=
  rcOfC WD36 ready36_cuts3 ready36_cuts3_ok 163756 ready36_parent_cursor (by decide)
#print axioms rc36
noncomputable def WL37_0 : ℕ := zfNat64 33248 "CYMABXeAL4QNouG4eAqAhAOQSgCh_xCBSQQUyVB_pOIIAAAbgoA+xfla8NoeCag5GklPXKF4MQmvwEaijEwiUSheTQsm0k5ASgAACAMANIyAsU7qDQBmjIlpH0qALMmwQT_q8NvKjaFkwgAAAQBgALowZcuyZGMcPHkhaaktCGlC8FoQ6Om4IRiXQApQvCoWTDPSKAAQcCgpDycAINxQq+AIlwBAiAIOA6oZAPuHgAYgA7oeAAAAAIAxXn9GPgiO+A4OBoHBAA2AOMPAA9AA2Q8AAAAAGAgAAlwSQelwkVoqDgDIbMwDmFyu0gHBMGZ1JtZLp+QuLjXY6H2UgAEaCgDBpa8HWxgMJdhRozABeRAAqKj_o0A9wI5A4QVAkAAAACYMAckuq84d9qHgnpaRchcrKP6hoGqlCs8jmq1kc6ULwSVkKlpmKjAACgCi_n7MXMSkpwQAkjAJ64OXRAAXjwaQD5MAf8NgAaSTAAfbOgAADAQB+l4AkjB2K4AHRABCEQaQv5UAGwNmZJTLi8Sk_3BAE5AADWDAHzXg4FcBaUDIg0nGy4CoTFZRNJaSXahJUpMCbQkgpTkAARIMAjNeDc1wAGiLEcRgUXIg0mQy4CpUVGmM5ktJLpJLkVKzA22yhRnIAAiQYM7OzAHNcbWNB+g+LSVbKgDB5o7JKV0iiVB_9uAoGhAAAQBgBZVyE40H9D4_+1FYSoA4WbFghgrpFcqAAz0hAAAF0jQT0KK0byEhcrADKHTdCAVJSwkbyoDiBDVCAAJ0TAALrgAckVqNB_k+DaWzKgC95o7QkFSUMJEcqA4gP1QgkzEAAAkjHKjQCpOH4aSxpUAD6Om5_EmK6ShKgANFoQaTSBioeBuZAQ8AdVwBIPJAebaNB+4+LSUxKgCu5o7JKV0g+VBbQI5oQAACkC1oQHKuAIVPgykUyoA9kdAEUSKVBaf_MQX0wQcAACS40AoD52WkNIXKwug80wbllstdG5lC8+w7W0BtKEg4OAADEAsCyit0aCen+2jePdKF4AHI6bklLCHJKF5uB+OIEq0LwCUcQAABajF0jQT0eo3ax7pQvACLHTc4yUsIWMoXy3+z8cQOmoxyw6AAKQAehAEhoAAAAAAAAAAAAinD9dw8bBSJw7DSE8LlZWRTaMAdEl22umUuiWi5XQTLZZyBViAUHsYZAAADhwBILnLRB42CXj52WkTMXK7VsmsBHZg3OMtK6NTKF_5FI620APqBHDp1AAHQeM7MD+IQUhQEFTJ5DDKVVFFysDITZqARf+Dx+kxcIE0mGeCcWzfQYh9k1gBVAADvC4MIAHXAARoAGLAAQoAaBAMBAf+WgErDwA_YiABHQ8AACwyAAAC4VwvImCYKnogVlLlsMpkkieLQsixE6alhqpR3SnC0MJJD+hENQQCcAFEOFNuVIQD0NIQouVgDXzRmWEFqsXTaJUB_5SDUSEG0qgAcKbExQIYAEPHYaSUhZIooxxTRmWGql0HYXKw2haUrZRADSJDLKYxeAPoAgOiRLzoD6HQCxioAIpYQo9mRgAAJx8HATgAAHRJaR8A9AFJqdaBKFhLJFFPYlIAAJ6MHATgAAADhAAq4HRJRZ0Eck4MIAQsRjKWELIr5OAACwfBwE4AACW1wOiTpzoBeJ08CJykAPtaM4AOITgAKaGkkgAprfEJ+atUhybxarmGmmEVqZNpNJLpZGDOVSyUS6XT3K1Msm0oz0F5HkMusRZMZdoIEEB4Jp6gANMX4ZAZQAopQAJZiAAJaUAAG06AACIRAPxQB9LA6JaWQgUEgOwwjr1CuesVgMpYaqXRnStXAKIEU_Y9AAAMCEg4LH0YM+pgCQsEwUBIyALh0BQsmANzlwAVbJgABiAABHG2IH5QhPCgMkR_5C2ohBdBhlC8AaUdNwCKHRaFk0l0GdunsqI1qJFG0kisAAO8JowgGAgC6AfweAOoGQAHkHgAAoGQAAAKsOH0KBygQwJoZapJy5i5WFkM5GRYaqWR0xcrDb+5SAggjBBEJ9AAD9XFAFN5OgrYdATqKgD_iMWEKIAAW0PiogCYDIBC4MMYU40+ByJw_AwqVAH3lKmV0AzysBhFoAPZqVfJoRHU+BuRoggORu7Jrw2nSkpJH1GGINNgt1Uui4lKmG0ogGLkYD0qI1KKllo2ogNmYCyVNmQn4AUZKKckVhVKgo0xLCA9Ut1kJwpUwsj0AHiI_KiNSiF0TIGPHiPnD8GIBCjJR3kisc1koq0DZnOQdLWMCS1XrJJqIWZabksZ0UHpURqUQ2p2NmYZgMueCcOKidA7xyANeTADJjIAGDpQABhKjUQACNuEABuhiMcEQdVoyCsgaWLgAAEJz4+AA+AXAAbAPgAmVwTh0IzoDSFEADOCUf2WiakUFIACGx0VEAMOhAMUriCBEAKjgCcME4dOQTUtMwMIpQAAABVKAAAmkkA3yMAAPSEU1wkseAAywTh1LT4DCA482ANWNwAAVSgAAAACC0ABJGOpQIYNiZNYYR8ytTAG5GS8LIOQS6pXAFoUEqNRKIUJupIABMYHIZF7HwKEaO4DoVIAKEYO6qYQIOqQAADajUQHzoQFqFAwkGezhSJ6LCZH_VOHI592LS0ylkwjnPZ9UaXLxVBaQQgjkgtmRIZRDCstIlgPc_dwMIURghMjADgJC2sm0moUxWpmEAKCElDqhHKJIhu3mlAAGSmiZL7Q3T+AEmTGFEYITIwAW43ZjCA3hWpgT0AekmolECEoEsTVkbFnCcg1AAmyWM8eK1NBaSEAAq_8QI5FJohEUPYCQAHa8QiaAqkBNA1CfABURSBE1UPAAXaVgWjEBLEMARk6NIyXglZtYTUxolHCVYAKNJDIGDyoAJIcBNGopFodBlIYTAx421A58+hgHhPoYBASaRQcgABSc2IxBnPXDoFsCQ8TF7bVn_ofUlkR8_npJntBII5lshgNJopFzyHQZC61CjlYSJ5NoNFHJJpI9nKijpvNZaPQYhhMBSXDpnbQnpHBKCzJUMAOJNIIZ8olgAAVSKPSC0Y6D2AkACo1qzlBX+aPxSSSDQZqTVtIkss30kkkik0AjNjH+fQyKTQklUinbSI45IJJHuFEqcrUEh4g+rTCYgJp4BWNKJQAfQAkShAADTSJ5BGI5FIAARxKo1jGMtqz_7UiaMJGfk0k0FHiVDKtRJJZwNNJtJJplFAlQyCORSRaabZGJopCIBEItFJCCJGDos2NYqNPAqAZ7JZDQQnSE_npZvpdKpZrJdmbGDM+hmGw8RYrDWRTETadbyfbSQQMER8AAV8B8k0mZIsjC0hNrJ0AIGHQF6mnWimEDspVibMxaZQAAl003USgtjIoIBDbdaLSTip1NIkMDC6YabeR6SY8p1OQjF+503TokQ6iSUqpUvlshLJxuo9nstHwRHwfFGhwGs3G60mm1FwYCHJtdMNNvM5Jqr1KfIVKljNRZs7INdrIhlMtkJdc86b7qPZ7LVuER8AKlUq3ULSGk+LUzACBgUU6106klJqAAASHLm8w3EAgACzNq5RoY5XaWWkyz0ajVOmaFKbUaDgRyNZiISKj2iz2GwmfAFFSyYbil44lkGWzkI5RoZD3aXUbSety1z2czlTICHptVKtNvM9Io+UKPMa6sk2dkWm02wRcvnMtkJduNxKNNHKdD52FYq3UJaGEsrhKAYG0mLBeyCQSQgekJ2BJQFLDlzmaTCRQYjhQn4FgIaGgbAvtKkYXkppVhJTbHrRRvsxmLQkJ_IRjOQgihiJOERNtputBJyAsuVgezKzY77_9qvN5qJZqKnIYHTbCAJix028zmo1GQmhLGa2TZ2Ra7WRDIZDEa6hBw_3Uez2WtEIj4GrCttSn0_WrSrN47lk4n3A102nk+kYdvc5KJdJIxipBqthmoZ5UBREs226kkaxk2REfCgUaGOtSn1EhbVvvNRtt5vtNtJ5vKd3rnSTLcbbXVEtW8g1WugHMGcllMRLNtEM7dyLNRiv4iPjAuBUq4L5dvZYbrfSsl5Ha5e6jUbLbTDbQgkxAIQsTNtpKg9d6SUmUgeEEuaz6NVcDqHUwIB1wJdNL_n44ltAkChAFTSaTqRQYiJGEYEgoSA8MYAzJJJZ1KOFpC7EBioIFdlo6hpBrbUaAOZNwBaAlDadSiDk7RUjDMDN2zaEdWpgdSyWQIqBLC7YaSXTibTaaTSE0ohmkyhFpoJVcPR1PJEFymC1ORUjCsAAywBqSbTSB1DaW5TgCyGUwgbY7qQAEBCSWHU8l0GXkCsBwtaUhqU8oM9ptBIL_0KOE2klnAlGkqYSpZRRIza3qoUeqLVaQunGy4E4nW8xIYL4RZCAbQTBvvp_RKnkX_ykSSDBFAlhVCyfTEJl8mkUmmWghtCiC0kSegUCdS7kZeIohA0ZAQ8FBy0HCRJOINqaJ4HxiYAHYYLyyTQUi3SBOAAxZUzhFII5DNIkBokw_dgASYwT1xEwAMRoMVbFYFJCgmVgAMIVM5FKoOQzKJAW+UlH0KhNGcKIJQAYmEqk1S4hG6dgAKAMlcJMBkKmOQMyIFwFT4OnkOQHU3YpF9iYAYYYOzCVQSiTVIACqAABdDgDHU+gaQoiJyBOauQgmEWMwqkkchZVSuAMQjo0dwckUcgvMQLgeLoWH7uC3GDOVSiTUukCcIJoIWFoFmK+VSSOQDSlTKphBSBbHTWahWLpJJoZcCAIGADi4AmTAExoAAAAAAAAAAAQYeFkXAQSgGA1AL3IgDkB0B_5KGsqQAAsEIAAG6EBoabgXBFQIYGkqgSYrdxOISQKhVN7cVaKOQlCtTLpdMqGwEEqJAEKmTQw0kCakBrVwBIaQUPgsA1ANTUgD_h0ADBFIADUCEBUAMKjEfZgMKaXYRHwFKaO4DXVIABIYOwAeepAAa2QgygDf0IAyqvjBcdNCA6hhPQKwRQNccMwq+pVo5JP_KVMLoKQIIlqKgVCGTaKYUPpEsDwGLrJBnQb+YgGOpQAMf9GQAg9KAAgkhEEAEHoQGQpT0LCxWCyE0qpmVqZhGo5CotLJVBzNRyK1Mog5AyIPLk4BCFDKI9II1CilYSHhGilPfw9d66aX9LGOsmGqgoVqdlJIByxeFRbVSrGZCfjmah4UqZZLoMSCTaCKpark0gjka1FTIYTA0fBSnj0IphrNZAOqWySK1Mf7JrIElwVFpZKtFHNUzZeyhXLJlACC05Yrl0JoYEAQ+7nZ+hCj+UE4c2FAhgaQwlJAQNdCqBykqOtdWAAgAULyoqrWL4GXY6UGoSABFYAshACCYACLAEhIAAAAAAAAAAABcOAAmYACrAF0IAVbACiYAIRABxYAYJAAAAAAAAAAACrAAKUAhJiCc8ASEgiDgRFwAwWgAAAAXwdAAIEAAJ+BC7OTBRcAA4Q_emA4GBQZAJ46Ax2TABzjZWAFWyYACKMQAARCwRxtiNgyySA4GA6JBdMuAUgPAEWiIAE6DwAAxAAVIHEzNjsvZhG7CAYCf2JBLQHCDwB8EqABsA8AAFAaAAAMBBif04aWjsbHktLAk8GShdiXhoCHk5a"
noncomputable def WL37_1 : ℕ := zfNat64 33244 "NDQBiB4AgUbAAYIeAAIoAABgIowA6tAiBwAHk6JUAVtNgP8rw1MqNwBBRAV4bAAAhBgBkkwI4cBk2DOFdDqULwpNJGolCCgpark0JJQvBIxIIEZB8FAACEGAOMfAiBwAGEWgBjjoAkgZSo3AEEUwh8xeAAA8DAAOLgCQMAyQlAQvKgASB03Aw10keVG4Aj_jEAuQ2AAAAHCwDJSUBP0qADLmDcDDXS2JUbgCDCVQ0YbAAAACi4ASQq8xObKF4AOcwbgYa6MfKF5uAIYmEqheI2C+yMAECBUGwEkCcBcrAGLmDcDDXTEpUbYCJOMVdFYBqBxAyIdAAuLgBJIyNvKF4AmEwbgXa6P7KF5uAI2jxVMYDlSmA1A4kqOgzsdF+ADhYBkhKAheVAERjh+BhrpO8qNwBH_GICDRsAB0AAFFwW4GAEkKzMTTC5WARSNHYlC7XRI5YvIwBDEwmEKypbACUh082aTgBAAykAJID3i5WG0EzGzMQjXFzHXQmRcrIwBARVTGUQHIVUg0k2yBIgVMNgEkiSwGzFysAmohVO_ouY66HULlZtgICqB0jx2GWqkELkkRcgvPeAJGTAR0BFASsPAATC4AAKDwAAJC4AAAwEAU4uNWLgkkmSyMmFqJQvAwg1EIYa6JrKF5GAJAk0wlUoo4QH4EUBRxDoptgWRAbfyYvMyZeRhQm+AImQA8uAAjQDnhkA+AeABiADuB4AAAAAMBFeegANqAIGQA4uEAUwADQ0AZYeAIFGwAGCHgACKAAAYCKMAOrQIgcAB5VeVAB5DpuBXSKpVyw2CiPQoobAABSBgAEm4RNVCzx4AYGCsgNyJgD1BsABHjoCCBhBIAAUgoAvhMCOHAHNgzgQWLgJItc0dgPSr_1O+AXcqNhiQQHohAACkFA+AB0ILQZcmSwMK3SheAEwOm5PZTXQqJQv5YbBhToqYwGoAEHAoAVq8AAImSwmgvNjKF5LQFWkSwmkUuisC5Xy42DCVQ4cbAAAQBgETnxAbEABhQ8VAAE0IqhioC5tyw2CSAntaAAAgDAABXgA6kAMPgAZkAHLgApMAPGgAYcAAAAAAAAAAAAFY6BPiMB1gqAEoBdIop6UdcsNg_sxAsRCAAAgDAASMgQj4N5sQGUA20jGUAsihjoAAMxsAABAGBNY+AkgJEWK4A6Jixn2WYsnEf2cP+VGwPTDVQSAAAQBgErbwBIyAGECQycAHlZgYgDNNgAAkMQAAEAYACQ0YgtASQNJKwAM5qzlyWYulE5QfAZSqGyGoAAAAGJIBLQBqRJYDDFiuAWXBydZS6UTox8Gh2DOVQ2k1AAfwNgAEBwsgpZIjhVBFLFccMxAalkzllLpRAQID_lRsVbCVTlisaQP_KwAMgLS5bAlCRHCqMNUK4AVhmxllLJRDnnD_lhsGEogHBozhVKP7GYAlEiMAA4MR8tB2pKAqgrAFpH3sxdKJYg+5YbBlAY41AAWQAQAevAEjILzDAAYIABY2AAAGyEABKCoABiSMAAcQAA3wXcKCIWgx0lAeIVgA0gXS6VEPuWGwZTCQYlKQAB4Y6AEAAsQBEaCgxQISkB+kYAZScAZvZgAWubAAGEP9JQAAsgBJIjktlYMOoVwMvL1hC6XSiHKjYAIwWyiFhDCXSrbZqJoSE6WAAtGFkEAJEcTsrBN1CuADGZsZhspZLIN1y7gUkHosGcMJdKp_xaI0nSxloeLAqWwIoDi1CuxBiAsJtLJZLNcWYVLl3As0kBYM2MMJdKv92YshETpYAIN4ACjAGL4CyZlqNKKWgJIBCliucQDKaSyWS6HkD_isBpCaWSqFX0oj7MFgZUTFx2NAwkHha+_MQAShAKSQ3AzE_soXgE1CzKT1LF8QiUL2VGQYVRL1sJqAABEGAG2XAEhoBDpKAkqVHfk4BqVWVR1XSLJUBVMIAAAAP0uAEkjOOGJ3BcrCaB+zBuVUc10PiULy4lUw18VgJIJAAAFbLqeIE4iyYCSRkwu4LlYTRFJQZ8wbn81SeOa6HzKF5cSqYSqKSUgA6QmAFgXBIkwBUTJYGF7BcrCaAfzBuE0c10IqUL_9FjcKphAAABsLEeOjoDoMgD1PUDpzAU4lARXKjQycE1FNVK6QvKiaVUygAAARBiPMb8jFwoTfAEjIAeXAOeGQD4B4AGIAO4HgAAAAAwEV56AAWoAiZADy4QFTAANDQBlh4AgUbAAYIeAAIoAABgIowFKzU6MGxSUXhZEAmUoXgBPTBuBXaS_MoXkkmm0yhFRgtVwABEgwBn2YAkjCs6oAPQETDwA6giABBw8AB_5KAAAMBEaCN2YI5jFIANB4BtZMAIkOH+B_wpAOfJgABFkwAAbgYswDBVBqKINhYAAkgIJgDbxkLMMgGwEwFkAagABuBgAQoQio+DYWAeYLAOQ_EwAAEUUgQOgAA9NwAAbgYBC5M+w9EwmALTNjAGaVABeTYon_jIig1yqqhBAGoAAbgYA9BMjQ8AZQEQpeFLgJJNQsdNwojko01ABcBBAGoAAiQYjQBZXgx58G7skkmgAAGHgAahcAAABIIyAAAcDAIRYk+PnZJCptnpxGImlSmEMsXk9oqXUaYhFmJdJJKC5WUSrVVeKlO20megAJ5CgPApSOORsN5GA7x8_Lo9HMlC8_ehBNSczUihayheSQs1UGRqlsAAjQUAKPGVEDdnD8CK5UAT3AgTheJ4lVVAA8B8AARoKAO04UZUGwE4CaAUGggFg6LovQqAAGIfAAAOBgetOZ6VBak6AKIElP+OwOSTKdZlQAAsEIAABwMAnW6ChKEIZAJoSAf2lAFhAB1RMAAAAAOBgDZOFGVA3E6AcOnAFlAclk5CUAAChTgAAHAwAfeITJjy03AHkCTaUAF0AHKJQAAfRIAABwMAAOSgA58BWE5MKj3IUMJqAvYmVgBJtJLRyFUqjVT7LikAHipWFQifQAc3KpAoEcFnHDcAACCZQUjkF0pU5pKwAZGIkYlDKPQP2aOwAApLkyKggp0wbgW5QgCpB07ADRKkTQJoAl6kjG0C_iUAigKQ2Zk0HyJUcAIgWM7KSGcholamUQAnIlLYfGWgmUkoUydLAHVamhQgnfQIdN_yhSpQqKQZjMTzkCOYk2YjEekWo0EYzGikWipxMm4lS+UL67QZ6SW1JUsADiePiMfQA0oNUEAHpxBSGRVIFWIwBFHoaQHJIwLCpV0iwX8_ovUEsgKdCjgCGYlkiyWQ6FKF6ax5GRQSiUACPSiVZIpkUIJJBUFquAR+9g4s8hgOhPoYBBS7zNKFIdI7WQb8WMwLCzYx6DJIplEihSQAWSvH8psFIIFnDhZFCeorZsZNpohlpIzx_ISiQyOp7SSyj0kkUg_+ShilgSJgE3Pyn_7sGmT4DeZEAX0mhJTVpNtxSACmk0Fo1BooobABcFtBPoC0DQ5UARk0g9IobE2d8kagArpJCqSQVKhRwASk6KfSswVFS1XOShwuwoeVSSzFU6VHKtVjodmIvCZGTQfJ0+AgEQymokmkxkMymWvVPH4PajSzyTHeIMDHIQ0CekrMnYlEMdGJERqF5AvSFHEIxmJdB6zdCfgABpsDSo5w4DeBKQ4WQQkIBNRKR0o0leKM_HoYEKKJRrNS6bfTqCAFxKGdCjm0mMBHIGyAjYhCAzEOw2KgGcs_PnY18AXDHA3U+pFWr4hGIxLJZqq0j5+AMtaABDUDpUeugARyCfVAGAS_Uo8py4ReGKG9VIM9GoHUKKIRiPSyUG+J9DAWUqOgVo3k1iM9R2dP4q0kSNzWWz222kSxGSsQXrZVJ+jP6CPSIpk+83mk00UjEax0_rNZos9D01CQAwhAI6YAtR5YtXkqs9B_qkAQCiikCKUkDAhSRaDUsiOkqigaop9YL2QiOoaNQhM_iIAAadLDoFSaXcCNQPJl1mrIhGIxd0xYwAqhboICgoAowixUpd5CrASKEgAilhwsukllpZUKOfb6OSzUSDlzMshNvt5roRFamKSCMTKYaSy0+hhiA_ZqByZGVdw7hdgNNAeYELAltFtJpHJZqonDZnqh6A8nEc6hXoIUEshFA4VMwdIz0BAZ1Ub6F0w4uTQlIH5kqvgS6EWckF5BMrvEvAAbSCEEegxLILEwHLxu1KvgQcmGAyaENALKVaSKRqI3KE4ATSDgSCEH2iA_Ai4gXAMPNnIk+BCl4cXJIHsAh4AGxUxkkEIpHWEyMigUNAhgeSKUUqhgQBYFKL+DCi60GFlUCNhQ8Ce2UqkUQy1Ap4_C2PIyqDGetOSiykEgkEm1AUibSQPH_VqY+3z+U0CIMLKp_4mwNRJSVRRrVcq0GSjUayEskmamPRI5Fnpq2rOPSSSSrTSi+ZKlgSeeTI2cP38vuBMoZYaYbTWV6lzNaaFHKtRnopFoCiZGWaqSUTHzsgz2yj0kkkekEguvSJYFuBBAm0JSBVcCWT_yMNSC_AmVgNwTgPI9CiQQehKTpYDsDgRAoE6hCEIBm0HtJT+y1kmj0Yz0thMjLJRSDSSykFvCQ_II1HI5XolSwPLjVqZ9ECgTqYHA20NoGFa3WSzWSKNRqUImR1mC6xfJpFIs9POybx6SSSPRyOW9JUsCQsHA1mVK8gXJWrgVUAQ8eQyyFglIMk7AAHSSI49CqRQ4alAKAIJYUUI8hFBWAdGhAH_0oAgkH1IACciMBJATEjAaCihCedgAPIAURSgA6KVUgABuoQAAQkYCwsNDwOBCQPFNhoHDkPiGQDHxIA5IlAA01KAACoAFpTIHZkdAEK8AaPgBB0ASEgAAAAAAAAAABFiLlC+ggQwwb0kHKBJICV7A4nMtVkKPkCOFUqkkYjeRJ45IIlAAg0JATJgrbKAA4wThQbk4ABLXFGALCAAPUYAAOAcAAA4GAEiZRa7ZEhk0JJVBliZTKISQu10oi00iDTK9VOokVyT7wyJNB08fCWgkEAQgNA6MhZqAGz4AkZAByYAAAAAAAAAAAWrA0tRgNCcPwF6K1cAMppXKlC0BC9bBYqlcP4H1VCUgAEaCgPjUAlYPBYzAERw_AwErACEGTXgQWkEe0rAB_5mAACNBQBgsGDhIeACF4AYfABy4AQTAEhoAAAAAAAAAAARtmggYzeAWnwHBxFBViMATIeAAFEQAAAAjzoAABwMAXNCAK1QbC0BAAomzKgAb5sGkYlEDuVAWQHBHwABGgoDb8XIy8Gv3wbCwhzIJiBEMmAbkfDEALWkwAAQhoAANwMF4AhLg7VMGwsADQ6AXCTAF8D4AFAkwAF0kgABuBijPcMCp84AkjAOqoBgOAcgP+LlYHTUocgBmWgCih_pGAAA3BQCeSe41pI4kCE1S2AREqAIEHVRov_1aqi3yomhFAii0AAJ4UAdcmFI6S6JAWQFslDeLl4AwsZkkalaOm59IJVLNNCKULw6kECLKQAAnhQHgDxeAIYQbCwALiI_07B8SoAIF0EJXR5JUAAQQqAAAmDAAV3gC+EDaLhuHgKgIQDkEoAof8QgUkEFMlQf6TiCAAAG4KAPsX5WvDaHgmoORpJT1yheDEJr8BGoo"
noncomputable def WL37_2 : ℕ := zfNat64 33246 "uADDhFAFAf6UgEXFQBUI+DiAhlOAAGIhAABCJgJEK4YnANQH1lC8LoDkNoaULKVRC6QY6AsMFYBCTCs2IpJMu6EoAQBgpIwEgNgADjilTQDKJ_TgABYMwAAQiYB3CjRJ0slsBBjFZzqFcLI9VAkRxyGkglEkr1UK4WZiOQXI1Zwgi0ikG26CKgCCww3BQUEYG3NQBMlIAT4bAAztOAAMoEkAAAkNE_JQNyfNYBsFauAC4PHZ_pmKyGHVK4BFAGDZrC6WSKES04ABbEyonAaSaYRDapXAByGWmqcDBUthX1CuAPQTGyawuleVLZFDaUQdEe0oDTARuB_itXAByOVfMwWQV6pXJIQUQgNIXSyRQlmnA6izSJ4Gk2hYYhZitXAByJJYv2EKoWFQrhlNrHD8EjsmsLpVIqikCObSiB4WqjBghqATmpf+SgLxJU1ADnjxFAA27MAAEJKAAHhAAa4GONZ0lHeYgAAVpwAFQyAAD40AAAIRKASloATA16CdLUUnSwMk3ayCGV0CtXEpSSWi0sg9LqbGmJkYlppOQsoBFo5otBrqK1CmDoC5mwiRnnowGkBoilPAKJ_xCAonkSIC0ikBpAAconACos7kSpZhwGkDeCsAHIXr4DzkB+SUAAFa5fOoDEAAEs32aVhcWJgaQAgqFcB7KwalUtk0BqAE9CuoEKCHpzoJOTpbOxA2BpAAAghkHuDiMQ2hR79NwD0C_L1887YVgmh_4+ERiIGY7Hf+DUdMONH4bMX8mDMekUMsBLGclFLcy5Wz1CjmkulUm005q5jLq93j3bbKXS6bT0nTcBXnQ0EU+gdVSlzMC6UmKgAUwZg+UKO05qCiguRevnndzkFUOKuj52BbApQEDYFUBaJQDCDx8FTQI4dDoKQmqFHAIoV06kU4isUS4iMPnYHgCFWEJSAAQIAA8QgACANAAB6UgAAXAQFqSUkWJlJNMpFmsmvAsUEh4VaTRQyTSc6xLkUo0M0lUoI6lerJ5qpdqNRNp0TpuBISAMZuakqrwkBinDOAgQAmhkKEpxhhKAAMp5AwhYUyAkAKKw6C3IhKe8JBbQABwxo7OvgBoA+wVKwAKYMx5ABfRsFYDp1raRJYoQwmFU0gWSsLFcCapUu+6qVzyA5CyqEsAegXpivnUqg5Cy7Q+dh2CgIABSgBh8AhMgA5MAAAAAAAAAAAIMABzSPJ0vAgaf9KQEiWK4e+Ugf6xfIID0fETIzSBQjR+BlPJVByF1NREfA131KuAlAaQNwKwBXSCBBDwlCcVSZXDBiEF1GjeeQAQIAg46Anj4NpZjchOWQgNICDE4AnoZAAjYWAA_oxAAAuRgpCJ+UAhJgeOgRGwE0YgHuHwAYQAAAAAADx8GseRUPYoTga80fwMq4lS2AD0ogVf_Ix9KoD0D23GkLvEFYihp1QpAKZ4ICFhIGGgsnYi42MzpPTxo2L1oAtPhWlMEwMGwGAAWwRAFSi4AFQEQAA1AAAMBBGa0Y6BY74UgYNgMEcGoAA_8tAAxBqEwAAhBIAANwMAAdKAGHwpAwagYAAAAAAL1EwAAAG4GAA2fCcDoUgYOoMABywyCKmH_KkARlkhMjC9RMAAACJBi1LQQFfCyTYBCVCkDBsBg_61AOEJgAAugBA6AAAAA3AwCnjoUgYNQMDnHYCKBMAIQC6F0xZsF6iYAAADcDFWXgIAwUYDgYkQAtAJaoVyXHD8JLbaqUssXgnYoTgAAAiQYAet8EwMF0KAwhQQ4rpTKgD_qRPANpU0qC9RMAAABuBgAKKQeo+CEGA_8LAKRRlQPQcC0AHHUSsBewmAAAA3AwBqD4JQZUiEAApWuVBKQUZ8CUOIOM2C9RMAAABuBgA4KQCEqC4GsyTAAKSkEwRRgTMBJC6PQAAAAAbgYDQQkfB6DQAIgcmJAKfXFxQZT_tWtqeQwDiVQL2EwAAAIkGDm5PQAFnBkKoScPCkDAZBgYkcPwLtlQAOQFvNwAaQBiAAG4GAAkNAFgwQBLgHllQB64+Awm0hGVABYJiAAAACikAJHgdCgALGS8B6y8oXg9LojI4fgZTaDbKF4GEDCAAAdCgAEjwvhRSzR2AtCauY+f4XKy01mopePHZOS6bSqb0oXgYQMIAAF8KACMvACR8GgoACBkvDiPWZlC8jJdCRHjs_+XGU2iNyheBhAwgAEGgoAlSEALHkaCgHeJQXSkR0CEPrIQGUshZSoADCAAEaCgAJCwTh05SYCvID8NpiMqAE7HD8NpdtJP8qACwTEAAAAEjJOUmAryA_DaYjKgBOxw_DaXbST_KgAsExAAAJw4ABI8wQdd8mAeixmjeIeLlZYQPceOw2lk2igSheHoGIDCAAAnDgAEDxIBUnAehtXUpUztFysu2EqI5DaWQCtG8qtHKF4Ri4omEDCAAQcEgPABI8TwwfkpFH4HD8ouibNZRLwXKzrYQHNFNJv1KuaRAZQvDyTEBhAAIOCRdlI3Yn5jczoADzg0FUL3HhZBn5BQsJyAcouVhgSan46bgVbSWlLgwMpjIOQABEgxSz4ASGh1goLblwBeyheAJKOH4GU2iaSheH9kYDHBsAAAAIVh0AoP_lwf8PmhlC8kgJgOH4GU2i2SheBFCapANQABQDROgBJWFwChYGCMl4D1UZQvAu1FMhw_Aym0qj_KF4HTaAAACJBgDACQ0AWDA6UuAZqVAGfj4P_MRpHQlQUqPgAAAAVQ4CWktHrti5WDIl63URyZOUq6a1o3lVyBcrAi1EaSMUZaAABIGAHahDcHAJZLIwRSjhkARYPIYGEujgyoCL_4+DuhcAABAGArSIBiVHAtpQvMdMw1IuVhhAmR47DCWTSNHKF4EWogcQ0XgAB3CgALoyigXMoXhEFzONOLlYHx5GYQMMeOzqYSyaRWZQvCSRaiEfVhaAARoKAAED7yLhtGC8EbGzMB2JQvABcHjs6mEumkXcXK_6KwAXENgByACVFy8W0GWCVMaSXXAIyGi5XZSyA5NNZLJpqLiC5WUT8yEA+EoXhRNftncwj03g0S4uALUIAAAAAAAAAAARtmd2IKLwg2Cj6FziYBCw8AVQMgAVIRAAAAABgIAuC8GwVqw2ALaIZUFwGS6DkEphNIqkoXgReWqQJwNF4AAHQYDTEAJCwPhQmxg+HED5+G0Q4XKykgng8dk9LppGrlC8P2I1RB8BY3AAAFIK0oPAPQ2i7C5WAOyOH5UQBLls0jKSheABsw2DKjZWAAg0KG6MHwHobQ4hcrKSnZaDZHjsnpZNI50oXgRaiBDVhaAXQYE8dwBAhZcFwUk4eBp55DDSPjKF5CafLxLQQmE0iZyheBFjsJNIA_QuAABChADCoAOHAAAAAAAAAAAAA2ByNBRXEKGBBAsNmscsXKwB2xw_CaWbCMrKF4AVDQBsEUUgAALa4DgY3Z0Ddj4B7BUAf6VgmhpAABdCEAAHRKAE1XDcFONOg3MpBtAAuspAGEU8nAAfxKgAA6JQESFLzPIYNQCF0UrBUKZRSiUU2HzsJpdtIS9UrhtKNdD_pQvHOLRFMoMrVLYH5nwFzeP4bTZisAD0Jr3mIukfVLqxUAAwi4AAY6kAAgyFjQIYOldPYbbS0VQrlFKaOQmu0Wq5dEDqlcummm0EBaGEIjdZQqq1VLYicPKJPIYHUNIvdQr_8SgByVSTe5SLIWlUrnUABqGi8C2jUEYloKSkLCQWXjQKnXB7Q4DgZ2I0CqTx+AAAAAHCoK7+UmChOQAWQGoA04FcLguCiwDwEENo+coXkJBHRkvBCYTSUdKgIsdU+FGkAKFEESlwAB7onBHAcDAeGgDALAPgHgAkgA7geAAAABCABJGAAoQAk+ABlwA8qAAAAAAAAAAAAAMPgEIkAwEAoCAAAEFAAAAAAAAAAAa4G6JCkFSXPg4QTBhKmlQAPQk6YYjSR9Kg_gZAAAQigYBKAEA4GJadAmo+AakVABVP9JQaTpKQAATxCAACERAB5qhuCgaGwICOgBtEwAZo2AAXyMAAOQAABTkKGBMTh+GkOIXKwggBo8dhJLJpDQqlfqhUAEpEvrGM0mUHUoksDkAaBDCRJw_LSFILlYvZGAZ5o7ptJqJpBVqlcACUzsMi6aRWsQKDRJYBeZv9CBO5k6Dfh8AoEmALeHQALkTgAJSABI4+AFYrlP50IB6IYaOYjAuVl2gg0w4fhJLJpCNqlcAIJJlP+y4wmkygT5KjgfOjaEyOekWXqlOSiaVGpwQi5XbSaRYCJw5sJJKJpKIXVSvWQCCAcKlZRrNlsII_RJZdlICCzMbA04vAzd+fgAK+RoKAyDBN8uAGqULwAegZTaLhKgAM3H0nIegAAIQYAAOcEoHgOBiKBQDELgDjkwBJBSANIAAAAAHgYAwUgoDIMA_i4BEpUARYPgP+NQhlKAAAAAPAwAlCoUgobIUG7CYADpQvAigqVh6BZNIF0oXgTUUgEAIgAMBgDHwMdu5+vsa0J0XwDAQCgIOeGQDABoAGIAO4HgAAAAAwEV9fgx4AUBAkseALCVAFPh4ADClQG0CuREAAG4GAiQY8wEBcx5GAvwuAKfDwAMgLgNoFxSIAARIMABMaAMBgBwNAANDgAFQkAACA4AAHA8AAAHiqhuBgPAwSjMgDVEQAAVURgTAADkAANwMAcQ6Aa1Q3AwHgYMbnwCUj4AIoA2qlIjYCyB9BCAADcDAOAfD4AkNBIBQAB0SoAaybAf5XhApUBJAT+tAAAAEhoJAKDDpcBFcqAJqBN_OuYyeJUH_loCUSEAAFeCt74AkNABqAvYiAMkFwAPuJgAAeDwAAF4CgPgDVUDoUToKAAZmVAD6TR2AYRz5UAx_81AfQAAOhQBFBQHLMG4BoyheADUegxRSuYxTJQvAsgVTQihKQACKFgAFIwAI+CGCgJWYNwIrlQBNTyDEATFfJ4lQAE5EYCbNBGBDRMDoCxcAUswbgGjKF4ANa5Lw9GJB1zGKZKF4Fn_ZEGJ0IAAKQcCrg8DWzBuAdsoXgAdTBuDEY10W6ULwLIE50KiC8AADakVWxoFaGzMBc5QvAFPmDcBjXSD5QvCqgGfPIZlJSBBMuB0ADHwAkORoW4APARQDRlC8AGoMRb7dYtimSheBZAnOhB_0OMIAKuDwLFMG4EUSheAJ2NmZ_4yGNdEXFysKqOQXIeQz2FQV0ExFQauLD1GDYFCNmYCni5WAA+NmYDGug4i5WBVYGbAB88fp2ZNZQa6ApB0XmTEzAFh8HipgmCgAAug8AO0NgALEPAAEUAAEwUUZeCpb4EAYAagL2IgDJBcAD7iYAAQg8AABAGC+dACTEABXgDi0AYFAAeQEEwAYoyAAXRMH9FIAthcAABMGADFC4TSdLoABBhSOULwA1h03D86dYQgpQvAwgYnIgAAJgwANi4BEEknS5eAwYWjlC8K0kpI1KjTTCexOICULwamGQg+EiAAAmDBiegA1mAJMQAIuDyUwADQ0AYgeAIFGwAGCHgACKAAAYCKMAOrQIgcAB5OiVAFbTYD_K8NTKjcAQUQFeGwAAIQYAZJMCOHAZNgzh"
noncomputable def WL37_3 : ℕ := zfNat64 33247 "BC7lQsBBAAACEFAGAn8oQgoJg0ACMcg3hUBdDIAFU45sABghSAACEFFqYjtjZgGY+BbVwpA0pS4MgIQbQzZUAADEigFTYAA0gABuBgAoDwsg35h4MyIQcSMxcAASGGgjOZAAfQaAAIkGAMFkGDoIxPIYV1s5qdVpaAD0AJLTC4pM5Aq69PgABEgwAEhoIkYPhZF4hPy2lUI5QvHOLVeihJAB6fwuXlJnJQSqQRCfgAABtj4UgqDY8AG06y0X8qBrJSCAfQGwWNgACCIwAAUgoBAaENYU1QOC6TQ2mXbxcDU08hE0DSHQaEQ2BSRQT4vEkAANYUV4EDJgpDrFEwf_Pj8zcGVKgADiUQOmVAHkKrLEoGTEQABol1NiYEkIT8NoN8oXgBFDSSQXGVARkXgTAfBH4yAAARownxUnGJPRq+Rw3iPSheGEGrIkMsmmggv0sXhRnpdCj2k+BQZD5CYAFmg0YGSJgfCsyEwf8Pn4bQzZUXsZh_hcBxJoARKgDyFUkiaCoAAABKQBFCAAlwAYqADkwAQaABiwAwSAAAAAAAAAAAAABwgbCkakQRcUj_jcAAUpCAAJpsAAIs2AAF2bAAtugftMASEgbCggEQBhKgD4pQB_5KABsCEAAFAAAAbCqekwEENonFUtgA0ECOGUDDyEC4XYshpBWAkgYEB9CpOJQHB8_LaMKWq4WTOKNQQyj3_yEKLPIaAB4qj2ohRKoMdfHxNA3qJLAAexCcFScJ6UTaPxVLYXWqIWAkYghlHpBChHkMKo9AIsTwolUWjUPR8TQPEiSxU0eCmQJzCD042kTstV6qA8Qn+UUagzmuj0ghmkJ+VSiPaiFEditTHoxCaCt0SWIM6A2FCyJFYPsKF4aRk6pbACKGkihfJCAEquXMYLKUgmiUAIGBgwmFAFckD4UnwqThZnpbSiZsoXhrlzGSRy21AjhfmbOQSCORaVGelmTi1UZ6EkChdLITNGAmg4TwqShxWJIaBHDaC0ZcuYySUUstBEzHxASxeUmclBKpDEJ+EWQnUAA6QMUAVG4mBbp5DDaFtKF4ALJUngACMqAIIUQpo9LJBK+GwAAYYEQYJZEEuz4BSJUAEUKiAAArBOC0q8AUkqAl3DCkFAsHgDcbAA2IgAoiEAExEIAAAAKoHct4JthAISoBgImgAagQgD9SEABDj4AAAAAgNACAMjMiAohtx0pAAZpGAAL6cAAMZSAACEVAA8hhuCiPkQT1UgFHqQARQAceRAAHUKpFkopAAAB5gGaUACOgAMMBwMBASALykAAAAAAAGBCAAAgXAKLNkaCvJkwJDSJ5XSoldloGJEQYSSJQAeCMQQJoYSqaQEqqWwooau2TANFMphZFRlDMAH4uZwygV7KgACiFkqmUzw3b0WgABrwApaADpQAJGAFGwBAyAHFQAEOABBQAAAAAAAAAAAAFu8EvwgeDgP+OQXRxokAf+XgAPIHAACEEgAAUBwAD+JjBKCpKhXCyZTKgAynBGoByJMABiQqQJVIoDmCoFJASiZTLIPFURMZKwAuk0Ab+ULyyAEWyBOGkmkKXgm+LLgdH0BidLt8tAEkymFUJYZKwwkUkl0ZL5ZsJBKstmKUhJCKRQQkwQiiQSiUSSpcoXgeAfGJAROlg01Qrn0uktAD8LF8C2wYgB2lC8OgABwmRiEqkED+BcDPGzNuiVHNJVg0oTzCUSiaQmV2UIpJLplLoAkB_IZWMJJSZWUSSEUgkdKtNMacQyiTSSvIuVmCOht6g4Je_JgQMpTwuiqDJWWUDKGmgmEWhMBcAHUwoELoAgUuAMCUO1STAUSshFypeAGUsps0IJRlQAskJ+Bn1CuF0AwIAoIjQVhUmBCKRPCiIEDbjEYT6DNjA_8XAAE0LpVOUuYw0k_VLYEldqACWoAExAB0oAYfABS4AUTABxoAULAAQoAAAAAAAAAAAT4CAAeYsJvAEz4BCTAgDS7IgKIDPjIAAAAAAAACA0H4AtPgDN0AhJgAAAAAAAAAABagIA2nSYF2plMNo_tUthRAclhB7R0fQAC0LFcLJVMIbcfFwCgAJaASnwA8mAYCAUBAAAAAAAAAAABgIqwmLgwWTFxsZsZ0Av7wI0+AQkwDAQdBoAADSUARkAOJaEYAAAAAMBAPDj5Pf35+BIaYQgYNgMAAAE0B9Ad_ZmEfFQEZDNx8AAG4GAO+bBsDB1BgAJXlQBFAfQHBj42AjIF8PgAA3AwDUToJgYNgMABdhp0RUARQALtUzYAATx0AAG4GKsAJB4OBQJgYBKA3CIWgQcVhvID8A4nSi4CMgP0eAABBwKBmDBVwmAFoGTFYegW0zy1vouAjITgIiugkAAAgDDEBKA3CJRJUAU8PgDaJUKgABujwAAbhIAFpcCAMJZ2AAxgXADRDyGAcTVBcB+saAJI8AAFEaABCXAE7EwCYSoAmkfAW0VaVAAAAANg4EaDgK8EwAtAyArD0C2vDVkYli8LJGQnkRBRAAbAQAEC5Gg4AA+x9OIuACXHkMC2lgi4AACiAAAJy5Gg4JaI1DUYAWgPaNKw9AU214asjUsXgRkAKIADYCAsNABIsjQcY5iA1xMBr4uAIyHkMA4nRi4D9Y0A+R4KoAAAOLgBIsjQcAAgw+FoFilYRSA_AOJvQuAjICdHgqgAACQuAJCyNBzkG4HIy0SWA0UsXgPWcKw9AU22qi5LF4WSMgH_lYmIAFxoCADi4A5cmAFoA3VCuS44fgW2qmDLF9Rg4skZCH5EAAnkeAAkXAE4EwDRSxeBWBWHoFtqpgSxfYZCLJGQiWRD2vzUAAFyLB+BKEGRAdPllwBhFYegW0FWULwIzOTWJFLZaApJAweABkXAmpVKCC0BGqhXC0cPwLbVTNli8LI8WTXGZaPpImGpE8AAAE1MEQZAKpKAW2VAFyD4D_TUKWKgIyBhPYhAAAAyLgBVBiIpKGKULwAXxw_AemUMqULwBjmY+P+Kx7EIAAg4s_AOpdvBcAAC0CxSsRZAfgHE1QXARkAjj0tCEFQDDi4AOpdvBcBv8yADeULwG8Kw9AtoHFoWgRkC5EisAhEvCyBkIuBkdHambDycAEFwBIaAPNJgBaAOtQrkuOH4FtqpeSxeF0jIRjIgAABCDgJImR04EwAtCCRBUK4YDh+TUNpVB2ULw0kZClRsAANQAxEwbBQoSIDaBZAuAECHkMQoxBpFylQGEAAACELADwUFcWBHx8AHcoXgA9ANptIuVgFULgmQHVk4GLLwATiwFUPgALlC8AHoBtCYlC8AqqAWi4ZkTwKAcgXImA7xIJoobAggHRKF4A_w4fk1DaNRKF4MCZiyWhaJiUQHNFKRkxOi9GAoCocwoCaAREng9NOlwBVHoDc2Dj6JYruRLF4cSzGQgmeOwAIODQFgGA+G4KAmgzI+GtlQAh5AfgGEfaVATSCGTGYAAIQsARBVBjoJ6AeMoXgDNjh+TX+ipbNoucoXhXYyG_jYLoLwFXloAJ1cEPDh6jYP8JQAAAGonIAgdAAf+PieBQEULyHQCWHQKORn4CWyheAO8PHYF02jdyheBpVzGHQGpPAoCSCIS4FwEASTWXkSrzR2fwUp6AUsoXgB3jh+XRyBRSNoi8oXgXYyB1DR2BXAcZgAA7DjQGhyE9KCDRKF4AKY4fk1KptDDlC8OK81zHGQRsaOztnwAZJKB3iRLTR2E9AeOULwAck1qoFG7WKMLlYPUXhqB1DZmUSqW1gzMWJOiXF50vJYEAPlwA6aTQXiwACXyoAJEeQxLJ0G0VSVH7F4jIAfoPgAAGKmEIWCWLAOYiAa2VAGzD4A2jjyoADCUQygbAAASi4ACJg4NAITJgBaD0Ko9JTJTaGRaZUXLw4gZGowpGKCNQGOqQBgMeAEjICOXALZGwHSC4_8jAohAfk5DiOHKgukUADGC8AegeAAM1ADDIYAaCfRMB2guAEkID8nPPSY4gtP6LxGQAqICriYAQAkZARi4ANQEyZG1KF4RSou2PHYhnMlNpVU2ULwulGMgdEsXhbQDmjiMGQAGZARi4BNo6A6oXBFBNyA_JyHE6oXH0ulEAERcAAToSAANTEoDRAh4AIQJwBaEUZwrD0nMlNpoloipYvPpdAyAHM1ICtZEAIADMgG5cAGoBVyheEUD8HD8a2dN5KbQ15QvPpdCImUwyAtC2gGsHEYMgJkvfQFuEwHVC4SAjAnBAflUDifALjCAABtA2gdAAdwnsQgLuEwAtCKBEEB+TWv5McQCpQvC6ABOHsTFQZQAFHQHgRamBoWBKJAN4WAKwRACwT4ACdEQAAtAAA0LAABpkaHkdDQGcIE4AHyheAD0HMlOIoFrnxcF0AKbQiAARoWAMARLwCqpMG0GwXLyIiHlYegpkptB+lC8OIGRqUeFHxoCYAAAIK9fxUBWcmDadtLgAWKw9BTJTaINKF4cQMhRTgcP_9jwBJIJFQOgUEujkmAe6fBtGSlQBq5CBaW0aKVBxA8AtBBDKASY6bgEPLgDQkjQ8FRIJMxg5_qViulC8CoVUyID8FolOJZFocQKhd74jBUQDUlwAgVsuRweAshxOH4bRX5QvAqfVVgCIT8FocT0xcHGoxUQcqWwDiApkeBk_Hx2pKRkxnQAkNFFDQB2OH4AdyheAD0HJeJs5hLyheG0shkImGQAACdGTJhoActB2OH4ANyheADcOH4OQ2lU0pQvDaWQyC1DBuEgDIAABajJnDR+BaL0gOwAnlC8AAIcPzqOQ2hMShfITaWQ6NRFyA_CoBMAAzKQEiLAPZIoBIAgTQArlC8ACcgPwSlqNjiEHKF4G0Bqp8FkugAA60JGg4BSpg6P2CxvYuAI2ID8AwjTyoKJZJofGegkgCsUIAK3MEyJgYCk1EwV0ACBUAAmPgH1MwASQAKf+UgBriEAAjmAPHwASWA2BwpBwABhAArR8OaRh8CkCOKgAAonwf8KgAAUQcjQcusmBHS5XAJGULwBABw_DKGUSCULwKpNDBhkEkqgZAFydyZk5IrAclBu4bLxKF4XSSDkbywZx7aRPhcrDTUaCTR_hkvCTXTdtnOy0WogAFMjKyRWA1Af8XKwwgcE4chloJpHMFysAyhPNO9lYegFksZikkhxA4CpTAFYjB_EwGiNgH5lQAPR1zUF0j6VFkCiA_nTmOQAkgpAi5Ir2STACA6bgP+LldlFUIksHNtroaRFRcrtoEEGvljMit2Ri2hUSzKR2XI7EbAAgcGwU7UeAwSNLAEmULwAHxw_CiG0KiULw2lUMg5oyBKEEAAALMDiQgAN0LYUApIJ+AWADli8BvCsPQCz+RWFoUSxLFcmgNNw7g1CLTSTRUASYGDEKPmTBiEkVgLJKF4AlxEhn_mYtJgwuAsx0AApPZSLyMgABZwFiSDQgxQBRPSYB6A5soXgASzyGAaSGBcH_1aOgFBOI9FIggyBkBAGCWRASA2AT8VABVANMqlIAAFgjAABCLgAw4RQBQH+lIBFxUAVCPg4gIZTgABiIQAAQiYCRCuGJwDUB9ZQvC6A5DaGlCylUQukGOgLDBWAQkwrN"
noncomputable def WL37_4 : ℕ := zfNat64 33242 "DAoAQCQAAHQAGJHQAAAAAPDgARGAGFQA0WAAAtANaiS2VGzMUh0rtJHqWL66ABqh+AAQZEAAhGABFQBIWDgeAABaAcGLWiUyg2ZkUK7SSLli8P+JQAAAFSADyoAkLnGPEjDgejkKCLTSDa0SWuI2ZuccO4F0khPKF4AAAAAABRgQw4FLMQFsi4AysbFkK6L3KgAFzDwAAoB4ACQsv5MNcWAwgbiLgD1BtiBSCunbi4AAqQ8AABmAeSpGh4yIkABzIuASzSShqExrpXYuAygRchGwAAiRoAPBUjg8HCi4A5kXAJWWJQ1CS10x8XAZQIuJjYAAUAkBpeAPCoOxoTgkABzIuAmklDUK6H1dK_FwFUAagAEIGgANlQBsWDsaAAOZFwE0koahXg+rpX4uBaVQBqAAEDBhYDKwgB5UASAgdFigCwAEUBBEAIQLgAHERAAAAAAG0qAJCyNDxmhYF5nwVEMJQvAdUlDUGpXf_pXgC4CiBdpIAAHtjZlpaBVioJrLBsJGSHgCIJAAAVBIAABhEAAAAHkAAa8HgkADoiECAEuj4AADhUAf8cgEcHAACEyAfhI_o0GxkItofcqAl0fAAAlKgAagEIOAAIRsX4A9SgAZUASGgGBIGwKwABNOoAAIiYAAEg0AAAAoKgQBYAIiGo2AsbFLA+AACQXR4Ki8n7l4A6gAQTYvSEAGLwBNKGElQuiWBYOMIAADkIAAAAYRAAAAEcCoACa8APKgCjYAPwJQhDoISLxhAAA4VAABNg4AADQA1LFWJJSFg_0TE0jYe4XAA6zBuAQR6BcAAMQAFVHQADCoQ4WAuRMTUfAXARuWpqAQRORdHgqDKElA6gAQTYnwVWVCipYNhIygBYmAAoRAAeCoAAGEQAAABCsqAAeVAEhoUg2AWgxBmHwAHgqAACBMAAAAAGhYHYlzEqKCdEsZlNHrKC5eAqRWmIBBGP7y4CqABuxOAHGfAA7KkkhYL0GRTSkxcAWfNgP+IQS8qAADTCR1hoA9TYGT8ADpQAs6AHlQBIaAAiwAAAAAAAAAAAABCUALPgBxcABKgCQ0ABFgAAAAAAAAAAADw9+BnjoAeVAMiQAnEgAD_y0AA04qAAB0QwAAAByoALLFWJALQADpYvAm0xEUC2m9i4CqBX4WAJplHHHQAMyoEAWAAFoSrXqvMQFEqOAcSpBdHgqCqANQ6gAQTYAwAkhAAyoAEo2IqC0CgLFo1ElhxDiWQLo7FQVQAOoAEE2AAGVD7iwDUABZQvAAUI0cuOEmK2gqyhfHQqCqAB1AAgmxYgKsqADSxViQE1ARFC8ey0AwkUAtDlvCktV3Kli8MpVnMxrNNECFRKlnQAfipdsWCDfMyCaPTUlC8AJi5jIoFtLKdyxeBVAulEWQgb_U7AA+D4Pz2_rbW1ByxUMgligJh6ARBIAACoJAAAcKgAAP1FwCeEieTYCNm4+As5rykJ+tkuAF4cAIEuAARBQACHLjyOS6AB5JoBIzyGAEEqAgzQ+HQALw4AFBUACODgAA4VfqegAA8hUAsR0DIA4YQJCuCImOkTB_wmAOaTAEoC4ADxkwAAhAABcbACwwgI9cGxUcQmCJxkAACkAA6ZMAAIQAAXGwACjJEjoWRsBpj4AAEkjBZAAqGx5AD+5cAAG4+DULAVuMARrs8KnXlQSZIgFdFQB8wiPIAvIqPIAAAAQjoswAJXFMdAkOgAAFkwADQOAAPIAGuXgAAXGwBgHMrdJaayXAAAxLgAG4cBSBYCSgB5FaAADyXABwKhnWLcWS4FtjwBXS4AJ4NVUAPuXSUAAACDhkWYBOrgUJUeh1fQA4HAAoKgAI4cAAHCr+BkAAAAEUGKcpmwaIVDIJYQgoegCYOABQVAAYg4AAOFQAAARi4Amk2ThE8qIXTRjvImAFwcABgmABIBwAAQJgAAAAYg7Ojo6NlJmOxseAISoGwGADocABQiAAbBwAAMIgAAAAAwEAGYMBvyGAExcABNDgADcXBM4mACMJAACJBgAGHwA4uAJjQAAAAAAAAAAAAEK8AAAfHQABUOAiAcABEYOAAACkFAABRgCR8ABLgEBMCYUACQWAAAAABx0AAAAATBgANFwhBwAAASAiACGBwAA7A4AAACYMAA0+AAmQCAuAYCAAABhwAAgKAAAAAAAJgwAiC4RQ4Ug0XAABiXAAUxIAADaAV5mAAAmDAaGhoIocAE0eMBGQGguAJJFQAEOLgACaEwAAIQYAEK8AMPgEx0AhJhCDgAAaB8AABx_gNAQOgAAAAEIMACFeEUOAY4hAaALgAegG0+MXBJByAxkhAAAhBgtq6ePAMUJgAOxcB7EID2LNSEgAUBcABHZOAAFSFALYdiI2ArZMf2agpBcBBAATCwEGLgAI6JwAAKQYB3Cg+eTAAkS4P+IQHsWABapcFxHIDlScBogSAAB6fBiFAsDgEkdAAf0GgBAgOA6AA4BMAABuCgB8KIIrASskVgdoLgB45QvAmkkFoCDD4NxJwAAdwoAKRYB5FSuXgUHBC4AeOULwppJBaAb4+DQycAAHcKAVlhAHyYAEPCEJIEBCAuQiAOSFQAKqIgAAAANwUAVVCCYOvYZAAOyLgKoLQJpJbUfKsLg8A1AFEAAO4UBqMhE60mCQlVyoUWULw_axfP9HUxLKRSSDxKF4FpDYCaAAHcKABQxAFMP7xpHpMAlFoCxKF4VQfmcPwykkkhpyheA946AmgAB3CiPABCMZCTAmgkRy0DClC8LoK+NGdpNJJIoMkoXgPcOgJoAAdwoHVKFaICpOAhnpqgmTeUL7LbRa_slAxONhnpJHJlC8ihOQXoLEwAA7hQy8VVFJgEIBGyheaQF6GjM4sPYM4KQWgA6g2AAA7hQB2aDYoJiXgDtaADVQBSiEEKAAzgccQIFQf5PiCKcAApioAD_CcAACcKAFwfA6FNUTgKklH+jIJ0XBKQAAhxsBpA44_AAAiCgDEKO4mUwJIMTDLQB6ER+jhuE0oixPDVJcD7nIAmgAAiCivvQqQoBbNRbQsBVLgIo1KEXAFQFMbAAR2TgAA7hRaxYuGmYEIMG+CaXZMAfcuAmsPC0P6JwRaLguoUHRZkAAFEGAEAYGgUWoJgAKpUAHwJgACeVAACoMglYHAAKEBAZr2TBLHgHTlwVBHR03EoAQjLgAoL1TIACDQUAA0mCEKDfBMFAyAADXEwAAAPQO_oNgAAYhQBCFAbQNiriEVTLgMQGwhCkhMAuA2jkUKhDEAAEwUAI5CCEKAeheLiagpyoAmp0AAF82AHIIvMgAATBQB4joFFVBCFFKIg+0bAAAhD9h8AYk2AGoYBTgAATBQHpexYBqIJNisRcAf4LGZUTVjMVgLgByEYjIAAEwUDSi8WB8xY3JqPRLF4AgQuVm0PqiGU8AXBsZmHJQRiAACYKAItx+U9GoFgFIBWCIAK4VAAD4mAADgVAAAmCgBSK3_IQFEjYmpOQuQIH_jIoIZT1RcGtG4chtIyAABMFAeA0i4ALVMeTANSLj_ZsHDKgCwRkTaiAa0qA2jk_ITAAAJgoEqkXNhoNOFjck__NjjBcAC0o1EVYzFOi4Acg5AyAEQKwAcgmSRAGFDYC0kgtouXiAkYG9lCsolELoAMsXgDUIJKSxmeRczgARIUNg7A093gx9aYn4C0KghCg+mTKvKF4BpS4CchwKk4AAKMgLo5JNBGoAAMQoCyMDgrQQhQfTJhaAFQ0ZgayNhCEZBVpYvAwkE41UMyE_AAJyFAJUPAAJSnhOJozvSLl4A1YUSIwABQXL0kAxZZKOaCdQ+dgAQcCgAJDQmg8DiFKeBloAXAAsOhKAENC4LLJT+qFms6AAAgAeZIZATQNGya+MFwAv8gTgBPouGpZZKUH150AAHMSAJgfDcHCbKgAuE3GnKgJyAAfs2AqgNCbgAAXBQAaa4Hg4oggdGAHWTADyB4AB4kwAC3DYAAjQcBmJUHok6ef+OjUBcASEKyE9i4DfMGcBxJ1ChWAAAA6HHyRRvNgJv8E4bBsXYLgACBIjAuhV4uCygOUOiehlAB0ABDQOZQvAmg1q4zATKF4Ac4cRgVR6INLF4GESlBbAeOy6AACFFStSoEMJE8Gp_guACaEB8CqHgC4DCAOQLJBGmqSjx4HQCwhAGup04GoekqAPjEwYS6BdyoLKArs+PURAAAAs4hfTyGUENyZLJqZTplC8av+TKZVJCSTLUR6AJKF5STDJRzQStHzsABi4sBRDwBTyGBNJqC0AR8OIy3TMUQ44XBXZiG2zoLlrTqWoKEnQAF9YAHVMHIQU0ajXhjNZ4uroApJEswBCC4K6AfwLG4AKCLgBOzEBHoxXZUBNGhHTc1YXAAhOIFJarhWIuGIYQACHzsolNAnWRDJJEjQ6dglJMl0WYgByheB9Yy+eOHzyWSaA7SheFZkpZtCnJlADHwsGY6gy5+X047UnpKHjIBYnghBg3oTAAzzYF3FxVcyAAEZUAEaKAQAANwMAAw+ADnQQgwb4JgANB0ACUAenE7RsAfyVgAADcDAGDmo+AB14kQoDokAADMuBiBEAACJLgCFREAlYEFgAACFeCYGAOkVAFcLgCiBEACGi4P9OwDsSIAAL4UAAZiADrwDokB+oWAHh0BXCoAIgHAAREDgAAAIAwADd4V2GgMRUHQ5erBhBqKY8hgAfcuAAiYRAABCCgAQswTBQAHioAAHcLAAAsIgAAxDQAAbgoQwEHvBWFGSEgADNlQD3+58B+gSAnJsAVcIgAADcFBqCB1oBCTBMFHcJj_yUMQJlHQD4KgAiAcAAAAAAQBgABLwS5CCYK_4JAWkoCnzkABVABDh0AAIQeAACkFAH8XgmCv+CQSSaF7nDGKQyACQQSkZFo7BCfoXAARMIgAIOBQA2F4JgoCSxpIng_RoxgHkAWhFKJ5DRmAVcIgAAg4FAOY3qGgg82AEkYccaBxZ8f+bg+JUAAADoeAubAH+DYAAAIAwAhEIoA4Ro0FOkItoa0qAAKP9D4ANGwHEBZBkAADYGAAkNA6FlBiE_DWtnOqmlLF4AAFJCIMxkGjm4GoAAAEkLB0AgnkMtpZYuAKElRHBuAHyVAAD7KgACNBwABmIHQMMhPyiJJy3lV1RcvADKpDYNIEmWJcBxAFCULwAAXBQLEOIzXjB8yiqj5+dTaURFlC8LoGZSWl7C9blI5BcXLwOJJA55QvAACKFGDZgAfKDYKABofBBnIBwVAAf6TgAPHQAAxB4AAIQUABHeBVoQDs2AQFwAEiDYKABofH_moA6TAH_FYOICUjoAAAACEFAOagBIaZRHgAIhPy2hGShebQVgQAYLwokUJjFwABnB4AABhseB9R8_LaHdKF41RUpgLQokUHUFy8C6PQPcQH_eMQAA1KRB0J6W0kSsRsoXhRRhxYzIqckSn_46Bq2YuXs8VgACptKoBbkiB2dGKx4J6W0GKULzfacCPi5WEUchIQu5ULAQQAAAhBQBgJ_KEIKCYNAAjHIN4VAXQyABVOObAAYIUgAAhBRamI7Y2YBmPgW1cKQNKUuDICEG0"
noncomputable def WL37_5 : ℕ := zfNat64 22341 "Gh0AAAAAAAAAAAABCXAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABs+AJCQAAAAAAAAAAAAAKMABQgCBkABGgB4sAAAAAAAAAAAABgIEwMAAACyDgAAGEQAJIBgAAAwEACEuAAAAAAAAAAAAAwEAoCAAAmHAAkgoAAHBwAAAAAYCAAeZAEhYAAAAAAAAAAAACEuAAAAAAAAAAAAAhKgGAg2AwAaDgAKEQADYOAABhEAAAAAAMBAKAgSWPAFjKgCnw8ABhSoDaBXIiAAAlpQBCXAAAAAAAAAAAAAGHwCEqG4GPUJAAAKJgACgUAAAAAABuBgAQlQ3Ax6hIAVEwAAJwmAAAgTAAAAAbgYAChUNwMeoSALIsAJsqAC2kwH7ToE+VAOQAAANwMFteADi4AmNAAAAAAAAAAAAAGowBsqBDDgAAYlwABUKBoAAAAXCgAAWgwAATIAcVAEhoAAAAAAAAAAAAAEyAHFQBIaA_DgBiHACDLgAG4UAAiS4AAAAAAAmQA4qAJDQAwMALg4AA4cAA2CgAAIHAAAAAAAEyAHFQBIaA_DgBiHACDLgAG4UAAiS4AAAAAAJmQA4qA_DgBiHACDLgAG4UAAiS4AAAAg43A6Ojo6ADyoAkLAmDBFDgBiHACDLgAG4UAAiS4AAAAAAHlwBIaAAAAAAAAAAAAAPKgCQ0AAAAAAAAAAAAAeVAEhoAQCAAAAAAAgcAAAAAACioAkNAQhwAxDgBClwADUKAARpcA9AAAAABRUASGgIQ4AYhwAhS4ABqFAAI0uAegAAAAAoqAJDQEIcAMQ4AQpcAA1CgAEaXAPQAAAAAWVAEhoCEOAGIcAGguAAZBQABILg3UfAAAAAAFGAFlQBIaAfDgBWHABgLgAFwUAAQC4PtHwAAAAAFFQBMaAfDgBiHABoLgAgAcAASC4N9HwAAAACAC0YAgVACBoAUJADAwAAAw4AAgFAAAAAAAAAoqAJjQD4cALQ4ANBcACBDgACQXBx4+AAAAAQACjACioAkNAPhwAtDgA+lwAI8OAAQJcA9AAAAAEaMAJKgCY0A+HACEOAESXS0AI4dAQAdJcA9AAAAMzMdMwAUVAExoB8OAJokAGguADQCQABILg3wfAAAAGY6Ojo6OjtOADToAEVAEhoEUOAIQcAAAB9AmAzGQAASQ4AAAAeXAEhoAS4WAAAAEABAEDoAAAAAAJnQBIyAHlwAMgsAAAAADjoAAAAAmHAAEGgAZBYANRcAAABKLlLEQAAwISAAAAycACPgBZ0APLgCQ0AAAAAAAAAAAAAmdADy4AkLAgHABkFgAAAAAcdAAAAAAAgaCkWRsRAl0iAQIvABpAko5zIS5cBEWgAACVBoAB5cASGg9B4ADEBAAAALgIQRUBA6AAAAADQAONAhiQD2Kiei7l4ANIAGg2EuXIKIgqAAgoSAAv4EJBynDACZ0APLgCQ0AAAAAAAAAAAAAeXAEhoADEOApMXABLjyGBbSwRcAAAABW1oAPLgCQ0AAAJlQHaGg0ikAAJSoAAAAAAHlwBIaAADPC4DuDQxLIA65KJEXAAAAAAAbKAHlwBIaAAABHQB_BX8W4DgdAAAAAAAw+AHlwBIaAACJSoAisfAf8bg9hUAAAABW2sOAB0oAYfADy4AkNAAAAAAAAAAAAAHlwBIaAUcOgIAFwB_42A22YOiHxcAAAABXgAbKAHlwBIaAAABHQCoG362zmC6NgAAAAAAeXAEhoAAf+LgMHq25jyGBUDY4mHi4AAAACttQAkNAFhwPlKFYD2SxeBdAMFScLTOQwxcvDkAgMegAAAF9eA9K4AkND9DQcKNgFclQB_UyABOxUAADQAAAamUASGgEhYAZkwAAAH+kYOcdAAAAAWoBcrgCQ0C8RAGijIioXAD4Pv_lwBNOGFwAH+g4AAAAFXAEho5IeCDRkf+Vh2JUATALgCaI1Kg_M7AAAAH5aAByoAMNFosR4AADpcAAPEgZcNAAo2A6_mLgAAAQhwAFioAINFosx4AAQJcAKjGgAESXCkOrxHYAAAE4cEYAOKgCc02hDGgAAJlQABkSBTA0B+xeDqAAABrIidAPtcASGhyyIAAExcSWPhKAZEgHIHgLgAJSAAAAMTgAVcASGgUB4AACZUAATEgABGVB_52AAAAtwACXAEhoBIiBABcAAIcPgP_oQDSLg6nUCSgAAAAi4AkNADjwABgC4ApqVANZCHv9DZJhcIE6gCUAAC23ACC8APKgCQ0AYdAB9ATFwAXY+P_hwApC4AAAAAAHlQBIaJINge0hBxDllQAVgqAAEpUAAAAAfgAs+ATHQBAqAJDQChcAAJo+AAA4_wGgIHQAAAAAAbKgCQ0BgbAAIlKgCkx8AOOg0iZSoAC8RMAABbVk4AbKgCQ0AAAAAAAAAAAAAWfAECoAkNADBQAAAw4AAsJAAAAAAAAYACrgCQ0BCPAAAmLgADIkfkQgEyFwHUP7NV4E4AAAB4VAEhoSAeAAAmVAAGRI_gZACpKgPILkcgAADGfg48DJ6etAIaUAPmiWFgjhwGQJgAAAAA4VAB94mAAAxEQArMoFBIJIcB7CIBCpUAf4ZgABKVJqUgASgAAbiYAAx0ASMgB48AYFAGYWAAP+AwAXQmh0AAAAAeHi1AAJhIClxcADuMG47waCyKHKnsKQBXImAAA3EwBghwNQIgNRFwAxowblVCyNNKnpKQBXwmAAA3EwYlpqAFB4JcSA8Q8AGUuABIDQ80COAPOMq6UEB6AB7Q2BgJBSAYDoAePAEhpUiIWAsB4DoAAD_ykBlAXHQAAAAAAOHnCEk2hwDDHEYBmSheXQI6mjs01UMpJkqAADRCQAAWmYAZmk8FgiBwAADioBCAQCgADiTAAGIIgABACwAQJpaSJFIkAACYuD_BEAQCgFoGiLgIoCOCIACUA0COEwbBIAAGJcCfihmAMCgAESXAAAAWIGE4AF4cAADEuDAQ0AUCgAH8XAAGvLvguwBTR4EwbcTJwKhhMAAGJcORSIQCYUDUUhVsujcvBBAcnGLl5ZAKas0kTk6JwMeAYVoAeVAEhYHRYB4UEdA6jMPgAmysAAECYAAAAAAQlSNDxJzoKVpQGWIRcAE2LgACUXAAAAAPxIAARkAPFgANUYAFBUAE2LgAA4VV0AAAABY8AAIqAJCyNDwnxIDbJ0soJl4+XBctSP_GQABILgJIAAAFSf3oAkOgAJcAOKgCQsGw0AwKAEA0AAf3DgAygsDoAAAAC1AChUHY0MIeAOgEwlIuAN5FQH_loKaVARQAAAGwsAEdeAHlQBIWDsa4MPABBAHFQf6WhlREAAHCoAAAAANA7GhKjwHePgF8FwAKQNtLQXEqAAqgAAbhIACQsjQ8cMeAeSA_CbMQFli8C0iEHIoTgFkVcXBvo2AAAAgwAoVI0PNWHgGoVWII1Si4A3oVAFkVcXARQAAAGwsABvaAHlQBIWDsalAPABJGoESoAF0TAACUqAAAAADQAeVAEhYf8WAhhw3DD_pKPSULwEwIQpwwdAWRIBcAAAAAADyoAkLJuNL_Fg_8bBdPxFx9FSA5xQnNoTQMmVAAAAAGZ_en4ABLgBxUASFgdFgGBQBkFgAAAE0KQBA6AAAAAAwR0APKgCQsDosAwKAEAkAAB0ABiR0AAAAADw4AERgBhUANFgAALQDWoktlRszFIdK7SR6li+ugAaofgAEGRAAIRgARUAS"
noncomputable def WL37s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL37_1) (dpk j 2 WL37_2)
noncomputable def WL37s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL37_0) (WL37s1_3 j)
noncomputable def WL37s4_6 (j : ℕ) : ℕ := dsel j 5 (dpk j 4 WL37_4) (dpk j 5 WL37_5)
noncomputable def WL37s3_6 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL37_3) (WL37s4_6 j)
noncomputable def WL37s0_6 (j : ℕ) : ℕ := dsel j 3 (WL37s0_3 j) (WL37s3_6 j)
noncomputable def WL37 (j : ℕ) : ℕ := (WL37s0_6 j)
noncomputable def WD37 : ℕ → ℕ := rdw WL37
noncomputable def ready37_cuts0 : List (ℕ × St × ℕ) := []

theorem ready37_cuts0_ok : CutsOk ready37_cuts0 := cutsOk_nil

noncomputable def ready37_0_state : St := ⟨26112, 285696, 51168, 110983, 29184, 45301, 53248, 83155, 29666, 44151, 52016, 111831, 28545, 91840, 26112, 285696, 77280, 396679, 106464, 425863, 159712, 479111, 189378, 508777, 241394, 560793, 269939, 622726, 296051, 648838, 80352, 140167, 133600, 193415, 163266, 223081, 215282, 275097, 243827, 366937, 269939, 622726, 82432, 112339, 112098, 142005, 164114, 223929, 192659, 315769, 218771, 571558, 82914, 112821, 134930, 194745, 163475, 286585, 189587, 542374, 81682, 141497, 110227, 233337, 136339, 489126, 80561, 203671, 106673, 459460, 54657, 377536, 0⟩

theorem ready37_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD37 ready37_cuts0 109 153) ready37_0_state = 66976 := by decide +kernel
#print axioms ready37_0_cursor

theorem ready37_0_covered : Covered (toCl ready37_0_state) :=
  ready_cover_cursor WD37 ready37_cuts0 ready37_cuts0_ok 109 153 66976 ready37_0_state ready37_0_cursor (by decide)
#print axioms ready37_0_covered

noncomputable def ready37_cuts1 : List (ℕ × St × ℕ) := (153, ready37_0_state, 66976) :: ready37_cuts0

theorem ready37_cuts1_ok : CutsOk ready37_cuts1 := cutsOk_cons ready37_0_covered ready37_cuts0_ok
#print axioms ready37_cuts1_ok

noncomputable def ready37_1_state : St := ⟨26112, 285696, 51168, 114688, 29184, 45301, 53248, 172878, 29666, 44151, 52016, 171646, 28545, 206784, 26112, 274669, 77280, 364963, 106464, 410264, 159712, 503505, 189378, 533171, 301209, 585187, 329754, 613732, 355866, 639844, 80352, 159989, 133600, 253230, 163266, 282896, 275097, 334912, 303642, 481881, 329754, 613732, 82432, 202062, 112098, 231728, 220224, 283744, 248769, 430713, 274881, 562564, 82914, 202544, 174923, 254560, 203468, 401529, 229580, 533380, 81682, 201312, 110227, 348281, 136339, 384896, 80561, 318615, 106673, 355230, 54657, 303214, 0⟩

theorem ready37_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD37 ready37_cuts1 110 89815) ready37_1_state = 152126 := by decide +kernel
#print axioms ready37_1_cursor

theorem ready37_1_covered : Covered (toCl ready37_1_state) :=
  ready_cover_cursor WD37 ready37_cuts1 ready37_cuts1_ok 110 89815 152126 ready37_1_state ready37_1_cursor (by decide)
#print axioms ready37_1_covered

noncomputable def ready37_cuts2 : List (ℕ × St × ℕ) := (89815, ready37_1_state, 152126) :: ready37_cuts1

theorem ready37_cuts2_ok : CutsOk ready37_cuts2 := cutsOk_cons ready37_1_covered ready37_cuts1_ok
#print axioms ready37_cuts2_ok

noncomputable def ready37_2_state : St := ⟨26112, 285696, 51168, 253120, 29184, 45301, 53248, 230341, 29666, 44151, 52016, 189094, 28545, 89920, 26112, 176879, 77280, 515706, 106464, 544890, 159712, 598138, 189378, 627804, 361024, 679820, 389569, 708365, 415681, 734477, 80352, 298421, 133600, 371654, 163266, 401320, 334912, 453336, 363457, 481881, 389569, 540336, 82432, 259525, 112098, 289191, 164114, 383327, 192659, 411872, 218771, 437984, 82914, 260007, 134930, 354143, 163475, 382688, 189587, 408800, 81682, 233245, 110227, 323165, 136339, 355552, 80561, 279014, 106673, 325886, 54657, 205424, 0⟩

theorem ready37_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD37 ready37_cuts2 110 152701) ready37_2_state = 182363 := by decide +kernel
#print axioms ready37_2_cursor

theorem ready37_2_covered : Covered (toCl ready37_2_state) :=
  ready_cover_cursor WD37 ready37_cuts2 ready37_cuts2_ok 110 152701 182363 ready37_2_state ready37_2_cursor (by decide)
#print axioms ready37_2_covered

noncomputable def ready37_cuts3 : List (ℕ × St × ℕ) := (152701, ready37_2_state, 182363) :: ready37_cuts2

theorem ready37_cuts3_ok : CutsOk ready37_cuts3 := cutsOk_cons ready37_2_covered ready37_cuts2_ok
#print axioms ready37_cuts3_ok

theorem ready37_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD37 ready37_cuts3 128 1) (ofCl (RC 0 2 0 1 0 1 0 0) 0) = 186190 := by decide +kernel
#print axioms ready37_parent_cursor

theorem rc37 : Covered (RC 0 2 0 1 0 1 0 0) :=
  rcOfC WD37 ready37_cuts3 ready37_cuts3_ok 186190 ready37_parent_cursor (by decide)
#print axioms rc37
noncomputable def WL38_0 : ℕ := zfNat64 33246 "lwAoqABkQAMaAHCwAISAAAAAAAAAAAF6AIV4AddDi6YAYJABwYHDIAAJoB0QuABzCEAATQAAozWjlwAkxAD14AOlAAj4AQVAAhIBCFAAAAAAAAAAACDhwAepAB0oAkjADCoAqFAAAAAAAAAAACHAFqcN3hguOhMnQAAHDYAA4JABTQAByAAPxQlgnJgAZiAHLwAFSADpQAxGAGFQBUKAAAAAAAAAAAFWKgIremM4fjkekVQitTHIVTJID8igHVTFScmlkugJVQrmHnCcMQ1IlEEijUWi2QkViChPD8AJMQ4nSHMpQBISEkG8IQAAAlagAA0hAAAoNgAAuQlDvAD0oAIjAIRIKQbUdAFkAAAAMdAAAAAX9+ABmIACnABkoAYjADioAaLABgoAAAAAAAAAAAT4ABYgCCsADOgARkABKgDwkAAAAAAAAAAAIm9DwAClCZpILh4SB0EH0oCAyZTABaAEH0oABQCI7AAqghAyACmIAqlEorYAcVABxoAWFAAQIEY6ABh8AABhAB9h8AAAABZgAdKAGIQAMuAGFQBIaAAAAAAAAAAAGHhz4KFgp_iAA39cEw5CPZMB+46AB1FQABLJgAA4EwAALkYQQUVFBcPCQOgB8TADmKgAYgCkDZbhMAAMQALPIQKgNSD7soIhoSB0ALCIAggBBAAFhEAAFgeAAA4PBqZjI6OioeCSaoBgISB0DbiYCvxMAV+JgARYTAANRyAAAYCKUnABiEABPgCBcARFgGAgAAAAAAAAAAANjbEdpwAcXABxIACBCkFEJDgcaVAMkLlZVQZIXKywnUGFlQAAAZAAAQl19CQnw4GClQFISoApCVFhOoMFKgAAAADAUADUuALSQ3CQCgSoCWJUASxKgsnUFglQAACUKIAAIS4zSIdYcApyheBKSqrTZiUlhPMI2YFoAAAAEIWAQiIa4cDZSoC3pUAW9KiwnUGylQAAAAC4WAbbhAARYAiBAwNDEELDQA1ABqACFhoAAAAAEIiTWPA+cqA0qVFVDSpUV06g2UqAAJoAAQhYANhcKJEU8eDVBcATwuVlJAnhcrJ7df9sx2guDqJQJKAAEIWAMNAQRcBhkhCIgBaABouVhJxqANFysrp1kQ1H+C4AAAA3UNAyBx8DHjIASGhAw4HZlQGPyo_urBj8qLCdQZiVAAAsDgAAAALUKkZhk2EAhLgaBgHoDCID_xsAf+Oj_p8A34iAAAAAOgwBvF4ADfADy4AkNAnp4CoAJKNZVolIEcnt5BZxUAAAAADLV4AeXA6FcYJiegFLgmoSU01VQB8_J7eRVNWesi0EIAAAAdCgdQwAkLA6EsSotIfQ8diMVYITFyssJ1BgpUasIgAAAAABFwYBA9YYwfBqJguVlpEKmjsqphA2FyssJ1MM5G+WLz+hcABxpGAAGwAhHgaCkpjQTrKj+7UbkOH4Bb8qLCdQYKVAAAADhUIAMY8ZBEEEYPhTcqLSDkAxyVFhAs7cwUiVB1BeAAAAhCwAVh4tUYPj3TBvKS0jcTR2G0JSWFerh3C8hcBdAGEGQAABEB5yxKNY0GSSo_y1DbTR2ASksKv3IDXlRhAAOJhAFbCwO1MCADioACTAEhoAAAAAAAAAAAANBWxTYGvcyotIOSTasCyC5WWE6g2UqAAXMlAADkIgDaGwNBWXzY_8bchKi0hrFCeAATTSUQCpsAAuZKAACaJAABtgVUsDQVDQ2B75UBfg6ANGqRbQHBlQAG0kgACEAEJMAwEA4SACwsABomAAAADCwAAAACDgdNQayktMUU4eZo7FkMV8d2mU6iW04mG4lRKF4ZSyC7GzmSSslUklmupeSpYAwJXNhoBhHwcDmsjB8Go3i5WWkCyaOyqgoIuVlVNIO+LgAPv_AwGAAB0KAMCLE4OBzUxg+DUKhcrLSD0HpFN8XBNKF5UTKRZzAQuAAAhpLloAAHQoHx8DeXYOBx9xg+DUZZQvDK3pOmoBNQwgCOLlYFpFocQAAOhQg4HMPGD4scwbyktI3E0dlVCUlduKy14FyULwelEA4axfAAcKhAXKMHxMZg3lJaRuJo7KqEpK6cQFyUL1OCQ9namUwGeL1sCj8VaDR60BcowfExmDeUlpDnmjsqphe6mU5SV04l2cm7KF9ICoe00skWUptWL4A9CUhkAIAkm2CTi5jB8HLlC8tIaU0dlVAuhcrlJZNoecLgKIEXFoCSAACIFkKSv+Dwlo2Y+ULwWjdrByVUFyFysrtxDPBcAAN9aDaUZ6ADIAaai1xg+TZjKS0jGTR2VUwkIUp8pK6kxy3l2cnjKF4USSUSCJSyMTaXadJwBfHEY9UpPAHjf0GaYi4KlYaRux03KqEpThSNSyaQQCULyotrSgCyHEAwERGLNgCZiMnGD4NReFyuw2kEiaOyqg8wwbiWu20CBlC8CiAtBcwWwADBLQABmIykYPg1F0XK7DaQSpo7KqD4DBuJa7bQIiULwKJPpKFpZJoAA8OgBAJ5kXyMHwoZg3lJltI+5QnlVMIBwuVgWum0sn2i4KSdECgs5+PgAAgkcRsaHjdBmI0ipXcTTTSymjsw1UE8pT5TTa7bS7OT7lC841FH6RPKoFnSicAAVODZgPBGMjGD4NSJFystIOYzVQZUXKzaXRjO3MIBF30k6WAho+DtZOIASbJhwAaJsPGyYi1JFdJNIRQ6bm2Ni0U0Unn+q5jNoMdKF5ZAm_ePgs3EsgC6hos50dgQEjPg4HNvGD4NQ1FystIOQcpXSJ4tSUXKym2mkzkBZQvCKXSCTQAAA6FE_BgiO6AYCBMLAEkmAIIAAI4hgA7MmAAAAAOhQA6y49g7bA8SVJZQvDKEUJKtGjGWdKienUwjmERcHSyDEI6AAB0KAMjo4EPvwS_hBDa4BgIYgqIeAGoANQAVEPAAf+MgAADAQCUF4Q3fCUqIJgYSgBk2AAAygA9oqAAogbAAAmBgEKrwXA1PSYBiAElAgk9OrBmDWPyLlYWRCsRZKTOg2AABcDB+ONjwNZSWkOOaOyqgVouVlhfK4dw9kXH6W6wgHsHmJBwAAAHmJt0eBrKRzaQ7Zo7KqANi5WWE6gJEoXiAW6wgXYJiSACMhYnRuEebkFYkNpSWkg6aOwihKSqmkAZlC8oCzVkCDpUANghgAAQHPQjzrg4al0KlZaRuJo7IgLEUJSVWygFEoXllrNJCqpUBYQABuIj9MA4auiKlZaSDB03CKf4LjxlCsqplBZJQvLKWSqDwC5eFZMU5VEDoAEmoAeLNLjwNRzFystIPE0dhFDWpUVU2hpguKanVaAAwgH_BYgZcAJNQUOWM+HggIVAf+OgD_hUAELioABAgSQG7jwI6KvMG7uShWWkY0dNwHCFwpKrYQbiULz8rNWQNuKRbTCB34WBHQ6RA2ZhaKla6ka001EJo7FpFooGCxWKR7VbCDllxcrLLWSaDqQiiW0wlUHoExAuR8GNyoASairuUAWJABQeAIoARQABAPAABEFgAAMAxag2zCA4CdMLA34iAGIBNYiABvxEAAAAAYBgAlepxMAWMyqvMLFYYQkQQHLIC_Dr+jkVTKFBC4CyAZY6AAg4HACE6nHgBcB_i5WWkG+aOy6Bq0qCycQEKULwpICYDoAADAUAL9WNa0jwNTbFystoTY8dm2SgyUoXhBOIGBKF5_o6pIFkT4AADYUB4AB1gFxkABHhmiI+KRqGQuVyW0iBTR2WbCCBiBrHbC0tw7mGci0snA0oAAAg0HB2AeGIAQjO0jwRGphCpWWkUiaOyegAIyXlNMIK9KF5RtJpEovQBhy3gAQcDgB_MQAHeO4HEc1FTFysNoMf3oxVLrDxZKJhsINVKF5hMpVJIRMOgAIOBwZgA7iADpwAw2AHmQBIaAAAAAAAAAAAADaRmkR73JFgo2lJtVQ3aygyWegnIuVlNsoWqLiqWUDurMAABsKDMAR62fHRSx4FxHQFjDoAIv+GYLJOQAAYh0AABgKAAolAAzIAGXABSoAGTADxoAGLAAAAAAAAAAAAAP49zGVpEINtlQDjDiGBRAsk00lEKphABKR0AABgKASVxAAUoRJjE6GTsL5kwAtADCAC_0YAAYh0AABgKD9lKih8D5DYIIBZJhmRhNpNNINsUgABiHQAAGAoASePIilAA+CP5UAXQDdS8H0CP6kEpAAAAMBQCiUK7oEB+TkyRUrDCFUKoLX4Llu0k0wgwpYrmGq02mB0DPixP7xuAAB1TTYIT8DTFyssoApWpgDKF628Zu11GTi8CrlauAAZckV4EcgACiA5Afz2cpQKlZRML0kYqlWmguSheWbSTTCBiliv5JeqpFsUdAJTDi0A1DqAIHoihGPgTGQAsIgA6IwBKhKABAyEABXICAAFIASRZRW4eQ57OZSUTCDsWK8mFYqgtLtpJpsmLH8hCH0Klsw1Gm0gOiai0QIBOkmIEVFEtpw_IM5QWUKwwwiRv8K1MppKSyaabWQM2oVyq2qRgHRjh8vixfuJdAcmzHEZNzo9CxXg8fAzkoX_8WgOAqWwsgXTSTRasGsNSLQAXUAAg4HAHBhMeDxoLZ4IASYhtmUAcLABoiA+wjABFAAFhEAAEQqAAAwFBqU4IGQ4gA28YoEGggwVAbgQgAcxUAAaCoAAYh0AABgKALzfADq4wCIAvREATQJiAAXoi_05AAAAAYCgA24RhEUAx4KZlRaT_R0AYzUg4nUHVlRxIoAAAAYCgAsDNXCKqo8DXipUW0AceOywgKtQrlROoZCLjjTa6TSigjouAAAgpnyxEpEeCmJUW0AoeOywgKNQrlROoMHKjj_dOroUUCLUQENjwNgMGDh6CAgYFfVgZ9kIIRHwayktIl00dlVMIVUynKSwiEcuZhnIOC5XVbbaSioGugAAjBgB3tTfg8dRqHAuVx20g5LpdDq0Y4fzEwkWdt4L9KF5pttlCio8NmYAALgYAkCM3SRGWezktI6A2ZlGohA9Ajk9qITEJiinleMICCWjeAACIGAKT1B2sZRAl6ZBVCqAZUPgAloVAABhKgAAXAwCg2IAFjBgrb+h4Qs3AHSoMoFECw4EAzWVGkAGHmwAALQYAAPU7pUvw+CGRUBi0yACycSzdJ2AAAFgfAAArBgAm8ZzpCqI4I4hk0B6UQBeHkOygEzVI0gA7UyAAAcDAJkxyiTm4GwJ+IgP_JQAAAoBiAACIdAAA7CgABdwHbHLNWnofABVP_JQBrxOsoAqZONIANsMgAADAQAAYPPRYvlgPIdpJVKVOESNTSY0EJq54aLmUmmkDgqlc02GsgOuPnYHEux2MhKhOqlsHSA_stFHymU56TSS74yZzmRRsDUImEkmUD+K1Mwl0AYkdN6yUbKFJPuKGwXnRQS5bY0gP7TRRhKVMm__UK4NS6FUgoGyl2_bMH_bOZZNNhAoq6jZnTQAFuJE6DhcOHy4LghtmDzuOdCaRY0ESSICagAhhYAAYkQAAXCoAAFwMIOKdhG3XXwaaaJA14eAFoAKQABAPAABEFgAADARdlOLg34aTjpOYhszX18bU15OOwIDHh5PDxIa"
noncomputable def WL38_1 : ℕ := zfNat64 33247 "BIAAAFgYBSOEiAFoALQuMwmoYeVAAF6GgAARAwAG0IEZLeWLw_2dSkMlldorSkQAUdTrWf9nSbSxeAAdkaAAByFAAtQigDgjLWi5eH6zoIRcrAylUIBcrDqbazOTXFy8AAUw0GUhoAABghqAnBGXbli8JzKQMvPFaU_1OjqbazOVOFy8AAVA0Q6GAAAAMQgftGs5FwCgC5WFlFAFysOtx_+tFpC4AAOUHIMIgAaDEAMeAUeYNg4IzdcuAEHC8nEPBtN3KQxDqbazVZKFoAAphoDTDQAAHtmAAoQbBwCYSoGITQzwzCPSheHU2gbEqAAFMNAaYaAACiIQbBwGX_h8E2ISVCIwbhWWOIwtAsy0BAXAAMomFoAAPRIAk6EAEqgF3kx8E0M+YNz_o0XT0RcBhkoAQu5YTAAAaYaAADxIQgh2+iYLqNToJoNQ_qtFgC4DDJQD5UUEskUM0rQGmGgAJ6XDPwTw4A3pcA0sqAGllQdTaB6SoAAgREAADcSADWhAMJITw6MkZdyWLwnMpAyYcaK0pAugIYrc5CkXLwABuFwcQUgAaAXEMkE4BfZUBQ8qAKHlQdf_NwL7KgANfIQTTKBMgmACehAAPlC8CUgXxmxkpDqbaqCfKF4ISiABk8hysMiaZSyGUyYAdKGTg8ALQJSBlJSBtDAxVz1RcCEogKwQn5RJskmYsg14mTg7HjYzOjNnhgiHCAYCAZsTAf6MgD_RkADNiYAARwkAAAYCAoAqigF8oXgSkG41ZyZMxKQ4nWpjMC0LoHQAAABIGAADhAEhprpGCUJUB8kqDSHySoNtxB1pUH+FYDJRUAAAjQsRRXpo7XWULyigpLCYRURUrLSG1s5mED6ULzqhkVQBSAADYoXgIoOE0duBKF5RQUjambGYSiMsoVlpOJhnJEyheBVABKSK3IEwRQBKCwAYFYRRwR0jUoXlFC6lCummWwhLipWG042EHWULwAII5KJbD6igNbGhOcaAMeQwRKULyqApuphCiKSbZbaYcenRiSheAAZkkV1Ey0jAPSGg7HZkdJToA4tqBHJqkcoXlFnJOyhWGWwlEtBUrDaJ9w52Gci0HoAcEmAACWFAAOKgAIWDgcqhIjgK8oXn90YTuUKyyguZsZKS0nEynai4AAACoAAAQsHA5VSJLAIZQvABkVKyyhKS0nE77EBbKF4EUsg04mACoASjFyJLAT5QvKKVeKlZZWcsRKS0nFMLBnBaD0AMETAADWCgHgAgWEkBaBKSyxSZiUlpOOwmY5sXA9AAeEyuB4qgDcDYABxUIpGo6bm_KF5RZyqMoVgBmrPYSUlpOMombHOScli8AAz8bAAAaiiSwKCULwNRFSssoaiKlZbTiBFyheBV_wrBA4m0AbAABLNwIC8rkF1oCvFQCsioAVkVAAV4qD+z8AYSABwAAACiI75ElgLQCCGkijMI8LlZaTifRmLkFwCQKnECABwAAA+ioAxIjk1A8XLwWhF3BcrDCUQQ55DLSaTKWQ5li8BIHTbHQgAcAAEJKIoCkKGTV3JQvKLORSWEwmuUp4pDTbTDOWllC8Zxo7JpZLNfE4H+SKyaACexQ2DCIzzEYHRlQHjSoA8aVFpOIR9KgsJhDIRUB5lYAAEARAzBFSgUSWBOyheB0AqVgHQCpWW04gUcoXgZa6G2SoHoA5AApCSFFxFEFGw_SheEUFIUfyHQ+EoVlpMLh14NKULwk2EuhbFYegRAFoApyJLBTJQvAFIAKS0recN4KZKF4eNYgBj7xKLNpAaOXAYjMQoYPkLlY2hGBSFEDopLKlBgvg2guV_KJqTUQBrD44flm02GourWL6wjJeBADKAIGQAIaBCOgA0RAEEAIIAAaIgAAXFQAAFiINR2ZExsABXwWOyRdKHQIwJgN_FQBv4qABGBMABpQuAAAsBAEyYgPeEah2XgAAQFRWQxohFpAQEVAABILh+BwAAHgANGABGRiyJLAY5QvpoPaMG4aQlJhtJtNAvH2i4LCXQukfECDgAAABYwKkyADDQAECf+SgIiUL6aECDBvYaKNQKCLFdttJ1D8hcFhXIwXwAADoGYCXNQDCyAXUxKTNGA1ZVMQZInSwAUlptoU3KsCACGyheKQAVIjCUj0ui+C5WVQFIYRaSlPFJNZUxazaTl5JQvz4ULyTURvHQCn_x0GElQjBOECOYszUoIpqaUABiWXFRFAGZQvAlJ+hg12ElPYUq0nFyrBnBaD0AGsTBkLIAABpGKsSI4KZKF4ApEqMGsBSTbScQIuULwGIC5DR2MSaVQM1FQAqjIrpIjkETGULwBSJeVLYCkw2kygbkoXg9GItDnQcASaVSSDnmhkASuqC4eFcfA_wqA88VAHnioAFfkwAH9DoJaAAABwgFdkYZEZg+AAo0hAA1AsgwY6AAa0ZB_pSALslAAdsnVImvHwMGUgP_GwBrxGAsgAAMIMiKABqkoAAesCyshB49GhNak6BbycB0guAKqAAFk4AHoEUIoCEEYA8DMC+ugsVmRRsABYmAmoBNf5pQBKxOAAIIAALkYAktkHoLDSgL_GQBroy_2nACw0oADXyMAAC5GAUwtAr74NrZbubf4OgAY7AAAYQAcolAAZGNgAAUIQCX14DHhAe7YH5ZlAdC4OgAAALtRAJ5JwAH+j4YgASpGAAbZBRwtS0b_xUFAVIDaSJLAFxG3_1IAKepFUAAIglAO8xAAIsgFMUGqBrkPvyIQR9UgP_FQAfQABGpWEAAeikSgGISgAD8wARiAHKQAFCAHGQAgWAFiQAAAAAAAAAAAADS8E2Dx+Ph6FVVYCywUAU4Rv_qR_xeBc6kaQACCJQBtC8AOvqBNXwacmAAzQAOO6A6HoU_TgAAAAKynAB6BmDCS0A8gIuSscPiCFAFIAACohVCgCkABtJCIuyDqWgPmSgAJGhzmai096hXGJTg4WTayMQSTSKhaiNZCfnUXMZNnNRLo1INFGpJQiYNyCJZaSRzPR+KU8AmwvcicAu5WArEdADEHomn_mIF3KxZAACoHQGwLwvOhLMPIYBuWK4AhAD6TRmrRZAMIadGAJpFAEsU5aA89MpgAPXgCSMAhCgAAAAAAAAAAABO2oBTTN4dAAjUgHXGjMAvoAQpQiSAFNDJZAGGJQIIBLoURWptUMl4MCKF5FAAiJDQJNqpVAc6FHMpEhCAFIeQyCQR6BBU8pTwANr53IUHnoKiA1ABAk0LoXzQgvKnAekRiKS0CficAFlmL1QpnEog4hwmRQIUpVyT_wyCafSbOSCD+USWXQelTk4QCJLIJJIotJJFIILFKeCSI0MYLh3Ko0sMJgC0A1SZTu+7eySPR6AWSegCESI5FIstCbRTZKU8A3acAHS3IQjyAAAASQCxYk5JiABsiJLIpZDoGsE4BoRoZ1KqsG7uXUMJkEMkpJpJG1DR9Jzh7JNBFIAEok9Io+ZGj0UikUYj2ikEuylPE9kI8gAFILG4AeaaTkI6AAAJInkUFoE_U4ASRoZ9KoEUNtkysAWmBdPZJpolAZYEfLIUNKfgEUikUYgQWxplMAANkJAKgoEsALjgAMEqykXQAAkFwADRaAAAACqB0DdrcACHmBOlxGK1M6_wVgUjRDAFoAeSTVZ6ABKoANEIE5JSgmV56FFKIAFOYPYjBQa+XBIAAAAAAAA_0oVwaABxUIABCUACJgVI9upAjC43axKKJPm4C_yZWBGbjMTDKQDGfT5SRkAAjkkzn+p8SaCLdMpgApWgKacAYPh2JEb1GbGKQnjRDEIRWWh_oCPIlpIBCAjEmIBRHDWOSLNXUHVFINBAAVnNiQIz0NmcSikzJuIQAIH9FY2zWumkOqgR8YhFAbEuZxyRZz_0+CCRBGhgA95gExUtIHMaIYFVADKB5AAikALCLSbOQJmoEcBRGILs2fgEXzJkBBMsRnpJA4I4DGoKk2ArI5IM5AguwRoYALj71S5mVZSv1GykGY87MigzkgyFEJY_QCvY5qOQCABGs1Esx7qVUVh6VDIJBnI9IJBBMjQwAaDVImz8qlURAhPxqBAEaGSYqJw59Mt2Gg1G+ghICPjUiz0AigEAxUIx0QrgJkYAibM6iVbSlRCf00Fpk3ioKTp_UabaaLXaaSbT0NOrLgAI+ZaSMZzKaK61CfmEmx2UubIj4lgImNRAKoVyRs2tEiE_mM1is9amhR6baaKFdav0Ek2mjadWWsAR8ajmazmU0VhqE_OJpsNZrppwIAgFDmAZ5wMe+AEWwHiuBfz2DFRlAggEUAsNhAICAAXQADyAI6Xh4ACI3kwmESghPzCAwEaGbReAFyE7sJZoJJBoIEfKoJQIdpUMkkEcj0gkELCNDA8PAJ1F2ZQrCYpXxKNTPIYxBOKpHGITkgjEcjEDCjwMYhFCyhEduc1II5_wfEUgqpQIYQgLa26YmTmESi7zyGLQN8rRwCafRiZaSEBGIRQL4LWMTB03Io5P+IxBYgjQwrAHm0zxMnHqcPxKZVxmz+Wjk+2EYlEaUfT7SMSaXQSABHxjGFIrlEegSSp5lrs1Ho9Ho9IIHEaGHoSbj9mB0+oACvLm0byKDlgI+ADBIhgB5AigAQPmdAEkwk9AKIik4AB5giVNdCNDOpVE6NEMghGSSANGG6byTOBAfh0I6WQDygUC5pOJo9CKQR6EdKFhYKbgAFeAQ5R6I0MAzx3KoE4cJkEJCACEZt5VOJJADSwDKIPQCL1ROJoxCTRTAKU8NQUT5GhgCcNZVD7_JCALRwvAKQoWz6SR6SQZ6EAwJLFMJoBFIpFHISSCpxSngWABuolCvAENYjVZADRIAMDsopAAAACUAAAAmgABUgNLmD3W1jIR5CWSUAAakakCAEJAAm8nEkAFjJwVgAxmABMQBJKAAnQA0yAAkwAIaACCwAwSAAhQAAAAAAAAAAAAEPMA9Xh1B94UBRQC5j0RQCwmkAPWIwxABWaUAARfMgiPoAA5AD6TQkgbQABPIksegtAncnAQxUjRY0cySHBGj4pAAgJuLraQSiOQwLHkh+RkCGj0ijEehBZcpTxIbKOXfs2tyhEfksx0SbU1xR03pp0c6b22gl0gl1wIxkoZDIdocJD4aPaLMZ6RSCMpSngSAAV4AHlAcrqSipGeSaJENEfuSIFaDSMAtpZDSGBHono2ACJBJo5CitiTKYagCFeAAkwA4eAJCQAAAAsgAAAAAAA4AaogXs81BUjAI8cyaAKNEYpAW1UMhLR9JtlKoHbdwZmF4ADyPaYIwxAHoPhYeAEOp9PIB6HCYAtAjQpH002UihgQnoFwECOXSiLQotiEymB4AFXiETpZpKoff5IwBSOF4BZPpNMLhGrOGBMITQCCRSKOQkhLRIbSFCeBceCoYSG4oAPXgAqsABSgBqMAIKgAxMAEEgB4UAAAAAAAAAAALuJBUyEJiiNDCnisAKQBAk0Z4vAfQAByRWzLQtAt8nALNg4AEYgBCUALRgAJcAKKgAZEADGgBwsACEgAAAAAAAAAABegCFeAHXQ4umAGCQAcGBwyAACaAdELgAcwhAAE0AAKM1o5cAJ"
noncomputable def WL38_2 : ℕ := zfNat64 33247 "BIXAEtAASxPKSdaagmkXAAJ8MgAAXCQAAr4B3LDyVFjHgL6VAABPEKGWUAL6VAADiLiDEQAD2yhewgiP_2Zq45iSULwCCT0oz0ZxIrsNJSUyayiMzLF4ACoC5eQQyAc6Fh1wuR+OI_4qw5X8XKye_0ShqA3hGhjkpptC3xcAA58sZkEAMfCwAHN5zypC48CJSonoAT0u2zATlEpUAAW4qAABaJFXfjqKZjuGAAb4AkLAsFAYDgAAAHZ0AABkJ6AAAAAr5UASFigDgMBwCINgAK6AIFN68GGNgAPgBgsAAAODAwBVLFAHDkGXFwAAQQB8NwMuLgAGAEwGEAewkAMiWBYKrUvAYkmAAP_nQABiSYACaRMAA3oiADCJFAHF6YgNcXAAGXUIA2gmQuAq1UADyBEQWAJIDFAHd6Vj_xtlguAAMpNACgJwA+tk1gAKa6STAnMLgO8OKpMRaAOQH1IT8ajPESWaRbiUw8oXhGRmCqGqPHYKaaFk4zFJgAdrxQB1vlomNVC4vsNAJ6GkEYCsRcAAEY4fgppoHGEZMBQBxVA9JQvHZNQOE0dgUGYhJtIE5KF4EFZNYDzzh+CksgQpJi_vZMZAQFulAmaoAkLAsFAkFgM2TAABtAAM2TB_BSALIAAAAEuDhjxQBykBolNWC4AAJoGYGoN5mQaS6SQHItwKAAAwAOnADDoAeXAEhoAAAAAAAAAAAAU4uKAOCYq1KgAKBEOxHwNQQMG8FjlQSkmllIDkAADmSgDalx3hyAkYmOWS4GpJAIj0ijMLgamH9y1OQgFy8JSTZScW5JQACtk4CQMGXHeHB_0yOEXLwemLCoCPbD4ikEGphLIJ4uXhKSaHEsyUAArZOL+Nn0ONJQJfLHiHepFgNuWLwALJNnIBlesmUynJcHELIDRiAApJQVJwBjyx3hybyheAni5eAA2ZUnz0AKo+ssXgAPRaABUkmABdLAsFAAVJgAAZp8AABZCAAD_EEABiLgAUywLBQAECYAAGWfAAAQJgAA75BAAYi4AwAoLHeHBKeLlwABDFAjgW0P_lwcai0lCKLxlaECAIeLiDAB9kA7l_3IgAOFQAAJ86AAA4VAAH+k4AA7JwArS4ACLFEZLwyqVEgLgAAAM03ALIuACegdB6Alk6B0AglwKA0SlnBcAAEUATDlvBShd_ZCAJ6APfpGQH1PiPAJAmDgsmBMlg1GGWLwAIpK5CfhWTSGrS4AJaAAL2RgDAoQAEuC4S2ULALI2AAACwgBo2CagMwOH4CX+aMGCj4AjZeDQsdQqJSYYuXgBVSqfBCfvZLg4mkqz13JYvCazkDIAlooDePn4A0i8GhZ0RMCkmJQvCSPc1lx_5WLqnkMLaaQc8XAAGQJCQQtQfB_YjIATSgB5cASFguEgAEjQAAAAAJGgAAAABmdGwAYnABzoAkZADy4AAAAAAAAAAAAu4uCryx3h3mDYlPCS4AJyEEKSwNs3hnkuCQzkHMtMCVSqGBA2bw58bm5upAXi0AhLgSBgCwIwFkAFqYS4AAFjwAAAAB4GAJwnAHS4EgYAhxsFZEIfPwBaAYQAsbBBAAAAEIMHoGHPgBZcAXgbAAE0ogAUwNsIB3JkIAAAAXBQBhz4AeXAEhYoA4BeBsAATf_KQAFMDYAAAAADDnwAsuALwNgACaUQAKYGxyxCADPwUAAAd86AOlxQBwHxS4ByCwuAm_mOG4AC5zBuEEAAAAPhQCOj4AUXCeLACCHj4TWYgTVXrF9ThkzAstBmIQQAHwFSsAAEdHwAguC0OAEEPHwmsxAmqvWL6nDJmBZaDMSggALGKk4AAGwPgE8sABEigDoIPwIiIgmoBJAAu+FQjpmwAAAEMgBgNgF2nxQBzcEIkr8iIJqA1JJZBMXAGmg10NgAE+GwAATyojQSKfFAHFoMgMYQHwmvoDICSWRiAaaCMg0ZmBAIoGx_YCGICQC4mRsbrR2bqTc1HQAKlAxq4GgYP_HwDCIAA_4lAADsIgAEBGwAANgYACQ0AcLABQeAAC0nwAAFB4AAHZEAAAESrwNA0YiYnrtC4PJBGIBXkYmgbQapMLjAoTat4BJAABcFAtKPA5R8XKy2uUVh6BQSCBtCCRcFm2oBHhMAAC4KAbZfA0FA0GgoETAEkAAAoETAABIJgAAXBQA0FdBHgcyktoDg8dhZKwIw1KabQxAXFJ3K2gQGJgAC8EQOOjwOQcFystoDg8dhZI1Iw1V0JU02heYuLjbQIlEwAALhIAEzUI0RHyqOQIFys0u3a6iOQsgfEaGNRjTTaWW2GwtLj_tq310IlFCcACDgsWaogSIj5inDeOTYFSstIfg8dhVAGI0MamWmm0BVlC8e3Ey66VgZ4UJwAIOCwATGpc8eMI5WwXKy2iOjx2A1NCHJ_VONoa4Lq6WkDZ5cYImAAAGG1KzjxhHMjSotojg8dgAEzR2ACnSqugACksXl0ADniwOgAMXqgyECQI7SQXjFSuk2kJ8eOwqjv0CONVtrVNNoC0u3E0gW0JgggAN0GQByBHaegIUmCpXSbSE+PHYBBGpTTSBvyheXQANaQJyaYZw3m0DuRETeKU4oCAW94GgoVA0A2yYAA_8rAB_5GV+bAACBIgAAXBQDw4ffhzY8Dk1pQvADIBfkYYZgzKabT3iMLQtICwiYAAFwUJIIwdR4ErlQAZAMAmQXEErlQOBbgEPEwABeCIB4ayPA5KyUL5fBQBkAmJ+lONo2JGz4XBs1q3gLgJgACFJwIijwOYAlC+XwUAVALuhHFMGZ_VONoATKF4WkDSxMFkugIAGgbVZNn3jiMHLXShfUQDJQX9LVBGJTTaWT_oEdJ5QvLjaa7TRLxQnKLSQHumDcABI0bKPA5PaUL5iAZAVEjJnMGZTbaEUWlEibkZQE2EwATQIEBMgwaiVGx4HLfi5WAJMUNhVKCMSmm09MjXgLg6tjZNYAD0WhSSyACRGAHAxyzkeByfkoXgBkBaiMMbSPXJuG8vgjC0wNtKaP4MG4AG0BFk6PA5aKULwBPChsAigHMGf7m6mm0rsjF7KF5gbSU0hMTBBAWsxBZgW7qAJC7aYgiAnI8AAAdi4AAKDwAAOyIAAAFoZzeIExUjiMHJTSheEtDIQSyRUjmDMptxYouWyKEkoXmB+qwXybTQUk8kIAwgHgcdiCuWRXY8DnfRcZQ74PABKjRmJQ2gzwuVm0AByEEBajEAKJAn6GPFUciKLlZtRYnAAh42BQRiUaabSEyMp0oXnW42kppwImJ5IQBhDBqUUA6iz5HxbRxGDkpZQvAVMOGwCKMQKoYbOYRWilC8wJprtNNIdFCeIEeykNoAA5SA92QEeGACkKgEBCwAdQyNIAWoqjIARBUg6f6PgAAVQt5xkhUcRg5P+ULwAyBWl4i_wMmYFTaXqRkelC+mm0012mh0bM5NAIPZSG0B0pk5MdAKPEwoTHgX+VBUBCBfZCROZAAf8qAAoUTDk2_+WgKKEQFaSK7bjwOVKFysCKgXcRoasjJmU02gRcoXgACUanE8jdrABiOIwdAEqsnSPA5ZQXKwAqSQIqETBmU02gusoXn44I0h8U4Fo5OJpsCxccUqqIQCA6z6SoWAkxEB_4aAHdGwAAsIgABAkQAAHhoCKTpZRxw+NRzKSSJfJgrcSqVSkIT8YlNCIyayqJpKF5dLoK+ThbZAnMJpNIUQEI4jI87HZvBAQ8BoGZiPA5tUXAABFFoBwJCqkXAAECJgAAXBQAwrYGgZmI8DmEJUE5ADaAArMqAAIETAAAuCgJCSuBHUMBZJwVk6BL1wNA1VAAAJyAYQL6bAf5Jg3AjAAA2BgCMpwHI6AB1wNAy5B4moAATkA8gEk2CqgGkAAEQMALROACIwHE6AHGQtA0f7NgDmwABOQDCBdzY+WjAAAADYGAHmnAODoAkLA8FALpNgACcgGEBdmxZVGAAAAAECnANzoC8XC0DxNWiGQABOQDCH6jIQ0UCelUHQUPACAAAPicA4OgSRcAwUVYeJqzIyAAJyAYQGIhJoH7T4qgJAKNCFIAOR0CHEgGClODxNQAAnIBhCFxsIaKAdXWgUgDTzYAQEsnAGjoECXAMFC4HiazcMgACcgGEMrGQhF4lRwB6VQojEKyf8eJmbm6kDQwMOnAAboACXA0DAUwIgAAc5OMgDTQe2FwSQAAaAAMBitBdh8CgrgaBgTKE8EvPjIKCMQkmksoSMgagdHoDiM__AXyo0EGoAANgYAxmcExQgEJcCwN_wmAC5sAAAf8egFnFQAAAACIGATMfAA64Ggaoh8TECHKEUYuB6aSyAf0HjJxEFVANIAAIgYMQAPzADD4GgYAAAAMqHwADioAAWCMAADYGAJEfA5C4GgYGCBHBq+EuCg5QMggmksgAdE3DiMJqBAGlkAAFwMRoHh25qBsloVNXBCDLaFgAqbAMQA_8XAAr4iAAxg1AAA2BgADoQQgxLCYLLlwEm3RsAAeTyAZDICMt+2fAbJ+AABsDB6AAUYDOhAQD4AWTIACOgAANU2D_JcAfFeAABsDAD0QgCRkDa5kSEqACOh0AA6F0Niay0CAjMAADYGAHohA4HxMaqlwAR0OgAHQahlWhCmstAmguYM4AANgYAbiEBkPozJgQeZAEMgAjodAAOg1jIczWWgTQyMmMAAGwMFJTHgrI+CYGKY7cxsCFHAApItIIBkFo5g0ZhJloGPk4AAGwMGJiT09OMgBMSFIGBCDByAuAk+ULwspJ8oXgeQngXAAHUCgAAAAokDQMn4OAZpYvDrZ1KQspKQPNl62dDNLF4AALAoPkDQAEKBSfA4FNlQEcyoAskXKwPIKbKgACaCwAAZwoACQ0AMGWLx0QlOQ5FysDKSkDzeJmzzkXZYvAAUWJAAAAEhoUMQLgLssXlBnMpAygvi5WAunjuZZygMsXgAKLEgAAvwfRIC3RcBKQsubFaUk3Co62Ut0XAABVFgWwVAABqHKWDCYC0JzKSsicZsZKSynVGbBnnIXSheAAnweAADOJABeLguDnUCQIDLF4TmUhdsJKR7rVjOplnITyxeFdKIALSKgAABZkCIC0JyIIqViSli_YQQRUrLCyR252GcgZKF4tACM2uuhl8iBbBUACrwkNgQHgNUoXgSkAlJVsppXDuBtyheCB47lproCEFsFQAFNOSmIARFgmDgBaE5H+UKwsIm4qVhlVw72EIyULwMNZCF44jBqAVu5mkEcCQABhpxkOAWgSkAlIAEduYG3KF4WGaq0BvCI+MTycTaEoRIAAKUKscEB4G7KF4ApAg+qIhSFhIIncoXsVZMYUSKDuixWdQ0gTdJjQD7soLg4AFhEAQQAggACwiAADENAAAaDg1nZsZnQ+ZAEJcDQUAAwiABMRAAJiIAAGEQAAAAAYCABCXA0FNkZg5cXACSLlYfxZgSRcrCbcbKcyLgAAAACIMRoASGgrEIEMlQDmSoAcyVB_52BDJUAAEASAAABYGAUjhIgBaAC0LjMJqGHlQABehoAAEQMABtCBGS3li8P9nUpDJZXaK0pEAFHU61n_Z0m0sXgAHZ"
noncomputable def WL38_3 : ℕ := zfNat64 32208 "hLgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADSAEEiAYJBcArYWAA9hQABILgATmDAAABgIiQRIME6QYQ5cAHsKAA9hQACHLgATmDAABnAQGAA4yACjQA4WAAAAAAAAAAAAAPMgAY0APFgAAAAAAAAAAAAND4iQYFIMAXjIAAAAAvGQAAjw4AARIMAA8yAJCwAAAAAAAAAAAACRkAAYLAAuCgAFwUAADBYAAAAAMBAAGPgCZkAeDAGIyAAAAYgGIyAABIFAAAZBgAIHwBIyCaDgAubAAAB_BiAC5sAAGYOAAAMBAATMgPw4DaFwAB_gyAhUtAbQuAABgFAAAeBgA4nwBMyAMCgIGbAAANAAIGbAAAwCgAAPAwagBMyAlDgHKXAXyIgC+RETEAcpcAAEUKAABSDBfGgBMyAPBg5EXACkLlYWUFIXKwPNlOQFwAB1AoAAKQMV9eGzYDocABAmACUHAASg4AAIEwLyFgAAANwMA3BSfgYESFwCRRoASKNAAyYuCwlkFyjwAAiQYJQA0VAwFBsCgAubAAAB8wyAC5sAAAABuBgAQrwNBQAFzYAAA_BwW+MgB4VAADgFgAA3AwABkoAafADy4AkNAAAAAAAAAAAAAHlwBIaAAXNgAAAt4ZABc2AAAAAAARcAdGyEAMxkAAAGlzIAzGQWQAAAkIATC5FDoAC5sAAAFtjIALmwNAAAACodA6Ozp+BgCI+AJDQAAAAAAAAAAAACQ0AAubAAAHEkK2xkAFzYAAJ5MAAAAQQg9DgALmwAAAYbcGQB5NgAt0jAAAPQ4AHZ8ADrgmDkMGQAaNgAAAPIAaNgkoCKEoAAEwcAFZmAJDT_BMHUuJsAAAb4Qh6AFzYAALR0AAAaDcHPxVgqqiLgACNxcAAlYuAAovwPgAA3BwAKD4htUthZIQXAAH3S4ECbYSIGLgAqtYD6xwsAAVoARQhqBolJeC4AAAIICSi4AP4qlOrh9YwWAAMPDHwAgNAAcmQAAB_5GtwZADkyAAK8XAAAAIEI0x4ADRsAAAFW3hkAGjb+BsAB+jYAAQY8DoEFQgCM1CREABc2AAAC2xkAFzb8ykABBNJRAEKEROzs6AIT41g4CqnQeTYAAAP8PQAXNgABiDQAAbgoEsR4HNEC4AABVQUfUVgA0bAACbFgAA3BQhgZM+DsOQIWtMgANJ_VGBAk1JWmQACpBYAADIMACEuKAORoNEpLwXAAAFle0rADkyAAAAIMCwAITICMeAHxUAAROQjaScAA+KgAAAAUAcABMWKASfYRA9p0XAAEPkIAAJpUAAFQSAAAPmIj9h8oUqAAIoIQAATyoAAKwkg4OAAAoBKIxED1X5UAAakQgABBlQAB6joAAUAkAA8eAcHgAyTAAC0EIAWhUAAAEkGgAAgQekJPdCFwAAQQUAvDPiYbcXAADVcxj3VRcABFAHgiRk9PuWLwAnJNIIF0isYJFZzEuAyQRiM3XMY994VCUggCXIgbn58AMDQUBEjJ6tMsXgAE0ghZXVIksUjSy4QgARkWBCAABp2uejoFhUfaCAABBAP2DQKMqAAeyXWkAF_FwGO+SI4kE0JQvAP2RATSCB_46EJBOMXbgPgA4iNWnSR8AEYLGYACJtIjKoJEf6QoflQG9iIAg10AEClQAFiRo2gA4guGzDK_JEcSCXcoXgAYiTiCKZQrgB2g2CLgAJhjQBmbWAHsDIhyvFnR2dG6kACnxMw0SknxcAAAePZjaGQM5ke4OYcBAE0AAFAHACTPgLA8DAUc4eADRsAE5+4RAB5BfxsAB5EoAAoA4pwAHdFAHB+GhJZUAATQANoZAslQAB7DIAAUAcADSuAEVQhBwAFzYAAAQP8n4ALmwADeD4AAUAcALI+BgKMwdAZTIAD_RkAQEAVJsAAewyAAFAHBiTgAFOACpQAw+AAnQCEuBYKAAAAAAAAAAACwUAAe6AHFwOQeAArNgAADTDR_RuBnBcAASQABQBwBwYAfugAJcG4cH9R4aRkAAdASAbYybtLgDiGFECA_AAG6HE_P1oDhgICuAJBQkhy_CID6lQA7hIAggH7hoFGVAAU2QgAAAa1cJIdJQiBd5UBVIiAIM1ADJBMGVAAHCPIYAAog4Ac9cJIcIRk5w_AaULwACaQXjrQDUMylkxcB_BeAvR5DAABGFADRrhJDhCDZOH4ESheAB7hOIN1i4BqGZy2IuAALgeQwAIOBRVg8qA+D4FPXCkHBOftmQAAAfgepCA7MgACCHD8AADwMAGo+AC1wMBQ5jIB6dAAfwMgAAIybAAWQAADQMADQ+DNjwNhQNBoAFHwAAAAJIOgAByAAB8GAMACnwAIuTbHic1OLgAAANvxhoA0bCBAAQIRDoYAAABeUCfuhCDh3DxdE6AA+8XAAPQAABdnwAAGAoABp8kz7Hic1MLgAP2iwFlNoZDEF0bipAnEKzvJGAAB6LAANPg9Fp9jxOamFwAH7RYCym0MhiC4QJxCs7yRiNxUAEkAAZ8BjlMseJyiguXgARUCjZTaGRhJcIE4gPhetkUnIAWgaNgA07gE2MC_PgE5cABKmFHREA_OgAADAgAKfoQQAaGI90fAAAACuhGOpXjxOagFwAEVAsptDIbYuECcQrOXEb8iEAPcWgDwCqfAAy5x1+PH_zqwhcAAAFxyDaAGjYQJxAZshVUAEVEQACc4CZdPArOLHv1D0556XAAAEUsm0FrlwHEKz1pGCKAAwGgBGowAEq+heD_50BMmAAP2OwQSyArc2AACQfD4LgAC1ABbGGBqA0ZAQToAAAkIAAAGZiT4rfyLgAO8fACZx4AaPgKBc+ZYzp+PE5RQXLwAIqBZTaGRb5cIE4hWSKIQAPmWMwdHbMBD7cCMHwmUuFtVRIhwBA6tQuAAAPkLF8ACulUHWtIEACDQcUs6PodaAIUIAmfAMBAAVNgAAAAAqbAAHkAAEQMAX8+BgKdkjEwzYAAcgANPrEQP42Cg00KCLQAAJgYMScns7EdpwAefABhIJgYEIMAAAABhAMxkAAEQKA98FAAEwUBoGAJJMAAaAUgAA0FQAAAAKAKABCXxYTAAcKgABNSkAABwqAAAAAbAwAEIlQBBCEi0AW0shVuJUgIOoYBAAAADcGAAkjAFgli8KCygwXgYf+KRxA4mF9CMcwuXlKgIACaJAAA2BgdUm2EZBSwuATAWMwC24oeg4hSwuAAEWJAAA2BgCISS0VBSYuASwWMwARTlvCCcQT+VB4DgAFIAAJgYMQAZpAFhli8KC64wXlJMJRtp1h4OMBFzGRTVFy8AIABfAoAAYDByYYLCoDgTuVAR0LgBATlvLocQTuVGaGgABTAUAAZmYAISgBZ8ABNgEJcAAAAAAAAAAAAcHACbUAVUXADkAmoE6cN57FKuEXE1gIACiJAAA2BgACBQECQmAoDBlQA5AImmwVucN4F3KjPBwAABUAEGhYDv5cBEHJiYqLJRGoHG1zEDBOllVLF4AAixIAAM4UAXCR5jIGNFwA5AJqHNm49ilXCLgAAAAFwcBtC0RhIJaAOQUstf+UhqE04r6YjTJ0sfZYvMwHAACmBYAAxAuElSGwROLgByBmBSMsbNwNpSeJFwZEagDSAABoKAAjvBcJAQILgEaID8AGoVTaXsQsnFwC0A2yUKYEgAAMDv5VFAIe0AWOXBMQC6UVMmQGEu0GVpd1QSoUBAAAADYGL0rD4MCXnwCYgACVzzZjA_m8fxKTHqAlQ4CAAAAGwMWoABPgB5cASGgAFzYAAAP4MQAXNgAAAAAAeLAEwFwABldCANoJgLr4BwAAAAXBIAAdcAcqKLgAABCNDAtoMKLr_BxFABJEwAAQg4AAQkoKpBNkwXAAAMEaGBNtoMELsDBwAADUABgcCgakE3ABcAAT0P9JwEbC7CAcGUDgRMGyHb2A2gWJkAB1xJQ0Sn35cAAMKRoYFtCW5dhAOAAPPpwADASEkB56o0Sl6ZYvAAJIqU56AaSqIgLl5TRqQQkorxw31WqgdsgTk2AHy4ZAaJTHQuAAO3oQBtBMRdhAOppFAAA68NAAHy4BuLAJ5IAQUUXAADCkaGBbQUUXYQDqaRQADsJAAAcCweA0f_KoBFwABlVCANoJgLsIBwRQAAAqRkALQuBKR3lQAAMs+AABGVAABgBIU9aVgFepwNjcyS4aGNgAUXADhY7w4BVhcvAmxkzjoF2is6MF4HEu0ExZYvCCAAQQAAAUXADhYoA4DuxcBFwkZMw9ovABB42FxBmxcEEAAggAAAouAHCx3hwD0S4CYgT2Ug2xs1g9EuCCAB15CAABwmbAU9cAhqhCDgqBiSYAA_+dAAGJJgAJpFwAALgIAIbMADFigDgyGkAAMFoQGPm4CMlQAAYiY+0LAARoBbrguDscqQOcLgAAggFabgFIXH3yoAYgFDh4AAhZUHodetSCacMuAAooBNNNPl4JKXABKYqBQ4eAA7w5DitTCaX8oXhSTLGzcCAKBHHJTTaAcyxeFZqoTSNHDcL7EQAB3h16VIJvoi4COgIXRg5GC8JpxKCnMoXhWQo0nSBsBQ4eAAC3bFAHDGTgEGVATUAYp5DACYmZKgABEGwFDh4ACaulAbVUASFgWCgkJQGJJgACcgAGJJgAJpGwAAEo+AD2YAeVAARoAiLAMBAAJNgAAT50AAAkaAAAAABJDgVFjMLLnSheFJMwbNyilljaBHHIUTaWQQhcvCSgAhIE4BhCA+AAkhwCCxmFkr5QvAjpRazGlGNoYLwonFqaxfoItAAHORAasHgAAt2whBwbC4AnlQE1AwafABMTMlQAA2iIHAEwABNWhgIKqAJCxQBwHBYCFFQABpLIB95qCGFQAEwDIAAAGKPAEhYoA4Pw0BiyoAA_8hAWdbgK0bAOQPIpAAADAA6cAMOgB5cASGgAAAAAAAAAAABVC47w6EyMDVMxcvACIs4Qn5FCamWslny4AbMQ0kUMMEQDEI2fJcNDABEsJocOsSCFBcAAZPPIYWH_zUDpi4HIBJHpFQAPAsAAOuA6ywRBzjk4BoFQAH9k4kgAGAKgANRFQABUhoAANkYENEpJ8XLwAAOJ5DANIbbLiaEkP9Fy+jZmI4gTxUAABZNfcnQWZSb4uAAP9nkMD1zUEai4igAoEsZkkAFzDQeaYN4+DxOVzlC8OioQxAIJBJIBDYuAA60Ze4SgAM6LCYtkID61m7XOTMlC8ABZCkPevmRJP9MxQQ9li8AB5hkzJIAGpFgrxQBAjomVBKVFFwABJBGP9GRbQHQXAAJ8MgAAmiwHgHhqLEGjbKXSFwBLQAEsTyknWmoJpFwACfDIAAFwkAAK+Adyw8lRYx4C+lQAATxChllAC+lQAA4i4gxEAA9soXsIIj_"
noncomputable def WL38s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL38_0) (dpk j 1 WL38_1)
noncomputable def WL38s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL38_2) (dpk j 3 WL38_3)
noncomputable def WL38s0_4 (j : ℕ) : ℕ := dsel j 2 (WL38s0_2 j) (WL38s2_4 j)
noncomputable def WL38 (j : ℕ) : ℕ := (WL38s0_4 j)
noncomputable def WD38 : ℕ → ℕ := rdw WL38
noncomputable def ready38_cuts0 : List (ℕ × St × ℕ) := []

theorem ready38_cuts0_ok : CutsOk ready38_cuts0 := cutsOk_nil

noncomputable def ready38_0_state : St := ⟨26112, 256048, 51168, 156704, 29184, 45301, 53248, 92288, 53248, 92288, 29184, 45301, 40672, 91840, 26112, 228544, 77280, 307216, 106464, 352517, 159712, 417152, 212960, 470400, 242144, 499584, 321856, 551792, 347968, 577904, 80352, 202005, 133600, 278176, 186848, 331424, 216032, 360608, 295744, 401280, 321856, 524288, 82432, 121472, 135680, 174720, 164864, 203904, 244576, 295744, 270688, 473120, 106496, 145536, 135680, 174720, 199275, 266560, 225387, 443936, 82432, 121472, 123104, 213312, 149216, 390688, 69856, 137141, 95968, 337440, 66784, 308256, 0⟩

theorem ready38_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD38 ready38_cuts0 108 28622) ready38_0_state = 65994 := by decide +kernel
#print axioms ready38_0_cursor

theorem ready38_0_covered : Covered (toCl ready38_0_state) :=
  ready_cover_cursor WD38 ready38_cuts0 ready38_cuts0_ok 108 28622 65994 ready38_0_state ready38_0_cursor (by decide)
#print axioms ready38_0_covered

noncomputable def ready38_cuts1 : List (ℕ × St × ℕ) := (28622, ready38_0_state, 65994) :: ready38_cuts0

theorem ready38_cuts1_ok : CutsOk ready38_cuts1 := cutsOk_cons ready38_0_covered ready38_cuts0_ok
#print axioms ready38_cuts1_ok

noncomputable def ready38_1_state : St := ⟨26112, 263183, 51168, 152447, 29184, 45301, 53248, 124864, 53248, 124864, 29184, 45301, 28545, 129824, 26112, 240671, 77280, 314351, 106464, 359652, 159712, 435823, 235883, 489071, 281184, 518255, 309729, 648079, 335841, 787471, 80352, 197748, 133600, 273919, 209771, 327167, 255072, 356351, 283617, 384896, 309729, 524288, 82432, 154048, 158603, 207296, 203904, 236480, 232449, 333728, 258561, 473120, 113302, 178112, 158603, 207296, 187148, 304544, 213260, 443936, 82432, 154048, 110977, 251296, 137089, 390688, 57729, 175125, 83841, 314517, 54657, 269216, 0⟩

theorem ready38_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD38 ready38_cuts1 111 70549) ready38_1_state = 108045 := by decide +kernel
#print axioms ready38_1_cursor

theorem ready38_1_covered : Covered (toCl ready38_1_state) :=
  ready_cover_cursor WD38 ready38_cuts1 ready38_cuts1_ok 111 70549 108045 ready38_1_state ready38_1_cursor (by decide)
#print axioms ready38_1_covered

noncomputable def ready38_cuts2 : List (ℕ × St × ℕ) := (70549, ready38_1_state, 108045) :: ready38_cuts1

theorem ready38_cuts2_ok : CutsOk ready38_cuts2 := cutsOk_cons ready38_1_covered ready38_cuts1_ok
#print axioms ready38_cuts2_ok

noncomputable def ready38_2_state : St := ⟨26112, 285696, 51168, 304767, 29184, 45301, 53248, 124864, 53248, 124864, 29184, 45301, 28545, 155136, 26112, 279711, 77280, 590463, 106464, 619647, 159712, 672895, 212960, 726143, 242144, 755327, 270689, 783872, 296801, 809984, 80352, 333951, 133600, 387199, 186848, 440447, 216032, 469631, 244577, 498176, 270689, 524288, 82432, 154048, 135680, 207296, 164864, 236480, 193409, 391616, 219521, 473120, 106496, 178112, 135680, 207296, 164225, 362432, 190337, 443936, 82432, 154048, 110977, 309184, 137089, 390688, 57729, 200437, 83841, 337440, 54657, 308256, 0⟩

theorem ready38_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD38 ready38_cuts2 114 113) ready38_2_state = 112516 := by decide +kernel
#print axioms ready38_2_cursor

theorem ready38_2_covered : Covered (toCl ready38_2_state) :=
  ready_cover_cursor WD38 ready38_cuts2 ready38_cuts2_ok 114 113 112516 ready38_2_state ready38_2_cursor (by decide)
#print axioms ready38_2_covered

noncomputable def ready38_cuts3 : List (ℕ × St × ℕ) := (113, ready38_2_state, 112516) :: ready38_cuts2

theorem ready38_cuts3_ok : CutsOk ready38_cuts3 := cutsOk_cons ready38_2_covered ready38_cuts2_ok
#print axioms ready38_cuts3_ok

theorem ready38_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD38 ready38_cuts3 128 1) (ofCl (RC 0 2 0 1 1 0 0 0) 0) = 130734 := by decide +kernel
#print axioms ready38_parent_cursor

theorem rc38 : Covered (RC 0 2 0 1 1 0 0 0) :=
  rcOfC WD38 ready38_cuts3 ready38_cuts3_ok 130734 ready38_parent_cursor (by decide)
#print axioms rc38
noncomputable def WL39_0 : ℕ := zfNat64 33244 "IJQoAANmRABsyIHIxh7_6UDwLgABpkQAALhIGwIwoNQcBRCheA1EiAGokQFJD_FwAAzxYAASIcABIyAAGdEjZkQAiMiCbLF8pIkUuAAC+LAACRDgAJDQAAyQkbMiAERkQ9JaKSE4LgAARCQAAAAAyQkbMiAERkT8Dp2i0UkJwXAAE0LgAAriwDeNAAGSEjZkRNEoBFhUFkpI5QIXAHdEYAAigVRYABYUN40AAZISNmRE0SgNVFwWSkj1lJYvADiRSkmDcA_UjAUIG40AAZISNmREkC_xUXaWik_4Ok9li8AMI5R2ULwC601co0SoAe4uyHj4BQQ4o4fHWVC0AMIiSyyDkG+XAAWVHgAAfhwAPNY4SoAoIGoOE0XAAGCIAUBfABvFwACph4AAGwcABJGAHoQAANQcBgiAAdjwAAcKgACaDQAAbg4APKEczsAAGoOBoRAAdCYAgAHCoAAJgkAAG4ODMzO0EznakAQkwShRzhoE8IT8DSpEAHBKF4ZSjSR7lwuAAAAA3BwCproIgoGgsAzC4D_x0Af+OgAYWRAAAAAFgoAARcBoUaoaCegS2IiukkRqULxG7NXKNJHpri5eGfuJlcAAOgARA4AwJQo_g0E9B_A8coiRgDrSheGWyClSR6LT5TFVQCBkisAAhRUACmWCUKXEZAQQFjkQB_4uLSF1z6bhcDS1YAfJMB9AAA0BQShR_hoByARo0ZgChyheGVxilSR6iEsXhhmWrBFP+FQDEABkAxBwShSthoKEHD8CqgMHPzrQQjKF4aaaD0OpQvAkho1zGC0lIVTzSQAlCmSDRPTGIT8lr6xg+IQskUeykMrK0ifSR65wuVlZoo1rs5OIXKwk02ynWmhfMG5LgwSmCIKBCJAMwuAx0TAGOiYAGNEQAApAAAsJBHKjZORgAVaBv3QShQORYNtnQf2AC4AS5LgIqK0KgABiCwAAbg4CzELsa0PKQGbBuBgThQAEPRgJjwAA2YeABh8AAFQSAAAAEsxEgwTULxMFFJmRAADZh4ANGwAAzxYAAGIUAA0+AHFwBMaAAAAAAAAAAAABWHAVuAh4aMCkiAAJzEQA7MgABniwAAMQoAAx0NwUFAOBShcAAAB_o+ANGwAAzxYAAGIUACbaCYKDYLAcQGuHwANQAIcXAADPFgAAYhQA3k4QgoGgcCjGoAA_2NABBGMGQAAzxYAAGIURZaABDoGubDcFBQDgjYZAC0DaQQKCB0jYAAZ4sAADEKAVQ4BqRUrJYERNzGTAFFCgia2JYBcAAM8WAABiFADAUCQSAUgTbsEwAqbiuaE_J7QQylKLl8uA4AAwQHAAAFauG4KbQLAKQAS0XcJgDCJ8FEA5RcAGBBhWAAAuCgAJDQGAkGYioP7J0tCYAgklAAKIuAAJsbAAAAC2ZGg4DDnAqD_ydKImACSC9UIC1FwABej4AAjQcAQ5CRoOZcTBlk4lAST3DwHEJIf1PgynlLgOgEWVh8AARoOMMC0Oe+OHwN0SKwkusThKWEJ6HWqjQmZ1ZYvA6AQW9GQZQJgAAJ0cDiNAjYqAb6XAAo0COHEAm5UAAGkuNIPBUFIOQACQsFYczgePgQwkVhJOknCUsIT0OtV_elGeZnVli8DoBBcAZAAAYuHB0XsoV8mJ08JIJQH6BQBD5+G3C6sAtCCAQXMGC8NJpARMdNwAl5SNB1gB4BSA8E4kgBBDaAClahBcAGyEIYhpAHOmwazY2L2M6PgXGuG4KRILBhomAtARAA1ABIBMABtI6AABcFBPT2IFFNhCCgoBwAAKSIAFoLuLhA0iNgABiCwAALgoBwDTtA6FADDgAAUkQADFGLmERlJPLQAAM8WAABiFFXV26CO4cDei4aBgBMKAYCBMDAEIWACAJAAKBIAANEQAAggoAAAAmZAIAwSkIgG4jwA3EeAygacqAAEEFAAA2BgAJDQCAMErCIBu48AN3HgMoGpKgABGBQAACDgMHlSICPI8BZI8jwWUG9FwAB5g5ww8AADSh1bgIBCBdEeALojwWUFslQAB_BY4mrWIBEYcDoBrNgVBgB7GjsAZJg3AAKif+XgNGwAESg4AACoMINBR9CZxEjAr6PAUQikd1Im0EwqtLF4AAmw4ACDQUAAFGARIQAo+AYCAAAECQABA6AAAAE2HAAAGAgNAWBgO5kwDDiZGVEAKokcpp5FSsXGi4AAKIUAABYGDGrBuDgjGQBaGgAgCQAQoeAAFhEAAAABuDgMSUg6mRARTHgCKY8f0NiyEUi4AAKIkAAIkOAiQ5iSkHUyICKY8ARTHj+hsWQikXAABREgAAOcUt5KwboIkYFxx4KyXHHgalmggRi5eAAK4WAAESHAD+nBgciAcuPADlx4KyDji4AAewsZIKAAAnBaRikH9CJGBc8eCUa0XPHga1kKHFwAEVxYogANMSJ0B0SCwdAWQCtEwAVomAqgLkiAADUVAAAWCgEIWEcjAm5OALIAjUqAqgQcmAAEcXAAAWCgEIWEcjAm5OASYlABZAqgQcmAAEcXAAAWCgEIWYkpBeRWAsYpABRBqWSNCFk4uAAJCZAAOcUgICUgKoU+VidKlMAKINSyVeQsnFwAAfzK25EAAEzlX_lIC5qFcABKZTAAEplMCyGUi4ACXpkYS9HwBv5WBHC5_ykasViqFRKIFm0ykoZSng1rIQZkli8AABCLQFiGwAgAyWA0UK4JsWK4IkVgCKlMBQSsUQalmgj0hBcvAAPMbHoRgzbQAAN4lGpNRNOCVisBHBSAI4KQf+WgNSVAAB2MiSXUAB2bErFIDQKlMB1aZTAHVplMqQsNyWK4C0DKA5oyZhlOoE3RoF1GimplMBEplMAuSlPADJJ08ijUq0EeoHKF4TTCAm4yZhlOtdBIwobDOZHYGHiYuDjwEPgwCihAsDH6DgAAJjQABMaCLMQAAAohQAAFgYDY0ABCFgAgCQAEASAAAAAAAAsCkVhwCFHEYGVR4LP_FoyqPFhsoSKLnyCQACECIACIKIMCRHQJgxzB4CdLFcACigfhPHc1AbhsAAOQiwcAAPBgAR1wJgzYBIFHFCcAQtAtLyABDBeWGy20xoXABCYaGoAAEwYAJK8AoMBwEiD6OGLGYHSyEEmtltq6l4qpYvdcHAAEvA4AAHqFgmIGzixmcJTgysWMws2X_jkOBKgBYxEBlAoAAAAZkNMLBxwyANMYLymgaYwXhZsv+nIcCVB0AEAfBSwmAAGJRYIrryxmHtbOdZFoxpoWRaFmwtNbN5BJWULwyJQJyWomRsANh6AFDHgbGNHrhiwRXAljMPe2c6yLSmn_loWhZOczY7aQSTlC+aiUCcvkJkfvDIAAKQAeXAEhoWQWBYxkB_4+AIiFwGT9TcJbKgAAAAIMAiIxVIsAxBAOQL4wXlNAORgvJJVMpxoItALZDiMPHKQAWKHgQQYP5_FgbcZLwBaAC08mV3TNjAl5QvAAIMSFIAHPDxZjs7fj9aCYq4FQZ8IkH6ioDoBMAf4IgAcgTAAA0AACoMACoiBUGhaLB+kuP+Nx1EqAGTjxSbCDGi4AGpLQAAKgxBgGYuAaRIgHyjwQayHYLFZUbCTmpxcAF0EIRMSHgAAABMIJHfAEhoA4OD_yMAgQqAECFQADsHgAAPCQAAABIaBgEgosfAAUU0IXFRKoHYKgAAoDwAAAOkv40eAZQhAMSUgBtZUVGwgcEqAIerwEGGgDyjoAPBcA0ehAXkUgg_tWjBxUVGwhLAuAIpdDWEQAAbh4DwDoXa4vAaTQgHKKFcINZBzFiue1Gw0GcwALl6BAil0GkRFUAAhjQAwi6BAZMhAP2UighR0q6KxVGwgk0qpA3B_xGroFWwh0AAj6mPiQuBAc1EBITANoiAFYPAHzloAHBFQAOQIEfAAAE6KiGioAAFI8T2gnFDIlopAMJUAF08khHISgAADAK68Az2RB9IwjwHQIJNbCAXSheBR8IpF07kRKQTgAACQlzgkQMbQhqF0F6WMygjEWhtBcrKjYT_p1PouAugpCTDEABpAJSXAoK6zBuGUQeWMygg3ouVlRsJOaIFwARWL4IQFpEpJOKSAs0iBm_JQH2XaQWMxViwAsIkYE2R4INZBfFisqNhoM5dqWLwCAXQ8BFNQDLQG2FjMHZ0dISNA5gpMCGRxGB+seCyH6x4sJlDlxcHGmgW3HgACNBwI0HMFJgQyOIwI6FkI6WEyh0QuDjTUiKQXdHgAEaBwAExoLwmAQgXRHgC6I8VxYrKC2SoKaA1YeAAAAJjRT5MB8RxGBHQshHSw2UOjFwdajnpSC4Y8AAAABmhSyRWBbRxGB6ceCyHpx4sNloJuguLLSSiEVh7AL8AADs6BhK4P8RBKBuTR2AvUwbgAcR4AAlFwdaiFTSByBIAABAokuqJMDPxxGAHQBEhcrK6XQTGULxDzMRS2g9DZmcZiAAtOHYE0EwFtHEYHPx4ALqULwqlkOtFwUkCUJ8f1MgBQpcA8AiDSUj1DyYF4jiMAOnXJS8Coi5XVa6XQFtBP3oEcuW3ArzBuYZiQQATt2UjYAB5geUsCuDn_SoCyBzMeCaDKSheV0ugLSy6dRJcltoVkwbnAEgAIAAJJYANHFeEwf+KgMejwALSu_5XgYeVAAJ9MiVh0NAqCBAAWZKPkwCRLGYAdCaAAi5WV2slDD5pJQvKJdE0hPyyTcDEKtBCphHnpE8OfSJ5LCpOAkSxmAtDoTQlIXSyVmPmllC_8C8AACSxmPSjdE8hhUwiIk6WVMDLgfSOAVHgCKNAZsIgCk5MAC3iYAAWjEhgAbqLAvN0IAYKgvE3_CUi4eBkA0AHQDdBEABgiIAD+xMABIwqAMcxAxK+ODoShkAACQePuHwIAKF4TS6EJyoAAW0EABJCwHgLsqC8TZGFSLh4I1EwDniIAmQPAAiAqAADoAH+EoAttcHxCiSFv6EwDuLFYCEChOABiHgACQXBSQD8aEAA5AEAJDQAcSK0JgEpps6KyEQALSq1UPjFwUko0tGkCoDiCkAArdwAOuAQTQScT+pK3wbBKAmAc2RAEXC6qgCBSoqgBN4qKMFAAHQAIjAC64A_JDrEwZ8MqKHai4AnOREWsgJVKgALOHQG0B1RcALEaEUJgGIBDyhfydOA+6ZGGw2kOxFwUBSgC5kwHEnoBmAAjIA+VAZEQAeLgAhFwABoWAABhEAAAAA2PgCktQAKaCTRySLwHjIAchrBYlgAhABRhcrpoAe8IjjTQB5xQvANglAUpu5kbYxMBFAAAAahM0qpoAMOJjjTQDcxcAQKbi5ChCRB2s2A_+ZAH_zIAAAD6pV_p2ACm5UE7okcSm0OyaNzKExKIf4YpjPaiXckrQ3BWrk0ADOkitSzZzptdpr5mbHQUdGC8BU2MFHwgAJkAgKj2ww8AtAm4PAE3B4AJIIwAAAADYqDMFtcUPnZkVQZ2dAQ8nBWlUDYMBwIiAzUPAGah4AFmEQAAhAAA2DFKTgwWuDYGokHBtIeAvENAF4hoAG4kQAAdAABsDFPTmIaOlMqXk47AwNeXmY7Hh5PDw8TEhsa"
noncomputable def WL39_1 : ℕ := zfNat64 10277 "YCADcDABsBgANgMAAAAAAAGAgAAAAAAAAAAAAAwECYGANwMAKQANgMAAgyoAAAAAMBAAAAAAAAAAAAABgIEwMAbgYBWwsAAABoKgAAAAAwEABAuAJDQAAAAAAAAAAAAAAAAAAAAAAAAA3AwASA4ACQHAAAAAAABgIACY0AAAAAAAAAAAAAChACz4BCZAAAAAAAAAAAAABIwAFCAMHwA0yABjQAISAAAAAAAAAAAAAKVgCacAIMgAJcAIEgAAAAAAAAAAAAGz4AkNAAAAAAAAAAAAAWnychwgQoAAMQsABiFgAAABwCwABOQ4nbcAMBABaDgAkBwAEgOAAFhEAAAAAAExoAAAAAAAAAAAACEuAAAAAAAAAAAAAwEBUGAAAUHAACg4F3DwAAAAAEIGABgIAAAgJAAEBIF3DwAAAVBIAAIQMACE+AJhwDAQDgYAMBwAAAAAIRgAASCQAAABpaAJiwDAQBgYAABQcAAuEgAAUJAAAkEgAACJBoDBwAf9EgvCwAOQaAAhxcAAJ4WAAgwNAAMQgAJ8ACMgBhUARGgAIkAAAAAAAAAAAACYKAD_okF4WAByDQACDKgABniwAAbg4ABiMOYHABMUSAAzEVyh4OgBLS4AAZ4sAAJEOAJg4EwUADQiYDAsAEUATkdH6LgABniwAAkQ4ADa0AhIgEAoAAADMRCPhIAWJ0AAAAAbg4AEAoBADwHvmIAFYVJCEgAHxUAAJMaAADcHAAVLiZDgAELiQAr0yemWLwCcuHLgIgAAAJEOAAmHAIBQCWHgAAaxcJCEgAC5UAAM4eAAAAECQCIUAMR4AAHEXGHKkhCQH+To6RcAANoeAYgAAelQCWHgAA8xcAAD4qAADkPFgEgAAAPBQjiS2SBOAjR4nrJBxGADFz5YvAJzK0uCqAEzLiOgYQAASFBXjwAAAGYuDFByqhIEPnQAAE0qAP8JQAaARiQCPJgAA3hcN8qSEJATkvRcXaSgMIABJASiwAES4AEsmAAD7GVIy5IQlNQ_+fQ2LgC4jAzIyUhASQKExABIUFiJAZUmAMm9iYFgFjNDZQvCCE5uUXH9nYylROmlwASQKcAkDgAAANBcvsoXpCEh0SpfBzJAuADCDhKF4BdRC40AGAcBUDoNfCxlAEIGzNIAkf_Vgi_ALgAwjJSheAUbiPY1jQXys2AxJIcYOB_pUAVABa08oXpCEgJyLQAiq0LeLGYAcRHgwfBmZlyeJoasAHHwA02OUeGgLAB_YeABbEx8AuALIAAM8WAAEiHAAhLiJFgA6kQA8iYAvwlABhUQXAAAAAkQ4CzFoACQEzIgD2EwBwJKooBhsiXAAByGgSn6GgAAEJkJgMFgSAoRMAkYmAOwJUNA_4xMqLgAAAAK4kAASKJsWiUJAcMiAVQTABJ4eHCwDDmUuAADkRfuOgAAAWDgH+RAGmJgDXCUAGFbxcAANYuiwvAAD7A9MQWB9JUAJYpJwDbEiPPQDDXIuAADkRRWXgAAzaJFjPhwCEBwhIjANGo1Dw4AvAXFEAE_nD84gCagB45EDs7UgAFaCu44eEylRoKtmwAhAMDIQAJ3JgAAziwAAFgoM5WnqzMzAB6EAKFglCgAETiRsyIARGRAUkSKXAABdFgagAABBCCUKAADZkQAbMiByMYe_+lA8C4AAaZEAAC4SBsCMKDUHAUQoXgNRIgBqJEBSQ_xcAAM8WAAEiHAASMgA"
noncomputable def WL39s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL39_0) (dpk j 1 WL39_1)
noncomputable def WL39 (j : ℕ) : ℕ := (WL39s0_2 j)
noncomputable def WD39 : ℕ → ℕ := rdw WL39
noncomputable def ready39_cuts0 : List (ℕ × St × ℕ) := []

theorem ready39_cuts0_ok : CutsOk ready39_cuts0 := cutsOk_nil

noncomputable def ready39_0_state : St := ⟨26112, 269440, 51168, 287132, 29184, 45301, 53248, 138496, 53248, 138496, 52016, 166208, 28545, 165216, 26112, 285696, 77280, 549208, 106464, 578392, 159712, 631640, 212960, 684888, 264976, 736904, 293521, 765449, 319633, 791561, 80352, 316316, 133600, 369564, 186848, 422812, 238864, 474828, 267409, 503373, 293521, 765449, 82432, 183797, 135680, 249872, 187696, 301888, 216241, 452205, 242353, 679074, 106496, 220688, 158512, 272704, 187057, 423021, 213169, 649890, 105264, 219456, 133809, 369773, 159921, 596642, 80561, 316525, 106673, 543394, 54657, 450912, 0⟩

theorem ready39_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD39 ready39_cuts0 111 137) ready39_0_state = 40817 := by decide +kernel
#print axioms ready39_0_cursor

theorem ready39_0_covered : Covered (toCl ready39_0_state) :=
  ready_cover_cursor WD39 ready39_cuts0 ready39_cuts0_ok 111 137 40817 ready39_0_state ready39_0_cursor (by decide)
#print axioms ready39_0_covered

noncomputable def ready39_cuts1 : List (ℕ × St × ℕ) := (137, ready39_0_state, 40817) :: ready39_cuts0

theorem ready39_cuts1_ok : CutsOk ready39_cuts1 := cutsOk_cons ready39_0_covered ready39_cuts0_ok
#print axioms ready39_cuts1_ok

theorem ready39_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD39 ready39_cuts1 128 1) (ofCl (RC 0 2 0 1 1 1 0 0) 0) = 43125 := by decide +kernel
#print axioms ready39_parent_cursor

theorem rc39 : Covered (RC 0 2 0 1 1 1 0 0) :=
  rcOfC WD39 ready39_cuts1 ready39_cuts1_ok 43125 ready39_parent_cursor (by decide)
#print axioms rc39
noncomputable def WL40_0 : ℕ := zfNat64 33247 "BBUEalCsaAnApEp55Mpi7yhWabaccnLwSQAEECwAAIPGQVAUieEo+JsT8kViUck0RJkKTTbTimBcthJAAP0PEMLgAA5AyZugEiYMzJFY6ZGmslks5Jsxf2SKzSbTaWT3oxJAAlIWlCeACFx4HZmzB02sAPHgCQsYhEKdEwExiYAmMTAAB4yAAAAAO7EFImAi6BKgUAdCkKiYI2lIHEugazR2AJSDgAAFAFAaAq+ISwppoDWUgloabKBJFY5KiNb_lQHEugaTR2AD8DgGQBwAAAL5xoNgGpbCoAP7OQslIBKGlyisBxg4AAY8HAAB4EBUqnIgGrEipWE1LOSKw4lFpRszlP_ToOJdHymjs6ocAAMgDgADMVQQEyM_ohFkKk4WSSlxKN6DZY5Ir3ErEW2jeXLYOTqhwAAAFTGCQGGj3YyIDKFScmlkBIVJy6cSiGPJFYHHfK8Dk4wcAAFGCgADu5Q0G7AGMsUGnAPoqVhNVfkisCbMXAFSsDiXQNpo7SeHA1ACclUBXo8AByWQ0FgzQVAXeKgKJd4qDDRxyD_x0joOAAYhBADZDQAwh4UUUNklFIDV+ZIrByTZiKQNpNDkEC9J4cfrEgQJFBqAQcIgAZLwBFhUrCavpJFYE2YlFKFYHEukkVpo7SWHFBnM1INVBqUEopQQhnjiMAYpcFJSSYkiseY0ZxgZIrAqTZibcoVklNpVD0pD1J4cSkCJdACgEGjYACQ0G2SKwQqSKwyhaSRWEEmkpCycU2LwhM4fgACGIgAABqSRWCrSRWGUdUVJwgk0DOUKwsp0bOZdJyABWAuHwPU0AJ2LCcZM+4qTg0gqTllJKEEm0PMmZkisrptLIOQCytAA2LlZFpoBAAeB0dpwKQFKSKw8DJrLtFSsHpRKnlQObKRRhw0joOAqkEggAAbhYgz8AJGQOaeASEgA+RAAkIgAABDJR1AAJIAAIhIAGU8okNBKQmriyRWXZLiTMQClCsLKYbTJw9SeHFE2gBQLhHwAQY_PgZyAE5YIAOAUhNXDFScCbLkyFIHEshZjpuk8ODLWQ5uTFNAP9GDcACksLISyKlYEpAogKNpSBxB3Zo7R0HBlA_kbA1_+tAZNQgAOVQJAKTcXglIEmipWFROQlQHGwzEDlHQcUX_hcAAZSKPALgCmhwsgKQN0bNwJkisCbMQ7FSsB8ZHFiDBbBylEOCaPf3pVFAgoEFopyIZAE+EhZAIgKWjFScCDPRSFpMoEBEhpPDgml20y0IAJjwSEF0kkGDIlxUBATa8AXIVKwmrhyRWBNmI7yRWEm2ln9TNixMlpRDiy1kJVkwXpKHoABoxIrCK2IqThldQfSUHpJGJryRWWE2lkmKNNUnhwZayBgCpOf9TgDgCUAIYSUAJgR6SKwyhBSRWD0mnnSosJxGoxA5AmgAHkBvxkAN4SvoOVcSKz_iMvUkVhlnoDCpOD0mzENZIrLCbSyF7NHYE0olFAPIFzDIAkYkSgSKwikxJFYZZ6WYqTg9JsxFJYTaWbaJQvTR2yImAlJE8mkGigHkDzRkB4eA35iAEjIXnJAOBQNLIgGbEQAzYiAAagAW0AChA8AAFuAIGQAEaEPyQBIMBoh4Aqg0AFUGgAZYXAAEkAAegAmZgFkUggM0bgEKk4E2YuPJFYG0smbRpqk8OCqQT_w8USanUwhusqAMpVA9CQfWKgOVFQf+WjlRUAAqDpujoOAAkgbQAAtpchIjBhlIOVGmwpAopSNhiFSsBJpIoOUdBwMf8DQBESgCl0khPBSAAtJD2FQNoKF4CISRWBxEQkisDCQQRwHBVA_YpBdOoEQU4C2vRkApAdEVKyCiETR0RUrA4gxJu1gVQN9IwXTqA+VOARooZgKQBSEEmhBMhSFEQThrFUtFpAqgEUlBUWTqtBgzg6JQriiJU88kVg4EkVk5JKUEm5iMmbnCpOFE2ll7qRLNIFEBjRTDJE8unEugBtMpg7HgtOADlIKPJAKmFQE3CoP+HxNwqAC7SEjoOAD+CkABNROA0Ek6QBIyAHjw+gTkWALYNABbBoAAJEwAAAACJCANyXGXmwe3KgLqFSsnNRLqFSshpt_8vDWzR2joOKCAABPNlDsSkBoDI3YuXsMKk4PSSlJJIxaGSKwNJZSyjTVHQccSyRQSkoTyv7BfNtdJofZQrlOcgOGAEjIflPAAKDwAGh4AA0PABo9CAAIIAAIiInwGDmQElGxsZr62vAEg9ZI83MWCUlEIYFSuuz146hTckbSl5R0AApAC6cQAA3AwAJR6zR5uosAbCpWUQlNdntROsbc5KjSAEdAPxLw9VIAANwMABjGDCj3FESlhYOIFQGdioIJNM7FRZJIxAIIAGkAANwMGcGAAp8BLs4aRkCDwcNKgZwdADKFYVEa_7KgFtBCqHQAHoWNFgAAALECrsiEMgcioC5WAQS5o7FIdKiNT8FysBDQQqjEJIApjRmEzxYAAYMB4Cg4gANlOhMBAUqA_B1KSiSajNbBlQAKGD4E9ACJBcAABAGAArxFCDB8BSEG_ps0AqTlEolFBZg3lIA1CenEjoARxUAABMGDnBAUNkAyHBucqBmB0KRaVGyBtKWkJEcpP+T4vOZA0ACyAABMGAFkVAMhwXXKgfYdNxS9owXlRGqOi5WAVmM1J6F0A+CE_CwYsAAGXjYDcUuGSo5OQwBcrmpNS7kiuMlRGspABKpw_JoRR2ydLHUljMAARIMAGJGO4ercRAJUkVhZDpkismnEo0WNpSbQAkpRQIuIwAAbgYKRHEYuxxH+pCCWFScolUkpVNpRvUbFpJFZpqIOEHhyTSigGXLGYAAiQYs7kAKWyDDRvhYI4FQDjCoihRHbFwBxAAAYhcAAG4GAAPrAYCwSkUhSjZ26skVgkKIgzJvKTaAFU0jQNyNgAAARIMAtWdz4EMOgWdUAmFAhUmAAWTAACyYdw8B5AJ7HQ_oxAABuBgH8nwCYUAyS4F_HzuUhVZqjYuVs7JgoJBlIEWm0metBWL4AAiQYLQNUpBmrIhGoXZKgP_FQFGtR1_4qCazkA1FoAPwNHYAAbgYEdFj6AnyhWA1VcVJwJsxOGSKwOJZClHTf_ycGmshr8mAAESDFyACrIfZgvgKSWz4Nk0FScajkmzFMpIrCzERo5lkmv_zYMNZCMBsAAIkGAFWjEzMF8OgpmstiMbJ6Kk5FHJNmJySRWfSjaSaMCKE8lDCWQTwgRwABEgwOAPRMXg1UVAZmKgKJvYqNJdQl4bAUZyMQ4gABuBgEb4wqgpMiAUIRAChCIALpIQAAekoAANwMAhHQnFoAAqKQGpAwqAwgiJKAAE4nAABuBgCCY3yHVdkoKuJwElAchUCyhglGAAE8nAABuBgAaLQxy2AYCD0jAAAAYkmAAugAB6SgAADAQAMdoQZrEjr7hjIigRQNKlC8AIIApAAAPCUAAG4GAPfSgAeM5h01RCDcCkAAJQNJSRaR2LG4EUB1BEAARoKABCvALTYAAAAAAAAAAAAUEvRRGnIEHTKYSQeB43KoxLsV2oASlPMIhMIxC9HjsBaCkS4nAABuCgno+zh_hxSGq7k6eZaKTXPGzMukWsmURydPspNqoxCIYTBuUTChNElzEBKDmuh0H6joADOF3EfEEEHJ08A8R43Lqe0oujRaiiaQwgpQ4blEJIGVCYAaAArxw_HINSaYRqJRNUIaMyyRSyZUrpk+wklXihXGIRakaLyiEkDIlDJZzYnE0kgCg8dkqMjNPEmoAGUgAKcASRgCKEACOgBBMAAAAAAAAAAAI2ZTAPojJE8BDqFMAUl0ek0rpsUTSSTCqQyByAAEJuAADcDAGCgz22MxCfkkejUOCdPoo9pruSRXVZyTZiKhKl2EKSsaRAmEohdJpdpLryheAAIkGAVNbSEfecUgsapA9IMFRVCaKmTKYAGUAAITcAAG4GAMrvQcLD4OzOwG1zAPmlQDWrBUDEmj9Codw8G0qksTh6ASQWkTAACJBjDAA6CpWAUFIFSaag68QVDwHg4lkdCaOwLoEvSYAANwMAYcuORQgai9JFYMRq1skVk9JsxFOUCqu2qcNZZAKHjv9KMBkgj2WgAAiQYjTmNAAikASRgGtcE5ngHISoP+GwpDCUUiHTPRRUQ00gDo8hhpACKAAG4GAAkjB2EIBBIqBqS2KgkmEh4VBXR7b42AAECAAG4GAAwjA6CcNoAFScJJJQskn+Bk4UkVm2cmksgMD5vmcmNJprIUkAARIMAAXSD5Y+wDwDuioEI2gmAEhEwAE0AAPSEAAAYCAJqrAM8YmE6C1RUBTAqBaSRNxVgQKaUUAD_owAAbgYDVCjmOiUkjkSeSJ5bUS7KFfvpswMkVrjWL85qpZopNmppZiya6iSkNydLAAESDAD+xgAd8BOrzWNTcHeCoD4JMEkcg0D_ycH8k4ABCSMAAG4GAASBtoPHZ5HjuBGipOFUWQVJwok0HUKHyqOSaALCY3_82ABXaUAACcnUDbEycKoOAqT_eNirSSMv7Sl6nkMigGZqVEDN6UABGQ+CRzR2dRWh9JZ6USYozbyRPKSiSZKngcLz0ckQTIY1CoZmplptBDo_sTUkINBmoIVGgZE5cOWIuHcJKEkCMVJ5SVVzqFMQKGkaGPaDt5CGsZmtlqoB4k6WAAIkGAdPXdunsEwkisGoJoqTkEWy2al6VqYBbTGpsADVjIAANwMAoOGgBJWAHoQ+CeAANIgAKEQABQiACAylDAAIIAABgInzuNBD2sOo9HEYOOJk4ElDSTSSg93g3AjMsZgAD_SgAA3AwdjzQ8DV_JIrCalA2koWSbMSokisqjkLIn00fgaayDoUieAAG4GI+zMQmJhJ0NUIFgqiRAUsIgClhEAAAj5mAAHoiAAAMBBick9eSgDhSywqAbQVHkIUbCkMJRaSYOxTOYaUUYcgSwAB_jQAAbgYBE7Eal1HglJ5ptLjo2JQrC6UUQGwpnIUUjglR1BFwAAAAbgYA7bF8xtQweBqKTyTRqOMkVhZJsxaiSK5zDQFyJEMsgXE5OZAABuBgpOQdcpo6bAPeOlRtHtZjqUw0qM1KyVTkAmkfAAD_GgAA3AwAJxDQ0+6WRAkckVnEsgmSRXUbiUTNZUEQAUEXAAAACgDh5sqHGOI8nLRJTiNdQrklpJtpogkkVzkkjhWL5JJK6oyAAAAFAHFiEANYADpARbI58CPBtYmAx4TAGPCYADTFQAGoAAGQoAdBc7aBHY+QIyyIUKk5tqs7zaS1U4lEaoxJFc5iM5P2GQ5ioAfcOgABuhwCgRlCz9GUgRBjwqAtsVf8XriUS2xUABSQwgIEAADIUAsvSEGVwPEQpDfhMBUAiAKgEQAAABFAAAMBAAIDULEis5Y4j_mrCRiZOaaiH6Jk9FMpNFukiucjWo0EaqEQn5ZNNlrIM4Up5lAAAADNdASKx4jiMDUFScBrBUn_2jGkojWCpPOQB1p5DDoxABST6YQDoA8Ds7CmNOUgIvcoITFwgeEqECwVRIgKWEQBSwiACYgAB4EgAA3AwYmZTUjozAgJSOx4eXhpu"
noncomputable def WL40_1 : ℕ := zfNat64 33248 "CGN_JwSkMIKSg1Gfxt88qCQzMDmiYAGIDYD4AA0LA0SnAKYqVlhAKkitHxdQSjMw2lIWUMtkxWYiAAtofAAAAUuqceJoCkkmnWr8_zZbpIrKNBJoyjZnKQMoIoJFYKQALaHwAB2HhSCxQngFMkVhhGrhyRWigioJNLkbM5ST0wgJQni0AGQKgAIOBwACKE8BSGHYxsvskVlBJpBDZnKSe3JYM4CU_ktABNioxA0AAAIYqhwirIfdKiujEKhKFZQajEA2lIf+ZgwATAAHME4AB6AJIrPoWrIe7KibDEM7KFZQajEI2lIGUL+EwAAUQAYgNAAzKlZAUhdL2aN2VkisoJNIIbM5SP6TpdhHahAlKKaYqBpxCloAQ8aA+bAVpVrg0WQlJKVeIgdCkoJRn8bF+KlYWUMtkwGkAKtBAEoDwOjliSDUieBpyRWVkatkKk5QSbMXZlCsC6LVNhCBtLIRTaHTsw0oUgD_R0PyDQ20ieCXCpWVkFJQWlKE+YsEKlYTzXgEIABXDp2PSqgRDFgU0BSGHVBs7ckVlBJsxQUVKzjp9WQEIG3fy8GmToQlFmoEBFgPACQ0d8mUwS4VKwwgpJ6NBQnzEDxUrCugIQ0U5AWmOgrICTRonQDIrAAZoADDLZJwfjKgwgMOhSZZ7UaZG0pCCLEAhAAuAhGkMICaiYHMJk9JAU24XiyFQ2TqSK7bSSbMQDkisGorQCEALWIQ5NpI2KsgCkO50ZpR1BJwbgocCcB+SYAk5MA5KkRAAdMIAAGISAAA0FEKBBOYAucqDiTrKgakka0RKgAwiMI0DgAEUJAAAaCjDAoyEAIykEP9zZRpIrBiUcKG0pAy01PyUI4DgABsJAAAaCgDxKQBzKTxRAfegdN37FSsKjNRaWH6asNSSeUnhwATcEgAIOBwADyoAkNJCNhPIY9CpOFmagUKk5cSiNREkissNdno5CUQJwAAAAAAeVAEhpsciBL5IrCyCvJFYcSidzKgwweZgEoAAAAAAhKwcHpCMqQn5UCpOFmahaKk4cSiNRvkisMNdBchAnAAAAIODwOjo+gdIRlSE_HwVJws6tNpKHEojUw5IrDDXQIsSIwABnjwAEGg4FmQgmEJ+ZYqThZmslP4zZzi5hSnjUTpIrDCXZ6OT_ECcAFYlQhAAg0HA3qxb_0RIz8Z8RIqTzUqzWS0U403lxsH8kV0kulkOwaOxKAApPURAAQcDgAHcSQiqzyGMAqThZmslDiGNMpjUKpIrDCVZevz0ciVbBAfAAAAg4HBvhV9wiBjxUnOpZFFkismnEonVyoLoEZiYDFSsAAABoKMHBj0ElAR+kASMi7SoGGFQBJyYNoAAdMIAAC8OAAA0FELcmJzfzYDXzJ+AIj4AULAIDAPKLlYTUR5IrCojUYhcrA2_0GgO+HAAARAAAKwYC4FysFuHTcUhUSClQuVgbQAAAShUzAoAAAtB0BWDBOsqAmuVBSRTNcqAAgo6DgABEFAAAaBgFBPp8ADFgEBgAIBGyeCoCiNYKgCzTQ5QcAAf+IgAAZAfABvkicJqTQqVgUZyiguVgpCzTRik8OAAHYsKwFgAcYcAmQ+ASSweBMAEnjbmpUBNnP3SoAqk0R0HBpAAAB6GQDIT4CESACzBt78qAmzn7pUAVSaI6Dggk0J_LQAAUhoJZubLZsAcGREDBwMAVKwmq+yRWBNmK5CpWBxLrJEocnVDgAAeABAJAAB6MAHoVKwmqvSRWBNmK5ipWBxLrIkocgAT4FjYBQ_gAOAAA18YAkLrgLCkGuFSsDBxUrAomDipWBx4YvE1AADqHAAAAB6FSsJqr0kVgTZiuQqVgcS6yRKHJ1Q4ABK4kzIMJgABoABkulFhFhhMAolCsJqvIqTgTZiKa6HFji5bJLjTR2SkOAAMjEhAeAAZmYABsgCwYC+FSsP_my+SRWjgSCbMX0lCsDiXQxZo7AAJoHoOAAXBQAKsFQF0yppQsFEumVBcQlqdBQQC6J6DgAAQMACwUEpCwJsKUNBQUYcmUpC2l0ESaOwVKhAKRUgE0AQAAA7IAKHBgwXwFGFSsJq+IqTgTZiO0oVhbS6LpNHZ+YuoNJA8CtTEkBwAAAGjgIRYP1lQMqOgGlCtDQUVE4htKQtpdBNmjsAA56cAAUQMT0jQP4KlYTVwxUnAmzEU0YKi2lIWL4sE0dlJHuTEoHpRDaSMAaSBJwAkJRs9ASkKEmwpeIFBRcGZCwKlYW0uiNTR2H_0IC36kAAAAIDh+AoP2lQMuOgBlCtDQUVFCxtKQtpFmC+DkAAV6cAVQAAEBwBRhUrEJNXtkisZUTE2YjjKFZYiotpdFWmjsKDST_B8jJWpgFUADZmPQlBgSCROoKlYTVlRUnAmzEA5IrC2lkkqZNHYD1ByhXCLTQoJxspjkeAKYWB1ZQrEJNW0FScCbMRCkisshUW0sjfTR2A9KoRQEKU8KCcXWsxd0eA+XlwMlAOQoHalCsJq4YqTgTZiKZbDwcS6ONNHYDWfpMDqyIABLQkAA8iAKBgxiVAbvKklBQUTZZUBxsIxH_joAAAfAEAAC+KgFyyoGck0pTMFBFMMbAMKlYHGuhKEaGBIa6AQIKCYHAAQgA8iAYxKgN4lSSAoKJssqA42EYj_x0AACeg4JwsAAC+KgHiSoN+kwpTMFBFMEbSkDjXQlCNDAkNdAIEFBUFgAIQBAVJYHAZpKgJSFRN0bSkDj3ZeByAAFnBb_wEAGguACcVUwrASn_w8TVS5IrewHDlEynMW7FStBxEHEug5AjIAAEBhBkR8zMg3B0ABYJSBKQrgpUz4G0pA4gwXgcgaQHhlQABCCIBzDgVBA8DDlCsJqmoqTgTZiR0kVhbSyJ0Om4Gkkg0AuVhOeklwDrGgZAESkEIOfKFYTVwxUnDSTfemQppGPBxLIhI6bgaSSDqi5WAARoOAAkNBDDwfrKgOQlQVE5CVAcRjMQOQNIDUSoAAAAkNAEEisApFSsAUhpJrPTIUgcS6LAOm4GkAm5QvAAAABmQUgKQBK0tA2bnQKk4aSbMUDkisLaWRxR03+wtBpJIOtKF4AATx4HR0BJ2QSgFcoVgNAKlYFEaAVKwOIYPNHZhMiNQEpAAI0HAUSkSYeAPxUrAlIVEyJtKQOIMF4HIGkB4ZUAATQORW9wTAkQqVgCkNpNM2ZCkDiXRDR03A0gHdKF4AB8mYDmVvcEwKvKFYARyRWG0mgRyRWFtLIB46bgaQB3FysCqQQscRAzAx9SAAqoBBICfhUBXEqZ4FBRK4lQHEJ7HQAAayoRsHAARtyDmLlsFpMyRWGZSNTcFScGjUmzFXpIrEGPVUWDdvLJJmoSTKSSiTVMFysADKZkAAfmAJKwEkZAA_8nHPVhDHwAAXDYAAGxMEwDgAAAkLMbDwC_JFYRRjRUnaUFEkmzTMhSFtLo8c0dgaQCOFC8AADnDDY2lAQAkrCG6YAeLAAEDwBqB4ANQPAAyouAAIIAABgYoyUACiZGhYCUk6jKz5sKQKKZjYxxUrA4l0DSaOwBaAAAEUOBGhYAehUrJ2GU1eiSKwJsxFIHEujjTR2B+ZuDQw8AAMgqAA8VBaJASknYZN8OhSAkFKmcA2lITGdN5dByF9A_IHAF6A4CDAAcUACQVKxGBlNU5kivBp0E2YvuKlYHEugaTR2DwkYA+qlATkAH0iMISkLQmyUyRWBR_+ZXaKlYHEugaTR2eSNiiAAAEaHgX8WJoCkJq4YqTnPUom9HMhSBxLIwk0dgADkHDpzM5HQDphoABFMJoHRKFZ4pCmq+CpP_EqpJNmIpDCcXYLF8NuaO1jFQbf+jQAAAbiYAGhWixEn5MjgpIqVhNW4kisi0kmzFN5QrGIaS6J5OHM1DaAAAQaFgpowF+vAAb4MQTMVBxEeFQFEkEVESCi4hGA6AigACQSAAXiQGxs7KgJ3WASkRUZAkSIZ4yRWBhSahCn_QEGUggBLocTCH0D4AAIocEsCwDuCpWDGauKKk5FCbMSIkisyhMW0sjFDpuFxNIOWKF4P_agP0MGcACKMTivgH4yYTIZHZyYAk2TABRIoAAAAEIWAAHjCKEwNGKlcJJq98kVgTZic8oVgaSqJ2NGaBDjXQO6oVwAAhCwAlDIhC4DyZUBvkqAom+SoKhxKYxH_joDiABoiAACELBmzkPEqIE4AHKFYQpNkqkisCazsyFIlLaWSa8gWg6gNMVqYDkosoFlARx5PhMEpAeB0KQKJwjZLZQrA4l0ccdNwuIEElYAABExxGRQkRgtPuSK56DWS0UJqqzBmdskViUNpZIwlR5qKVMp0U4mUKaTZaZa6VRWidLIEdKQCThAEkFSsLKsTYUhpKJwjYUkZOJZJyigeLTPXcCpKsHAFgALGDgbMlo4EGA4wA8yAJC6DDwZBpJEAzQiAGaEQAf+NgAAAAADjjQ4PADyKlZVZqj8kVhpJsxFMtDi_JYvjnDpvCEOAAAAI0FAbZgalCBUGopoNDFCORWMFScFt2Eymq42ZykAFsHMijEem9DgAAEHDIA4AAAGsSegKaCWdUtz+NmdFScIpN_iZCksNtLITU0dhBoWAAAAPBQAAxpPQQGSKwmqpbGpMCpOEUmzEKZIrLDbSyG9NHYAE2BrzREAAC7PQQGSKwkapbGpUipPKaaTZiDEkVlhtpZDemjsACbw0FWGgWgDYTEPQFI5tWprKNmZFScIpNmJ1SRXRS7bSyOMOm4EoUgBqAAKAOAAUTFcuYx6CHSRWUWaq1MamqKk4RSbMRWkiuil22lkW+aOwC6SUGDiQAA+B3bo5l4LB8DhCoAUgTQUgBJJQlgQbSAMDEgADVmC+PR7CE2ckV_9SqiNZKUVXaRPGJ8yRXRaqbSyOVElzUalUyuGct4F0YOJAAAdGASsZPQZ6UKwsjCSRWYRqTelmQAyhWKUZsZinLeWQ4lOEgABBAcAAArGIPQFIiVUvvUNmZFScGkUmzFjZIrHolmS+bSyDkACkPA1AAFAHAAwYgNs8HoCkVeqX3JG0zSRWDSKTf+mQ6yRWPTKNxw3lkHP9i4AARwHAAT52Zx46S2IABZgAjEGBwgAV0AcrKKj9ysRmKguk0mMVABXFGN8HAADIA4ACxA5ikkINVfFyvcaENPNHYpDjURqvAuVgcS6BrNHZ0Q4AAZEHAAABJiPkIE4LNJFYWRuxUnDiUQRGwpCKcS6E9NHYUGGgAY8HAAAAFGOsIE4LFJFYWR7hUnDiUQ_JQrCqqkY4l0HIEqEYAZAHAAACViD4JkZ_pCTwVJzKWSSlxKPSjZyZIrlpFtqbFi+DkCVCMAABUxQkFmG6EyMG1kisLIp4qTlxKIH0kVhFtpZELmjtHQ0VW2hEEuGQBwABGS3KGfgffiFNoQAG+NQMNlR_A+JSFROubSVKgaWEijUf8HAAAABPCgAsIwdg2CUN_HQETjBuJcNJRRJvlQZSqLQAIXCQAABSCgAJCZGGQVBGpQrGgJwKRKeeTKYu8oVmm2nHJy8EkABBAsAACDxkFQFInhKPibE_JFYlHJNESZCk0204pgXLYSQA"
noncomputable def WL40_2 : ℕ := zfNat64 22427 "QcTgGAgFAQDkP_A0pD4DaDamHwABuBgAAAAAwEAAAAAAAAAAAAAFp8AAAAAAAAAAAAAAAAAAAAAAAACEuAAAAAAAAAAAAAhUgAAAAAAAAAAAAAAAAAAAAAAAA0BgCSTABPJgAJ5MAAjAoAALgUAAAYCAAAAAAAAAAAAABQEAFhYACgkAAUEgAFUJAAAAABgIAECA4MgYEh6C5WE1LKSKwMEpUxrKQAFqJAAEVFgAADAQBwsfB3NCAExoAAAAAAAAAAAAAEyAHFwBIaAAAAAAAAAAAAAAAAAAAAAAAAAUBABcWAAwLAAGBYABGBQAArgYAAAfGgA0uAAjQBMWAAAAAAAAAAAAATGgBAIF1FQCsioP+JwrIqAAKAUAADsGAAAAQoQTAwEKyoCUhUfim0pAAEwUAAJ4KAABKDAAZPhmgoFmFysJqI8kVhURqMQuVglAKkAwAAeBgAASgwAISoIgYigMEKyoB1pUFRHWlQAAiEgAAAAEQMABIWAYGAhWVASkKj8U2lIAAiEi+QwAAAAADgUEVSoCUhUfBm0pACsBcdCGAAGwsAAAACUgEKyoCUghqPwzaUgBWAuOhDAANgWAACiHAAUUXKxzStNRlkisKiNQkFysAKvF1QAYADzCQBAoAAohwO+FQcZKgwhiPhSUGo6MNpSAFYC46EMAAMg4AAKIcABIyALIKgFKFQIo6JIpQqABMpcAAHYOAACEHAaDSihsFIpBqaM0btZJFZQSa0EwbykANal1SAYACIhwAAUQ4Ob85AQ5syBSBcrCakFJFYFEyZg3lIE9moXShfUYGAAAmkVAxASFAATIXKwmpZyRWG6DiijMwbykCejJSqpAMABdR4CzUQNaJAyABDoHoKCCZUBKQqP_TaUgbQDpQwAAiCgAALAwAAUIUKfAEzIAgGAB3ZsngqAojWCoAsk0AABEFAAAWBgtABxUD0FBKQ56bJTJFYE2Yx9KFYHEugbzR2dKGAAAABEFAD0FBKQ6GbJTJFYE2Yt8KlYHEugaTR3DgGAAE8FCAAYAAAvJA9BQdRKgOQlQfdUKZyEqA6qqYgcnShgAHeRAADkABwkAlJVJGxCbJTJFYFH_5leIqVgcS6BvNHZ0oYAAAACAsAA8SF0JSPWVn6mwEyRWBROkbSkDiXQNJo7OVDAAAAAMFgF0JSPaVn4mwESRWBROgbSkDiXQNZo7OhDAABIp2AAcLAyAlVIAcJANelQG0yoKibTKginWRy8FU6UMAAAABAWAAcJNnEwJlJFYXQ6JIrDyVSUgcVULxdI6OhDAAAAAQFg5MUOBAegoP+FSsLNmzJSRWBNZ2ZCkLaWSanShgygFXIE4HmkTcFuxYGRklrz+tG6WvsQAKfBsJBsDgboVALcKgKItwqA_sTAAAIQeAADcDAASPgoEl2EwKsKgE+FQE0T4VAQQAABPEQAAbgYAAJ8ARLgoEhLJQY_Kggcdf+KlYVEa+XKgIIAAAfhYAANwMABI+CgSE4LBAkqAlIVH_ZtKQIIAAA9AADcDAABPgCJcFAkEwWDH5UEDjr_xUrCojXy5UBBAAAGwtAABuBgARFyNCwCii5WeZKpqMskVhURqMYuVgAA1AYg8DhUgABEgwBgZ+Gh3hwoxIBaFysJqjEkVgURGmDeUk5AJA4bFpZa6BAwuAAESDAASNigDgihwbDKgmo6SRWFRGvlyoDCAAAeYmAADcDAFRPigDgihwB9KF4B11JQrAczVtxcrAFNdIIAB5iYAANwMFdWBuT4IRXBMFWAKgtCVBBA6FIVEa+XKgAAJP4lYC6AAG4GKcnrwBJZECLAQrKj+gsSkKj8U2_GVADojYAALmVAABuBgFISAj6VE9E0dSkWEbVEH5o3lIAAAArh4AANwMBQBwBOC5WT2alLJFYsI2qI1BAXKwGvOiIgmUAAVwsAAIkGIU_AFBgchQJyLlYTUcJIrCojUPBcrABOhcdMOAAAx0MENAAJDQFoUAxC5WE1TWSKwqI1FEXKwson4+dk0AAG4cAAANwkRQOCRZUACYqVhURr5cqAHUHQAAcIKAAAwFAKQcBj8qCy8o6_4VKwqI18uVADqDoAAEgNAAA2CgDEKppuZiFJaStGzdCBUnJqJZQnjWUlRDszYyaOSaAAqYeAAGaFAAhZg2CgGZFQDOioCiNlKgB1B0AACOGgABQBQBblIbgoCjlsqA7lY6lIEUWvDKgB1B0AACOGgABQBQhgYh1myIBSdaWjpxUXEqlMCoAA7CwBbgqAAAEQUJHHVmyIBSdcWjpxUXEqldCoADbCwAAiR4AAUAcCzpEApgMbFkLmSKy4g6UK9cDaUgBS0mAAJoRAABPChfwiPsTIyCGdJFdJLI+EkVlxKI1WkVKwVszBJQACaEQAAoAoQY8DxVwPAzGx4GlkwDHyYATOTAH_jIKgADkAAUAUE5OI0FLqIgaoVAH0Ki4k2VgAIpFAABHDQAAoAohbm5v4MdAPx0BIFBFUqAyaVBUZr2cqAQIFDqOg4AAdBwAAFAYAyB8DoUAAKY6xiVBUf9m0pINFQSSCAAF8FgAAKgwB9D4bgo0ghkqCPh1KQqIOjZvKTMasEkggAAaA4AACoMAe0+HpFgiiVExxwdCkntRGspAJJBkWXAABDDjjBQAAcmJaVgBJWAkCgiuVASkKj4E2lIAQ3TgAE+EwABzBIHYASYgJAoPLlQf_OiykisCjww6lIGUG4CBcAAmhUAAcwKCCASBQKQLlYTUupIrAmjFRRcrAGpBEnhwArI2AADnBQASBQExJgCTkwTUOgADCI6DgACATAABCgpKRsJABkLlYTVNJIrEoUR+mDeUgYZ7qlKpoAAERYXEIDwAAAQrAA4FysJqqskVi0slENZg3lICtXMc9pNNAAC6LAmgQWBeBIAPAmDgKhQCMLlYTVB5IrAokVMG8pCukUUqmgAC0HsCCwAAUhoDl5UOiWpqRskVgUe7G0pCFDEFNAAHwLCFAYAAEkS70VB8MqDCGA+FJQajWg2lIQHYg_2nAAD0Fg+AMAACEJALIKgFKFQIY6JIlwqADBIwAAPQWDFQwAAaFRiwCaKlYNQUlBKMvDYhxUrCFjEFNAAHoLGkDgAA5vwAcZAMFAQtKgJSFR+GbSkACYpwAAHyBgAAdBYmg3IqVh_82LKSKzyOwUTkGzOUgYQK8QJwLIDQ1YMVDAAAAyuFIaAlIWexmwZyRWBRrAbSkLCAlP_HT7FoBUqsHgCgABGhYTSZTABZQrDLNWIkisjEXFGYyknrnVzGAhAskkBxqlsG8FwAABEhUrCalnJFYMSia42ZykDCAYCBOjoSCySQtYtDSoYApJc39OAExYDA4AmJMAScmCoh0AAYQ2g0AAAAELBwcHdgAaWB4KPoa9KgZcdCkKjyg2lIQHYg_6nAABxHiEpiAgAAEwkDwUE5OlgKoqVhRmq2SRWBRIqYN5SFdHvJVNAAm8THuzoACZAeCiSApNnKz7zh23kkVgVZqyIqVgXQRyEDwLofqNhiB1gGzAj0aAHgokgyoqVi3FCvNVOFScCaMQCFysAalUAA24ZAdWQMwG7GD4CzIBg5g2CgFHFQBlioHP+joMsVAA_daAAEILAABSDgBILwpBUpBCe4uVgEg6bikKiNZSFZPvJEd96cAAOAWAAI0HByhjfycEpDCCkoNRn8bfPKgkMzA5omABiA2A+AANCwNEpwCmKlZYQCpIrR8XUEozMNpSFlDLZMVmIgALaH"
noncomputable def WL40s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL40_1) (dpk j 2 WL40_2)
noncomputable def WL40s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL40_0) (WL40s1_3 j)
noncomputable def WL40 (j : ℕ) : ℕ := (WL40s0_3 j)
noncomputable def WD40 : ℕ → ℕ := rdw WL40
noncomputable def ready40_cuts0 : List (ℕ × St × ℕ) := []

theorem ready40_cuts0_ok : CutsOk ready40_cuts0 := cutsOk_nil

noncomputable def ready40_0_state : St := ⟨26112, 285696, 51168, 255307, 52016, 95804, 29666, 44151, 29666, 44151, 29184, 45301, 28545, 232684, 26112, 230251, 77280, 491961, 129296, 543977, 158962, 573643, 188628, 603309, 217812, 632493, 246357, 661038, 374538, 687150, 103184, 307323, 132850, 336989, 162516, 366655, 191700, 395839, 220245, 424384, 348426, 450496, 81682, 125470, 111348, 155136, 140532, 200437, 169077, 373216, 195189, 399328, 59332, 81875, 88516, 111059, 117061, 321200, 143173, 347312, 58850, 81393, 87395, 291534, 113507, 317646, 57729, 261868, 83841, 287980, 54657, 258796, 0⟩

theorem ready40_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD40 ready40_cuts0 113 19930) ready40_0_state = 57765 := by decide +kernel
#print axioms ready40_0_cursor

theorem ready40_0_covered : Covered (toCl ready40_0_state) :=
  ready_cover_cursor WD40 ready40_cuts0 ready40_cuts0_ok 113 19930 57765 ready40_0_state ready40_0_cursor (by decide)
#print axioms ready40_0_covered

noncomputable def ready40_cuts1 : List (ℕ × St × ℕ) := (19930, ready40_0_state, 57765) :: ready40_cuts0

theorem ready40_cuts1_ok : CutsOk ready40_cuts1 := cutsOk_cons ready40_0_covered ready40_cuts0_ok
#print axioms ready40_cuts1_ok

noncomputable def ready40_1_state : St := ⟨26112, 285696, 51168, 255307, 52016, 250271, 29666, 44151, 29666, 44151, 29184, 45301, 28545, 232684, 26112, 230251, 77280, 491961, 129296, 543977, 158962, 573643, 188628, 603309, 217812, 632493, 246357, 661038, 272469, 687150, 103184, 307323, 132850, 336989, 162516, 366655, 191700, 395839, 220245, 424384, 246357, 450496, 81682, 279937, 111348, 309603, 140532, 338787, 169077, 373216, 195189, 399328, 59332, 81875, 88516, 111059, 117061, 321200, 143173, 347312, 58850, 81393, 87395, 291534, 113507, 317646, 57729, 261868, 83841, 287980, 54657, 258796, 0⟩

theorem ready40_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD40 ready40_cuts1 116 97) ready40_1_state = 79766 := by decide +kernel
#print axioms ready40_1_cursor

theorem ready40_1_covered : Covered (toCl ready40_1_state) :=
  ready_cover_cursor WD40 ready40_cuts1 ready40_cuts1_ok 116 97 79766 ready40_1_state ready40_1_cursor (by decide)
#print axioms ready40_1_covered

noncomputable def ready40_cuts2 : List (ℕ × St × ℕ) := (97, ready40_1_state, 79766) :: ready40_cuts1

theorem ready40_cuts2_ok : CutsOk ready40_cuts2 := cutsOk_cons ready40_1_covered ready40_cuts1_ok
#print axioms ready40_cuts2_ok

theorem ready40_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD40 ready40_cuts2 128 1) (ofCl (RC 0 2 1 0 0 0 0 0) 0) = 87967 := by decide +kernel
#print axioms ready40_parent_cursor

theorem rc40 : Covered (RC 0 2 1 0 0 0 0 0) :=
  rcOfC WD40 ready40_cuts2 ready40_cuts2_ok 87967 ready40_parent_cursor (by decide)
#print axioms rc40
noncomputable def WL41_0 : ℕ := zfNat64 33247 "BQJ9Df5giiAdQAA3CQCdD4KNXMGXbaKgO4XFJDGlQT0MYXATUWgtwJRAOoAAHgoBOZ8EbriJHEZpixWFljIpJlMuCeyWDZcBNRaDX_MBTKJJA6gAFfCgpqR2nBHO8AB2gFqEAwEYQdcjAG2HgAAw8AAAAIRiAAAMBAACbgCCMCWQgE1TIop8QuCgk5i4LrPSiJcAAXo6AAFAFADKQgCQsjQUE5dmYNyigySheFBkvSC4DzPf_mV3S4AAVh0AAACEQgARkAqSZFFHmlQUET2VAeZ6WvLhKAAKkIJ5DAAALpCG4eCczEouuEZkZQvCgyXoxcB5nsxu2XCUAAIIQnYiAAAdaEACMgTkHBozCKRXllC8CDJfdFwHmezFKhgvEoAMyOga_2WgBpjiMG5sAHqQAG+APYMgLLlQAd2sLAeZ6eiXgAAsGw9AIAAAPykA1gZAhJnlQEkdyVAeZ6RNNHYAAWDYegEAAHIDxQgrAoCCF1Uy0O8oVhtMotLgXKwNv_iYAABUHQ9AIAAuRSAwC4UhIJyJw0ZhFIriyheBBkvcC4DzPZjZAuAABMULxYA8AAADEIGsXCqLBOUuGzMoodkoXhQZKLQPM9lKZbXLgKIBVREfAARQABIQL4uBORiEXCSM+8oXgQZKJcoXgeZ7MeMFwFEAqyuOgAAB+FwC75kUUgmVACwSoLjPTjhcnYqFHKQAFU4gf_dgbAXBcCcjEIuDEZ9pQvAgyUS5QvH4dPw8g6Pn8xIIYLwKIG3FYOoAnIyACWhAIy4BEcyKKNVKgBAZUFxnpSQukIUQAunEAJ0dAeAgE9CBwl0tFwH7OmmGjMIokkoXgQZKLQPI9MiFwFEAKO5S4AsIAQkIJoXAS5v_lICeRkEUeSVACjyoP_PQ9NNF0tCiAFEAIMFwAGRrnDoJyRQyKKEsKgACBUBPQDDykA+5eFIAOcOgPGwCYhAtC6ei4BkhszKKJdKF4UH_JN+IuC6z01eXAUQAOgAnouB0dAScBZIQBRxozCKNpKF4EGSkjKF5ZCoPI9PwFxVTjSQOJxg+AD7IQBD0OKlIDIxkEULiULwIJwYuA8j06EXFVOIDBHDeEEATQRA2A9kNdF4AfnSTDZmUUZqULwoMlF+ULwus9JaOaqcflpQI4ct6PCIAAApyH3a0Akg2ZlFE7lC8KDg8mFoXWenbS4c1U4gMvaN89ABDQ8DseA20IDnZAnKkDRmEUQaULwIMl94Xe8Kg8j0vcXFVOIADnDeAARoOAHOhI0TBOVIGjMIon8oXgQZKLQPI9DOGC8pJx_QlARR05gAEaDgHS4xEJCeQNFGQRQ2ZQvAgnUi4DyPT0BcBtAl4JAAEaDizMwRmhAgbMxC_p0pI0ZhFEjlC8CDJRbBQ8j0PoYL8DVTiACpgzgAAuCipqScdqZuzMa8_Aa9cIQNasSBExUnJ6GeLlZSZ7JTiFysPNlno3QqTgACUqsFAAAAvXUYDJsGgfOcPwGllQA0sqDzabSnxKQCiAAAG4KAHmXUYDANTKgI7lRMQrKVB5741GEHIBl0IrAAAG4KCMAU1wBIaLCGgnIEYyosmlT0KSULw82mejrShWAUQAAAAexcASGgDoSoiGRElyomIVlKgcDx3AI1azCDkAylUAAAIwADXE_iQC3JFZPRjZQvKTPZK08oXh5NM9moXShWAAZ+DiaAK2OgAVVxuI0E5AjKVCH0qekZSoO08f7TPQUgFEA5AkAAAPYuAJDQB0JURDIiS5UTEKylQN5472kwg5AMpVAAACMbAY+BAZNcPoVgwaAaiVmYEsVKw4l2SoMLlYeU9smuekpAKJBFoAAH0KAH3XAAp4bgqqg0H+ToCI5UARHKg6gSCbOYABtAADcFAGAJhuCnbjQDkOwhA_SoGs9BrlQba79waAAqk9EoAAbgoAx8COFwCokD0SheSEfWULyYz2SskLlYebSk5cxg5J9DAZSqQQB+AQAAApuCY4QGQuADVQAgaDsSQyh_oyARQPACKB4AHxEwAAAAFQCXFwCsVSUXKyQzVexcrJjPZKtouVh5tKOlzGDkGQcBlqJ9kJ+BZqIClCYgZkCkF9hmQQxIGPFyskP_TZ3xcrJjPZKyYuVjk82lrjBfByDQMpVIIGDA4AAalhBWL4KQJoDsh4AdkPAATQAAAAAwEAREuAGSQ7IQF7SokJYMqJj_0+MFlQ6547mkwg5BoGWqg6gSBqAAFgL1FLh0DwabKiQjEC5WTGeyVDxcr_MdHm0tsYL4OQaBlKoCUIICVyInY2ZAWRcAdCVASXKiYhOMqrI5HG0mEnIBlQmrAAADcKI8JVYQDAQpAmgOyHgB2Q8ABNAAAAADAQCxsIBCXBQNNCGgAF7EQAvYiAAigAAAAbgoANmMABwgAJkDkLnEAoKkAqkqAHTlQcQwg9DfqEWSiAAALgoAZZkAhpqQYgAXJwA9SYAOCTVX_j0BNg+NIWEqgAADMKAK2XfYkT46BRNXkR8P8XKyYz2SlyLlZlOvHWTWXQ5po7BpQTCUQAAD6FBTHhcaZ1JHO04RAJAKQIWlQaPPiFpUHk06PPgUgAE0IgAA3BwFOCQLJJFYEbSheUmeyWNpQvDzZZ6G3JFYHECv5EAAEIKARbhAATJ4AWD_hcAwAmAGAEwAf8LgAAAAAwEBDLCCpXwBIyB0CKAmcSAEziQAEUAAEB0AAA4GAVvhAETIACNGhDQAC9iIAXsRAARQAASHwAABgIDUOhTSejGC5WUmeyVnhcryubP1cO5+mrPPRH5IrLTaQFcqlsAAnIUBcbBh4eAEhckCI8wkBZyhWA_EqD_J8PxKg8mmLp8SkAARhEAAApAba+DgUEdIoXKwmr7i5WE9ko4i5WHU01U8jFVLZabakdgzn0nIAB9h4AAPMDPJwaClcFysBKKlsNoAQuVglHuMxpRBcrDiDUn4pFZJIF0AAM0PAASFn2HqPDwLUPIYbRmxcrBKE7SoNppB7ClPANoSgNgAAFIAITgAh8AIOgB5cASGgAAAAAAAAAAAAEg59g6vQ8BBDaCkEpZZSGcVKw4qCaiiEaUp4AArDYAAEeAD8IEQaiQ8DWESGG0FIJS5ykuUoVh5D6VkA0lkogBehKAAcHMDTwgANcAFDgBoECIMvQiD+y0AACX_ikART1ycAAEZeAAAAHlwBIaAAAAAAAAAAAACnwgAdcAnjgRBjHHQMsMgCiAJQAimRUoAAoy8AB+g6AZIbAJY4EQZMx8A5AqIAJVIE6kG2ohUAnAxHUPqMwAF4kIH2HuEIQf+MG5apiCiD0gxiUqNqFMLIgRUvglAAIIzAAKKOgTw6KOgQwGIXbEJQRkimD2ek0YqhTKiTUJKlMDpYQ2hl5qAAFJQoY6BSUlaDgUsVAhgMQui0ShTJFMHpBKKCFiuGUDacT+7EGkIwNQBehKABQcAApwAZKAFoQBAuAJDQAAAAAAAAAAAi40JAxc1G6M_CVOkASBgRBq4jQAGRHYFECIAogRAAFQmAAB4PAAAcgY5eB84QAGuBaUQIgwFGyoCTRcE9A3FysLv8GoDCWEAnoABPDoBiycBewgm9cCINr8uAIjLQLkqAANJFnoWQAP_HQABPDoQcClrjB8E_Hz8NJRFIUbK0guVopKFZdbDPQMhIrLDZQOikRJRKbS6ABBgoEQYyYwfAegJhJFYURMZQvlIeacNU9OhlQV0ACaLQ0mfm4gQFLzCaToHpXAiDHgJF4FkACZUAATKg0kUAAD8B0frTgB8h8AA8uAJDQAAAAAAAAAAABTeECIMOYsbgOQPblQB7cqAAcgAAfyUgJ8JwAzKIEQaNhsCQzyGBZ0qKSJiLpSdgcgJ6ABTQaz0NoAAOLgCA0ADFgAAAAAAAAAAAAATIAaXAERoAELAAAAAAAAAAABBwKeIcNwykkMqgkYCrYZC5M0ZhxMNh38zE0_qxBRCZ6hXKacxSqoGEAAOkvYygRBgOkQBAMgCKAEUAAAAAAGUzAEU3jgmUPBwgCQUCINHVKAAIoB_9KACggAAAAAAHSAj3RNOuMnjwKmKKAK_8ZADQOWMQAMQAAAqEgjYAD_DcCGC0BDR2EVCqQnUp4RYFKQ5PQdNwyhZEhKE8AigUYkVlN30pAGEAAiMdMaOwP8NFwqiFfadTCKbxApjma4Ey0UshGlCeARQKMSKym74UgDCCKkI4bhBitJKohKqpTxiRRGKEMcheOm_QnIy0Usu2RiaARQKASKym70UgP_MQZgE_WeXsGwB0FgrBVCKUfuHRMDpuANE4shRAJIa0Kj_6cASMYhHneKAiDNENgTMSKwLqEUNwHwaRTi8FUABvhUU0AkcxASAATIAaXAExYAAAAAAAAAAAVc+g4FbMOgu4EsJ9OJVSUyRHUAdNwBDhrDSHiUJ4BVB5RQnKaWUOOMQFxcKAiDEANHYApPIYYcZKVtCyYSKMwwdhdLIBmjeEEAqoBNAD2rwBhMPEwMGG1orb34B3DgRBrUEwHOVJ4SQ4xcrAqCF+pQvDaaQ8spAACkNiUwUwgAALrgDlMCIMzgaD3RcA_cqAIllR_huApoAH1DYDMpIIpABRCUJTwgRBgyGjDYAAAAIRHQAAQCIAACJEAgdSBEGDoGPLgQmryoAq2DKhAmmETUH0ADpyMTU_4hA306AEQYQhfhKAAAzXJSDaEE+6nAAMsMj_Z8AFoNgBEGEIY4SgN7qR_5GAyBtCCdLTgAE_mQH_kICGGwPsPb1GgGpPSKuRSnhFrJNPQpTw2hNKSASQMsbMwsp47lJBV8VHlj4BNNcNwkvwWAcgPLSgBpyUABtAAAAATmQAFq4Jw7WxcAE0OonTw00U+cpF1KoflSgAG8KROQAphsAmnCCcOAMoDTkoAaclAARQAA9JQAAJzIAnDglnQJkbgDZKQAbRSACLScABFhSCckEABU2ELUNgiDo9GwEUBzSUAAILgAAABCKwAAKD4AHisGMeQwU0qSyek1w6ZTOpFnIZEqoUwy1Ek84RqTMQnoSQqKVMoM5HIMiTJYLrnkB+FEkk1JoVUqfbSKKgudhkcSlP6WpGWokkimoRpYE9CTUeKJ1BGo5AmyZLLsBBKwLZ5DAN6ZTB7TUiplNA0GaspGD5RDKElVyMSRyAEkUKZTAtBHM5AridLAOEaGU04fmEokkozUmk4Up5hGItDL+FKfUa6EkivvSI5NACSh9Sn0EgB9DGo5AECZLLspCyeUE4c3o+hgmZark9JoAkiODEyhFDaAokZy6RPAAKorUygzkggnhMlhrVgCFSAIhQRBwAB1AAAR0AAWEYAAEx8AAAXAxoXBgAdSAGIQAEyAGlwAwSAChwAIKAAAAAAAAAAAFWUg4Tc2oCLg1KKBEGeONB3EqBSakLgK__Jh0hUrDaAEEJ+RQABSAA2ocNgqAIVIUXJAiDACUBXREAK6IgAj8dAAUsIgALDjRMhprSBEGJwPGwHIFF2Q8AUqHgAEYTAACEHgAATjQcjY3N1JPYg8OuAYCb+HBoIiAYEPADAh4ANBEQAAhAAAMBBPb1pPTjoGTmYaGjsCAx4eT1tu"
noncomputable def WL41_1 : ℕ := zfNat64 33243 "FbAR1kSWBAjx2AtIuVgYZKjAuVlFOpJHpMDBeYECq0bLiClkAAeACBJCiq9bMA5AviVBBLI9QuVl9F44kkScYNwAAECASV2AGbAEMSH0aTovWwnICji5WTGuyVRxcrKqqh250kZIZLwAAJNxAH81ACOgFsWKsSAHIAGUh7FysDDJRrFysAgjRziSQWmBPJVAtRQvCakOA50UknBgIAsNcABlkaDjKHFDoCIJUARBKj+SMBxQuAAFIAAjjoGEJupLwPrNHYAoi5WDUuyUURcrKqbSSGwMl4f7OgPTFxIxqNoBBACSxK6A1TR2AVQuVg1RovW5LKQq22kjNC5eE5AQaULyT9xmtP40IC_ID8ASCMlIvARTSAmi5XQRqXZKUAuVgbRCPaKF4AFIC4i5majaAQ5AfgnY4jOcvWwfsdNzaPCSgOFSugzGsyUmhUrOJVNtJHlljMJyALSSCBaN9BAdR5DLPBHY0BfVwS4OEIKdMdNwIiaOwBaH_1zHpMmFoHEkhDCxmYEAsgA5AYgCAA64CELI0HAPCOH4GLSoDCZvKgOpJBqGC8wJdQK0WMwCbUQsgCgrg4QkGwV_huCMw0BKQKNTD6UgcTCMyPnYBNP1KQEEHIDEADKkAwrhkU8FwUACc2AAwTBpADBMAAQESGAAPQAATkQBLM4NpXCEFf0Hg_8pAM0IgBmhEAAAB_ROAABERAEergmCgP_IwQRmpMEkFDkwATiTgANNFQAAJyIACiUASMgB4sAAAAAAAAAAAANZhABpIQgqqguQ6bgOPJgBx5MABNAAAqoBMyIDVl4JyAKQrtrlIUp4HhbDcUQvilPAAWmoVwmlVW68ApBXQHIApKDoNYt00U4OQmAoEeymKTp5Gz4zCdPCdaFSQqISfxpE+uukUgUgBoYk9F4ByArMoVhJJMuW6aQskVj1kCUaSaACUJ4xAAqgo1Orl0NEFQR6OI6yWjPgTmjv8DcEkEJIroM9LJNFJVDKTean1NGoEklchQEUqY9bkgRySXQFJgmZnBmsbCnIyNi82AIS4MJJCEFAOOMgDUEQAagiACDBUAAKQAH7CxMzNeOzdOT3ZbWgbfSAQjwhAxBBkBsAXQeAC6DwAAiDgAAAAIQMAAxCAJGQAIuAGiwAAAAAAAAAAABMi8AhIghBuYlQAFEBxUBlE+FQAAlDgAAAAEIMAqReEIGBEVKwAKpDi4DLAkmFoAETKgAE+BQAAQgYBR68IQNKQNcjAVTglwGWShjLF4AB_wGGIH3DICIDAANAYA6G_DQCUaAWp8AHEqTQBAdmIAB1A0AAE0GgAAXBQEajQT0rgzESypNAFETCMhKgAE+NAAAAAGgoB0GIwfA_Z4_DCUWslC9DwILiJhkoCyheABIBoAFMGExCAAB3CgDLQAkNATjB8E2nj8MJRaWULyImGSh9KF4AArDgAdMKEwAAAA0PEZjQf_PitDMRJKiImEZCVGsCgAAABERAACgFgAlGD4MDPH4YRYJQvIiYbYkwt_AhAAACQSAiCYeAABEFFmASjB8GBnj8MIsEoXkRMOTSYW_eJgAAFsJARAABQBxCgAhWAlGD4MDPH4YRYJQvKsRMPdSYWgMcMgAAIiaDgAA3CQABFYCUYPgnc8fhhKJSi5WRYiYZKfguVgU0gptLGYBX0WCIAAIkSC0AA66yT8YPgvs4fldGvFys4xEwyVCZQvABblwAEMAoAAEGHABqxbMOMHwf2cP7dM1dDoFys4xEwyVvZQvAnpz4uAA1wQTAABBhxWgCneBWqwCEzCQmAfGfBlEPlRRDCAAA1GgAAAAUAcB4ADVgAKkASSgBiMARLgARMANHgAIMAAAAAAAAAAACBi5XI0A9KjrxGoqVzWIgVXMZRlIAPoSgACQjQAALwoJPLGZGRg_NR6PaKXSppxHyhXNYjXaiBAuVgWVNKxXQACJJx4AAF4UApqACcajC5po0A9PArxHkqGMRrotEqlIBdAF6CQAAALgoJhLkmjB8BIHzsil0PIVKxjEa7JUwFysIpVJIFVElgF4EgqAAALgoq7M7O7OdAH88PoUGsYPgPR_K5nHJlC8iJh_6TfkLgAkMjABhgpZAABMDAA4nh9CgKjB8HUnj8MotMoXkRMMlAcXLyWRsABFCaYYKSBaAaAAGBiDACQcPoUGsYPgPR_K5nFilC8iJhr+TC0ACCFwAAdioAABBBeMHwqj0TcxXx55QvIiYZKVkoXgAMUsZkloIBiSheAAMEKAAwjAXjB8B6YUVM18cmULyImGSiHKF9dAL4GRJaCAAg4fgACgCiPAMRg+A9EZM18cqULyImGSkDKF4AdOMiS_7QgBWFC8ywEAAAAIRBsHP6HgIIz5uIFlQGTCLTKgAMsZAGk+gkAzBQASQBiEwbBwMRg+AOzh+V0AyULyImGS8mLgAFQZElDoOSaAcAoAJIQgAhKAGHwA8uAJDQAAAAAAAAAAAAFRg+E9AeMV8FJEa6UVeFSsAklRzBuC0irBZM_1E6olFKF7kh4AANQFlNAARcfHoc40B6z4AdBUAEVKgAbiZAAJoKhCgBZAKIxDILB4PqIQZQwZQvIiYZK50oXgf4SjU5kBFsoEgKF4AB8kYDx5ZYzbGMHy6Tk2l06KdKRbEa7JVzFysAkgHTBmQZSRXOM2MKLpyhf9daAeYVBNJ3BHaMAJBw3Bw6yBOBFDormcaCULyIlmShBKF4ATlNj+R0UQHYGQAAACAOG4OSuRAAJKjk_WIceVERLopcqAAPJcEZAggA1ArCEAIS85gA6kAMPgAMsAiDgbCp9GQFkAAAAAAAAADKZA2AIt4C8hg0JcOJgAWYNwyjfipWREui1TBcrDiAAhAJurFYD_RsBCh4AbCi0kCcIyGzMroU0oVkR_4sXxbKQugdGUgLZNwSQMgAAEVO8AHygEIkDYUTQANTIQABQyAAQSkAAAABlRgBOCYNBxnyBOBFK6CXKFZEZlLlsWkYKlYXR6CERiiSWKy0IIABQONgqdGIsBMRcCASQTBwVRoACnD8CZpUATNKgAAKoBBDAgD0GD4AAVIC9JA2FBOHglAfAJcKgAtRMABVAAAwICej4AL1UDYUmUaCcnqF4ZAXKyIlkpOVAAVQAHJK1MMCAAANPgB5cASFgAAAAAAAAAAAJO2kIAuHzsASuYw2xcrHsVJMlcWULwALIAC4FauE1xTZrAmSlCoghQIb6lamVZyWa7p9OJ8XKyKkmSr2LlYLZaEWqjWSkElJNP6oV5ySXSsmuizkaGkTwN2QgHo0VcxiCyheRWknXi4AHeLxZAA+asSRyApk1gHhSgPALyMxshBfU4fn_V4veVEVJJK0qMIBWQAAaK1Mik3qjcBshKAAQlADD4AkZADxYAAAAAAAAAAAAwkitKSE_B6Hw+djUu00UkVIpQFKeHYqVmkigQSrQRCTU1RUnJqc1CuTSLYaLOR7SdLDWzHQ+NgYMFmZuBHbMXJwEvfD6FXOHgYAfOwyipi5WREwyUDJYvP7F0hC6AEsh4AAAhAwBIDofQrKA8A9C6Y8LiIpIYL8lcsXA9EP_nYIoAEdjIAAIQMACKeH0KG+MHwIacPxBi5bBSREuloLlcpKDUTaAsRoYH2FIwgAACYGAAkHDcFEfGgvyfASkDDLwulJQQ2nG0IAA1JsAABRRESkYPgak8fhdBSREunILlZeipWUENoRhGhgAOhNgABQBQBzjB8EonD8LoKSIl0kxcrL0VKyg1E_DZrKCFJAgmbFKDgAADnGD4EpOH4XQUkRLpJi5WXoqVlB_6pH8aN5QQADHGxpBYAAAHKMOeNB0M+AlJ_8SMLkC6UoGghpNjoQAHNkYmgAWwaEXECOxkYPgZY+dhZBKkiv_KFES7KY3FSs40ENIlc8hgADWqy0ACDBYsxU4eBDyA_DP5mIAGUKyKmGEBdKQDaUBQgAIoC+GgAOAsAAHeCqq1vKwHxr+hkEEMmUJmUKwMIt5CVFBkWpG0IIADoTYAAjQkB6et3GD5VKp9j52LBarkYWL9NFJNipdlK1ShWUGomkgKpXIJJaSBJribIdOH5FAADrOH7BB42E5IJZbOmTxckismxVMy9bmIpJzTTKB8NmYAoAiIpBKP4DIAVcPAELxjkqQ8bAclGqk0UkUI7LWt8lQAiRXeSyWVhykrxMljEA4wjCkGIAMQeDMdO0Edm0EXJ60xrx+7vwpRpAIR4QgasAwfAchq9SRaSKwCSgABQKAAAAAhAwc3JvboYI1rhuBpICwQ+MG4DoCoAHEVABUWgAMRLmoyAADcDAFfnhuBgTCQDAMgDcHQA7Q6ACJFAAHu2jYAANwMD4HprhuBrTCwAPRbBsuAKyUb5QvC7_JInz0HMWMwAEvFjMAANwMA39OGpVwDAQlAAAMPAABh4ALkGQAA1AAAMBABVzgclcMATAR4ChLEU1FwNQ5EXAT0loH11YB0HTcAANwMBoEwrhuBhiBBDhDwl0oVgtNIUyheKQuk9HGli8CFMQA1AADcDFuAEDIB2XANCQBr1KBclQABMqC6UZqLQ+8_ADpEIAAIQUABwXM0HEoFgO8XFJKTFwT2StYLgulGai0D6AOiQjjQsAABX7oBCXAATFQBRioAKMVAAeQAAAAAwEACEuJIaACIXBK0oBiVAABSoLoAAAAABuCgFAEp8BgLhWIgHoD0dqXBCZLcEuDKfZr5U+LJFPoBqBCONCwAAKADJcspMagWB6GgsZlJMqlwT2SwdLgulGai0IJ9AGeID8IoAFYiAAeXBtEwACQfRUAAOKgKJ9TYJwoQAAAALh4ACtcATHkFJgZChsCiF0QuULw2lX_pN54uA+wmMlB_4_BNBjh8UEAIKTAA0LkHJhMCwPXLLFcHrM0aHLQnslWmXBdPoigoWLSgn0Aer8QiggBByYH4sBAQ8PgY8ADoQBIaABcLgjqUAyKgABxUf+gjaAElAH0lAAAAGToJg4ng0EnC4pIeMqD_p8C3KhAm0AJKAiFOAAxUVAAeOghCozDwOaMl5SS8RcE9krWC4QJtACSgQMUjrwsAHySgAZVwbBTah4FuFjMpJz0uCeyWDpcBtACSgELUjAgDHR4ADZ8CzOiDCvmDwAGMF5STnZcE9ksGy4DaAElAx+mUwIz0C+ScDY3NzoASRgbh8V0PAEhjKOyoAAmVAdTrNmsAABYJQAAoAoACSMEYPiuh4AkMZ9uVBHRbY8qA6mkF+hBJf3owRrTgAAPAwBGz4Hh5Yw8ASGMykI6CUsX3ZKgOqBGjeFnQiiSWig_FOAABMDAFAPjrR4Yw0JDGQFFysI7LS1FysDqbZ3KX_kYFy8SWijkZkpTwAAtgwBcz+wzKVY8Q0JDGQwFysI7LRvFysAh1NpRNqgRwktFHNBWIpTwABBgxZ1JnZ1pOCUD4MlXAEhpiYqAIwpQJoqAAIFQH+zYAKIB1AAAEonwXKubaKgVAXFJDylQT0FuVATUCfQ3+YIogHUAANwkAnQ+CjVzBl22ioDuFxSQxpUE9DGFwE1FoLcCUQDqAAB4KATmfBG64iRxGaYsVhZ"
noncomputable def WL41_2 : ℕ := zfNat64 33243 "FmABMALeJgP_NQAAB6TgAARBQGhQBRjxIOYIQCzCpWALVmFSsEMn1Y2hBAAAAAThQBT8IJgpqxsBFAJMPABJh4AE6HQAATC4AAEQUAcNSCYKqiJAB_daG8XKwMstWsXKwMlE0i10ieBVQq4nAAAnCgNAaZcUAUAJRCCCKx0cqDKDX85UBkNJ542AHslAAAcgBzLgAaD4DpJUGUGvSSoGYNBpL+GwA9AMsJAAADkLgCQ0AawhElFIlIZbqNQ1MAVKwMjGmzWDUAeyUGgAAAQIuAQeQjuCkSkMsqGoaykDP_E40hNDhuAPZKDTWLxykoAAAqhdlhcAGc+A6aVBtBrKT_Q0Gk88bAT3sxUA1ABlhcDs6OwJyBmIHRUg29cEwUAJJCAu6VBpBbd0qIiPiagAiJDAAJIAANgoAAgchgkeEWDTyEBKT3TEDGUgWkq2fAACQUgBSAAAQOjYWSaLAQQJSGEecZL5SWjEgyzdrJ6ADGqogz5SAsIARwLJPFgIIEpJVLmMCUZL5Sf9Eg0jazh+AXQUUqUwDyFdiIF5cGpFgw6hASkMI84yXykAULRvJ6BUQZopZ+HgABU8ybCLBPQJSF0GgZL5SSpEg0jDzh+BUQNIqUyiAHLyoAJ1kVCLAPQiyqUpSF0CYZLz3FSsiJRNIgo+d_wAqiZaiRRZipT_4RABKYeIEAJDQ+IsBaEB+BKQug4jJfKSI_2UjSLzOH4PgZNdRAqgABOgH8WNx25p9FgHoEpspdAmGS9RRUrHMR1ApGkdgfOyrVTLUf5IwVQAFsEQeAfO4AiwD0P_J0pKyS1I5QrIiWUPGcOwFmJlM4EZE0ymkxLRvrpREgHzsG50AA2RL4sA9Jqi0YlIEmC+XQJhkvQYVKyIlE0gbj52IaqZajPxWCiAAKAOAB8jEYiwEEggkQqVhhHqljOUn_xILoJpCfgPxqqIQqUgAD5FwAcUYokWFJ9w+fkG7KMD+KlcdLohAyXykiNFLIHM4fyEomWo_MRgogAFdGgCZowAGCIUuADafAclKgP_GXJSoAulkz4ggAHtMpnUAHTFwOjoAJyXUIyrRYAeHD8CUhZAyGS+U2kDSMoPnZBAoh1RWFILQAAMQUlaBHgeLAOQBUnLBKFf90oDdGS+Ul0DSNQPndFCogYhQrjUFoYQB0AKYwAGujY+AIIDWioLoNaKsD_YyAnidAADMTgAAbDwCXVYFfj32dAsUgD_SkTzKgcgxeiVYEAQIABNFIAAGw8F_oEdBqBDIspHJNIJNauUKxyTazLQolCtuapbipZVkJ1FII9K+eQyiTmmkmajdQI9RtIIQ7BhesDzQs0OH+Dj4_wVDUCbtUqAPXlQBlAAAZKcAAFImDuNFRmzQSkdKTmnBL+GDgULIQLhBGoSSa_YqVh5pecsXKxSBZSiwo4fgAF6DgAAbBQY09HNndaWgV5aAQlwhAwERATifAXQLZ8AAIg4AAAACEDAMWTgEJcIQMBSQGrkjoA48dAACIOAAAAAhAwehcaAGV4AQrAGzoAkHAAAAAAAAAAAACIGHAVBEk6A0uVAYajpcqAB9BUAAK4mAABEDBqAi+YNgaqhOQuqYUp4RSheBlkqjC5eAMYAnwAAqYeAABsDAAWugeBgVlQA_OH4H2i4FplkotBSAdAAB7mQAAHgYAlBuXmQVZyT2mqXKF4LUMMmOSlpKF4SQaikRxGA8YaGoAAAlBgBEnwWgy8VYMgHwHPi4DLJefFwQTaKQAnoHZKgAAWgwAEg4WwoaZUFuzh+A8UqAyjxSoDiGhh4AALQ0AAAB5pgeBg1GwB2DgBtEwANomABqQ0AAaQAARBQI0FGNKgnIBgSheC0yhgSheBxD6A8EDhoBOw8KWCgAAACFAyDB6KF4TkB_ZQvBaYZK_coXhFS00b+WHQGQDM9DZg8AAQEuAGQaIRcBRD52A5soXgtLslc2ULwiv8bgjIBmehsMmDAaMYQHIAZRYGQYAsR87ALCULwWmULCULz+CMcQ78PAGeqnwANQBeZcAIqAUgoIgYegOQH7lC8mJhkqWyheJiSnnNwR0AzZk+Cog8FEDiAADlIAClABEIAKdADi4AEPAARYAaJAAQ4AEDAAAAAAAAAAAAC0GNiePwnIBvyhWC10a5jKJvyhWUVq7UEZC3QtPT_hkJQuykohJUmDWVG5slF68DB1QbgyASoLnmjsA_BcrP_F1dkrAC5WAOFIgqABFFoAANwYJSMxBCBhGlC8CHHD8CrhcC0yyWKRcAKTjHQAIlCwAAQgYhTkBxKg+0fAPHKlSAQZR45UBSTQhkAAFMSA4gUAADiVBbE4fh+hSjGULwMslYkXK56CwUkgvXLGYABWxoCyAE0OJkAHlwshQjSoEtHzsCi6IuVgZZK24uVgUkgszLGYAAAHqCA4VACUnwCEuRoKAAMkpEBKF4GWUzyLlYHGaikAAAABQBQAS+YAiXAAyYWQBAfOwJxlQGEnGVAdaSU1LgBiAAAKAKAB1zAAiYQhYshyM4fgThKgMJOEqD_TtSSmJcAMQAgMHAAAOuYAETCELFkJyBCEoXg8hgz_7JoQlC8DrSRiZYzAGIAFmGgAAH3MAELgBRMAhkhCFiyD+lzGBOEqAwk4SoP8O1JGHljMAAALIAAPeYAIXAiyYQhYshOQI2lQGEjaVBXZ2pJF8uAAAHIdBIh0C4zMx4AhXhbCgEOHzsCPZQvAyyWPZQvA60kYiWMwCrhkAAAQgoAp6EAGLkaCrGhwVSSGkUmULwYiYYM8lEuULwOIhAFFwACEAAA8FF+AClYAHnAAUoAGjAA0IAMdABDIAWXAARoACLAEBIAAAAAAAAAAACNBTiioAiHzsAUktMJX0ymKT_jccaSEFOH4AAsAoIDBwAGoANLgAokjQUkwqCcgWrKg_kwZy1ZUcYcjrSRZpw_AAAgFAGUAABxcCODkaCslEwOucN4CcyheBhE5lC82o3f+cO9JB6AAAgOAugAMgsbCAQlwDARdAagL2IgBexEAA1AAAAAPCwDVo4BgIQicAgDYCPBMAR4JgA_gcPwAAADNREAAEyAQFwLamAzRwDAQAJioAnhEAE8IgAYQfAAf2FgAECCNBX9k6WAAKSWlFrCcKQynE4iDESGAAeouAADclAArLkaCjMKE8ABNnMCUktRgwX5LKQsmUkk5AysjA9E4WKwUl00gadIngXAwYbLzNic18qAiOYC+TBEFFEB6BDwuVgK5cxiFwxcrAJJFsyAUnn_BEAAAMQYABCUAMPgCRkAPLgAAAAAAAAAAAAhuYIgoohPQuiYyhWAkFzGSRSASQfxYzAOukmoaEYNwAAYgwakYABrgCQlB4Uvk4fhhnIELTKbLi5WSUyyVjxcrApJBZqWMxAmgSo5PQAAAAIFQBISRoKPMdBzQ+AOKULwMv_yY4pQvApJfIyAwikAAAABgXAEhIUgoCchCVMpqOLlZJTLJSOFysP_qVJIJYDJeHk6gPmJgAApSMABlwAwWAf6PgHolQGUeiVAUkUaXLUCgAAAOKFQAqq51cqAAR87AuaVAYS5pUTkYikhQjRmAAJTKBwAAAHi4AxQ+dgUX1lC8kplkrpi5WBSSChMsZrgCjyAQzPgAwHCEQrYHgAwBaXJwKGwXlQH8PnZOSi5QuVzWSmWSsQLlYFJILOSxmHkAAEJpArokAAUyAXFwEuOADTOH4CoC5Wf1JjKKgLlYFJCsGS8AwhKQKqBDbhEC4AILi0AWJw_AQuULySmWSsDKF4FJVAhDHBgkAAGxlIAnwkR4yNgBIaInOH4YZyBC0ymy4uVklMslY8XKwKSQWaljMQJ7kqOT0AAAABxcD2VAyo+dgUXRFyskplkrHi5WBSSCzUsZjYNHZ5PtoQAQGMgAADpcATGgAxD52H_FJdBcrJKZZKmIuVgUkguMMl4eQCoBMBxAjqTAyKSMACJwAlKACnwAI6AHlwBIaAAAAAAAAAAAAB0rk5CcgCk_OTJUYr5tUymKQwlJA1GjMPvJQElMQPAABqAV0YDXXOQnQTkCDBcrBfTBnH0lC82mEpIiY0ZgASkggAm4mEuR4pRo7AcgIELlc5CEMV+SoELldxLJSQYheRKD_60vkkVmEABpiBcsx0BgFQpCRlToNrHwFEjZQvJKZZKaEoXgUkgzkMj9T0QQCCAAjg6AB0VAAhIUg4SBsAASYqCOjMEmKgKSAEEDPSEAhAtoAwCuLE7Ix8A9AonFKF5JS5MmuSpLKF4FJIM5DIPP_EIAggAQaGgB8lQhCxFToEiHwGQC4DLJRaBSYlIR9jIDqAQQGIFAFoAawkDokJA2AAFgTBMRqBvEwFJPAhAABBAAb8dACvEwcGqSHwD0CicUoXkHyY0yVJZQvApJBnUZB5OoBBAAWYdAE2KhCFjzGQZGPgKIySheBlkpTyheBSSDOgyAAIIQEBiq0DIyAx4yAgYAJXigDgDynD8DuZUBhGLnzyGE0pIXssZgcQGdFwAAMQoAGy8d4cEdnIJRTKbDi5WBlkqGC5WGGiz0YqAMl4eTbMQMYWMwAAYhQfgQdCAVTQIEcNIf0oXgxMPDyYWgORCHMLg8mkDDRkYgeAAAKIhIqFUNyBHDSWUSlC8GJhkqbyheA5EIR24XB5NIV_CDH2DIhBYzAAAMAhAAi51SYKqc9AjhxFQlC8mJhkqvyheA5EP9hLvxcHk0xUF4ljMSgAdUmB0dvwDqXBRBQTkBKxcrJaqRkxyVKxcrDabaSE9OH5_Z6OM9AMQPAAABwLs0RlwBwDkBAhcrJaRdcxyVAhcrKptNtJFxnD8DSAAeQACCQAAm4I1hAsDIF3VmIE3joA4ZMAHDJgAisdf6hg0gBAB4AADwDqZAAarCzYewUE5ArmULyWhEZMclrmULw2m2khPTh+BxACSAAJg4AaReEysOcGAER87AuKVAYS4pUZS20kZ+cPxiHEAAegAECgpqQFuXAByAcQuVktRMxX5KcQuVmBNtJGIHzs9A9W0BdAMfwqDzSQOWLAADwghxc6pMAOQEDFyslt5VzH_kmQMXKzAm2kkXzh+H_24AEoeQJPkwOzI7Yks7UjNyAEholUqCcgUVHFysDLJUFFysopSSCWoyXhtAqsJy4AAA6At+YEOTAEhoTQb2cOwP8Fx+IqMMlHOULwKSqJCGJgQCaAAAACxIkEqBHZw_Aa8XKwMsla8XKzpA1FKSNVLGZ_ZmLqB0yxmAlAAAFjSqeIqAZBw_Ad2ULwMMld2ULwihJFfFjM_2rB1AtBYzASgADxmZgYuqAJDQAOSA8DgHIECCoAgQVAALQAOqFQG0ABmBZKRUDxjx2BAMoXgYSAJQvAJInwwXgHUN_FwVTqA3hQriDBkuAqArh47AokwLlYGGSlKLlZRQkj0FRgvMCHU0lkeRgvP5lwAQ0uAEBGaMEPnwFmuEIKJoAQiUiAlC8DLKTslC8mJxmopDAgWkUhyAAEEKBWwEdZElgQI8dgLSLlYGGSowLlZRTqSR6TAwXmBAqtGy4gpZAAHgAgSQoqvWzAOQL4lQQSyPULlZfReO"
noncomputable def WL41_3 : ℕ := zfNat64 33247 "BIO5CDaWTrI0M8WDBJRqADdBISgGk9aQgAJiBBkwBAaAiRQFjBRIhIAMRcBJdLFwBFntAS4AHIAE0AAB7MALYgA40EEigAAYBICxEAE+IgAWsbAADEAA4h0AAEaAnBwAQAkAAsmAAFkwH2TIAAB6Y2Qgmgc5qAOBAHZMLIsAxQyAigXAf_JooFwBFFHlwAAT6NgOgP86ACQTAACUpcBJQEFy8Aiz1_hkvfwRDlbxkAAYDoDs5hYjavPgA5kwdiwCdDYCU5cBJZaARZ6+QyXjaIE49DoAGyIHs1Ds5Iv0T4GYsAEJQAw+AHFwBMaAAAAAAAAAAAAB7JnyUuQGwJDJgGIFysFJVRzFysAiz1_hkvPAgwAAB2cl_j4AApMAHG0MMgGIUCYAGpUfmKgDWVAAEQuAAAyAdnIEtGA8A4EwHquAwm6kiAZAXKwUlVHoXKwCLPX9GS_0RlBQAADs5lO3T4DbUnF5UAHkwGeatQ6D_QECUSAJWVABKyoAiijy4AALyf6SgAAyTWMnj8ASuIWJRDROMuAkoZC5eARZ6_wyXhUC6AXkJIA1QgBAJpMASGgKVCgB8BcBJdLFwBFnr_DJeBtCIAAjI5DpnQAciYAkNAsEHADzPIbzy4CSjCLl4Dkiz12BkvAAAJMZHPo0a+x8ABdmAFDQKjQAAH0mAQgfSYAAUlQAAGDjL+Y0ANE4AUJMASGhIioIbnQFui4J7JbcFwBFFIlwCUAAihkGDnQM28WAAWYImTo+bDECstCYCYZcBJQxFy8Aiz1_xkvFvGgYADSLQMjkf6cPwACswPYm7I202hBLQIoFwEligXAEUUeXfMLgADSLQMhR06AAgXA0CcbTY8BEAUigPWsFwEligXAEUUeXAABpAM_sOii50BobOi87Oy4eHzIIQUGFgYkQcB2wuAkotAIpoUuAPq3G46+ZAF4FgCoAIWcFhYAkQcAmUqAEylQBFKzlwF5CSBkAAKUaAAkNAW+DEgDgGAFy8CSlzKF4BFfUfC0A+m0a6YMwAAAFVMA2FAawSA_0XAf5Jv9FwBFNAlwF9Dq5kcgeAAB+hofIcBcBg+AEEoXgSUl5QvAIpeT6WgH1mbcDEmgAfMeB0EISBjQILAHYZDFLF4ElLmULwCKto+FoCKXj_aQYgFWqglCpWAFigwA7jI0pYvAkpLyheARTSH0tAPoBG7WDFXREFJ+KnDHSYACLMAMTgA6UACOgBxMAQGgAQcAAAAAAAAAAAAAlNF8LD0EHEwApSYAFKTAAUsqAANkXf8TgAN8RA_Q00ROB5ZMBKQEIqFeUgEU8aXAH0AEmDMmhe1KCeJMABfaKAaE4RAeQO_lQBV6KVAEUrOXAf9egkcZAADkJgNDTUdFwAYnAHaYoA4MLAwAskqAFklQBFNLlwB9DOhkAAKUaAAENBZDQVVQgJSBtw0XSkAik_S4D_70D5DISgAA_Q0NkcRgwZGhgGhKFYG1GpQvFIBFPGlwB9aI3ADTBmTQAPmPA7b256Oh4ATpgKyBiQBwGqi4A1UXI6BgIpwMuAPofOMgC6A6hIAA9MAJGgKgBgD9xcA2Ab_ZN+4uAIprsuAPofDMhKBdAUwkACemAEDQcQsBeBoBpJUAcaLgCKd7LgD6H4jISgXQFUJAAOZgCY0ABjgAqBoDiRcBJRaARTQpcAfZMNx18yAAAAfoGFiNAANKF4ElGmULwCKeNLgD7FluP8GTNOg8BdAVAkAA9mAJDQAVA0ALQPckwtAIppcuAPod_MgC6AqhInR0NAAQ0AANoAluGRC2KgP_IwvIuAADIZCUAAiwAg1AD2YADTAAhoAGJAQI4AAFkKg_wTBZCoABOFwAAUy4BKKQAAEjQFYAypjJeE9foXKwIslaGULwCKoo+FoB5tIC0sZ+8JgOlUCbCQMgBJuAHswjeSAc2KgGHEwAw4mADshUAAKQAHnCQMm5uACWoDOzAFY5JD9gEB8OAamVADUSoAinkS4wgAMTiAFRhoADFMAAP_FwDYBv_k3_i4Aimyy4A+h+EyLgjTESgugHQSA6x5pwsAA5WKWLwZAVSUaJQvAIppD6WgH0BjcDGCzEBdAoAkAAIWM5VgAO+FwElFoBFNClwB9UU3HXzIvCMSQugEgSA0DceAf4ZLwnrjSheBFkq_yheARS8n0tAPuAG4GJFE4khdAOgkG5uAM04ADTA_ZYAFDAiAAAgiASgCCIAIAFwAEJi4ABVQ0IyNRuA4O6mQEaSheFN_2TRpKF4BFBaAjR89gZksZgYTKBhRIN0ZGodgcAG2iL8hcBJS5lC8AigtAPoGZLGZ7BiDKBURIABzMAMTgCyUATGgAAAAAAAAAAANIQVOBkAHIuVgPUVqcpAIovj6WgXkBAljNTDEZxiDLWQp4kGoBqZgCWcABpkVAAAzxKgBstkyVAAJwuAAEkZFwRgAC3N40bjwBIzAA5ochHBALAAaDgFvDwAt4eAAYgAcsKgAAqACFmDwUwUDQAgBIBUBMAKgJgAAAP9KwAAIh4AOImApMhMsZkNEIAryheBJUilC8CGzldKpb6qjAcTaNGcMNBEJxGNBHFkwBzE4O_JAAoYKBo9Q0AAAsmAygCyYANKqQAH_lYAB1g8FVj3vhoB9HzsAtxcrAyhbi5WH_0aGm4FauABXV6ID8OoxAbhAnDcZMJHm8iQBUCTDSdyheBJVklC8CGjRlquBcQrtBRCbAxDDRMAARmAxiWEjxVISABdKF4ElIGULwIaZSWL4B5ho1H_2KghhAGYTBH48hZAjkNEIKEwHXFysCStaLlYENAGqlcCaaQBwvW3+oDcamEolEKEQJwAGsy6jw2hIAoAR0oXgSUuZQvAhoWQDyihqDfsGMagAjQmAuZCw0FCV90Wo8H+woQAkBJQHhHSCyRWAGUkgAHzMkcGwAEQJgtACTUAPZh4EcAAkFAMAHgBgA8AH6C4AAUgASqGiXAR0DWswYya3oWAACYJImJgBGxMAFVCoAAWgAN6FidnbMXFyMtAfHMFYMCQiRgeQojGLBkEUYyVKpcANfKgAAs5EAACsGAAQzAAVoAUnAAkYAWdAAjYACZABy4AITAASIAeNAARIACHAAAAAAAAAAAAA8JwTAwQBYAI7DcqBA1Fk5UABZh4AAmhEAACYGDU9AOfMAtOg2BlfEQHkGMFQB_smHOVAAAADtGgAAbAwBBeYQgauREB5AU2fKgJb_EqAOIxRGhgADBFgAAhAxWgB66DYGBeJABHQ9kwIEBudBy4iCIAACeGgAAbAwAIWYDonAEhIUgoACOhUKgQIKI6D+BEBZEIAAGAkAAAAPZgQycASRgAEdBcVAgQZh0H8CICyIQAAaBIAANwUAJVOBEEgAjpESoEC10mL7FwIZ6R0RgADzCwAAoAoAtCcBixi1Tw0AEdHMVAgQwIPcWjpSEAAGgSAAFAFADDThiLgJyEdRwXAgZKNIudopEhnv7zrDKMAAegWAAFEFAeBNU4AHjH4RHLGgAjo5ioECBVHIhe0tGVEIAANAkAAKAKDOzM5kvPa0BZcwllOEIGEIgS6D2Or8MgQMVcMaMwAEYJAAHmFgAAhAwhgBrmBYJwhAxhD_x8Ahg6AsiGDoABdiwAAhBYAAIQMASk2CKVwPAx8hIP8HQB6yYAAWTABVAALhFwAAHgYABCUAtOgAAAAAAAAAAABeDCBEgvQhAPPKF4f6aiq88oXgYYQgAAGePAAAvBg1KwiQoQIkBBD6atasuA0yWQpcAWQAAPILAUaDgAAAnQBIaA7EgKMhAHwLgP_kx8C4AsgAAfYWAAAA5EgIISnWsTlwGmSyDLnvkwFkAAB0jwAAiRIHQBCpAGTYAmTAAAAAAAAAAAACK8yNB1QkIP_JwATyYACeTAA3JKAAFcPAAA2CgB0KAe4hAPVKF4ga6VXqlC8AG4JQABIR4AAIIUBpqN6JMXFgoIGuC4NIZm6S64LgJlqwSQABniwAAQQoBzElgCwEEDaxcGkizVJdrFwD6lo_8lAAKmJgADNCQFaiwPzPIYAtDTmFqkotA2YrBJAAC2LUSEgAAAGJwAg2AJGQA8uAAAAAAAAAAABzZNB8WCelVJSWUytxVK42i5WBM5SCTY9WAA+o0YQAHKJAAB8bADxEoAAFMZB+koAANQsAAB0OI81LvFp9iwNqOH9NAQKQtrJlMslGeWLwAMJwSSSAFVBq7BsAEayBOBiizcxYB6V2VgmZQvrJlNMlFqULwHbKFsJIAAr4aABCRMAIEVmrTFjTCQf+OgB2FQAOwqA6UZBJAAzURAAfCGgAQjR3iz3xYB7TSqCVKF_9Vi2ZXCMmuShXKF4BReWeOySAAAAIOJgBnToBbPAsBCDx3TSql5MpyksmUccYL5SAURCRAnfmzAApDp5AA9gkAAE6AWGwPCQGg4B0GwAHhoAAILAAAACQGgAAMhxCzp2OwMecgLM6G4KECJB5tCAA_03SVohcAfRDz02AABkJAOoFgAB9HREhQgRIPLIQKnWgDTJVAFwB9EM1AjoSgPgCCC+B4AWx0NwUIESCgyEABiBqkpgSoA+iEAAZgbAEECdEQAUzoCGHESFCBEg8ghAptaANMlUIXAH0Q_jNgAJCowApD+ZMAYCAkzoYwoOIkBSjoDuhcAMZ6lQB9EIAAOc6A+iUA2EQBlToARJDcFBsEgHoBXDoAAmVAH0QgFkD1x0GBnoTsIiZFxcrMxcA5EgIIKhWnZFSuxAkGkWnYKlYVE2jokaGAABwMJgAQcCgAJDQGAkA2D4DpJUB_4u6SVAG0quhAAAsDgAAABYsIQkDkSAghpJWdkVKwNItKuUKwqJt9stUEACbAkdYNgAB0DYKAi8hASkP_NQtlJ8BiNMNG8N6gRwADcFwAAXw4AQBjsiQZAQgJSB3YulJ_5KDae3QgAC3EQAA5AAWrDIiQEEB2hUrFo3xozi10ZQrCSG0iS1QQAI7EQAEHBoABLELSJAQSqDtCpWZTQTULW7lCsJobQkiNDAAPsRDlhoABSQ6XuJA1I8hgKlKFZxAWqlKFYtIoMho3hBAAMgTAABCFgAHsQ_okBAjyGXQYEVKziGUWt5KFYhIo6Rs1hBAAdcTBV9SlABoFDYZjYyI8vQWAggSmbqkG3C6UkGIiUG0oIAAoB4ugUAACKjiP_YsA9NpNN4mU0DlCsAqdTAWsZKFZBoICZs1hBAAecRdrUgADJOoN3AmIFkwgEJMAwEWISAagGGIgAwxEADxDoAAAABMFFiBPeYHgotSE_Aogd3KgBb3cqANpb1CAAIIPAACgDgAFLQAFSAApwA8uAJCwAAAAAAAAAAADQAEzAHi4I5TAARYQgoAIBsAT4iACfEQAKmPgABqAAAYCAB3vA1C4QgoAKGA+BCHHKgAL5UB_pqBVIQAH_i4AAUAcAZ+BFa4LgqOiUH_kIA0BMAGgJgAaYdAAR0TgAAThQCP84akhCKroLgr_RcABZgATAC3iYD_zUAAAek4AAEQUBoUAUY8SDmCEAswqVgC1ZhUrBDJ9WNoQQAAAAE4UAU_CCYKasbARQCT"
noncomputable def WL41_4 : ℕ := zfNat64 17947 "BacAhQgAJ8AAAAAAAAAAAABadAAAAAAAAAAAAAHmQBIWAAAAAAAAAAAAAAAAAAAAAAAABafAAAAAAAAAAAAAWpwBQEAAAIKAAAAsFCSCgAAAAAwEAAAAAAAAAAAAAAAAAAAAAAAAAFAQAABh4HCLQAYeAAVQUAAHgOAAAMBAAUBBEc6ATiVB_xiE4lQAC7CgAA8BwAABgIN4MDt7cALT4AAAAAAAAAAAAAw+AQlQAAAAAAAAAAAAFqcAwEAoCAAAEFAAAgoABACQAAAAANwMAoCAAAMRBvZiADEQACMDgAAAAAbgYBQEFu0IDu5UBtFvdyoAAlBQAAAAFvbl9uAATIAkNADhYAAAAAAAAAAAAAAAAAAAAAAAAEKkABTgCaUAAAAAAAAAAAAbgYAXYUBWUqAKtZSoABdhQACpAYAANwMGoATRgByEABcFAAdJgADpMAALgoAAIgMAAG4GAAeZAEhYAAAAAAAAAAAA3AwJgYIYBwC5i4CSrmLgAhgHAAAAAbgYADaEASGgAAAAAAAAAAAAD0IAkNADshwCtS4CSq1LgAOyHAACpDgAAACQ0AVsXAEUKgAihUf8bgFbFwAAjA4AAAAkNIJOQInHgCklQAUkqP9NwCJx4AARgcAAAASGgAAmMuAkqYy43AsXwAAARgcAAAaGgJLCAJDR4QkH+CoBiZUAMTKj_z0B_gqAAEYHAABYmNiADE4AElABjoAeXAEhoAAAAAAAAAAAAA8uAJDQAGIUA90oXgVV7pQvAAGIUBUAAAANQAYnACEoASZABi4ASNACRYAAAAAAAAAAAAAINAAZhQD3yheBVXvlC8AAZhTBiIAA_0nAAQIAPLgHYtxx0ADMKAe+ULwKq98oXgADMKAAACAADpqADy4AkNAAA+RcBpBKSnyLgAJILAAAAAAA8uAJDQAkgsAfIuAkp8i4A0gkAAAAAABfLgE839CEADMSARsXASVGxcAAMxIAAACAK8RgAJGQA4uAAiwAFwkAAwaAAGDQAAuEgAAAAAwEB4AdLgDksG4MAlDILAI8LgBURcADvCr7x8ABJDaFZL6AIAuAEywbgwBlSonouAuAkqNC4AA5iw9AADabQECH4C8LgL82vysADESARoXAf_JkaFwAAxEgAANoBfQAulwigwAMRIBGhcB_8mRoXAADESAAA2gF9B2DACiUAOLgCY0AAAAAAAAAAAAolIAGIkBFUqAqMVSoAAYiQAASiQgAMSEAA4uAJjQAF4kA90oXgVV7pQvAAF4kFEAAAAABxcATGgALhIC45UBVYRFysAAXCQAAAAAyOmoDHwsWAgy7xioADwUAjQuAkqNC4AAPBR_N6AA2loZgBAgAMTgBB0AOLgCQ0ABFgAAAAAAAAAAAADE4AAQ3KgP_qUNyoAAaCQAAXA+QYZAAQl4CiKgBBEQFxyoD+apXuOVAAIAOAACURkABiWgKAqA58XALuLlYT2qruLlYAAnCgAAvAdAAoVYt7c1gQH6XAaJpVAA2FAAxKgAGJUAAGwoggAF35QMARuNgAXS5TEwAGgoBWpcBJValwAAaCgAABixDAIANA+A8bAA6cABSgBh0ASMgBxcABFgAAAAAAAAAAAAdy7MzBmABoKAe6ULwKq90oXgABoKAAAiACukCOAF0uJR+AACkHQ3KgKjDcqAApBwNQAAAApFxUmo7OjY6AcD4ADXA2DP+MgAG4FwH+yZuBcBU+g8waAW2EKLpQAAGwYAeBj1CwACOm4OyRkrlC8CjJSklC8DaC4Bw2BYQjKZAAAeBivAeBheiQVKKgMilwElyKXAVHLj_w0AZQqiZAAAeBgANqQBJGAEHQAAAAAAAAAAAAeBgWoHC_1oQf6SkWFysAqr2LlYEtAyAilgzg142ZgAAeBg1vQ0B4GAJAJAB_KgJCH82KmFwLTbGQACaGQAAHgYhQCgYGcgwBFAuAkulC4Ai__Pp_lwH41YAhAkEihgAACRNewMD9wYkQkBFIuAkuli4Aiz2gJcBVQAAAPhQAEiaODo9Q0AABEqAAIlQTWJlRIwAVUAAANwUABImjg6PULBEMmA0EXASUVZQvAukX_p91suAqoAABGgoLwAczAAU4AmlADzIAeLAAw4AAAAAAAAAAAABImjg6ZyrFbwYAwaVAFV0RcrAIoo8uAqoAAANgoNQ0AFhwsiwLUDhYADDBvP0uAkoaC5eARZ6_wyXgVUAAggAAHDhZFgySFBdKF4TXw5cE9koFSxeARZ6_wyXgVUACYgFuAEhoB5AoOSASAZoXLwJKbsoXhRCKPRPli8CwhHUK5FjIAAAAEmAJjR8NwDRjICVxcB_8mlcXAEUXmXEkAAAAAAWzAA1IACnABEoAWfAAToAcTAExoAAAAAAAAAAAAAImAJDRzNwEBoBDKwFeSoD_qlXkqAIovMuJIAAAAGoABMgCY0hTcBswuCchXLF4UGSihKF4BFnreDJeSQAAAAN4uDABQ0wipTAEkNFgoAwfOClwElEmULwCLPSCGS8w_ACgjp+AmAsIAj6kA2HQsiwNcBgdCQABUkmE+VAAdABmhUAAATxIABA0DYQkDoSH3kxKQBa9gqVgG2fS1QQCjhY+Io1MIAAQ6RQeJFYEqIE_70IDrFSsAWi8KlYBtF3I0MACKNVSKlsACvjQD+QJwewGCx3EU9EIOgqVgC1_xUrANr_VS3QYZqRVKSNSKNSaRScykcjLGD4GztaAD0IEsdAEhoAIASAGabASUc5UAB0APslEHGQAAABcmAJBQKiwAgBIDo5UBLfQlQBxGpoEfjhULQ+__JgAAAA01wHgmAJBQPCRBAAAsTBQwiQeXAAAqPgAAAAACITCyLOINg64ZACYKlYEkWpuKlYBtC2oEcAkoAH0BIA3AALMBgJhZFg9GIF04EQCki5WALZSDuQg2lk6yNDPFgwSUagA3QSEoBpPWkIACYgQZMAQGgIkUBYwUSISADEXASXSxcARZ7QEuAByABNAAAe"
noncomputable def WL41s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL41_0) (dpk j 1 WL41_1)
noncomputable def WL41s3_5 (j : ℕ) : ℕ := dsel j 4 (dpk j 3 WL41_3) (dpk j 4 WL41_4)
noncomputable def WL41s2_5 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL41_2) (WL41s3_5 j)
noncomputable def WL41s0_5 (j : ℕ) : ℕ := dsel j 2 (WL41s0_2 j) (WL41s2_5 j)
noncomputable def WL41 (j : ℕ) : ℕ := (WL41s0_5 j)
noncomputable def WD41 : ℕ → ℕ := rdw WL41
noncomputable def ready41_cuts0 : List (ℕ × St × ℕ) := []

theorem ready41_cuts0_ok : CutsOk ready41_cuts0 := cutsOk_nil

noncomputable def ready41_0_state : St := ⟨26112, 285696, 51168, 130269, 52016, 95804, 29666, 44151, 29666, 44151, 52016, 95804, 28545, 107646, 26112, 285696, 77280, 394294, 129296, 446310, 158962, 475976, 188628, 505642, 240644, 557658, 308739, 586203, 334851, 612315, 103184, 182285, 132850, 211951, 162516, 241617, 214532, 293633, 282627, 322178, 308739, 586203, 81682, 125470, 111348, 155136, 163364, 242465, 191909, 271010, 218021, 535035, 59332, 88302, 111348, 155136, 139893, 218994, 166005, 483019, 81682, 125470, 110227, 189328, 136339, 453353, 80561, 159662, 106673, 423687, 54657, 371671, 0⟩

theorem ready41_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD41 ready41_cuts0 109 371) ready41_0_state = 39769 := by decide +kernel
#print axioms ready41_0_cursor

theorem ready41_0_covered : Covered (toCl ready41_0_state) :=
  ready_cover_cursor WD41 ready41_cuts0 ready41_cuts0_ok 109 371 39769 ready41_0_state ready41_0_cursor (by decide)
#print axioms ready41_0_covered

noncomputable def ready41_cuts1 : List (ℕ × St × ℕ) := (371, ready41_0_state, 39769) :: ready41_cuts0

theorem ready41_cuts1_ok : CutsOk ready41_cuts1 := cutsOk_cons ready41_0_covered ready41_cuts0_ok
#print axioms ready41_cuts1_ok

noncomputable def ready41_1_state : St := ⟨26112, 264025, 51168, 209371, 52016, 210219, 29666, 44151, 29666, 44151, 52016, 82070, 28545, 107646, 26112, 264025, 77280, 394294, 129296, 446310, 158962, 475976, 188628, 505642, 240644, 557658, 348290, 586203, 374402, 612315, 103184, 261387, 132850, 291053, 162516, 320719, 214532, 372735, 322178, 401280, 348290, 586203, 81682, 239885, 111348, 269551, 163364, 321567, 191909, 350112, 218021, 535035, 59332, 88302, 111348, 141402, 139893, 247964, 166005, 483019, 81682, 111736, 110227, 203813, 136339, 453353, 80561, 159662, 106673, 423687, 54657, 371671, 0⟩

theorem ready41_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD41 ready41_cuts1 109 40577) ready41_1_state = 89693 := by decide +kernel
#print axioms ready41_1_cursor

theorem ready41_1_covered : Covered (toCl ready41_1_state) :=
  ready_cover_cursor WD41 ready41_cuts1 ready41_cuts1_ok 109 40577 89693 ready41_1_state ready41_1_cursor (by decide)
#print axioms ready41_1_covered

noncomputable def ready41_cuts2 : List (ℕ × St × ℕ) := (40577, ready41_1_state, 89693) :: ready41_cuts1

theorem ready41_cuts2_ok : CutsOk ready41_cuts2 := cutsOk_cons ready41_1_covered ready41_cuts1_ok
#print axioms ready41_cuts2_ok

noncomputable def ready41_2_state : St := ⟨26112, 264025, 51168, 209371, 52016, 210219, 29666, 44151, 29666, 44151, 52016, 210219, 28545, 166816, 26112, 264025, 77280, 394294, 129296, 446310, 158962, 475976, 188628, 505642, 240644, 557658, 348290, 586203, 374402, 612315, 103184, 261387, 132850, 291053, 162516, 320719, 214532, 372735, 322178, 401280, 348290, 586203, 81682, 239885, 111348, 269551, 163364, 321567, 191909, 350112, 218021, 535035, 59332, 88302, 111348, 269551, 139893, 298096, 166005, 483019, 81682, 239885, 110227, 268430, 136339, 453353, 80561, 238764, 106673, 423687, 54657, 371671, 0⟩

theorem ready41_2_cursor : U (walkCut TOP BK TOPD BKD PT REG WD41 ready41_cuts2 112 40553) ready41_2_state = 138873 := by decide +kernel
#print axioms ready41_2_cursor

theorem ready41_2_covered : Covered (toCl ready41_2_state) :=
  ready_cover_cursor WD41 ready41_cuts2 ready41_cuts2_ok 112 40553 138873 ready41_2_state ready41_2_cursor (by decide)
#print axioms ready41_2_covered

noncomputable def ready41_cuts3 : List (ℕ × St × ℕ) := (40553, ready41_2_state, 138873) :: ready41_cuts2

theorem ready41_cuts3_ok : CutsOk ready41_cuts3 := cutsOk_cons ready41_2_covered ready41_cuts2_ok
#print axioms ready41_cuts3_ok

theorem ready41_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD41 ready41_cuts3 128 1) (ofCl (RC 0 2 1 0 0 1 0 0) 0) = 149030 := by decide +kernel
#print axioms ready41_parent_cursor

theorem rc41 : Covered (RC 0 2 1 0 0 1 0 0) :=
  rcOfC WD41 ready41_cuts3 ready41_cuts3_ok 149030 ready41_parent_cursor (by decide)
#print axioms rc41
noncomputable def WL42_0 : ℕ := zfNat64 33248 "CUoipAnANyxXAHotigrFkqI9AQI5GUAD9C0PQogbeUgFKwejDQAcvABdoAMlADUYAeVABhoAGJACQoAAAAAAAAAAAXoFyEIMCAJKUAKI6AAAKM7AAAgy4AAFYsAoHhgIAbKhhM8ASGgAAAwqAAAI8IwABNAACfBXCUofAwXDGSsBMaaL2XhAkkAbyWMwAH_mjsehZAroTAOFxrXSU_IMFhrEqAHNNDCL0Vq5NCaDJyxmAA6UuHoPZeAEMzACAg5mACF4AWjAAUIAGXADCoASNAARYAQHAAAAAAAAAAAC1D2J0vAm0spsLlZBnM5HJVLpdYAnGULlYhIpFGofEsZj2ojWg84Up7LZyXSKObaCePIYAhqKBYsdNEYcg6AqAA0cPwBrBUAGgEB+AAK4qAABsPBnHnZzNioDKXhFk3Tw8SQRYTAQLNgBgBMAH_CoACYA8ABp4eJ2ZHR0lBRdUAwEGIiBUhEBVAyAEUjwAUuJgABSAAAYCKUnlQJvvAMBGECtEQD8WYABsRAAGAiAAAAADAQAEkYA2hAAAAAAAAAAAAEoMwDARBAWgNsPg9o1B4CoABNEQAEShIAANwMBqGAyUIAmZALmvRNKj_aEcyPimm0W2VBRQAADqCQAAEgYAmqEAhLg2DgmGRWS4lC8oIARAflNNqN1bghcFFEIAAAAAQgYACSMFENgJC4CdkwE+E4AAgVBRRCAAArh4AAFwMABJGDqoQDCR8oXgNBqCU09HTg3lC8KKIRws2MAAF6PAAAuBirAZSEASCgrDgWYxRNKgMRHxTTaLbKgooAAAVx4AAAFEQgSjIrJbyheUEHpTTakFW4IXBRRCAAB5iIdEMAAAVY2CkOCkXAf4qAp8nAAECoKKIQAANwTAAApDgEXIQUhx8DoMI8yheA1KakNQSm2mkTKF4UUQmUP2BQBWAuAABSHFWA10IKw5VBkVli5QvKCD0pptUwrcGLgoohAC6QQhIAANg4AwAGhBQyoKw46BozKyU8oXhBB6U02sCVuNFwEEQgAAHQABMhwA0kIFMXAMKRiheEEHpSTaSpW40XBRQ6dYKgHoNAlcfAAAC_QgtpcBQm_5Sg_8xR+KgglsD4DaIlKgooSCIAHoNAKoASkNgBatwBDmA+Gf+BwGFURUABM2AADjwAAD0AKycMAyAAA8BdIQXYupcqDCDEs0qANyfFNAaJUFFACegBpHIA_VMpgACqgDg11R0EyGYghUACQ+AAHFQAAT2KgFhOGIAOqOgBKQF+hBMy7SC4DDbwsVhBGFHkMDaIlKgooSCIAHoNAFIANILgdHSUEKIQ1jiOah+GK+f0oXlBKrVDh+U02rFUK4tCiiEAu12kgG109gABFDgC+IYSBhrSVFBPgnxTbaL5KvoJxRRCB5K6hVKBwD0AAG4OASehAHLM1C4C7WsqKCfBPim20XyVAEotLiYDKV0D_7sAAG4OCmPJyedAZWzJynDv7MArMwCHCCdXQCEuG4GA4gVJgNHHQBAgqDiAPQAAAANwMAA8uAJDRGpcERyoAelNAI2ax+ZUHVpLMDbCoAAAAAAOF4NBwxBxLVsaBcrKCDkpppGGlC8OtlgEsX5rogqP_owAAAQcDgAHlwBIWesMishGLlZQQ5R47KabQ9ZQvSYVHWyhDAqAAAAAAB5cASF2qFhiThWvIlR09CByU00i0SheaTrZQyAVAAAAAGYmwZBmMqH3oQOSm2klEXKw8mkO4lQABFiJDQcAABzizPyxmFmUlBKI5KaaQvJz1i5WHmy6wWpqKRfSxXKpFB3xIjIoAAxFDZOgiDB8npYzCyCIuVlBByU00jDSheHWy24WprogqICAS+DgABQCQADip_4yOorX5SooIQI8dlNNokMoXh1soSaKgAAngUAAAL5YzCBqluUlBVcpDkpppG2lC8OtlJrvwqICWYSHwf8EieBQAASgBZGBzLGY3dUtykoIOSmqNZNYrUoXmk6mEOPlQAFxhoQgAMsiABh4+vYyXlVlJQSiOSrTQrNWc0yc9MoX3U62UAVlCsgP4CYCqIcAATseAA2rAH8NOw4JZYzFKKluUlBByUSCARk1itShegTiZQ_8bAAJ8EgAApCQAeEYeUsZj0FS3KSyVSiOf+tGMymkTic0MoXoE42EDrlhAeAAHgQLgABSEg7jzMA_NQVy6AxLGZtLKxi5WUGeClNRLTTSTRvFys2nUwhOQAHEBwAAUhIBeLGa7SxnaSUlBHkmjsq00xTRnHEFys8nWyh+4qAAMcHD4FgAA1gsZpCLl9pKpLyhWUEovgOm5VptlEgFys8nUygWkkVgB74mBo1ACchEDuLZzuKTjdPO4YGPZgpWEABuhuBgOIHioByBw_AJmlQcQB6GUAAAA3AwD7sIBgKFhEDAh4AYgDQR4APqFwAAAAAYCAVvpDcDLsIgj+TAUEASaPAAAAAAAbgYAPNcNwMEx8+pBJCCGam4jOVBpAv0pAAD0AANwMABjCA81w3Ay5lYJjFQBRC6ZQABkycAAPQAA3AwBFa4bgaaytbCZpYzCKAWayBvUKYdS6Al0ieAA5mIAAbgYARdcASGkYl4LSlQH0nT2f8YjSUxUi2gWsUgAB6AAAB5rkaEsxMQbLKgGMtnMMJpEkqlctu6F4CiAAPQAFGAwAea6jAbMTEGyyoBjLZzDCaRI6pXLbuheAogAD0AAjQkAHmuBSXMYnBalIz5mLaGE0iWVSuhRaNJdABSpTAAHoABGhIAPNeal04mrK7KFYIBivhtLCZQqpkUK9t7QtAoxQngAD0AAjQkGYBhVgUtcLpVUBlCsMII1s3nkCDNjso71Urik4lkEIKE8OgGGjYcgAEaEgBBVwiDx9eaxXnO4lYApQrstdqWnW062GymVJKhXrttLIKEUJ9FAByPQACNCRdmYeAjoSDhoKAPzobgZdRkGEi4AegaR+ZUGUchBAmAAcgAAbgYAwMBIUw3A3zDI+mtf_KgDeNGcpppHalC8PJpDiZUADEugAAbgYowclbAMBAiIgBAPABmMgB15EABlAAAAADAQAGS4AkNB+lwRHKgB6BtIblQZZWMwSiNg4hLQAAAAJGQBEuMuMgvuVAHsPHZPQQNG8tSVBlMoYQNg4hxloAAAiDgARlxyDwxKyG4uVgt+mpDkD8dPzSRnKF4ZTKUTcpQ1DiHGWgAACsKAADnADi4ABUmABqbAAER4AAVGRcB4AAAAKQUABwuSRnljNbKUkxYrykFtB1Icg5NI48oXlEykYWM4DUynEOMtAACDQUB8eUzsGQ4YF6ZgheEAWuhuBgOMMC4BJJo7A0i7i5WHEAehNAEOFQAAbgYASBvdGRxpalIm1CByU00jnSheHn_LJrCUhptSAQcPAAfSEgAJGQYnGFqUlBByU2IzJrFalC8OtlDWRUSaTqiAj4eAAg4FAC+WMzjC1KSgg5KahpozitSheHWyhuoqCbUQE9DxcAoAAGDLGaYyxmN1VLcpKD_RSHJRprzmrOPRKF4dUMsmcBSE0ogLYHEexFIAByAGvWOUoGS8KoSShWUEAIdN0DTTKGQLlYdbKH_ioJtRnKhAqocRgAKKOg7VIHywgiCkREQNNJgK8mwAbEeAAagAAAB8j4CfWEASEgiCqgEQflJgBqAQFHgAAAAXGQAAAbJYzNVKluUlBKI5Kb_5oz1KTnplC8ONlB6yZTW4RE2o0EAvID8HMhA+UfADtIhtEnNGS8UkqW5SHFlisPQqmk0QXBxAYmQVgmjEPoQQcyED5R8AxFSGsSrwRBJAMhmj4CjYAuAsnEI6Px_JOAENHwAA5DYADeEKQkg0uC1pUAUQMoBxLobeUg_sxAI6OgABRGQAT0Yl0sZhVTUVKwqjNzR2W0yj_VSuG2wgURrBpOqIC0GC+DkA0cfAMgSLl4VSAlCsqpRMiaOw22Umq5VK7uFiucTKDClamTfMokumhkGYHoOZCB8o+DMAU6wTCA9fhcvHJVFIXVbplM2Jo7_7BXEyk0q2W22UCbs1SJpNDCCMOH4OQDRx8EDhIyDV5UARc0dltNIwNUrh1cM1ZwqIADRz4loA2o2AeABZokkuCDZUBPRJzkbR+KkHUBjCl_xCAHc5ANRBwkAcQdDzsAB4QshcA9SYBGR0AEGTgAU0nCUAGmHQAAyDYI3RJa7SxeTaiKSj_xWcIpT0kmjuu2kyk0q2G227ZgDskTyaQSaALo4fg5ANHHxHlIPc0JSCgYR6wgRBpeEQNoHgMfFQA68eAAagAAAABgIBU+kCINtYuDSRUAQQDAhUAAAAJAuAABEJAG8kgGAgREQFmHgNRHQAYceAC7KUAABwkXgADUAAOEAQFgAQEEQUekuCDJUB6o+KabR5JUWkBCikAAHYeAAAD0KMGWMwsyk1WhBNzR2U3_LJrJCFysOrt2YCiE2o0EAIqAWwmCF5nADxYAGBAYDAKFgGoAAfPLgABYbAAAeQgAAALws+sZBZlITQklNMoj0oXhtsILGUK5TaizFCA0zEQAKIqA+gqAF8LHSkTxiMSWrcpCihdQpkkpppN0nOvKF4xNthHYoEMo0Gm1GgkUhi9bNIRWCgKQAw4w35cB_ioCFKcAI3Ko7_9uAmYpBUQGDvQpAB3xEAOwX1w23YZDLFqUhNH6JUcpppHglC8m22wgohWpzUqIACSKgLKLgdM52JAxsA0ywIg0Ki4L8FQBNBqZQDaBXNOAAjyXFpADWEwg4FDWMl4VR_GS8nMtgINSzKRfJlMNv7lzGEUSiaEEmhJHOljMNJVHo5DoGC8L8ImpGS8KpcipWFWxB8XQi1kCssVw2l0GtplMIKFk4AYlpqoMRrBYzADDLBEHTuViYgH_m4KCPaUj_zcBWNOAAjOXBpADTEwAgbIV0sZjxlaohVKyEWsh5FiuG2i7EAS0ymABfYyINlqoBuCIAO7EbiWMwqq4UqYVRUi9bCLWRD6hXDaXQOgpTwAEzljMO2mqgG2MF4OgAHiBeDQAQL+wG0EZFZF0rUzqBhIJWRuSxXDbYQKIQSaBI4yDLvlKloT4Mgyk0dq6Ll5ZUwrUyiFWojPWL5hItZqpv1CuVTaXSiU3_SkQaSBBesZL7gplO01UijEHoYLwdwQACrABxoMRMq0BBWplRBEpFk0kWsh8ViqGmwglJUnhBAJplwaSqTQiIYLwCmKx8JcE+1IA2hNsuxElVI9g5AU0mgAMS6qhuAMRFwOgK0adoKGIGLUK5UROixj_w5GGsilFivVTSA5BOCCAD3LgukkAphkAilC8iJYv_ilBRM8qRRLIKm7WRayVRSK1MumkBWidLJoAS22ppZNZVACcYLydux0LKQAGrAA1IAYjADy4AYJABgoAAAAAAAAAAABISAB1IAYjADy4AkHAAAAAAAAAAAC9AEJcNNigRBgAFjwAIS4AVSdABr5CAAGIAEiCIFQcFaaQTrKAQjwDAQC0ALIA0EeAAAAAAADARczYDCwcyNjpSN4ZODd64BgJyocDiCIDjRkALjHgA3gRAACEAAAwEU5PYmNuOk8DHl9fBk9eCgIeTm4a"
noncomputable def WL42_1 : ℕ := zfNat64 33247 "B8TiCAAEUOANgYATJQvAKscPwNoZUoXhNppRGKFisOanQZSaQQAAihxGgdGqC4GNwZA2MmA6wdACtiYABiEpAFoAAQg4AYJERIMACkoXgDkDb7BWFozoeMJZAWFC8JSGkUoiQwAAihwBkoAVZg9BgJklQB8Dh+BtCplC8MJhApBYzD9y0AmsyAACKHACgQg9Bgrs7SonIAJAfgbT4BcBBc8PGCi4CSA9o2AACKHCGBSDTUkrsC5WT0qjkpNpqK0C5WKYZs9lImqWx6LQsNVci2cx0xszAAADEGmpJWiFysnpVHJSbTUV8FysUwzZ7Kjxarp_PH4tCk022l1OxszCohkPSiRQAQCOLBMDAMpKF4DnDx2BtE0lC81I1GkGvFjMDCAjkyCiRf6HQABnWYEehCC5YNgYABhEA0QyACqjwAC0ACoh8AAQQAQoQAAAAAAAAAAAABG8ABlgwYUHoNZk6CyB8ASQtIe0qAAHhcFRP8MwBxFstCCQ8ABJWCLNgXqdAZSPgNox8qABHRcAA0AyD_xsAiAuAAkrJIHwd6PgCHHjsDaOLKF4GkDqGC8KiBpcyP9Nw1AaqXACuaPwIcgPwByA0WjeNALlYZRSNWcBaFRB3NxMbHJRtGpFtpD8uBnxoBR87AbZ4_AHI5dKtI3wuVnZWDPZQFoVEAYm0mprRuJhlwO3d3KgCFCDOSQAGOAYCAM4XANEMgA4REAAtAAh0TAAMsJiZiwGbGbEAGcw3AwDnTYDvR8BtHYlQTSqC_C4AAgRkAAEUOAKGhDcDAkBrFQEVj4DaIlKgFPRkIAABwHQAARQ4DcOhgZWhwwiMmCc5UAYA4fhaSJ5Uo4G_6tGkNTFwAETBIAACIMABVCADdKF4PQ6Rw_A2glyhepAGJppLJPoqAAiYJAAARBi_ACQ0RGTBOcqAMAcPwtJE8qP3rRpDUxcAAfQSAAAAHjQRjR3yRWDByhfMQqmMPHYG2or5KF5WVVNWcszkWgAIPEgAmgAAKaAKhVIG0SDYMTlQB9jx2TQ2iwyheVk0hqQuAAOoJAAAOzoAkZgFF9pUAPw4fhaSF5UVH8jVnC1ZshIKAAHnCQAA8KAEwbkqcD4SheAvY8dgxNomMoXlZNIawLgCcgnoYAAFIcCVycFHSoBIRw_C0kfSorJpDkRcAAbgeAABEFAAVKmL079ZUFTKF4DIjh+DE2h2yhePAOrJVLJe4uA2gAAAUg4OcYljIwUdKgEiHD8LSR9KismkORFwABuB4AAEQUI7M3_koVkvLGLlYBAjx2DE2jjyhfJSSaQDyULwNoAVhxGAACIKA+lADisponBmeIXKwHTHjsyjE2iZShfFayaQXLQQQAF2EQAAIgoAHJmNBUmpIng9guV1EjEpDk0kE0jbi5W8k2rJpLM5FpRAAUgABSDh+AuJIKMLlZRLjqQ5NK+kJ+aRkxcrLNVMp+M6IGULzKBE5GBCAACIKKk7s48G4KgYhBFUqAEkgPwNo9EqJDUQjkXAaQAW4JAAQcGhgGGuBMGNOuYwZ4XKwCkHjsJNpGMlC8rJpDpZcfmDhyYE4gAAJwoCpjIKAlQB4Dh+FpIylR8BasmkJaC8D4Ado8B8BoAAAkNI+GQS1KF4A5A2kAyhf0tOrNlBL5QvAe0UDTjiMAAAeZgBIaIeMG4P0LlYA5C0sxUKblC5WVmy1WcwDKF4D2ig+ccRgPSSBEBImABIaIeMG4OyLlYFUcgbai8soXlZso_lqvOSzlC8B7RQNGOIwWYjE0GoAIASGiqjILxlQC7Dx2BtKUlRWQGNWcBaCkj4BOo8BFAT4RAyMgENmAVTGlC8CqOQEI3a6i20oXlVstpC4hDEmI9qIU3IsYgwAAAZSIUQzTZnYEXKwB6Tk0qgTkblC8rKx2TWWZyLQHIdQISuBgAAAEDRUitTLSfwuVgpByTl6zdrE8FysrNlHenwtAe0U0h7jZmcQAAVED2FysAjZo7H4nRpG+FysyItWUBaE5AmJxiI4dwCtI0ToE8LgcsZkulC8_cHAxUMNSG0h8SheFGyg4I6dhLYabVhKwAAFEOAFFQrgowuVgDknKJWjeP+LlZWTSDQDBeA9AXaZZ6bgAABMid2GUolKmCkC5WAAg8dk5No_8oX12smkHNGC_8RcD0AAA2YjA6QKVPgVqYHiLlYBLTR2Tk0i8i5WHxVLZlAWgNSPjMTEIpxAVYnSwA7BUClVRLKuwuVhBqI5JyaQFJzTi5WLZVLZlqq5j5+LQuj2emkooONmZHQCGgN4oVwSwXK5eFQBdNHYOTSMGLlZWbKADjBeA9A3oZExoJ+BuJTEQAOGo6JWpgoIuVgI_NHZOTSLyLlZ0ZaMoC0K2nQExCpJoIGZCIHQBWNAYw4Y5SC8pUAyQMJgWSOZUKSwh0Y2D_x8Ar4yCKAQASkogJ4uVgDmejk03ATnDFysi3sViYsGcBaH7TIMOpQxAcULyrI0eghtJSDqLKjczTgNpeE8VwAOiAJDQ+gdsiAjqbACuCIABqABswyAACnAx9kABKgCQ30g17hOBVJMBcY6AEREwAC0ADgBcAAAABYgB5UASGgJkYAAEhkAAGDgAB4XAAAAAAchiALrwBIaZYRgiXSflQAFdH4FRQf+MQTcRgAA7GQAAB8eABOIGJSB0JUKQ0AfAbReJUUT_ikByCoAgAbZWAAMITACFVjRlCuWk_hcrFJ6ioHIOTaO0LlY1rNlAiylPFIPaKZRhRozb4DABkAzAPiM6ArA7wuV2EEdHju0kk2jGShefR7WQwoDC0Ho+5qCaAAYIeBKaaTQeBcrKotqI5NpFNMek5ZhcrONVRYzYyqC1oqxfJqwhGh2EmzESm4QI4C0eeULwdlbO7QSkPocMA1TTtkCMASdLKoKguVkUqI5Ko1NN+k51RcrqpVMoNZKF9RB7RQbOOIwDJScPGQ9ABpJModGFGgduUL_ymwHaPHYG0XSULys2UAvlC8B7RQM+OIwkyUsIABQDkaHnuKlsCVFysAWR47B6bR2ZQvCqaQ+YXAPQD6jwIQAAAcJAegpGh7CSsDbC5WAWQemkX6ULwql8aM4fyLgHvPE4P_EQIQmgAAB2gpwUvw8eIgThKf+GwFkmJptgnA1KF4VTSWQjRgvAigAIbKRQMpYOgZFxsAErwDGaABxRSBE8qAnoG0fSVH605_zUDvToAAK5V_56NtFAAAErwO0W6hKApqVAKcOH4G0oaVBNNIOOOH__EoACZlQRKKHUAdAvqkAdlgNEMNwtCQZuVAYDPgtItkqJq9BmCogADUwP8WoDRRcAFCaOYVnD8CgFysBJpo7CyaRdhcrP+KxlBchQvAagOALlYbaKBtYiAak4fgowuVw0ByFk0jwShef4VjKA5iheBoDxuAbkoXhtooEICIAxjWVi0BkwuAnM9sJpFTFysKg+mYBnFC8cgAS4yXj0y0UAMg4jAJkjArToDtLbotAXQNgK4HxJP_Mwq8qASgAAf+Qh6F0C5RUAQiKd5GbgFA2AqApoGW2ikE0A_8bAAbmMgAJ7FQAQqIERLNUjUGCgc0VAD0AbmnABx02AAno9CKAAcb6h4ucAhLlUAcgZQPgBV5sAAFioAAAAACw94kMX_A4ACpKRVAojGU4P7IwNaOgABiHwAANhYAYkU7yMzEOB9ykARQCuw8TQmm2NgAA_81AWQJNDQ96lA0H5K1MAgjkHAvXwSvLQIYBZFgzgADUilkomz14AAB5arUbMokDdlIDUSMATJIgAAY2awyAYQDpZLIEkzYAXnUAil_8TgN2KQACE6X_5KMITKHiqAdTRgAKlMRNABfRkAJ_OAFnQ3wmCRyzwoURDYbEAABORoAAA_w9APcCFQJKOMpTSB5GAnlKmAJNEjkEKoE0JIEEABHLBnHseF4sgbdSgBQHwAE2qxKlhEyjjFamAfMG5NSbMXRHTuakmgwWAgHaKUUCKwFcx0LQIZZqNRrJSQAcG1YpEuKmGc1GopAVq59EaqVybUTrTXnoksg1U+lUDNFJJZqO+0qgl0glUyS9bqNZG3p0sLwBB1BMrYAGZA_xoAEHGSkwUPUgKrkisQlZOMoQxAKqAAH_FIggAAGzpxAwmAoxSpgAEgj0JiNDKKRRyARtUnkkAEPFy8okksgP2Up4CPc4TTbAMysQDkASkdAASgACNGgAAAAi8AFRgBh8AGOgDJcAAAAAAAAAAAAACdAvbYitCjhpNeACo1CSQ0cgBlAA6YbEUMIACUnGKHZIQAINACABYZAyPQCZUBDxKBkEou3MggAmYyXjUGoPQQYwfABmpAAToAAAAAAAAAAAAP5SARnaDBBiCsJMrAioBE9iTCUEoWFTCMAEpJL4DoYgLFDiYAZzoRUaGyMoXg4ceRgQkggpAuAQ8ekdAdbdzGp_4WAAIlFIZBCD1Eh4CGkoAJb6QfAFTI4BdPnYAdLJHSBZEXQih+lu5gAGkepGTiCBdwCAAGfAZ7fVD4TihDAAEpZJCAGmgF1AANIxM8hDEC3wEAAI6uU4fwGYihUJ+E5UCNFx7PZ6GSWgQsYy2WhaaCZ+RgroD1quPRzOQmhHxouCao0NzR9HCcgREekEUkBJINQNSuZySD0CokEuSJDHoEZAy0aGOlOj0EoID2YkUgy2648kUOFj0GIEpbuY5PplwFESi0WikHoAZaNDotBKCHYTJujMiLkEgjEAJBJqGBHoNQaYvCUegTNH4tCKAnMl4OGfQxcpU+glBTChEGcykg0GayGAkEgzULzOSYhTT3EysczUWu_JkZ30J+SUT0CKlPmMpQo1loZmM1mMZlrcR5mgYyZl5KFcNjtttotEsZkP_0JZ6NDbiQJxbJQ7IR6DlLk4ntNptdwMZ0SXSSTMaKptGl0WWvPHmdBIs9jttto5HMxEWPI6ColGhsHIE45moxkI9A3lycAAZ1fqNDsoX0C7E1QjlUuS0WSY1kLoXEkgBMSKRSCfmRj1pczAsLBwcBELRoZn0amSSgkEiz0Sp8zIpJGMhWyFDzGJDsej0NHt3MmhRAwJFIpJIJZAYDxsAwkNCzUDObkPALVvMRFTQwIAZ_wfDXEIkJFADyAA4g0flEJIFbQ4Cw+xNUEicpBcoVySERWprtNHY5GaeP4SPSCSQ7gZ7OR6CS7vHek00kkH0o8DUWlEfqRPIodIJFQHCR1hInKSiSQLK1MnRo7HI9go9IJJCLe0SWPR6PRWAAc6r3RJ7RkqPPR6A1FpVKNJFpNMCAIaAVbonhImGSaSWRK1Mikmo2kmjyTKZdOo90KOTayZcCdSDRaSTQGpKyxeVTfKluol0kjt06WFoEJt1dEv5FjMMMKwBBJrUlYqjc0CWTQ0ycFVAAQIAAbkYAwBEVAEhoAAAAAAAAAAAQc6Pq8Bg+FRAHo9IMAFC3Q4+IagSxyfo6KIE0ACCS5bKpZAMqUwsj1ESmB4AG6gBykAZRgBokAAAAAAAAAAAK9jlKIqQJwDcsVwB6LYoKxZKiPQECORlAA_QtD0KIG3lIBSsHow0AHLwAXaADJQA1GAHlQAYaABiQAkKAAA"
noncomputable def WL42_2 : ℕ := zfNat64 33248 "DsXLwBxFisAtmXBdJJBOTlQYQA9IkAAAACagFLMAQKgPBgNoPTYB5B0ADUKimgIMPgKIAAAA8GADwbAECpGgohRcBiCoCryMAAOKgqkELIBRAAACNBQKhGRWQzlC8DMRUAasLgukksMzEkNsKQAXAOAAAAaVQ8aOzJGTMrIaSheAWYsVgA3C5eF0kkEhTJjJJ+ZiKIAABBweB0BiYQTByMi4FfFQA1AFGFQAUCRg_0pAH0AAKQUHtGz4DJmLaygMoXgC0HIIrLF4XSSAaZMZJP8NwSmIJNGxlAABMFAA_YyEehkzHtZGGULyCBUiBOTRyA2yxeF0kgGmTGSQ2g6hKGplAABsFBeg4jJeWMx6WWulC_MTkEkck0cgdFpdLNFvQfGEkgBPkpOxsZQABQBRgosGALJ4Jg4FhMAPiYA4hUAA2IgAQEpAB_4eQIAABgIAWBUpYZH_Vo7pUAABQi4GsdBeyUCBKbTVEJQ6IYAAAZxUvyFcAyKzAwuAACjxcDWOn_mb2iUCBKbTVAJQhAANwsANgqwwifEZMyu57LgAAyOXCkax0YmUSSZLBAlNpurkYQwofAALMBolQ1kTFjJmF3FZcAAEuy4mICBY+MTK2hMlggQpp6EiOAAGsiAaeVClZv_jrMBUAAD4qAAHFQAAAAikoqgB_46B0dnQMfxavDAUbMIEwgGAv_NwFDHgABCgAPKZgABPDQAABgIAOTMjQUANcqA_+dAB6Sops01IIvnwABLx4AAjQUAOAiRoKYGMHwopGOm4KSejCTElJpS4LM1FCeH_y4CyNUCHQAAjQUAepSBL1QHgzijIBYxAAABJaKH_moP4LQFqCIAAB4MAfAuYkKfYRAPliuOR94obHIhJ6SZaQ0oXlRqKV0SWTRyBZlptospAAMSFBzQ4eGSzoFrZg_NcALpgeBgLoDCIAAQoAELj4ACmhkAAAYCALgaapEEFKpQvAFIBCBbF5cVlFqJLAUl1soDXyoADx4sABJGRFIggnhKF4ApAKEFx7dYvkkOsFQXpagF2lQAAoA4AiikASGgb2QjulQAAAQSSAzEymH9WoBUiEAAAryRBBdSULwCCWkpsXWKLiskkBSf5dqfs2sBhZUXAGAADkDDqQDpIEd7RcAABES4HpJIIUTA2mwzOZhjCNHlcNAAAB_3gTZEzWRBBdKULwCqBIEqAsgJuKg2lkknEKkqBoAASOOrxkQQW5lC8AehlArZQvKyhtElk9NYYLy62UOI3g2Zh95WAAKgWwqRBBZUXKwSUnD0MoLSJlC86hdWaKT0Wh1xyzFtAPGTMKp1AOALEyMuASIILcyheAPZKZQCaULys0UHnFjMsy7WUOIvA2ZgACgDhXe6kQQU5FysAekkyi5C5WUUoX0Ws0U6mfACMF5hutlDiC8NmYSiaLRMAAAPQpjVi_IaSQVpFyuooWYqaPSKZU9JUcWk9KF9FLNFmWfT0Wl262Wsi8cTDMZyAUQBdkP7Up8iE_bkXKwJo9oplEflC8tJQvopZoo3c+FtLF44goJuBjOSiVQ6jqxg2So6AYtZ1V6RAi8qApYfAB9So_ytAPkMgAA9mUrhoAAASLUs+RBBMaUL5CW6TiKETKTEWlZ2qjABz5CRgvDp1sIfBu1kxlcNAAAD4RsYNgBkCc0kEUZQvAN8YO5iZQ9wXA5kIPRbGSkmZG4rWoVwvsTAAlpOiZGaSCZouViEIoxmJlHelC825QvWA6byzSSDVpSnMZNKFkp+JTKB0L7EwAWeKUnYEls0nFjmkCMnrdi5WH_E4enCGYlP+i4ugAtAATwWMwAFaEQUx93Q3IB_VkDSIIJaSheB0gqAJKFwVSSDpDJeFlAx6ZE3+asAT+HgBhIxrhMj5ybEE_ZQvLJaA6FpZnItPklxhLNFHJsAeEN1MtZCCj48dkEqgD2SIAkFlvw0foaA7pEANQF9Qw+CIALwFQAAxJIAAApwpGhg+WIiRzWerkLldhCCNarOZSGV5lxvXDuWSSPRjhcrqp1soBmSheVR6BFJCAICpahFKkCwxgK11KyMA1A4VAH6BYAMJFAKoAAxEIAAFwsAIprHZCDVPIbzi5WQQmkWY2EizEhJQvNpZmYnG0Dx9RSScTCF0lJdsJVMJ1FCyaw8jBsuQAp1Cq1IMPjAA5__kYADhUABUAMJFAvUoVwABrIQAALhYAAPUux03BwVJ0DSQxFyukq0E0e1kykpI6UL7iWQehSSRXXQP1rwBouVmWwlUOoGsYNlyiytmdjs7ZgKHTipjT046BcDApBgAxkxAAEImAAfg8AAAABuBgB6pQBE+D8GBSDAIYqCMikARodAOQAAIlBwAAbgYCQWKnB+DApBgFoRlBykAWVEGwQX7hcDcMF4AH7w4AARIMAAdODYGBSDAAw6AAABbx0AAAEwKAADcDADbTgf58GwMCkGCLhkAAf+UiIkwIGOkEAACYFAABuBgFhTUAGHwA4qAJjQAAAAAAAAAAAADI8KoMCkGBYpUAYw8hgbRMZUDeDoAA_gNAAAG4GAXxfB+DYUgYFIMDDiID_60AAIIgAAgAARBIAANwMAC02FUGBSDAukqAQkeQwNoiMqAAAAHALAABuBgDG3wlA2FIGBSDA7MmALoAAgmAygAABiEgAA3AwX1YDIMuoCAJJQvAqiIOH4G1cStTFoUkHsnFkAAggkAAIkGAAmZAIhQO5KgE0IT8LaNJKgzsnB_5aAADcJAAAWBgAJiwLAwEQoHclQCaEJ+FtGklQZ2Tg_8tAABuEgAAACQ0OoHALQRaqVwBHD8DauJWpi0KSLcUqZZAADsJAAAFAFIEBaAkpAfjMHY2nZi4CSHsFoAAgQkAAKAKADKzAiDAMpKgMgskB+Ck2nyC4CSHsloAAggkAABEGA0DYKmcvBB0qALQgPyim0dCVASQrUbAAG4HgAAbBQAAs4AjRCEFHmXgS2VAEEDCJFKgAFMbAXQAAAIQUCNCUzl4IOlQBakB+UU2jnyoP_JQVqNgABiEwAAARBX9l4_w3MLKF4BODh+UU2hAyheBJA5Bg3CKgeuKgACdCwBsLwIqKgJvHwf+bhM5UABADIAAKxMOiGAAAACVC6fqbn4lC8JpVc4cPyim0MSULwJIUVcGjOPA0RUah_oqD_Y0AX5CAEBAQCHNVMNG0F4FQGjj4P+Nwz0qACFRkAA6QqAAP8RABnYyVLi8G1DJQvLJVR6UU2iMyheBJCiFI0ZhFdAGwHRSEisUgEUBEOIwPABJXjw8Us0dkURUXKzqA5JtFNo0koXmEJICcMF4RUEMDwpoOhAB_IaAACrAElIAcXAEyoBgIAAAAAAAAAAADARG4M6SgXWqRoKLp9duBMXKwByUW0j_i5WB_VGFHlCsAA71I2bgAEaCgBrTwIAx6F4AkkwAtDoACETAAPQAFzNwAAEAYnyWhAGAjzLwBJJgBaHQAAgqAP6MQAAQQSAAAMBEKBPWYBgIACBMB0dcnA5AdBMADcloAAKAcAAAYCB_4qNRJ3aSoJoyo8dhdNoFUoXgAm42AAH+LAAEaDgRoO_8VGok7tJUE0ZUeOwum0CqULwATcbAAD_FgAAAcCEAILgYCgdEwMPKipAsD0mJpGnlQSkLoAApAAAMBQEWPbsKgy6VFNCYHjsLtpInlQcQNZGwACKh4AAjQcFaiw4CRWKjSJcpCa01SHIXTSKPKF5JtpZCjMQAu2VEnHgAEGhxZ2IASFn3CoJoFi5WE0S4eOxqXTaCxKF4EkI6GwAAWh4AAAAkrBqZYlgiBOxMBiI6AEiEwAC0AD4hkAADRJAuFUSKwmykJoMQ8dhdAM3a6idsoXgSSKAJYpjUAAohEjPdqwBSwiAAqrnyVACJFYTZSE0RYeOzSURvtG8J2ULwgkkKIpDBuAA6IiCqAbaIgPAZsAJhQUnhk6UhNDkHjsLptBMlC_ByMd4SgZsbAABUHgAANIGu7FQaxKiJKcDmql20k_yo4gGVzIAAKw8ASAAgDMCOIQDBUC2SoCoRY4fkxNJpouwUjEpjJdAACXnwAAog4BU+kABGgCIMeURAwsiA_8hAC+CIABsFwAALBoAAHi0r_hUGsSo+0nA5OpdNJKcqKoBYg2AACsPA3guAACYo__BQDuyos4nGrD4LJtGLlQbS6N4YgAAMRMOqGAAA+PAC6MANwgpF8JxKi5WU0HIXSGN2sNWULyKcf9rQDUAAKw9_RCLvGQAToDkIm7io7AnSkg8nA5C6aTPRdg5GFI5AATUAAukkFekQAEkYASfAEhIAAAAAAAAAAAABJiCG2wDBsAJiYALJsAGtQgA_+vAAAAALh4IgPHa5kJ+DaTJcpqpNKI5OJZEo0ZxbpQvDTVQGIAbf_qUjFYLs12oB1QsQYAHshjzyGOqTJcpCaDkLIimTWG7KF4MmC_bbSqwDEMhdAtGhBdDCEohYqY0hGbEkQaN8SKwkykJoD80d1UsoYaM4dkoXm0q6YSgGPrkIAA5BMAAGMDTGiRWEkoRUrCaURzVSyPxk1i2ShebSqEEbsYL7qaSyA8wmEMSKwAApXaGkFFCcJJgyhWE0ojmqlk09sTjPlC80gQSSLTCAYQKj6EB84mEAzOJA6Zyt3TgIeAwDBQJgSsVAU8PgMohsqADCAAEEEgAAMAxCoZzhzs3UhoCCPhCBgSgwGELgo6jEEDLVfWFwFTqAkAAL0JAACJBgrqx8dt7XBDYGPACgIEmlQE1yYAQeVAaQqMVAARKDgAADAQDcDAKAgSaVATXJgBB5UBpCoxUABEoOAAAAQlxEgwFBC4ADBUnD_Z0dILgtJdHulCsAAAAESDAATGgIgYASEwAXiIABUTAAFomAAOoHAAACJkoIzfDcDAmBgVCTAAABNRKGEAATgcAAG4GAHAnCkDLsHgAqbAAABSQcwvAABiFgAApAwAAVYG+nAShQAVNgAAApIKgWgABPBwAABgIBGCcNwUCUKB_5sAAEECkg5heAAAAApAwCHU4AmZAIhQP_NgAAggUkGkLwAAQhoAAAwEAOBOG4KBKFABU2AAACkgqBaAAE8NAAACHk4AkNAIhQQBNgAAggUkGmLwAASBoAAAbqnA9BwTUBLSUB_BMhhONgpJRJIFFzGAAhEeMoHAAAMLTk2EjGBwX3NgDzJQBBApJRJMyFzGAAboeKIAE2EidHQEpAw+xNQCzXA8DHEhQLC2KgFnHwASoqAA+hUAH9EqggAAeBgCsGP8dAAgA2iEoXgPmOH4G0RiULwNJClolIBmagyAeAABWDBKAIWYLFVCkDAH+JgK3HQAgAmACaRMAAKQAApAwSgAsiDYGAiiVAe0PgNo3sqGdD3_GoHGFQANQAABsDAASCgRBgIolQHtD4DaOhKhnQ9_xqB+BUAAEcaAAABkGAHOULwEQHD8DaFpKF5U4itP9Vo2KVAAKkHgABSAUgy6h4FKlC8Bex47A2isyheBpLJ34qD+p0DfE4ggABFDgDYGAEyULwCrHD8DaGVKF4TaaURihYrDmp0GUmkEAAIocRoHRqguBjcGQNjJgOsHQArYmAA"
noncomputable def WL42_3 : ℕ := zfNat64 28818 "iTgCSMAAAAAAAAAAAAAkZADy4AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAFIwANCAJlQAgaACCwAISAAAAAAAAAAAAAhLgAAAAAAAAAAAAMBBXBgPuXACBCgArpcAATgoAAjqwGAAAMBAAMQgCRkAPKgAAAAAAAAAAAAAVYBApAEj4ACHAMBAAAAAAAyCgAAAAAwEAAxGAQlQAAAAAAAAAAAAELMAtPhuBgAxmwAABoWAAAAIlBwAAbgYACSsAiPgJAoAKmwAAAAAAESg4AANwMAJAxxjYAAxQkAAxLj9QsX6GAAAiYHAACJBgBDswKg0lDrVUyAAuHAAJi4EMQwAAESg4AARIMBoAMPgBxUATGgAAAAAAAAAAAALT4JAyAAA4JAACiYAAACJgcAAEIGAGgoRxkASSYAWQkABCJgADIAESg4AANwMAAdKAQowAw+AAAAAAAAATAoAAAwEAAJOADJQAxGADGQAkiAJBQAAAAAAAAAAAAA6UABRgBZ8AFLgBJUARGgAQsAAAAAAAAAAAAHQ6AJ5UAAEsDgADECwAALQ4sAUAAAAsLBwO4CfH_2JnRcBBo2ABdFwABlFgAD5EQAOQEHA4kiE_LDkMuAEIDlhJg5cAC7SRWAF4XrdNFIUQtthICLArNzZDZgAdidJCDgZABc2AAABBMCFoYAACJQcAAG4GAAmxLvnwYUpFwELzoCiniLgN4FB0AAImBwAAiQYDwAYnBcLCOMgF+bAAG0IgIWhgAAIlBwAAbgYAuEumHxYddFwD4ihODkukSC4AFsEwAESg4AARIMG4BPUhZEg5UzB2NgAqD0FAGwIWhgAAIlBwAAbgYiQAExAMID8sMtHNJE7Ew1KoHRLgUg6hiKEisAAImBwAAiQYOVjR7_Jw_ouYV78BddayPTwFC+qkUCclwdKEgAAImBwAAiQYwUE1BQ8B0GAohCNmYAmA4ABMXAhiGAAAiYHAACJBiNAGiUAwEC8aAHxMAAAAAjBoACJQcAAG4GAoArxxED21RcBWQAjhcAAqhIACJQcAAIkGLUCsG8cRA9tUXAK2FgAgRcAGYHgyABEoOAADcDAAEPiUKo8AYCoAAJIACWhYACJQcAAG4GABajACwhAQJgAAniUAAAARKDgAA3AwAA0oBabCEHAvGgB8TAABJDQdAAAARKDgAA3AwAA0oQg7xxED21RcAAEkchsAdmYgACJQcAAG4GAHWhCEHAPRWFx8AKXIhAFJYYXB9CCZW3JwAETA4AARIMAAhWRlJgetFKgPaIQ5AQoXBlAWwlAARKDgAA3AwJ1kwPfBFwBBP_owdAywIXXLSjKBlNQmSwAImBwAAiQYd4KijFScHo9SheAxIJNopd4y92XG0ykEMJXkSWAB+0OAAESDFndghByBSYngfAYTiAST6ANReq8ixKAAiUHAABuBgJsaursw8DBKQJgxkyYEqNC4BiAOa6Yo2A+MRAABEwOAAESDAASVhMR4C_lQGwjYNIFdKgANcTAARKDgAA3AwABUZ_4iKEH2lC4AahpR4rDfC4OgA_CYACJQcAAG4GGCjIXo4jJyIkoXgDEK0yayiUILiqAXJOgAImBwAAiQYABmsCKOIyciLKF4U5GBj_A6NJVMClzjDSGAAAETA4AARIMAFxqCE41CPr9FwAxH0NGcKEF1JAMOIQAESg4AANwMPLGXeyK0kGC5QvAFpR3QzBgwuKoAKwsZgARKDgAA3Aximd2Z3dyALT4FgYAMpsEEAgAAEEwAAAESg4AANwMRICt3gFp8AwEUweAeRMBgQABRMAAABEoOAADcDABcTgFp8AwEC8aA_ZsAAdf_DQAAABEoOAADcDASB71IGAZpJEDkIpUBUIodAWaCABUpGAAiUHAABuBgCsGXmOIycj4LlYXQalxWWuYwJpQvJiJRRGw9IoAH7Q4AARIMXJvf2oLEoY7h3aHHnMCALT4AoCAAAoJAACiYAAACJQcAAAYCABafDcDAKAgAAKCQAAomAAAAiUHAAAAET4bgYAAAoJAADioByAAATQOAADcDAATYgAKEAEPgEQYAKmwAAAoKgHIBQFgAIlBwAAbgYAA6UAGQgBJ8AILgAZUATGgAAAAAAAAAAAAIS4HgYABA8AABGhgAATEQAAAAB4GAAaXAEhoAe0uAfyVABWS4J6BTyYGIAAAABG74AkZADy4ANgeA+glAAAf8NgAAAAA8HAATPgCRkAPLgAGDYAAGjFwATXqHQAAAAKASCsAHmQBIWAgOAAgTADUNgADBMAAJjIAAAAAAPl+9iQANC5eBBGoHQNHchqeXBbXkL1sYzkGIAAADdEgAQmZKB+EuAGoL8OG5OsuC2his6AAAABuiQAITJJyIAEpUA3o6AAIPAxKgACCbAAAAAoB4D4+brwAMnAEjIAeXAALmwABhAP1BQDSRgAAAADwUABIyAHlwBORcBl5CAmiXi4AAukwAAABI4+AAcZAeJAf_LgvgpC+Qn4U0Y1DLgnoFNJgAA7AJAAAA4uAJwLgMvIQE0S4XAAF0mUcnAAAABCFgAcWYWI2sBoGNFwBBAF8FwT0H0kwADByIAAIQsABiymJGFaHAxwuAIILIThfBcH9T4F8kwAH8i4AAIQsC4qwAtC5eBRHoA6UJ4xpuXEUnoFNJlaMRRAFEKQAEHBoACJmCy8n9SAABwfAAEyoPrnwBNAAvCkAAEIWAMDDY8Ajl1jnQDHC4AghTRfBcGgz4CQkwJAAEcLAAaQAdFwBIaiM6AJuVAaCQg_+nCai4AAukwJAAAAABll5BnQAHioAT58AAzKgACoTAABZBoA1JGB2dKQAOlADD4BCZAAAAAAAAAAAAAHGQFOWo5KABKVACYPgAGJUAAUCYAA_gpAAAAhGiCUgGOFwBBD0ChPF8FwABdJgAAAAQhkDoAMPgQRkQikAQsqAtIhB_JOEMFwAAAAWQAWapABWMjlRhKF8i4AASA_DiicWKLgtocWOgADDkRZAB9SsAJkyvtO4wbAWguXgD0ptJNnlwW1JqxfCJHTsAALP7kYAzurACzMobTgRhwD4Ll4A9ANydLNnlxFLaXQnJw7_oBAALSyRQDPKsGdzXzofHzcCbgAZOAHFwAC5sAAYQD9wUA5UZACcAAAAD0KAGFfADi4AlUqA_8nAAEyoAqYaRxMSsAAAAD0KAIgfADi4ABc2DVR0AUQkhUAEEQAnAAAAA9CgBMWbkEQRC+RcAPQCxRcFB2oNOHQAGvCYAAHoUCOlpE4XLwI4pD0CaCJKF4G0Gy5bJo5J8yb66ACYHgAAehQAIC4ACNAAEDwAAEaGAAAsVAAAAABgIB8QqIKxF30rC0Aegy5IngTSheFU2m4E4c5mYgAAAAehQH4YASMgB5cAAQPAAARoYAACxUAAAAAGAgAEoRJJQftIkIFy8COKQ9AmgiSheXE2_IWiaOT7NmeugAAAD0KA8AFFx_o0SkBZQvCaTR6EUiiGKF4LyheH2yhQEieOSxMm+ugAAAD0KDHDja8rNwBCzHmdANQOFQC5yYAHAVAApYm_sJAAlAmAAFAFAAA4uAJjQABhEAHYmAANDAPHgABMRAAAAAAICAWBZpUoAgxcA4YqACKFwf7PgKWTBEAAABORcANsvDBCAai8UguAcYVABFi4J6BTSaIgACEO_iKgJ6JwBAS6kT4eBMBBi4BwhUAEULgnoFJJoiAAIQ7SQIPpQGjY7NjqGUlJSOgLquBYGLoIYKgBaAH0KgAoUXAAXINgAA3AwABb4AkFA2DAAYJgBREwAAgmIMFwAAADcqAAAB5mwESuB0GcMwXwYuqLl4A9AAZlxOf+GwpKIYELIAVLGYAAEwYACQUE8tACUeAEUTAByhgAAYGwAAHiIAAD9wweBhcxiMDJnLQFCkisAlpOZ6MKYM7c0iWHUMJRZfmQA4oIHhkA8HoYgOcXAXUKgC0RcE9P_M2ukoAAvRkAABgKAP_XCeysGg7AgB42AcAVAGDS4HP+zYMsyEieYEEpRQACDQcAAQTBwO2YxAxmQXAEsJFYAN4uXhPRazBnJJ+B2JoSSgxkA5AAZMYgYz+LgDGEisAG4XLz9x1PQ7zBnJIdSaBCIyR4NAAA8AlTpcxmhDIWgSUAG8XLycz0NwxEkCaAicsZmkcmzAECMl4AHAooBI9DEDHC4AcgFyC4J6GXiaUDpFiuAcYyC8g1AyAEQSKAS5wxH+zJ6BcAJQDVhcTmenrmIkgWQwnrTILyWkqoNAqAj0zEDFFpYvALkUJwDkhcvSANDkDCoZElgTQHTljMMNpMoIgLGYAGVYYQYnfLF4BMihObQAWli+MjkDC25IjjU3ImgPnLGYYbSZQRAWMxDkiLo9BQlC8CSOTKE5Kln_CoW02cz0NIxD3RJYEUAHJYzCrZTDKQDEOzOZAlM0iwobdKsXw_4XACUB0QtowuAAxiJLAAMMZLwACLChsHR0ZJQTTVAwFCeWgWSRADUC3kMUomAAggAbMOgAAMBRSh8rVgDm+C4GAk4XAPGPHYEUioXF1DaKgcQAC9GQAAEgYAVF8AwEEMWAzBUH+GImgF0kxUAEqlIAAXZcAABYGAAOnAAUIAWdAIS4AAAAAAAAAAAAYFCB4G9AdBUQ2A_8zACk6RsF0CLYRmAAL4ZAAAWBgNCYXDFY0AJBQMAw7hIE4lQHfioAQCVBd_8lBkoqAAFYNAAAAAS4AkNBSCxcA7Fy8AcRYrALZlwXSSQTk5UGEAPSJAAAAAmoBSzAECoDwYDaD02AeQdAA1CopoCDD4CiAAAAPBgA8GwBA"
noncomputable def WL42s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL42_0) (dpk j 1 WL42_1)
noncomputable def WL42s2_4 (j : ℕ) : ℕ := dsel j 3 (dpk j 2 WL42_2) (dpk j 3 WL42_3)
noncomputable def WL42s0_4 (j : ℕ) : ℕ := dsel j 2 (WL42s0_2 j) (WL42s2_4 j)
noncomputable def WL42 (j : ℕ) : ℕ := (WL42s0_4 j)
noncomputable def WD42 : ℕ → ℕ := rdw WL42
noncomputable def ready42_cuts0 : List (ℕ × St × ℕ) := []

theorem ready42_cuts0_ok : CutsOk ready42_cuts0 := cutsOk_nil

noncomputable def ready42_0_state : St := ⟨26112, 285696, 51168, 220224, 52016, 96519, 29666, 44151, 53248, 79646, 29184, 45301, 28545, 113424, 26112, 285696, 77280, 421743, 129296, 473759, 158962, 503425, 212210, 556673, 241394, 585857, 269939, 614402, 296051, 640514, 103184, 272942, 132850, 302608, 186098, 355856, 215282, 385040, 243827, 413585, 269939, 614402, 81682, 126185, 134930, 179433, 164114, 208617, 192659, 277538, 218771, 563234, 82914, 109312, 112098, 138496, 140643, 225522, 166755, 511218, 82432, 108830, 110977, 195856, 137089, 481552, 57729, 142608, 83841, 428304, 54657, 399120, 0⟩

theorem ready42_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD42 ready42_cuts0 111 137) ready42_0_state = 61062 := by decide +kernel
#print axioms ready42_0_cursor

theorem ready42_0_covered : Covered (toCl ready42_0_state) :=
  ready_cover_cursor WD42 ready42_cuts0 ready42_cuts0_ok 111 137 61062 ready42_0_state ready42_0_cursor (by decide)
#print axioms ready42_0_covered

noncomputable def ready42_cuts1 : List (ℕ × St × ℕ) := (137, ready42_0_state, 61062) :: ready42_cuts0

theorem ready42_cuts1_ok : CutsOk ready42_cuts1 := cutsOk_cons ready42_0_covered ready42_cuts0_ok
#print axioms ready42_cuts1_ok

noncomputable def ready42_1_state : St := ⟨26112, 285696, 51168, 220224, 52016, 141022, 29666, 44151, 53248, 142254, 29184, 45301, 28545, 166816, 26112, 273919, 77280, 505920, 129296, 646942, 158962, 676608, 240596, 729856, 285897, 759040, 314442, 869040, 340554, 1061504, 103184, 361246, 132850, 390912, 214484, 444160, 259785, 473344, 288330, 583344, 314442, 775808, 81682, 170688, 163316, 223936, 208617, 253120, 237162, 419936, 263274, 555584, 82914, 171920, 112098, 201104, 140643, 367920, 166755, 429047, 82432, 171438, 110977, 338254, 137089, 384896, 57729, 212117, 83841, 331648, 54657, 302464, 0⟩

theorem ready42_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD42 ready42_cuts1 113 70560) ready42_1_state = 114510 := by decide +kernel
#print axioms ready42_1_cursor

theorem ready42_1_covered : Covered (toCl ready42_1_state) :=
  ready_cover_cursor WD42 ready42_cuts1 ready42_cuts1_ok 113 70560 114510 ready42_1_state ready42_1_cursor (by decide)
#print axioms ready42_1_covered

noncomputable def ready42_cuts2 : List (ℕ × St × ℕ) := (70560, ready42_1_state, 114510) :: ready42_cuts1

theorem ready42_cuts2_ok : CutsOk ready42_cuts2 := cutsOk_cons ready42_1_covered ready42_cuts1_ok
#print axioms ready42_cuts2_ok

theorem ready42_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD42 ready42_cuts2 128 1) (ofCl (RC 0 2 1 0 1 0 0 0) 0) = 127202 := by decide +kernel
#print axioms ready42_parent_cursor

theorem rc42 : Covered (RC 0 2 1 0 1 0 0 0) :=
  rcOfC WD42 ready42_cuts2 ready42_cuts2_ok 127202 ready42_parent_cursor (by decide)
#print axioms rc42
noncomputable def WL43_0 : ℕ := zfNat64 33248 "CATYcIw1LDJSsm1C4ACDgkBoCOZhzCgG7FwQXdJxlANwnA4Ll4BBDKFjMJKSRiE4NHYAEHBIPwCQXAmu1JKSgAADQXAAIAyDLJQti8AnZyAAABKkDXLgWlLSMAD0eAANlQACAMgkoAB0WgLAQgbADikAZLgTB4Mq50oAAFslxFAOHGRYZKF0k_8LgC8AIwAAGqkBMkhBBoMJ8FIAADeF3+EYAp4ZFhkp_laL_FwHQAADuXIYERabRpQGQPI8ANtLiKBNfEGQSULpJGIBfqkwVGbJkDczHgBo+ARHgRrUAAAbwuSoXB1BiBkWGSlZPeJwzg4qgAAJMuAFiwahMGlKaJLCcy9IgnprEuA0hkGJYZKF0GaXIiDiqNQALwGcXAOZYmiq6REWmvqUBkDOPADvy4wgHVDIJKF0kjUNpdDSYEAA_MALqgAo0D+TMzNKAyAAhwuMIA8oyLDJQukKC4_AbAARkx+AIBsPiCx4Mq40oDIACHC4DqDyjIJKF0T4mSzECwNAGqHQAky4BlToiSwMjmnxEA9PdlwGEMifCxmElC6SdKGxiBYG_9JgMenQXjYCCLo8bt4qBxGZUyM2ukgZDTj36jICZZcZQJqPSwyULpJaYXe8OgACzGwAD3AC1IBsjAAS4CxNABoLkGIXQ8DSZgAAEoFwASiMiwyULpzBCAOgAAWy4mkKQxEWkmidLAyEjHgmJDMuMIE1GJYZKF0kviNmYS0B1JEDIB8RgbZcAGmgPMEwhN5qValAAAaAuABbRkRSSn+FoKuBABAZYzJ0BIaQWKqG4aK0RAUQAAVsTABBYqAAFoAAUhIALKkE4sOMmAABARABOioALeqQSUKI1AAAdiQAAVIHEXSuyazPjxUZk10kD_hlNQK3lx1AFIHDcknmSldpPplocgANsaAAVVrEdATlozsnSgMgAKXLhqATAMgkoXY7JQBFiuAAEISABNMw+OrREU9tL5E6WBkAmJx0uABHoksah5koXSS4o8d1UAAmGQAkEJSbh4I4IwAAG6KoyAVENhCACyFIAAKQkAYIv6RSCrNNeSUlE5C6BIaWF0ZAEVGwpJLESSoxOAAA1iQElJmHwcTZztnhkJyAZdIFmXAnpIJg4AagDEPIJ5CkgXAAIYGAcgAHQA6gAgFlOxYIqbDJeW2svOLlZfTSOdklwACyBgwyUA3mVDWMgQW0BA8AQBUXC3CwFWLGYbRIJQvDyaRze8uAAWQMElAOFlRN_qjAAAgomqAYCBoJBxoqA0ATAC2iIAIqAB_wqAABmLAACQhRClbCwQALGYDrSheH3_TUdULgMIRcCgkoFE4gAQcHgGb6QAdCAClwBweAYCqgRAAEkAcERAAAAAAASCoAB2kAMQgAJkAgLgGAgALIwAAAQHgAAAAAAJBUANQuATyYgHZKQniC_gUEqNsJAAElACArA5JIHxk4AahcemNHaEaultKaH00_2Qiyli9QwkAASUARy0DkkgKrTJ4MzOJCwUXpAeM4AeVAEhIBgI0gUQOqJQAPQKAAAAAAABnekALQgApcAcHhuCqoEQABJAHBEQAAAAAACgeAc5pAAUYAQXAGR4BgKLREBRAABbw8AAAAAAAoHgAGIQDsuAJCwZhQBOl4A6SkPifgE+VAABJQAAAAbgoKBMB8l4A0icADKKgAAkoByFIAAFJ8AUMWBFgwZhR3DYAAEacYEDhlQD04eTASUAaXQAP2LwBDy4CAPDmFEGKgghkYL4YRgyZTDqYQWgPQQqWFDYSUP3hQCWYgJT5KE8G4WBiQsNgYOFGzklHQADhCAKoBgIZRkEhAzSPACTCIAJCAB9QiAAAlMQMcfBc64AkNHaEwAALBoAAgVAAAAf+ZgAAAIlcASGhVhIO_EwHeiICif8LgLJRO_Ex_pmAHrNwAAV4K3XhS1cABogBgkCAMAAASFgBCw8AEJjoAAsgAACAgAD7wxVSF21wAwSBAGAAANEQAAAWQAM5JwAAAgIAAKkFUrgBc8UAUB6AyBSf+LgBnBUAGjj4AD+TMAAKAOAIKpAAq4FvPRsHMFTgD9xUBEJgBo2wyAAghXQBHNmsAAKIcAXBSA0VwAeeYI2GKmSw80VAp_4aM6cEwA0AhoEEMtdDCDQbNYAAUQ4AmakBIsgQk8TmmSwAUjEIhMANGXGVyjimAEEMtdDCGUAAKIcAZ1SAEVwBye1I2TmmSwAUjEIhMANGXGQBBA+AAaPIYZa6GENoAAUQ4M6mPjTk_AAO8GZrg95ENwVaQaD8h07AQ2YNwABxUAABhDSAC0hoAAeNcGwUAPT+i8BiNHYaQWMVABG4OAA2I1ALQGgADQ8wAtCAF1wQImG4K7WfBWQAuIwAaLmVAAAISCkh1ABaA0AAAoOCIKc+hARQDvkisAc5cwCiULwK7FREQLmsX6TeZqDaARLIWUABCEGopg+dEAwEAGI2AGoAt4eAAAAJoAAfD4AcCEFYhA6Y8hhZBiF0mg6Shfg4eAyClBBQvDKWSLyBqDSEkkgQWRgAd1wGaaTYNnwcGPgPdGQXQZuVABVoqAA4k3AAbCRgCTISnkisHyBHCqnJAf_ySiyQDLGc9LpNGqOSheAZEopFoZSyRVkNGcNISSSTQYMiSw7nYUBJxQ3BRxEIIzIQDDhoNIZgLgAwEJAVURgNoABVJUXowBahCF6YQgoDC8ABZEyAFWEwAZBCgAK6AAFYWCONoQA6hACY4NgosQsB0WhZbUrBROH4aTCUTdli8Acn9A4Mv_2avYSCTObOYUQcgAFZ0iANcCINAYSD0BMB_wmAGiDQAAABFAAAgLAEz0g91cCAMJQAP1JQA3giAD+QcABixaAAAmLAAH0gulcCAMeQeD_ysAABwCIAMTBwAEvloAACYsArc+EDVwIAyfixWCPlYA6ikf7agGGVAAAAFkKoxAAiKJwAT5wWGuBAGOMLB8BOA_8nAEYioKiAAB_5mAAI0TAASRgB6EANEgAoEAAAAAAAAAAAADYhBpDwNMUK4BRC67RaFQHD8Kif6MhSGUsmHEoNvthonJJDlRMADdCCPhQviTVB4CiADpSnhdCxh8FR_0dFui4AHIgRqB7ORaAxAHuhVsZAFcUK4Af0ymF3_ysKwOH4VEGI_ixWRsWiiSQLoUZzTTaChKF4ATVYHyhBoBXFCuFEppx+YuTyrfJKcocPwqI9FoHCRWGSyUSSSSCWQozmmmWbNYG0oXgAC1hKSHop0BE9SAnipHEsgmY6kp_paAnoAVkmlW6Z0BOsqLsplQBChAEhIAAAAAAAAAAAQY7DwpeExcKNi9yOgCq+CcVwAISAIAQQgwxBLxMAMQAmQ8ACXiYAB6y0AAFfTgQ6SCEGFQGEwL0TIwG5jiMLIItKF4ffptwLaJkYAAhAACIBesIHwYIkxD2QJwJCGEojCSheYEbMpUxiCkgTmBNIBFAADmJAASGgsAwmCByBOOiUiCIQs00baWLw+nGmg1SBOAAWsmAAAAJjQiwcCjSBOAIQsk05kXCBONCE4HGQJwACQEwAAABMaCyDg_8TATCIgA_ZUIHNjkH_iYAAKJEAAA7OgjAcCjyBOAIQsk03EXCBOM4k4EeQJwAeQsFhVIAACkeEASGgA1AHIBAAeAAagAA4IgAAAQeEAFMh0RoP_EwFYyIATSVH9oIDLpMKQKiH_Fa1RMAANhDwMLIE4AhCyHMi4ac+gziBqyBOroqABNJMD0SgU6IgbKvFDYSxw+CYyBOFEgghHEYWSaB3KF4fbaTRWpAnJMlAqklwJIrsSpAABTGkIMjzGD4C0DFISARxGFkCJlC8PttB6JAnJaAOmJkbAmjOUZiA_omRgABMgAJcABEhR0cBILAAVQIgBbhEAFziYAASgAWkHgXnQQFhAEhoHELA05ITQrEXAC0AMoPABWIuAAAAAABgcegJAOQohBxxGFkmnJi4Dk+gziTQapAnAAPSFxtEP6GYI7DwABw41oSAlR47M_KQIQsk0y0XAKoD+cQEoAwjoDL7wuNohAABAATMA2FiThIDtkCcGI9QwbhFJoQEoXh9OIwHj+SRyAASom94XG36JFbZyBLgAFuF6YQBEaD+iwfuSEkBiBfgqAErDwADEAAFQ8AAAyNhSPCAJDQAagDkAgAPAANQAAWDwAAAOg1L0TJwui1XCMEyMLNND_lC8PpxpozEgThxMICkq2ONncOns0gUfFgD54Qg4iAJDRng0FYj4AegACCIAAAAAAADACuEBIohURoP+GwC0gIASOVCBtoSLLgELFRSWONgAAAOYQBEqAMGD4MfIE4RXtGwpCiQQWiBNJNHIFiheBRmoFkDYAACmkw8AxNiKQTYoXhZJpyQuEDbf+JwNUgTh0ts5Ayw8AARoWACBhPkDwDEAWhZDmRcIEA1ZAnC275OgPtjjYAAACiMx0PB_oyA7MXBZDVBcIH+TcBGyBOLS2gLmRrIGwAAZhCZgYPgg4wXgWSzFiuslkmjvShecT7bSaI8JkYoEqa22cguUgThtAEHGDcAHA1QxMjBuMHwSIWMwEolC+slkBglC84n22gt0gTkEts5hKLAlLoACkAbMpHTB4BiFECwULwsk0zIXCBCaALIE4UtbgIZEyBOQxAAR4BeGgA8s8kPANYsZgC0LIcyLukuyBtoCE4NWQJwAApkQ5OppAAzJaMFN0QAGeAJDQCQsAZSIAMo8ALaIgAXcaPwAByAABDQxs2AOpvvyKCw0EySIAQgCzCoAJkkQABgaKAOIHgBdIyfhUDCyBOWOUgQhZDPRcIEAdZAnIIAESUK9A4I4kkAYgAG4gZYUS1JGgHOULwBSAHpKjb3CCA9kTAACOVjTRRaAAVzwgAIkdwJALQCyANSGgAFoAAQjoAABwkBBkCfbo0AeiZGEWYgFOH9RqJBGruyheSps1nU0hKSaRSyA5BSpmmii0unEDuOIwJlbODAAOEAkHAGciADOPAASioAAzkQAATiJRy0AAAhDhBUr4DCIQgLQNvEwAq4WAAWgAAAAEhYHKTpeFR4B5EyMB_Y4jCyCnShfcT7bQSkTI1ONQAAUVqZxLoBDsiA0AExpcUr3AsDCyBOAIQshzIuKp9m83AasgTnxzIegBxABEqcAIGAx8eAuFZG8aBe5AnCaC1HEZdJId2LgakB_CaIqNmZJFIAR8sZmUii0A4Q4jAXBpBQPdiGg_8bAImJG4AzQiAAAADEPAAA2HgCUBXmkUPhoB6lC8AUgA9SqxTUAIHUgAApkRpJItKaAAKsIHlZmQZL4FgEoHJSIAW6TAByBOAAHJdAAAXBrHMkwf+MgL7FQAzQiAAVicAAHomAABQfAHiwgoOtIDwAA9AEWEQAfGTgAA9EwAAKD4C7QI7tBo2RQm2EkzWQ3Es0UWgXKzSeTFNWc2ycPRCppJFIHAWqSKTKRRaHEwkKTpZFh8DKwt2OzoeOwcCYgh6uAJCQpAzng4JfDwDHBYASwRABL4eAAEIAAE4KNkhSBgThQckHgLXDQAt4iADkg8AAHQALSCRM04XMmJSGjJPFwtmOwICZjseHk8TEhsa"
noncomputable def WL43_1 : ℕ := zfNat64 33247 "BxHSjwAZS8HA4AARgrAwccPwIo5RSULyqz0iqcQhiFWghZNejB8PSMQcTK_0eADSXA6FACkCaAeI6lMii4qoD9DIALoyUaAP_OQV8eIu1nTGblQDWfAIS4EwYAAOgkJgABxUH_FI1oLAAAAAEISD0rvQUAVpQCEuBMGAUkZAAH_lYCkgpIyAAAAA3BwAFC4AVJAmDAG1HgP_JQFbWKRxcBdA2o8AATQiPzGw1AKIAKU4EwYAAXElFSg7AhpC4BaVTIqcG2CIABCxkAAAQQgTBgKzmQAGEqOBx42xf+LgmlECwjwAQeHgAATI0AJgwqixmExCuhRQI444uNpdb0XLw21GkjkjyGAC0agSePgBeDRY24jQUgQVGPAR8RJYFh2UXH_mougqMeAQgGXIgv4TAAI0FIEHVjwAEEqOBYRaFdB1Y8AlA4ORHLj6agGNHgZEaCgDqjwBJAo2xSQLgLoXQIjDBEAA0IeAADQAcXAExoADQeAA0XAABgoAAaDwAAAAAAGMgB5cAL6OIwF3IksCw9lLgLoF9HEcxKSAkciAAg0NA6Bdr4ADdAiFBCEgGoDDDYAKIPAAvouAACYXAABCHgABVwBIaAPfPgCSBKlikgXBhpoH_Hg_efAF7PgAAACCEbo0AtpCfgL0SI4EmwsCLl4YaaBwxxGE9AuuhBwMkTgd+TgdCwBwhBWHS0HnlQBJAEwzY7NlwYaKAhCCgA7QikqKJFY5AIEANkQVhyMCRWA_SxmAFhIjkpJJhU2WLw0l0K3HwD0_krAAXgBGAACBLgrDgAsjwD4kiOBUMK1yheWEKplxokTwHpRMoHsGAigEAFCYgAYuAUVQAMWDnSQTBwFgjoC458AKwJgA_cPAAeOHgAB6AB6SCsOATWiRwGQJEcCaYVHFy8C6BxxxGFJAYmRFWg4Gl0AAQBGHBWHRSOgiqjRI4BkkSWBNMOkS4ABcEQS0AA_4vAlwuABCXAkJIJUHBWHAIEBZSUAC9Kg_4vATkeAogAD0BCBcDI3MgKquBriwjqOBAKAAGPFwAbYeABsxEAALQACSAXa+AA3QIhQQhIBqAww2ACiDwAL6LgAAmFwAAEhIAGlcDYcBJfYfAEkAQ6VBTQ1IRB_tKTkzA_8+LIND0MoAAL0IKw4BbyE_AIoEkUS5jEOULww00G5jiMKSXQeaeQwChx6SpGADoGwsAhFwAWOCYO_4VAGAIHgFmSI5KQwjVLF4aSqVThB8BFAAoptBRQ8AH8uCYOA0CRAEWSI5KTYjELQ02UAunD8ABnwMBxNoOQHiZMZsXqaclBBukBdvgAJcAgHgTBhyGxioDi58AH8HgAKIAAAABAOAC7fCgR4TBJAmDBQDg9EVAf7PgBiBEABRAAAANhjQABGYEwYC6rgiAPIkRz+Y0GFFJYvAu001wTAAbCVgLIAfhYALZ0AKLgTBmCDwOdTJ4C7kSWEEqmHAhcAlwIAAMSqBBACsLADeQgEJcCYMAtPMhA1CSEE3UxeQLgIJN_0hOqLgAAAAGwsVqGFM8IBCXAmDB0BaB0ouAIADwAC0AAAAAgHAAtLgGMkPIHB3YmCXyMRQchhFoYTaHNTYABqSoWJwFCEAABqlwJgwCgiBOAkOckRyOkUwotKF4YbKURcMmOkgA9Gr6hQ+fqAgBMRkAcLeBHEQJgyHRg+BpDR2AQQACZUf6YgAADnw8AAFIuD8bDbEfMbmBtS8DAHTMACrgeFMDIMBJWoRACUAEmULwIhZCCkiswJga6JvRJYAAMwoAIBIAY0LC0LwsIQHClyYhoAJySKwAunOU4ACDgkARFKBi1xQB0RBIKGkwAASQAKGkwGkD_yUAAG4SAEXJGaHAB4oWAQjwQmFEY68uAqh_w2AC6A6TpYAEREvU4SIwfqplDEnSwFqBxxGAahLgIgNoKk4cTSF2muyTpYAEHCIQJTnniBMGlIxNkWHIApKJlwEQGfkisMrwGbGF2mk0ACDhEBYCZrhCFkvCwAE9AFWlQAVnJgNIGvEoAAIQ8AMquEIWSENBWhSA7efACpioAAAHISQAAhDwi2lCmDg_GrAEEIDHwLQIhKxGKMrUyqGkLIfdIngABPHgADWQAGuALRVgJNIwA9ouADWKt8KCDSf+XjoycAAE8eA8N8eBIGEwKItVwCCA9HQxC0CIVQQI7VVCuWTaZSBy5bCaYQABNMeMQGEwKoScQkGIT8ALOWLz8wkCNEaomEAAy0Um6l0AbaPE6UwsWBd0oDVXCELL0HgoIAhAE_Gx_ISAkMTAaQDuJE8AAIQ8ACFCEIWAHIAhD7Q8EwOgABARAAB4QgAAhDwFhICRrhCFjaDQZoSgH0IwAi4qAAAByKSSAAEIeAQhYxo0DikoDZCUEEHuFwA9HXKwABek4AAAtMaARSZLAopQRmzENUoXgRJ6K3UK4BgRaCahw2LpdAYelBvA1JcaAJrRJCYR5DIoQRezBfU2ULwIg9RUhFEALIypMlmkqgCEUieDsDC2seA2oeAEhoIwiBNKEAtUiACFlQAIDJgsoD4k4AAAAFXAS5MGg5AhEEJUCOBokiCmnWC4CIFYSRWFlC6VWSJ4AH_zIOcCrIEwKBQI4FgSIKaS0CIDoipOamcrKF0cmkTwAA5iwBKWiZnloEcCw5EFNARFy8CIDnCpOG2yhdFvJE8AAOYsAL9GZRpE1h_2zBdQI4CeSIKaUNLiCgFrJFY9OJlC6F4VqYAAcxYjwJnXAmHfmHgXgbAGkALsRAA5oiAAf0fAABuFgb5QnqlIEdVLqPEKGQZiU0klNl4hHLKF5pCIBkCpONTSZaCWaamROlgABzFgAG2RohAnDCiZGhg5BQKU8KaQTWlC8yhEBrRUnEJtsv50Iuk1cCZLXgLAAAAERjRCBOGFxqBHByPBTKYU0ghfKF5lCICgSRX1giNp72YLoAlImgADdHgFVowgiaIIuACMhABdTgAFBUAAPCYAAo_6fgA9oZA7O1J3J8IQFqgQwGqKU8A+kXGnBBdSQ_cXf+UiygW0TjEDwAAAEBIyjY2pEAaT4ASicABIKgAEsXAABLRgqG0ADGzyGEscRgQs8hgU2gghBCIaULy6UkBaUQAWCkTySAoSpYDzxYGR2zibMPAR0ALZwARCBkGCIB2QQLw0GJEEhCXlQADXJgAB7pQAAMQ4DTfDAmhsDUrgZBnYCQBOIFYAlAAYlwEQJIYEwgAaTJYAAcxIARakBcrgZBgAikQCQgREGUACIGvlIwIBTQAAmhwAB1YYkSBtJUAv0mjv_F4C1lQAIeRgAB7pQAATQ4HyJkwiQCkUahAZipOF0ugMyheRUCigbTaacabTgAAmhwACEYfUSCUgbPJgjXf4L1830XXWKgRvRg1g3AOgTgAAmhwP+eQ4NiQDZJFZJnoJaCVYsLUxFowF63HQakkglGwmkJoOhSngABNDizu7s5A8W8AsNgAIkDINggmCMhsAOQABBEAAAAGA+AAAMBABq3gJaEAKNgZBgtjx_lqAKeIQA1F0ZASQEIAETFIACDgkBoA83gZBoAjxYfVowAAEsNgGRDhsEIABx04AAFIcIZXV34CawgCQ0J2JAkUqA_sNABjCoAEilQAAOCIAAALLhAEholgSDLhcBRcqAEkkwABEAAHZEAAAGOwgAJUASGl7ioP_EwFnSoARATABwQuAABUNAAAAAkYBIfACRoBfJAEYIZiQHB8YiAa4ZABCy4ACsGQYZiBUlOAqAAABG4AIfAGJIARBJGBwAALC4AAmVAAWUFgAAKgUAIEACtwBa+AHFwA0aIkDg_kVANyLgBjRcB1C2xkAAAlAoAF8aAp8IAkNBrBwEEBT5UAGoKgAZsXAAA4IgAAABxe_B8ADs6ACGVAAKioBA8AA5LgAACEwT4CAAYKPipiwI7PgL9GQAdsuABUBkABCgyACAFELibAAyMAFLgHhYAAFhcAAoLqyAAYQAFxMBFAIAAAKjADxYAWs+AgIZABBC6sgBqjIAAnRMElAGePAAGRgnBYDOnkMDYRkAIZLqyAMCMgAM0GR_gCkoCOC4m5kPAAJcASGgQRIB5nkMAlBkzADWlwAJWMi8gCES4ho1ApeZACpwgCJUABGgj8s4EfB_46AzCVACaiYAP_FwAH_iYAAegASGgUh4DHnwBOC4AIwXAAdYyDyAADUAq5sAAxCABlwAwqAJDQAAAAAAAAAAACZGD6Ix4DcnkMBV5gzANylwARWZqFcvIDRFquXSGjUD2ZkABIaAESwCyEI6ARsXAB_i4AFiKwH+EYGrLRCQApRcACsaEUWDwWbjIQDbDIAuWXABFGcsVy8gFVny8fzChqAVQyEOPhQONHQAYhAAy4AYVAEhoAAAAAAAAAAAAUrCAJDQcheo6Al6VABzCYAL0FwAAOCIAAAANhAEhoCIaAAAABBMHrHYAAAHBEAAAApPgMx4CrJQETF4D_6MnIuA6hNcSEQABtJgAA8pQEgAwuAbZPgMDlwU0qUXAaaaANLGeJCLyTEAAAAeUoLw2BgbMLmwWJAqOEIQUlQaDKRcBdYqAEikwABEAAP5EAAC4WAAYfAoTYDTXCEFDeGgE8NAEtHgAgB0H_nYtv_hYAA0gACgGgBYHwAiuEIKKGPAAhhILiIAMIXAdQumsRjAlUA0gACgGgrAP18BprhCCjhDwHECzBsAMSKgMID0AA0gACgGgFYXwGmuAwGEcLB_hGANIA3AiADuRkAAaQAAMiQAIUICnJBOFAKAUgEepwAQAqAA_pcAB9pqCOgG0AP2cAgrhCChqDwf6UgNqpwA6MqAwgAVQP7NQAAQkYABiMABQgB5UASEgAAAAAAAAAAAAaUITE+Aqk5ENplMP8lwNkIWhRZr8pKrqchYAD0tGsLpJAcOlABpmlUcx8FRlYAogUoQrvF2NhIIobKYgADSAAyFKAKsjAAa+_zJMScB3UgnIAAEyoCyJoTgADCDUF0AQklACYQ3LUkonwFUA3qZTAWhIQhbOQijWHyVXS6ABpCqlBKAe8nBnZzoaCwMTFl4AEIhCCg4jwHaJgCeEQAiA2ADaGQAYgAAKAaAMFBGeEIoVo0eABaAQPiwCUEqULwOoEMRoYP4LgAAAUQ0AA7aAH4QOBUmCIAAxRMFT+jcJ9LgAe3ESgHoJQSRIrAAFANACt2g4CkAhKhCCv9EwADUCBMAIeQgABAfAAAAAGRIPb0AYFQhBRiR4DqEwBOCIGv_RoVsXAAH4mAUgpCIAAKAaDkhAnGEGwUOQpCRACHHEYAv4qAAugADEKgAAIBQAt1IIXVDcFY0JgAggHxYDoDAKgAvItBJQP+FQAAJQ4DQA+pAAkIB9VCEFAH0NgESGQAJ4mAAwxUElANIAAEAoAEKkBWIhuCgIgHQFODYKqA3NgAFoSUIo3laAABKHAGDnNIBCVBsFCkPnFwHIioAWYPAACAuAAAAAIBQALV4cwo2BMGEAPscNwCSXMoXgE2HCMNSwyUrJtQuAAg4JAaAjmYcwoBuxcEF3ScZQDcJwOC5eAQQyhYzCSkkYhODR2ABBwSD8AkFwJrt"
noncomputable def WL43_2 : ℕ := zfNat64 27680 "DAQAdQYANgMABCJgADqDAAAAABgIAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwECcGAOoMAKQArpcAAdQYAAOocAAAYCAMDABZ8AiLgAAAAAAAAAAAAAAAAAAAAAAAAIhgDcDABIDgACAUAAbgYAAAAAMBAATGgAAAAAAAAAAAADkIAoZACyoAAAAAAAAAAAABgIBEMAbgYAJAcAAQCgADcDAAAAAABMaAAAAAAAAAAAAATRgEQYAgAwAUxIABUTAAEAGAAVIFAABSBgAYCARDAABIDgABkMAAAAAAAGAgAYCARDAABIDgABkMAAAAAAAGAgAQlwAAAAAAAAAAAACYkNYMCcGAMYcAboWABvlwABjDgAGwhQAAAAw+AQlQDAQAAAAAAAAAAAGAgBAGAAAvCwVWJgCZUAB2ioAAQQcAACIGAEAY9QEB2ioAGhMAATKgKrEwAACCDgAARAwAIEICkfAgDAACCSYP7qwRUqAk_3VgAAECHAAAeBgAEbQPW+ENmwDAQBFA7MjAACCYDaLQAACMFAAA1BgAJBQNAwAwCYAWhEAAsJgADojAAAqCgAAACQUDQMeoCAUgCUGYLR3YuA61QWoOM3_0oAA+gkAAAAFDgaBgqAAcAvEisASgUxYrgiyxeB1gAqWzCSQABrEQH4D4AAaBgqAAcAKEisASgAhYrgtA6lXVTELBElgJSagOGQJwAsgCxAuS8rK1deWm5eAEzIbYOAMYcAboWABvlwABjDgAGwhQAAawYBrCgAALwsAAvLgIiACgAAIlCQAAGgYAEI8KQUBkKALYcAGUSAAZEwYgaAAAAAAKQUAA4UAABMSAAHFQ1QaAAAAWCQHxBgAAAw6ALEYOBwYQ4EtkQBrRg2AAzLgAAAWgAAIMKAAadAFiIGgoMI0Bd0YAdxcAARKgAAAWgAAG4KAASRg0HABgRhKRYzAABmXAD0bxVSQAWgA_wQWACcKAuJAG52DgcBZAAAFaXEuEYNp_RGAIfNw7o6ApYMAC0KEHA4gI0f4WoNIQAA90qKkXAB8kiALaeiPgABBhQAElYAShACjYAOTAEhIAAAAAAAAAAAQqGA0FBhDgO0RAAC7DIAA7RsAAqYeAADcFACaOgaCgoBwBaHgADgyEUQqALv+kIAAB0NAfEGAA1K6EBoKAOFAAf5IgEhG11i4l8dBtJv6ToAA9QkB7wYAAC2pA0FAKyIgHIkQAlwuJKWRfCcYQAD0CQHxBgAQcDgqEFuRkvP3KzZkSWHQCKhPKoLQkxUWgmiJNHYAB5BIB5ggsAiByYgAdKANoQBISAYCAAAAAAAAAAAIkBoKFQHAEQJiAa5Gh02LidjMAuUiAAiUJAACDCgBoKAByNFXB4mIGuka9BcABVSIACTQkAAIMKEHA4AKuDwBkwZgEXvZcAClB4AFoAOcEFgAtCiDQcDgAH0aOwQ5w_AK8jQ5aAaRiRw_ADSP8QgKWDAAtCgAHCgAsQ8AZMGYBFwUXZODgAIJcAAS4eA94MAAAcUgDZsASEgGAgBAwAAAAUSgAAAAQDwAAAR06EUOAOFADZB4AJKlgqAOlNQAAD0aAsAEAAyjCDgB5xcCmMmYFBImULwDieZgz0kAAlQ8B8wYAAQhaAgcDcCoAYgb3QhilC8A4ggZMdJAMDNxIQABBhQg4NALSOirg8TEAGyNDJKULwDiG5kx0kANp6siA+IMAAWAJyYQhYA4UARcHiYgJSRoYtANMnmafCdLAPoAED4gwAQYGAHAbWJiuDwrRCfgUEiZQvAOMRGKkgWH_Q8RbIgLABAAACjIMAOACvFwrRCf9xNgoJNSheAcczMVJJoWEOjdSICwAQAPtDwlRAuPXNj+y8DFx55DmoUErJQvIoW1FDESTiBdDoQskVhlIKABMweAariLisZxDKoWkB+BFIKEyheRQNphPIiS_LNwF0OgpBGgUB0A9qbsANqQbmiAJCQOiQBwoAAChUAHSIgAtyhAAUEAACEjj62rs6uhizWtgQCfpAEhIGgoiA0BWToAIyFUGxDQAAAKwSAAAEBHgCuRCEACnD8zhIrjMFKN7y47gPAAAAvRIDMggsABGhI9w8CRCIBUBw_Iyf8Up0FwB0I2AAD0DQAAGQYADacjQsJw2AA9UfAFF5hcAGRRgAAIwkB7wYAAACrAG0IAKLADRIAAAAAAAAAAAAA5iBSoRRCEB5pSBCH3qj4jIlKPsi4NIE0AACcLAe8GAANABrEmAVApwsVlEkg5ByGVNKQtDCCxErVxcAAE4WA94MAFiBgQJ8FDwPELFdanIByNYyIYgKQtJIAQYkXgABOFgPiDABggRBwUBoBBFQD6DoDRikABVAAAjCQHxBgABTcBTaQBISCISHULB_xOAO4ZAA0CIAAuDwAArBIAAAAOnADEYAeXAEhIAAAAAAAAAAAAMlCAJCQTiSekoIRKwABMhaMKTA1AggAAJg4AAA0LKytBBOOcDQUA4OCcgEAMG4A2YuVjVhoAAAFQJAfEGAA3NbkPHwAapAEhIIgYBIsAAA8WDiACCYCIBG2IAAHgUAAAEKNgmBm8jQC0_0pHbCoFJRADlwLRSBRTBWAAEYKA+IMAAASYi1RoHLkwC9SIFIIDKiigJ1TgAAuiQHxBgAAEJcEQUpcaB0pMAv8iBSB3So_SjAIRTgAAAAUAUBaY0GKyYB1pAnBSSTWxdVEmoopCaikAAJMSA+YMADF59JcaDsJMAvQmRgpZYlAtLtFFIJ3TKYAAkxID4gwAAC7WLJGgw6TAOdIE4Kf+JRqYuNJBFIHMRgAA5CQHxBgAANCsWqNBFkmAM2QJwUhYguGtFFIkpqroAAkxID4gwAGYXKJH1iNUUK6QJ66PRqM4mRmUSkUWyULybRRSKzZNdNAAEmJAZkEFgAd3ZnT4JWcgfLSAJCQTA2xBoPfGwH_DIAVATAAHQaAACgFAAAcgrW+AJAQpAwDgYIzEwAxAHJpCIAIzEwAAAAFeYgCSSBoGIoHAJQGkDwAN8qAAuo8AAxYiAAGEJAHBIg0EkCYMCcKD0R0ANQADBMAANB4AAAAwkRAA6kgTBoDBwJvHEYHMR4A8uXAXQolfOH4AADEyWAARASCEA3SQJgxFA4FkjwGBh4AFwVAH_i4SgAKDHgADlCQAFFoEwYPIcAfGo7UfTkAgjCS4AFWEQATTKhMFJC6VYQiwAQFAA5HgAyjQADEqAAliluIaAAMIHwAAApkgTBgAAEg0H+D4CQh0ANB7VCkAApAmAmgDyEgAEhQJgwEXS4CBJUH4mrOMqLiQx0AHJaAADmTABJAAAO0B5kghwUCYMARQGunkMAAmVEhjoAATjEAO4uDAx0AmQAOlAIUIAYfAmDAAAAAAAAARiIAAAwEAFgwCpDJeFVdCiRwsphU+WLwqAw8hgKSiUkHZLVc2GZAVa6cbSQkYPlrKm4AhLgTUkNwUAyIiATmPAA2iYAMVFQABFAALkPAAOLgHEkAlyTAO3IgqJFwuKTzhWCWgAEVgogQQHhoAAJgxABYGfGQATEMp1yoqpBDJxUAAQQSAADgVAAvFgTBiFDRsGNFysqOCFKmlNIpBX0XLyqkElLlC5eAAANQkiDC4ABxcB4CgTBsNDQclMgOdKR_ZWBTxcVUBjxUAAAZJIVQBsBUlwJgwCByIDoP1MpkpCCZUsXlVoIGJKF4H+E4ogXR4Aw3EWGVErEjZOADD4ACbAIS4AAAAAAAAAAAQpiTgA8uAJBQAB4ScCQaAHvlwBQYxmVViIAABCGUCEJAATMgBRcASCgABEFCeCQaAgkxS4AoL1zBuerJgAAQhlAhCQAGxYKw5IhkAH_E4Eg0ARcLjei8FBxSZAADJIgiiEMoAAhLgJkkFYcAASQSDQAPgqAA2pcAAkwuAQgMWdgAhSQVhwADrE6WADJC4AoMYTIBPRcNQLnHwJALsbACmCgrDsLHwAEkEg0AMoLgCgxnMgAUgFHgL4pARIhAA4FgrDioEQAAMagSDQYGRgThUAALy4AFIA9AEWIQGkICAIZYKw4mZEAH7lYEo0A1BNHQABSMgC6gsABQAlBkAVhxMhoFLHwEhCIASEXAAyw6AAsIBRCAbI2ABCXBWHAAuOgAtCwAP4mAP+AwAAAAArLgBXFwEYKCsOIKNBBJAeQwq+oWhKBFGWlwA8FIj2UADpVzoxAFEIaQqALBgDguAEEwVhwJhoAC7JQAAxKgACkZAAB9oGABYGREgGIiCsOPeNAB9FKC8bAC7C4AoMYzIAPWBwAUQgGyNgA9lwMkKCsOACU6fSgvEwAWIuAKDGEyD8ycFksgCEClZUEJHQjc3Uh4BmFgTBgAHQJQJBoAiQXBRClykPQACWFwYaVg6gAJgwE70COAMQXkjGMC4kMdAHVCmIE0MIbAuVhZQ8gIhg+AFgwAgEYKSAHJAfiTSxeFSFHkMCClksZhRJoYaif4uVhYQ82kcY4fAsArlwBIaAAFQTgSDQAOUqKqAi4yAKiLwAAAAZS4HQoCVxcBoQ+ANWFxVSCHCQhiFUC6bpGgMIcR0o8AGUvBwOAAEYKwMHHD8CKOUUlC8qs9IqnEIYhVoIWTXowfD0jEHEyv9HgA0lwOhQApAmgHiOpTIo"
noncomputable def WL43s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL43_1) (dpk j 2 WL43_2)
noncomputable def WL43s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL43_0) (WL43s1_3 j)
noncomputable def WL43 (j : ℕ) : ℕ := (WL43s0_3 j)
noncomputable def WD43 : ℕ → ℕ := rdw WL43
noncomputable def ready43_cuts0 : List (ℕ × St × ℕ) := []

theorem ready43_cuts0_ok : CutsOk ready43_cuts0 := cutsOk_nil

noncomputable def ready43_0_state : St := ⟨26112, 146782, 51168, 101999, 52016, 153677, 29666, 44151, 53248, 138496, 52016, 112351, 28545, 96880, 26112, 211766, 77280, 197950, 129296, 249966, 158962, 279632, 212210, 332880, 318464, 384896, 361024, 481776, 387136, 693460, 103184, 204845, 132850, 234511, 186098, 287759, 238114, 339775, 334912, 368320, 361024, 546678, 81682, 183343, 134930, 236591, 186946, 288607, 266321, 317152, 292433, 495510, 82914, 182647, 134930, 236591, 163475, 265136, 189587, 443494, 105264, 206925, 133809, 235470, 159921, 413828, 80561, 182222, 106673, 360580, 54657, 308564, 0⟩

theorem ready43_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD43 ready43_cuts0 101 22252) ready43_0_state = 55718 := by decide +kernel
#print axioms ready43_0_cursor

theorem ready43_0_covered : Covered (toCl ready43_0_state) :=
  ready_cover_cursor WD43 ready43_cuts0 ready43_cuts0_ok 101 22252 55718 ready43_0_state ready43_0_cursor (by decide)
#print axioms ready43_0_covered

noncomputable def ready43_cuts1 : List (ℕ × St × ℕ) := (22252, ready43_0_state, 55718) :: ready43_cuts0

theorem ready43_cuts1_ok : CutsOk ready43_cuts1 := cutsOk_cons ready43_0_covered ready43_cuts0_ok
#print axioms ready43_cuts1_ok

noncomputable def ready43_1_state : St := ⟨26112, 146782, 51168, 171838, 52016, 172686, 29666, 44151, 53248, 138496, 52016, 112351, 28545, 96880, 26112, 280019, 77280, 197950, 129296, 249966, 158962, 279632, 212210, 332880, 264226, 384896, 292771, 481776, 318883, 693460, 103184, 223854, 132850, 253520, 186098, 306768, 238114, 358784, 266659, 455664, 292771, 546678, 81682, 202352, 134930, 255600, 186946, 307616, 215491, 342444, 241603, 495510, 82914, 182647, 134930, 255600, 163475, 290428, 189587, 443494, 105264, 225934, 133809, 260762, 159921, 413828, 80561, 207514, 106673, 360580, 54657, 308564, 0⟩

theorem ready43_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD43 ready43_cuts1 106 177) ready43_1_state = 75061 := by decide +kernel
#print axioms ready43_1_cursor

theorem ready43_1_covered : Covered (toCl ready43_1_state) :=
  ready_cover_cursor WD43 ready43_cuts1 ready43_cuts1_ok 106 177 75061 ready43_1_state ready43_1_cursor (by decide)
#print axioms ready43_1_covered

noncomputable def ready43_cuts2 : List (ℕ × St × ℕ) := (177, ready43_1_state, 75061) :: ready43_cuts1

theorem ready43_cuts2_ok : CutsOk ready43_cuts2 := cutsOk_cons ready43_1_covered ready43_cuts1_ok
#print axioms ready43_cuts2_ok

theorem ready43_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD43 ready43_cuts2 128 1) (ofCl (RC 0 2 1 0 1 1 0 0) 0) = 93296 := by decide +kernel
#print axioms ready43_parent_cursor

theorem rc43 : Covered (RC 0 2 1 0 1 1 0 0) :=
  rcOfC WD43 ready43_cuts2 ready43_cuts2_ok 93296 ready43_parent_cursor (by decide)
#print axioms rc43
noncomputable def WL44_0 : ℕ := zfNat64 33240 "9GgekZAAAAGwYCgDqoowSktNiDLfpUFtLZnwAEgGgAjwPAAACa6MEpLTeoy36VBbSqJ9UAaAAAHQDwJB4AAUAcAAZWbtRgZyUKy05oMpSUG2m+T4wBsAAAR4HgAAUAcABJWH2So4M1KFZaa0GUpKCbQCCE_AkgvNCAAT4lAACgDgzACQ03ajAzcoVlpzQZSk_6hW03yfAASAaABBg8AAAD+JUcGclCstKuyxnKSgm0XIhPwAHGTAAEsKnIHQAAJ2LUUGclCsRCya3CGS+UjEUI2k9AAYpIrAAYmTGkANXDQOgDG6C4SjwgRwUQVKwo1IMpSZHQraT0AC6AEeB4AAFAHAADwsXFhCJUcLL4CpWGlaBkvlJQTanxWpz0kpdADKMQcxdIQAAd4cAARWCaRIYO+KlYaZarQqVmkgmkbYcPySm2uh5jBeA1AoqnAACgEgYwoXlDPIYKLKFdVMsta2UKzKRTSJ4PHZJTbXQ4RgvLCNQLFpwAAoA4uy+xLZ07MwEAVTwpBVU0YJSWmAhlv0qAwnNz4CSEIEYAA0gAAaBgAQzwxhSGkqOVkUBUrLS7csZykFphKpzEJ+AABlA88pAAAdBgDnz8Ab6QBsqE0KAToXKw4jF9hcrIjbRByZLLZCQAAAxAAARAwD7CBOD0UhVVEcN5SUk2qUVmEIT8sgUA8AuAAClnwAALgoARBnYEiM_8fCkKpmDhvKSkm1SSswhCfgELC4AAGIPAAOcJgPQJEYPRSFU9Rw3dOUK7VD1JNv+FaeklCqxcAADEHgAIOCwFWEyMHoFSRWFkauYKlZSTbsZWnp+8mB0BcAABdHkOBQAAAB5pZfMSIweil9B0VUVHDdshUrKSbdjK09AE8FwAAFYePuIwAAASYgXcszURBYIqCqYBKgIE3H_z4AAAD9xcWUqgDUED4HqUCRHMpCHpayRWFUaiDKFZQRoN2sqz0AizUCaAh42FUWMzjbMVQA6Ao2ACkYwhqRBEACyhWRSr4g6csVKykm0Y+eQxiAAAArCJPx0AAPrERWCRGD0mJIrJJVGoiShWUlKTdrKs972hAAEMF4AAlXQRKSOgAAzAg81zo0uceCARUA7AqAL_HQAAAAlNoATlFhPEeE0RIwFJJLKcDp0RUrKCaQ0Rw_ACgu8VgACKSKzaAByxYACakEwQgpGgDikxwBeDYkwfscgAAAgACuJgAAciwCgo6gzqCA2MCfnI6ggCFCAt1Q3AwAXiYALxMAC_NgPIVEI6AvhqAACEDAASMg3joG9FSsBj7kqD_bRvB6EpDEI8EG04A6p8AAFEGAAkNAoGwRPKgHllQG0nodRKgjEPAAB2PgAAAdCjzHQShKFYE3LGcpA0iWjh+ElCOhTaJqQTBPgADmAwAEhogQZyUKwJyWM5SBpEtHD8yYvCUI6BNAXqfAAAECDNyhWCpSxnKRYjcaR3xw_MYTF0SgmUcPgTQAXnkMAADYkIODSBCCpQrBVJYzlJ_1qNI8I4fkSF4Sn7QiOgTQNgIQI_EgAACQkDYkgQZyUKwGMpD7zVrCVHD8YwvCUOYjwE0Bep8AACDg0gQRkVKwU8ZL5Sf5ajSGWPHYB0CjjB8CbUQMKeQwONpDF5MTMyZzoAnXgRBpSQ3_pUHUY6dKgNoPQHwVJwmYPAAEEPgAAOhQhiz6UGZSo_81FmSoDaODPH4CUJODwABBD4ACSCEABJGUlSglIaVtGW_SoDaFJPH4SkJdDwABBD4ACSCEIOCzbE6WC+ipWGmWoWKlZ+tSNI2Y4fgDgkRz0DoE2ogyU8hgASQQgzDznB5tidLBfRUrDTLULFSs_WpGkbMcPwBwSI56B0CbUQZKeQwAIODQA_S4MQktNKFYMBcxjFdxUrFpaaiPQcAXK6DQUBER8PpFlIZKKABBoaAgBOlnrlpxxUrDTLSRFSsW1E0ipjh+SkQ0tPgOhpBImSyiBBAAjIvAAxrgi4U+SlAKQ01LLkjlCsWhtA3IT8BaE9R4QNNnP5y4AggGwTYAQCeJEEKlsBSGEKi_KFdrDIsi8XMYTSUiXaJ8DsJkZhhqJpRAghBA0g0BSZqWRDkisDyya5aKSojhZNYZQ8dtHJpSGSepTGD4aSbUQenmQn5VTjabbUSDkicAESspGlBnkqDSWrKh6AKbtYPQdqTB2MeAA+shEEOoCmSIHZmVpwIjrALUYpMoDdHgBujwAh4yAAAAC8ZAABCFgB1oxSStIngOYqVzU0y1CRUrNJhNIs44flUFNBLeCQU2og1k8hgABCFgPH1LGZNqIFskV1Eyy0EpQrK62c66aQcmUchkez0R4wfpITR1KVMmjezyGBhixmAtACfMQGrGb0VglITQzv0qIoPJqCAMWc2gA5AAeQfBUQC4jQbqWMySVTQGzMYpIrtI90ieLRSZabZSVJw5Mo5DJPV3jB+kgXESXTQHpNKiVSiB_GD5ggBLmFIuAV6VAJDKgtpMU+BiFwmAAAIIfAAEaHjDGbM7wYE_AR0pLwZDfEGDDpGgFIFzLpSBJBOS4YOwA0zEABUxEAAFEGC8lAmGENwMBJRKVAlEqlQabSUwOH5HQFOHzsAATwkAAFEGAJ+pAIS4bgYP7ESfioGIfsqDycTlLQAALy4AAAAAAIqwS5SAQlwP7ESfioGIfsqDycTlLQAALy4AAAADcFAECUgBxcATGgSEIk_FQMQ1RUHn_jkAAAvLgAAAAALCpABy4AkNAEPMyoGMxsKVB5OJzloAaAeQ2PpFQAAAABYVIAMXAAxoAhJAXKwYzE5xcrDycT9LVcggNhoGWNHYxFIAGEYgAAdlSAFTVUlwSEIk_FQMQ1RUHk4gAE3TIAD_hEcQAWUPAEkUgHZcJZkAhJEXKwYzE3BcrDycUzLVcggNhoBVooBRs6FXEQe4RgAMCnqQCEuEsaAQkOLlYMZic4uVh5OJulquQQGw0DJGjsqnEAAnIVUBJg3BudnR2PgQAkxAIS5X0aBnJQrB6eoyXykOJtERHz8joBrhoAAAACiDAASMkdBoJSD1Yxlv0qDjbT558AAnhoCqAAABRBgAFGTb40UOLgClCsHpLDJfKQ4m0QQfPyOgGsGgWgAQ0ABSDAAKLnNxoFopB6EYyXgsLlYcTafpWHsiUb_o8AOgaBaABDQAFIMB8GAe8IKQ6rREF2CoKpgkqD_zcSDPgECaQAAYgsAAFEGAKihAEzIAcXAOFlRJf_GWnyoNttNFowA1qLvAoAAAACiDAB1oQA8uAJDQpw0DsSoko0MqDabTtaMAVEAAAAAAqKEAPLgCQ0A4WVElGKkC5WG22jTEqOANai7wKAAAAAAx6EAHLgYEhjjQLRnFyskoxKMXKw221uqpXooA1qIJnotAAnoABgSJ0dm6krBuDgSGTMJkFSsHpKQ4m0FQeOwuzoLg7ARAG+j4AAAogwABMIAFPDcHFDMGYLQ+kisHstCUXKw4hVagehVEoDUECAeQAAogwMeTDFMGYLW6kisHotAWSKw42UBoeOwqiUgiURxGU2agPU2J0sAAKIMACRiEFMGYLWuFScqj0hBkvFIcbKnxOHIxLopAihMjCTNQOnpQAAUQYLrKF5QSxnXRVpIrOtJUUZCmm22ygvDx3MajJQR2OIw_+bAX9SgAAogxg2YB0LlrzIJmFSsHqBDKUhxNo0g8dhdFoVWIpfDR9AACAAFEGAE0XrsjEmNmYLUYkisHtSDIUhxso3Q8dhdFs0E4EINPoAAQAAogwASzMSy61pkEpB6b9Kg4m0jkcPwu+iLgpARCE+gABAACiDAeAhi+gjpvxkzBa+MkVg9pIZCkonGyk1Dh_Nf_LkcWhtQiD6ATQCAAFEGKmpA4OfMTNBuQbzfAIS4bgYaQ0BryRWKKPgAZQrAEsmDcABiAAAABCBgvP7EEtLw1KuAYCAAYRAhAIjwBtIyADVRcAALQAAhAwAIS4AAAAAAAAAAAAx9eG4GJOeQwmI8AJQkpxBktUUACBlQAAqyoAAKIMBoCmQgCQ0HeTAboqDKISKgAEh8AABV_whA5R2AAABgoQBIaLMKg0UVFp_shelKgtpMU+AACKVSCFjnoAAAGuhPTlRC5OliktII0CHKSim1bSs2c8hgABFKpBmI814_uWFgAACFIR3DVaioJISCxWfybM5BBkWKyi22qgsQH4ABQSqQZiG1ePc5AAdw0To7OgBIWG4G48VAYskVhl_8hAYLFYWUWEcPwmlUGDFScDCAyM+AAAAJMTjxUApDL+xCJEWKwsoGw4fhNKoTpJgACTnwABGgoACQ0SqSKwkqJJFYZRbIT8UlFsoORIaRPKtBA7FScsJhKtJF1IT8AAAKQEySKwywiQhSc1Rm+smsHJTSqBAipOWGwlUHXIT9DhkAAABIadcKgNeSKwykEUgZRhBw_KSVQVkVJzqzEYQH2nwAADoB+MgpAUhImTWqBCdEVKwNJIo4flNKoNHNHYGEBj586ZoxgBaRUgH4XaRSApCRMmtUCE6IqVgaSRRw_KaVQaOaOwMIDHz50zRjAABcyo45IrAUhlLkhOiKlYWUHISapKwAIOm4AAZDh+HU2gIZHEZNjVpE9ipIrA15IrDL9c+FJKbKDkJJRAiB03Hp0mKsgNgPn5lvWdAExBuE4mhIrCSgkkVhlIIpJSZRhBw_KSVbgowow0d_zJijOaKDJEKyl0egAAgAIWKBO0AVAW0kVhl+4hCklJlGcHD8pJVBWho7AwgMdPrKcYqAQAAAjfuGyjihOEk+RUnoJlnpfSRWSkyo8Thz_oupJRBiBo4bhhroDmjh+VEG6pbADoNjIALMiZiRWElZZIrDKURCfik_6VGUHEeOyklUECHDcMJhKoLMQn9tqIA+pSFTUh4CF3tIAkNHODQNJGgGEiwARQAAAAPFQAAXM6FJMCpOEmaZIrDLPRZkisoplGUnDkckUolQDKS1sagANgcPz6VayAAoUNgFy6gA83_ixn9wSKwkoZScIT8UlFMoNo8dlJoIDSKk4YSySQRkhPwADDEQKSFQBALFYZSCQAsVgZQegWQUOULwML6FYJXnwAATxYAsDEQ__KvwDVJJqSKyw2LQIcpKDZQch0mlUCoFysc2EwqwVgWGeQ0vLwAABbWNRiKuRUDNShWWGgykDSDn+g9TWPqwEcLlYAHqT4EjkATaLA6HgNZGJhJFZhJLdipOeTLCxCfimk0U0gFDh+E2egW8kVlhLNFB6SE_Mk3ASR6AJ0fO5LXaKWYqTnUjTNjnqwSRWUaLZVyJw5OtFKKbEIYyWimEwlUkiqEJ+ba8LRRIo5AMwAILGI_CpOYhevi9yRWdTKYc+FNN_ujGUfCcOZaSSiAfipOQfvMVdAnoJACUgsAAsaygeNyXZS0KfJFZxMoKaSdKZgciUggdQukvej4ADpHjsEnksgZNIgbHcGzRQNnNDolA15IrDksGcMSEKQ7AzA5mJFzoBaJQAATHTf_UEAD9Rw+Do7O4I2Yg+_CAYChYPA_wiAaCPAAxAD6hcAAFwaAACEDBjfn5PThtubm4LTjp2AwI6Gx4eTm4a"
noncomputable def WL44_1 : ℕ := zfNat64 33242 "C2xAHE4AElASbIBISAAf0bAEkABydIuAA_0fAAAoHgBkMQBBOAFnwLayAUEgAH0GwH_EoAAggAKEMgAAUDwAMmIZASCHRdKSSgGNgDEJksABxiE_NJxMIHAz4AAjRMAG6yAW1xyqcKAoJMAAf8SgAGoHQAD5DoAAFA8ABliW5GAG6VDkk_TJgC+icAAlc+NIAKdPgAAokQGh4KBg8DAh4AvYxpXgDnF0pJKAouAvYVAAb8IjSABbx4AAM4UB5SBcHAAQJjEC0AYJgAAAYA8AAeYWAAAgDAFIUBSUqMhMVJMKULwB0RMAAxx4AA8wsAABYGAUgrmBUDoipWWkkh0LlZRQ6cTAAMAeAAPMLAAAdBi_vwBEnAEjIAAAAAAAAAAAApBQJgoMbFwFWGZUBtNoAAwB4AA8wsAAB0GD0HBSCgTBQWtKgJM+yoAKAADAHgADzCwAAJwYNwACvAAVoAcpADE4AkNAAAAAAAAAAAAC4OQIC0tLklCu74uVh_o6CSAEMCIAA8wsAABMGAHAzAElYNQAcArFbJgAfCEAAwB4AA8wsAABMGA09BJBiNGM0BcvKLJdQl0OhoJ79pOAAkBEBYIOAAACiFAAhLgjiYCxFwSV5hdDoaCe_cTgAJIRAAAAAQgoDQAEnAD0IAWfAEhoAAAAAAAAAAAABAqUCVgdYWMwclV_ZQvh0NH+josAlAADQeAogAABGgoFVGbNmtIBgvByVUmFytTgwfJqFGSo4AC0DraQki0qwsZgAATBilvQC6vACFYAdGeVBzkmP_DwBqEoABgDwAA0RYAACYMAAhWAIFTwRUC5ipWWki+bKg6RQislAADQeAcgAAAEAYABCsOOSKwkiktJBF0XKw6RcjlQBJGjgCGD4WgdQ7ctMSLGYAAEwYpb8_J8MCUpyKFRnDYExGwf5DgciBErpWIABgDwAB6BYAACwMAB5SALpwbDwhAeR0EUQ0bAAAAwB4AA9AsAABsGA0AoL1mlUpBS5QvDqMUFlC+ghUos2TqKAGySIABEYsAABkGAI5OAFhEACkeABrGQADAHgADzCwAAFAYAuzHSBMBIEqK6MX7lUtoIZpRgAGOPAAHmFgAALAwHgcj3LEoMclQaRjXMqAAiowZYMgAAD0CwAAFAYAH9GEkoy0cpKjaaRq1wuVlGvx8EvEoBiAAAegWAAA2FCphERf3NQR0oVmk0jELxUrAG2I0M41mXqaAxAARCLAAQaDizAS_BP7cAyaQBrpcG2StRLn3HQJGtH1FACGBEAAiEWAAA2DAiqRBKQs_uOt+lSSDIs50AEoFgIIAAeYWAAAsDAAtPgtGFnzkipWVkclSLlb8Dqcg7ZOAAAAPMLAAAbBgAHlygZEDNyhWVnmh1KX4HU5Akhlk40g4pCAACywcAAACx5bsiBm5QrKziA6lL8DqghRRICcaQdYhAAcQAACYMAFVia1IiT58KQsrhNHcpls5AEqBDBbfhqCsCESQANKbAAAUBgfQoXyEosfCk4vVVLYODpvKScgntAhz0WmkCCAFzm6+B0AABYGMEAQqwA1OAAAAg4AAAEYdAAAAABgIAEW8GOVkUAQpMEUEOTABlBzzsBZDoAASBkAAAYCA+PACSsG+ThyOEd0RAeAiAMWPAAxAD_y0AAJAyAAAMBFjP09eYn5yAItZxDIA6BcHGSnKLgEhiJKAAYA8AAeYWAABKDA8ZEJQmRk9FJWXOHTcIRcrqM5kp3D53RXyFisAAAEQiwAAFgYAXDEEkTIyeikrLNTR2OouVjGcyGA5sQajTZ79pSMM5AARGLAAAlBhBQqyERBKTqVYdHW_SoArkjGEAV2TAAOIKgAAJgwACQ2wpVzoiBmpQrOpVmgdSmow+OgIphAPnFQABNB4AABni5WaMcR12cl5JFZ1Ks1FkVK6iOZDKU2oJhpI5ByUkkV1UAGTjwAAWw4HQJxNFJTxxGAAyhWdSrk82dAVKwA5B47Q6vAB8CpOAAIQAGcCQOjtTgmZ+dnYFLTg2CgTBQJYOgK4GwADQAGAPAAAAAJgYB4dBDR0bBQMAJpwCEuAAAAAAAAAAAAABTgAyUAMPgBRkAILgAI0AOFgAAAAAAAAAAAAB04BCXDcFAARKgAAAB+CQAAAAAbgoABacKYUAuUuCSm3LgAyAPuMgdUFAkAAEgAEwoAG6cKYUAlkuCSm1LgPeDQEdCBSE6oKBIAAJAAJhRXl4fAgCdOAJDQBgMCVS4JKbMuADIABKRIAAOYkAAAECzguBgNAwEkIgB5jwAdQALgJAADEEgAAXAwBeEoNgYDQMAPiYDKRsABkAC4CQAA4BIAAGwMA4ATTgCRkAPLgAAAAAAAAAAACxU4A6XAqDAVMNgKqsC4AgiUABACQQQAAAAqDB6Cyk4D3XA6DH8HgrabAAFJAAjoFkCqqMAAB0GAHGnAoT4HwYKAsC0DoAAIIAARAAEgZAAAfBgFBFicASRgfg4NyGwAATQA6BYD4AAco8AACkKAT+nA+FEUDg3EbB_kmACakRKAOgdY+AAHKPAAACbU4HoODchsElACbS1GAOhNZCTQOIwADKPAAAfCgE2pwPQcG5DYP_kwATUkJQB0CuHwAAZR5UgsAAAZ0nAu64Ng4QhuI2D_JMAE1IiUAdDWB8AANQAAiCwC0k4Jg4Ww0EJDoAAJoD0UgzpCAAAAAhCwB4k4ACXAWRa+EoEY0FUzYAAJIAAbToAAIJcNUCAAB7E4SyoLjNTXxkJNNgKSAALI+AADkZFvE4AAECJwAcuEIqOWNATI6B7_oqXgVAE0AAFx0AABNABOOQfh4LPTkaEiwDwbkNgkoATaWowB0EmHkMABBRg3IPqRlAQICLU5GhILjNQYyFphsBSQI6Cnz4AtGpBozIAAPKUAwFOCIOOWNBRo2B6KSjlQBN_olAHQH0fAAAoAyABoKwfwIABXgCacEElg2DgAMGwKQAGbGwASAOgAJ8FwACVi4BmKcGwcDUYPgtj8bA9FKvC4AmkkA6CMj4AAuBkA9AHebB+NjcHGwI6UgNnXg65OBLVwbg0ZAagromTkSMgCb_BGBSGQfUaOw2l0ugX40dgAA3BgnpzUdpwJgYBKhUApUqD_TcVxPgAFULAAAAAUQYAmBgGFlQCsyoAON28tmfAAAACuFgAAogwAO0lQDHPJUFtLZnwADAHgABXCwAAUQYACaMA5mVAMcllQW0qefAAHAeAAFcLAABRBgAQlQHBQHRSoJixIuVhbQW55DIQFAAAAAABRBgABFwA0qHMSAJQXKwmIPi5WFtqoEEJ+ABICIGv2jIAAACiDFmCaHAfHKgAsZM9llQW0WmeQwAbknAAE0OgAAogwAHbpGg4BCBcrCYh4LlYW2qiiQn4fwYgAAC9FwAAUQYrTmiYCUhnAy36VAbQehABs1g3wqAAFSLAABRBgC4SAb0VKwGIhC5WCIm7WD0DaCKCheAHk4ByAABRBgAIWJ1GICUhx4y36VAbQehABs1g3wqAAHAPAAARBgAJDQD_5UGbDLfZUBtB6BPGjeDfCoAAMw8AAAAbsVKw_8Ze5KgNoPQLG0bwfGVAABxHjBHwAAHQCrJBcJAM3KFYaEMpSFpHyHjsDSGCCoADiREH9n4CkgAHqguEgJSHHDLnpUBtG2nj8DaDWioAcgAYQFLExAgBMaALoKlYH9LGcpA0jGjh+BpC4BUABL4eAolUGnlwI0NADEKlYNCMl8pA0iNjx2Bp+CtBRixWAOQvUPAUSqBhSxmFglwDNShWFPDKUgaQrB47A0ggoqVgAR14j57KaBQ0uB0dGRmdwRclAuVUFwkAkAmAQoTAFojoAPoFQAEpAACEDBKHl9KZx4LBgBkuANCoFyt2AAHJiH4uViZHq2vLVK89AA74kB0IgAAAUQYAB5cASFgRBgEEFQCQyoP_NxMU+AAkgkAAAAAABzIAQXACRoASLAEFFQCQyoDaTFPgAJEJAAAAAABNGADlwBMWAbnKg_8ZYJKgtpMU+AAAADQHAAAAEhYcBIBBBUO2ShIZUH_m4oqfAALQWAAAAAAARcATFhzEgC2FysX0lTEOxcrC21UCCE_AAKAsHyBYAAACDABxcATFhuEn5nQf_Kg0_+Mt9lQW0oKfAAGQSAAAAAABpcATFgnEgeEwFsLlYTEOxcrC21UUCE_XoFAAB0AAAADb8AGlwBMWMUSNIHANwuVhMQcFysLaulUrz0ogGFh4DoAAAAZmceAEjIAcXAARoBwkqD_xlicqC2lBT4ACSCQAAAABEKAAeXAEhoBwkqD_xlicqC2lBT4ACSCQAAAAAAfLnCHgCUFysJiD4uVhbaqA5CfgAdsSDKAAAEHCYABxcAQQVAJDKg_83ExT4ACRCVdCoAAAAIQsR6FzkASguVhMQfFysLbVQIIT8ADqiRqiRWLQAAAg4NEeADy4BwkqD_xlicqC2lBT4AAAAnsfAAAA5Lx0WgCUFysJiD4uVhbaqBBCfgAEcinIAE9j4AAAAHOGc2A7WVBMVqFysLaFTPIYABHIkdIQABRAAAEPhQAcXADpp8hoA7xcrCTMRrFysLb_9WAkhPwAJEJAAAN6KgAQcGkCDCipWKVUhiAwuVlxNrxFYegAC0SADpJQL6KQEhCIAlS8BxLhhCL5UH_yJ7JUC00nC0oAASiQAAUo6CCAWkqA0BtlyrkwAHCoAFBUABiPgABWNAfQA0g9A4grABCpgGNSoIMdTFjxcrC2hSTyGAAsh4AKgKkRj_wkBdw2AEASlwAEqAbBKgGOJyoLaFJPIYACyHgPoVAMQff+AgAPpcDNGMgJwuAozSyFW0C4GnlCsNI9_2VBbQpZ5DAAWQkAAE5AP4KwCOPFVKF4M3KFYZR7KSk7qbt4nU8hgASISAAAgYRABnNgBAExcFYYLwkykNKBD52GAqVhJNoBVCvPQAB0JH+F4ACiIk8mIhAwhEDIAB0gAmcAOiEAAlJgAKh0ABIBIFJDwASQ2AAA0BVLwA8uAKSVFysJjK0oXhbaqBBCfgASASAACPGwAAADy4KQkh_JFYLRm1kG1BUrKKbSr6c8hgASISAAA4Gk8AAv0O_AOpdvBcB2EqAUBkzzmVBbQpZ5DAAAAJaADeC4AMZdvBcGylYxxcrCYg+LlYW3_6sBBCfgAEciAYgEtABvBcAHUu3gu2wlBhIEVKxiqMMZSFU2lUKJ4_ABdBMAAS0AG8FwAdS6KixmAImAlRcrCYhALlZPbbVQJIT+xgkAAABLQAVQWMwNwwLHjAIS9OCoJ_HQFSYCoHsmAKAHQADUAAAACEVABvLxoLh3iwC0KlZMRiAQuVhbZzq27TyHVQAg5EAAC0AGkFwf2cKOjpTOlM3NoIAaGgLlbsgAOTEURcrC21ULiE_NSCQADmyBHMQSjIIgAAogwAD0IAYVAEhoBucqD_xlgkqC2kxz4AAAACQ8AAAARXgYChaGHyoKIxq6VBbSgp8AAPRoHpGQAAABsGAoA6qKMEpLTYgy36VBbS2Z8ABIBoAI8DwAAAmujBKS03qMt+lQW0qifVAGgAAB0A8C"
noncomputable def WL44_2 : ℕ := zfNat64 10895 "U4AMlAEkYAaVADhYAAAAAAAAAAAAA8uAJDQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQjwAAAAAAAAAAAAFycAAAAAAAAAAAACYGCaBcH_lJ0ZUACVCgAC0DAABQBgAADAQez8aAAAAAAAAAAAAAAAAAAAAAAAAAuTgAAAAAAAAAAAESDAFiLl4FVIpQvABKhQAB1BgABBhwAABgIPYMDACY0AAAAAAAAAAAAAPIgCQsAAAAAAAAAAAAAAAAAAAAAAAAABwcABAKAAAAtAwAAAAAPg58ADqwAxGAQkwAAAAAAAAAAAACqsAGUgAJ8ABLgAosAMEgAAAAAAAAAAAAIFYACpAIxFwFFqJUAA2CgAC0DAABMBgAAogwe0IATGgAAAAAAAAAAAAEjIAeLAAAAAAAAAAAAIkGA8DBM8uCSsRLgAT4cAAAAZESAACiDAA0TgGAgAHHQAAAACqFgAAAAAwEAAdOAWoQDAQAAAAAAAAFwWAAAMBAATTgB5cASGgAAAAAAAAAAAAE04A+Xg0JAKNLgkpty4AAADENHlC4AAAINCROgAtOAJIwA9CABnQAUqAAAAAAAAAAAAATTgfBgPBlwFUqZQvAAWYMKwAZjQABejoAAKIMHoAjXgtqcEmwgCVsAwEAuY6AybANgAACHJkAATQeAACEDAAOTgAqUASRgB5cAAAAAAAwVAADOHgAADAQACk4AMlAAz4AeXAEhoAAAAAAAAAAAABNOAQl3OCxBBYCTFQNQp5UAAABSNgAAAACAMADROG4SQ8NASYqBqFPKgAAAYB0ABHYmAAI0FAAVwgaDg1CwBrJgAD+ysAAMkyAAEgXAAAQBgAnpxmkWUBoC2lQNRaBcABNQDuGwABBDIAACAMAAlOaUGgU5KLgayWGhcAGbkoAAYbAAEEMgAIOBQAtk4BCXRyRJjFgLaVA1CmlQAGH8h8Ay82AAAAAIAwZx4PBx42Zn5iAA2YFgvB604NtXAAaYBgIB+B0BkGoAABAouAAGoAAQgYAdicAorgfBgyCnKJcLWNGclbeXAATUShe42AwmUADmjsAAKIMH5PTmIaCWDEUCgUsXBJSxFwDwioAAEogXAAZwIFwAAogwAIk4AkZAAAAAAAAAAAAEsGBMDBNAuAoujKgBA5EADHCYAA8wsAAFEGD0AJiwXAwEAYESFwf9JixFwCZioAAOA8AAM4WAAAARJwBIaAAAAAAAAAAAAASGgEAYJKFwFFu5UAFVIgADoPAADeFgAAPQBCpAAU4AMlADBIAAAAAAAAAAAABtSG4KAABErAOKgMoAAMAeAAPMLAABuCgC4KACgVABPJgAGhkAZWLgAASAsAACYKAEwYAWgn5Qro8LlYImNH5FGIAIQI5NIWlwACIxYAACYMF5uegAJqABMQAtOAEJQA8yAIiQAEKAAAAAAAAAAAAAgFBFQuz0dBRaOVAA3yIAAgDwlAAAxwsAB6AHk4AGhAEjIACNAAAAAAAAAAAAADmQLpcGTi4CrL0qACokQAByHhKAATh4AAM4kAXIsSV0RcvJaVUilC8A+cTAA1Iig0RAAxIiCqgCZEi_PRkA8JwKqyH+FgHqTAAAxAAaYZf4XgAHIAAGgoAHzEABsgFU0DsHAhAuDypMAbUKgAC7DwAGFCIAAIgAuY0LNgCBwHELpSerJgC9hUAAUseNIAFvHgABnkQAHmIHYOATxdUQFsXFUAABLJ0VQAZCfAABRIgAtsQBxOABJQEmyASEgAH9GwBJAAcnSLgAP9HwAAKB4AZDEAQTgBZ8C2sgFBIAB9BsB_xKAAIIAChDIAA"
noncomputable def WL44s1_3 (j : ℕ) : ℕ := dsel j 2 (dpk j 1 WL44_1) (dpk j 2 WL44_2)
noncomputable def WL44s0_3 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL44_0) (WL44s1_3 j)
noncomputable def WL44 (j : ℕ) : ℕ := (WL44s0_3 j)
noncomputable def WD44 : ℕ → ℕ := rdw WL44
noncomputable def ready44_cuts0 : List (ℕ × St × ℕ) := []

theorem ready44_cuts0_ok : CutsOk ready44_cuts0 := cutsOk_nil

noncomputable def ready44_0_state : St := ⟨26112, 271072, 51168, 290605, 52016, 171734, 53248, 79646, 29666, 44151, 29184, 45301, 28545, 97680, 26112, 285696, 77280, 561677, 129296, 613693, 182544, 666941, 212210, 696607, 241394, 725791, 269939, 754336, 296051, 784273, 103184, 342621, 156432, 395869, 186098, 425535, 215282, 454719, 243827, 483264, 269939, 758161, 105264, 251380, 134930, 281046, 164114, 310230, 192659, 407910, 218771, 625963, 82914, 109312, 112098, 138496, 140643, 236176, 166755, 454229, 58850, 85248, 87395, 182928, 113507, 400981, 57729, 142981, 83841, 371315, 54657, 342131, 0⟩

theorem ready44_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD44 ready44_cuts0 111 137) ready44_0_state = 42919 := by decide +kernel
#print axioms ready44_0_cursor

theorem ready44_0_covered : Covered (toCl ready44_0_state) :=
  ready_cover_cursor WD44 ready44_cuts0 ready44_cuts0_ok 111 137 42919 ready44_0_state ready44_0_cursor (by decide)
#print axioms ready44_0_covered

noncomputable def ready44_cuts1 : List (ℕ × St × ℕ) := (137, ready44_0_state, 42919) :: ready44_cuts0

theorem ready44_cuts1_ok : CutsOk ready44_cuts1 := cutsOk_cons ready44_0_covered ready44_cuts0_ok
#print axioms ready44_cuts1_ok

noncomputable def ready44_1_state : St := ⟨26112, 271072, 51168, 290605, 52016, 171734, 53248, 230341, 29666, 44151, 29184, 45301, 28545, 166816, 26112, 285696, 77280, 561677, 129296, 613693, 182544, 666941, 212210, 696607, 241394, 725791, 269939, 754336, 296051, 784273, 103184, 342621, 156432, 395869, 186098, 425535, 215282, 454719, 243827, 483264, 269939, 758161, 105264, 344701, 134930, 374367, 164114, 403551, 192659, 432096, 218771, 625963, 82914, 260007, 112098, 289191, 140643, 380080, 166755, 454229, 58850, 89452, 87395, 256268, 113507, 400981, 57729, 212117, 83841, 371315, 54657, 342131, 0⟩

theorem ready44_1_cursor : U (walkCut TOP BK TOPD BKD PT REG WD44 ready44_cuts1 115 105) ready44_1_state = 73735 := by decide +kernel
#print axioms ready44_1_cursor

theorem ready44_1_covered : Covered (toCl ready44_1_state) :=
  ready_cover_cursor WD44 ready44_cuts1 ready44_cuts1_ok 115 105 73735 ready44_1_state ready44_1_cursor (by decide)
#print axioms ready44_1_covered

noncomputable def ready44_cuts2 : List (ℕ × St × ℕ) := (105, ready44_1_state, 73735) :: ready44_cuts1

theorem ready44_cuts2_ok : CutsOk ready44_cuts2 := cutsOk_cons ready44_1_covered ready44_cuts1_ok
#print axioms ready44_cuts2_ok

theorem ready44_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD44 ready44_cuts2 128 1) (ofCl (RC 0 2 1 1 0 0 0 0) 0) = 76516 := by decide +kernel
#print axioms ready44_parent_cursor

theorem rc44 : Covered (RC 0 2 1 1 0 0 0 0) :=
  rcOfC WD44 ready44_cuts2 ready44_cuts2_ok 76516 ready44_parent_cursor (by decide)
#print axioms rc44
noncomputable def WL45_0 : ℕ := zfNat64 33247 "BBaeWLwB6LSwlkKDlvrqsjZmIRSAAIQAB4UDoAOVhJRIHZplMPXIQtGoD0uJQvDDVbbXQwGzMNtdKqKtIE4AEHAoA8xICiBzIuAwofC0MJdtpoMyCOy8AOwiIdDAAAAWIweokAXUymBBMeWLwB6QUoXldqttrpejZmGUulVB3kCcagQQSGeQwHTviQFwUp4HMi4AHJ8LT6ZQ1bZzJiAAVciecbAAd8+DMAFixQCzFBYGpJFMGoH8oXgD0Whhc4tW0ATM2I0ZhtLoBRCBOAHkABPhRQCRlB4G7KEsAWgPsPqVFwYS2jujIAAMxEDUigANzZgA0hsSAZ6ZTA0kXBZAYhhOdtnMQUbMwAM8kwlAq_3chmAsAPIkRRyStTFpQQPlC8szEnqnDJeGGqm0ulEMmYba7UTCCUSRAfAqnGgq5FgPABysHmJBUQQmhJALl5ZB6B8LQw1OWraTEK6ACk4UgULDdW6sRfRYnQB2xCSiQFEACpQvIIRuTjSGGSy9bQCRozDaXaiAuSBOB_lSNo1YYLBYxYzXcLASSSQkPiqlC8whkA+Gt7lquhtBiBUQKCQJzDkicAmjWugsIJ3KgQGaywSWQJASQFGFQB0YuADTRkAB6wiAAZYJA7Azt2TgCFeA5LQihwANA8sEOgAnhcAA_jIAASA0AABEGAJUfCKHTqZgD_BkLR5lQACwuCiVmJSMAACQGgAAIgwehceZhcHWgCFeBoLQGu2G4GAAPoDioP8kQQQPIYURgABXBwAAFQYBCBsdGwX0SgEolQAfsgTlluoTrJgAC9CwAAA7g2PDYCSALQ90pClCZGWW69uUjIpMAAGAOADIYqRgAKBw7g2OjYKSB4wuDhSkMYJkZZbr_5SL7kwAAAGQGY7ACAEhpSo2CvSUAiMqADFkCc_qzXUJDkwAArBYAABSo2Akw0EgqDEFcoXgUQRhMjLLdSjlJKkoABLRYACDQcBuiWPDYGkJUcDClcoXgUQehMjLLdSj_hKDwVJwAagBCpKDRxUAAQqKISx0bBSQP9FwFET4TIyyt+eu5RMlkwW2I97BgAYoXABGABzJSw2AkgCNKF4LAUg7BMjLKdfmKRJRaHmsgm0eAdMZABkIkN0wbgztElgHvKF4FEkNRsNx68pDhCZOdQ81kH1ER8CKW42ACmlAC4sUAk6I2AkhQJiHyULwKIywkRhlupVGKFCcAAWY8DUmtBAHyBhqBbUSWG2MgwpQvAogjCZGAFZsZ1KJJQALcjwYSa95QjSwkACpg3C+6JLD3zE08oXgUQEhMjLCdSiKeJk4FRDP499pCLJNaCNPECYHgHdWCRMG4UkDoRcCklIbcTIwy3UD+FSeegBxEqKplP_mwEIFDYAnUYa8yDl6UArcqwIAxMpcQAoAGgzqg8GZqaBTIiDARxHMQMwlR56B8yhe1hy31FAikS06mG4gUUiSgAejHiyYSawXQgE4YTLO7HRsXQZ0EyxwDAQrjIBGIQB+B4AEoAPIHgAK0EQAEHBYlxcBva8ZACRkDCJAJIqJ6CpLgAMAsBJAAACOHAAAVBgAJCwKgwYRIBJFRPQVJcABgFgJIAAARw4AAAACNAERYhBaJAAAQKgAMAsBJAAAJoNAAAAJl4AkLC2HABQKgAYlQACAaE0qwGUAABYHAAAC2HCNGD4T0NoBFCuRsoXkpBkxYrDDTQTqWMwAAehwB0ZiCCw6AA5zgCQsKQcccaChJ8f+bgzZUAdNIAYYaAAAI4cAAALYcL8YPhPQ2jiUK79C5WVUMLWEqOGEog1IOSKwAAihwB0HGCCwiFrb34ASFhbDgWiQABvC4A28TASaaHbJgAAjhwAAABs2AJCwpBymh4HQnwaQyJUAAgIgAAAAgBwAAABveCVnwBIKFIOdMfABhBvlQACQyAGIBGCmAABADgAAq78tDwAkNAliQD6KgB5FwAF4WDorwf+NgAAmg0AAASkZEgWkVE9DRlwAF4WK6cmIhqAAKkGgAApBwOgihwVBEBYzKaKTKjfz0FAC4ACiAATQaAAAkFAAhZhFDgApFQAgyoAA8NAAGOufMwAAQQiAAB2JAFGXhFDmhEwRaiA1YmAAPDReFWBiZQAA8w8ABBwSMMACywih30h4ARoEMOJTIuBtFwABAB4agACERYAAZg0ABEeUeHgIIbd0K1eC4mgXAACgDYAAggAAbhYHah4EZnkMOMf1aWizC4AmivANQACCJYFgAAAD1IIRYARJ0AEsmCyH8UYpIGtn4AASBcAACkeACIPFuNB0AdnkMBY5bx0hcBSkqA1a8AAAeYqRQAGmRALAzofBghBxDBoHInwBpCoAAw1EHImQAAlzIAAIQcAAgOEUOKWMHwPchPw2gGSxeFkCKV3jykG_DYADbb46AJIACKHHDGD4T0tsSFZKZQvKiFBDCD_zoagffWgC7UgM0dhlDqByRolwRQ7Bg8FZkILoqguAACSKQABkzkb42AACkHAODz4C3ShFDrckQJESJ4bRvBcEkWgBJIENAAAqQaAACkHAAIDhFDiojB8HAHz8No+coXhlKoBFzGRSulFBiUSTsLV8AAmg0ASQAEUOPOMHwnobR7ZQvDLZ5WsoxEUrocgSqyBxtaAYhlDqByRolzU5v4WPAD+8BaJAABFClwAsckTvWDgySZDCSdkisGIA9EiAAC+JAAWwgVBiKkwACBS4P2KwKQCb5pSZoeOwAFTDQAAUg4AP6ECQMc4uAANIXAYSbhsAPf_H2uBIAAVw0AACYOACSvAvj4FQYAACgTKgS_2UhRicAc0bgABUg0AAFIODE3ALN0CQMPBCAGAtwJEmAAPEQH0AAAVw0AACsOAEyfAAy4bgqGhMCDT4OIdEqAAPEQAhgoAEAAAANCQAdz4AkND9EwAzxyBoFQACAiA_oRAAAFA6AAABTnwNhUiSYCCG376tjwuAARkQAhgoAAIU+BDAkAAC6PgxCpEkwf8Qg2_hVsdFwACEiAEMFAACXnwAAoB4AOh8MjghSCj2EwBBRmBhlQAB4iADoAADtWJYAAxBmZnacvC5+Ea8PgVBr6AMtbgYZUAAjIjAn_C4AABFiwAAUg4sb+xLRsbKQbgYPYkApArwXBhBSKqkQHkK2kwAAAAG4GAGgYPIkAeyRWT080XAUTzJEB5KNNUb_5MAAKYWEPQwAADyJACEkVk9Hili8CiByJkYMzdPZRoslQ9DAAKYWAAA0DBGgUHkSAEJIrJ6PDLF4FEDkTIwZm6eyjRZKAAKYWCfAQAABF3wcDjSA1BsCJLH6ULwKIu4mRn_D46jknGTAACoFgngEAAAZ14HQoDOxUBfAuAoiUDZmFm6lUNWaOwABWiwtwKAAMQADtA9kIALfAATYAkLA0FATdXLwZR1RcAApIgNoJAAAVgsAAAqBArFuMHwA6ePw2jTyheBRAdEyMqsCHTeRRRh03AACsLAFjA4AAPbwCJXLQBjB8DUIT8NobUoXjEKJV0iKqbSKf6OgABUCwBYYOADwBcjCEjB8HSHz8Nos8oXkUWlkJUUJzjVTaRSR5UAAKYWALGBwB+CcXMYPgMpCfhtEHlC8Az8TG2qm0inJzYAAnREAAC4KABUXQIpTx3jB8B6JEbtY1MoX1k4kpAlNtVNpFM2mxVZ6AAFjA4Az5OnmPGD4D0tIncoXw_WgIiEyc4k22qqRialkNoGmEIAAwQkU5LZgCLiBzGD4D0em0cKULwsYpG0yL_idVTiLS+psAAKgWALDBwAGhV7lLlWDwEEsnEvsXB_xOA7jxFqtxVUjBdAAFaLAFjA4BLUuiOMHweKcP_2LVpJUlC+2kEEAEyOsk0IocA6bgALsJgAAZhQAAtYAUZACR4AOLGJ7Rg+A9LSLPKF5pnoCWq0U2zIRi7psPT9yMAC4DgAASMZL1rDxsmlWclk0m5TkFFyu2kGokhqpFf43ayKNRfmDc000sgLpLGYAFUEDw1AEpJbszQTsJV6QAEyAAiwBEGBoKi4LB_42AW4NAGRioAAAAAAC5MQRrhAEhYGgo7AkD0i4AsA0ACkAHEEQAArBYAALG_DwHkSAEJIrJ6PFLF4FEDkTIwZq6eyjRZKAAHIWJ0OIwAAACcwNiWDsOGcNAy1WARoVAFUCIANjEwAEpBoAA6gBF5gJUsABDg7DsmFQFkLoWcoXgUQoRMjC6lGi77JgCKAB_ACAYZsAIAVLg7DgOBFQGiC4CiB2JkYI+fu5Rov+yYPoBfIiAHDpEMHIA1JYDFHB2HB0AhnkMB15UADmKF4AGqLGYAAVAiIDUAXhcHYcJQyi1XNQhPw2lUvZQvAojLyBOSk60kUGTB9AJ6BEQFacOwDhFwRmSDsODlTF_9ODyI+KgAEREAAAAKk+A8gXqMgZA78ATLwBMWDsOA9oVAeILgKJ_4mC6lElJ71WspdFnLWAi4AIIEsSABtHB2HWgHgnoaQ8RQvDFCkfVIguoCULCSQ28RAAIEAUYcHYcyEeB66BHLSeULgCK5EF1_0pFzyYGNFAAiIDBk4AmeEAEjg2DmiDQcSPgIzFwB+cuAD_5kH+1omgXQAAhFwFIr4AkLB2HAMEg_8ZALEGgAAD_xkAACQ+AAACQCwdhzWx4ls9C6VX3ljMoJRCCDHnLmRSSgxrNJEmYMysgNSLIb2Fw5kqOA8GLwN+Ty46BWVIBDLI0FAUSrmDcno3ouCz_tKGDkQHUJiEUAFOYNzAmEBPxcvAALLBXQ5GgrCpUDK1S2VkBOULy4hukqA6lEtiTH+EamgBgSSAyg2AHXpAoJZGgoAkgSGKgDrBsAH_CYAD6REHEA0YXAGwzgA0sHjjgGAgQFQEUAUgD5ix+AAABF4qAAXoRAF73gm8cAwFUA+D_ysBhoqAAALzIwAH_jIAA9REAA8uAJDQAAAAAAAAAAAAOGkGrvgA8sAwEHwqAALARAH_lIAP3IwAAVhoAAExEAI_mDLpQWKWRoK2AfB_5iAAAADTiMAANQAE2EwATq5GgpXB8G31IB4x0AdqUgA_8lAAfUKgwk0AAOOvAh5ZGgqACkFaEgAiAB9A4gmFElgACkCiBMhaAAijEpIUMKaA8btYOQ4lfF5oaZPEJlONRJKwEqOD0e0W2B8CENJdLpVnI7F62IkDxSTyGBIUieGkEKcOQ4gHVMnnEylRzklUUHNBIoCEGmwcyzVSiL8XrYABuoADpBt5u2DbDR8F30oC8h0AdiTgAIoAERhoABfSMAY5jGWnoQVENONlYYJw_DiAXUieGW4gPJKjlBAGskCOUm0u1kBFLVsDwNtxMAHwFUC7x0ADKTgAGAjAABMGgAAQIwEQnSwuIT8ylUM6RPOpppqAjp2ZTiATUyeGW21EktxRJc5GoRR6LRCWbCslUt1X_SkIaWrZHoM6Z34DaxcSDgsbL3M2D8a4AiHA0DKRCg2cPAJmGgCuAsAGLhoAAMgABTg5yOBoGAVDAEoeAR8NAE6hoALJDwAAhAAxELEuFEpYGgZdAUAdAY0NAHCBoAA6AAIQALdCRNzdTNgdffk5jYhoXFjpmdxoaNwICUx4eSw8O"
noncomputable def WL45_1 : ℕ := zfNat64 16738 "NEoAAAAAAAAAAAADAQCIYA3AwBHC4AnoABuBgAAAAAwEWoALPgEJcABKgAAAAAAAAAAAAAAAAAAAAAAAAIhgDcDAASDgAJAcAAbgYAAAAAMBAATMgBwsAAAAAAAAAAAAAwEAiGANwMABIOAAkBwABuBgAAAAABCLAAAAAAAAAAAAAAAAAAAAAAAAAwEAG4GAAkHAASA4AA3AwAAYgYAAAwEAAZGAHlwA0aAAAAAAAAAAAAAhRgAIsAAAAAAAAAAAAAmNAAAAAAAAAAAAAAAAAAAAAAAANwMCEGCQw0ARwuAFbCwABABgAAAANwMABIaFPDgKCLADnLgA5AsAALAYAADwMAAAJ0FAIwWAEKVABChYABGCwAAcBYAAIQcAACrALU4BgIAAAEHAACA4ABGCwAARBIAAAwEAAJOAJCQXCQygYAABZMBJATCwABCDgABvCQAAAAJOEUOW2HAAAxLgJICkWABKI8AAJceD6zEAAF2TghUkIQcToKAAAgVAXQCosAFTDIAAah_5yAiUPAzMgVhy2w4JiAf0COM0oXgcR6xAwXgA5cOAAFQHAJ4OAIgADz4AkNCRBwK9MgFEFwf8chaRcBVAAADeZAAAADz4AkNCRBwcpMgIotA48kPpOFwFUAAAN5kAAAAhPhjFgiBwHUGGzMCKCsoXgcR65YsZgVQAAFTGwAAoB4HR0EWyQJBQH_i4BPREAVAJgA6MTAAAAE1BYBFDlthwTEC4I0NI5QvA2j1Z5QvC6lFlSNHkoACMS4K6AGkOAOvmbc3AWM1vY0xYSHn9B5noobA9kXAEVAB7w0XAAIsZLz6FUCXo0Amm+EIOJ0FAKQHzkwB90mAAUgAB1FgAAhBwXjsDHjoARRgAZcALKgBwsAAAAAAAAAAAAAShAAz4AeZAERYACJAAAAAAAAAAAAAGIQAEyAGFwAMqAEiwAgSAAAAAAAAAAAAAPQgAI0ARFgRBgAPCQAFCIAA0HAAB4KAAJoJAAAAEgORbaQEAdS4AMkLAZAB2FAALvEgAAIgwAEzIAI8WAECXAAXhYvyNAABAkSAViQAAEQYAB6EASGgAgBYADpMAAaDgAA8FAAE0EgAAAHDkFFQAAMS4AC8LEdBoACIAB44SAAFhwAFS4AYVCkHAAADioAC8LEfhoAAAAAApBxGgIquBEGp8RBN8eAO6VAC2hoAAyAAzAeAAAiDAAESgRBhIDwBgFgAD_CUAAEoWAAE8PAAARBgAWrwXBSCioAABZMADOJgAFUTAAECKgAA3BQAbFpGgpRBkAfzGgCZUAHEOgAJYPAACeHgAAIgwAiDEMIE5QSOKU8pppAGULwKpZHoBiEmEOPAALvIgAAIgwen4C6SgEKECIMAIAWARAdAHkGgABQWAAE8PAAARBgHAAVcEQUJgeCogBEJgAVBsAAThYAAUw8AABEGAA8Pg0FWtJgIWQJwOblwVRgitTHoKQAAByAAQaCgADDw5hSCioADmZcfsQgqgPPH5lYmAAAMIaiIAAOYUAIgwpCBOApA7QXBxQAtV_9qTDjh+AEWiIABUyUAABEGAAMhAiDLAIg_8VARILgw6eWi6x8GUAAAwhJJgAAIgwCnIEwcEQSA1ysADYiAAnFQABgKgAAiEwAABUhS8SYGJKlsCSoMsXh_xWCgrUx6AFDjYCshtEWaOwAAVhwAgBJCBEG_YVAUBGAcv7LF4AG1CuPQQgJmNgCyG0p5o7AAAiDAXPz8Wa2oKAA0YAWfADjIAiLAAAAAAAAAAAAAQqQvhQ8koAAGJcfsRgCILAAGQADEhQkMgAAvhQAiDNzQglpKtGIBlxaQcoVAADQADIRLTIgAAIgwcgBIWEIOBYpAAABMEoICEQAAAEgeAAABEGEUhAbIWAACSAjiIAX40AAqQiAADcJE2AiDQERgK6NARJLgEdrF8egA1s+AAXeRAAARBgBEGgIjAXEgTgTXLgKyfk4fgVGiuNKgAF3kQAAEQYAAKMAGQgRBkWJQAESS4KK3VYvj0FJUQtZUAAu8iAAAiDFuWgK1KBAGBYpAAIeOgDz_wONWEQAAAJ4eAAAgDAOAElYmpGCbXNSA5qXAHHUK49AAaI0AAvEiAAC+FAASVg6k4AB_MV3C4Aq94PjVhEAAAKmIgAAvhRFgA0OKAOBYpAAAAVFYNWEQCVFoAAmBEAHQAl4eJOhEZkYmgIcdlxtB0ChXHoADAGgAFSEQAAUQoAB68OYsapOAECBeblwBV_8fGrCIAAAVMRAAA2Ci9AlDkToEcLI9Da+paFpTR0CpTUggP4oEwlAagACpCIAArocACdCFRTgRyjAIqLgKi6s++0TC0CigAKmIgAAVhwF38vdmtrCxsaTjpSgjdOBgCEuAYCAAACQwAAABAOAAAAADAQA6DApDjDxMAFsLgD_xMXCYgpJtSRWAAFEOB0QEAAC3OhuBi+DQVUUgBVHQAB8iCiHkMgACpBIAANwUAJw6G4GC4ipjLAWMwUjkLxsABeJgolE8hkAAVIJAAQaCi9BuBgQiQKQBfhcANSLg4ElHEaCZAAAAAIg4BuBhuCQFUA35UAQ0Lgwk0HgGQAAjhoAAjQUABJGBaAqAAclQAIYuCfSkAXzIAASA0AABEGAtAUgF4y4nYbA9FoT+Uji49czpQNmYACph4ACDgUAAYuAJDQARqkADEqAA6FwABNMj_hUAAAAAAEuBsOGaJAJRSphQWnli8Aei0sJZCg5b66rI2ZiEUgACEAAeFA6ADlYSUSB2aZTD1yELRqA9LiULww1W210MBszDbXSqirS"
noncomputable def WL45s0_2 (j : ℕ) : ℕ := dsel j 1 (dpk j 0 WL45_0) (dpk j 1 WL45_1)
noncomputable def WL45 (j : ℕ) : ℕ := (WL45s0_2 j)
noncomputable def WD45 : ℕ → ℕ := rdw WL45
noncomputable def ready45_cuts0 : List (ℕ × St × ℕ) := []

theorem ready45_cuts0_ok : CutsOk ready45_cuts0 := cutsOk_nil

noncomputable def ready45_0_state : St := ⟨26112, 285696, 51168, 242370, 52016, 144910, 53248, 138496, 29666, 44151, 52016, 144248, 28545, 91840, 26112, 285696, 77280, 459685, 129296, 511701, 182544, 564949, 212210, 594615, 264226, 646631, 292771, 675176, 318883, 701288, 103184, 294386, 156432, 347634, 186098, 377300, 238114, 429316, 266659, 457861, 292771, 675176, 105264, 198158, 134930, 227824, 186946, 279840, 215491, 308385, 241603, 594081, 82914, 175808, 134930, 227824, 163475, 256369, 189587, 542065, 81682, 174576, 110227, 203121, 136339, 488817, 80561, 173455, 106673, 459151, 54657, 377536, 0⟩

theorem ready45_0_cursor : U (walkCut TOP BK TOPD BKD PT REG WD45 ready45_cuts0 108 161) ready45_0_state = 35151 := by decide +kernel
#print axioms ready45_0_cursor

theorem ready45_0_covered : Covered (toCl ready45_0_state) :=
  ready_cover_cursor WD45 ready45_cuts0 ready45_cuts0_ok 108 161 35151 ready45_0_state ready45_0_cursor (by decide)
#print axioms ready45_0_covered

noncomputable def ready45_cuts1 : List (ℕ × St × ℕ) := (161, ready45_0_state, 35151) :: ready45_cuts0

theorem ready45_cuts1_ok : CutsOk ready45_cuts1 := cutsOk_cons ready45_0_covered ready45_cuts0_ok
#print axioms ready45_cuts1_ok

theorem ready45_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD45 ready45_cuts1 128 1) (ofCl (RC 0 2 1 1 0 1 0 0) 0) = 49586 := by decide +kernel
#print axioms ready45_parent_cursor

theorem rc45 : Covered (RC 0 2 1 1 0 1 0 0) :=
  rcOfC WD45 ready45_cuts1 ready45_cuts1_ok 49586 ready45_parent_cursor (by decide)
#print axioms rc45
noncomputable def WL46_0 : ℕ := zfNat64 29635 "BgIADQ0AG8GAA3gwABuBgAAAAAwEAAAAAAAAAAAAAGAgTAwH3LgBSABvBgADcDAAAAABgIAAAAAAAAAAAAAMBAmBgEGVAK2FgAAANwMAAAAAGAgAIFwBIaAAAAAAAAAAAAAAAAAAAAAAAAAoCABwcAEgOAAkBwABuBgAAAAAwEABMaAAAAAAAAAAAAAbRgCQ0AAAAAAAAAAAAAwEAoCABwcAEgOAAkBwABuBgAAAAABCvDcDAAlKgAXCQArYWAAJQMAAqQGAACWDAARVgAJkAeHgAI0ABCgAAAAAAAAAAAAGgwA+KgAqiWngoAKokAA_AoAAIQMAAEIGB8AA9wA0yADjQA0KAAAAAAAAAAAAAhLgAAAAAAAAAAAAJD4KwYCoMAAGQWAAyCwHQAAAqokAAEsGABCPBMDAaBgBARABeEgALwkA1hoAAAAACEDACYMhsSAABmPAAXhYGKDQAABBBIAAJYMBCGoOANBUAAXzIgADtDwABNBIAAIQMAB4yABlwAAAEbkQAAFxYAAAACEDAAQQgmDgAOFQAAi8iD_RsAH4eAAVMPAABCBgACpwAJKALHwAQ6AJiwAAAAAAAAAAAAthxBDRpcC+Vp52AyAmoPIgN4B1AhMAAKUSAAg0HALYdrZCBgRcBcAWAFZEQAhw9gP_JgAB9iQAAGwoBbDj0IQB6LgAArNQuEQB_4+aaTAAD7EgAIOBxE1YLYcaEaPxlCtgpcAADRIgm0xEUAACJgsABBwOAAOnABT4AOdAEjIAeXAAAAAAAAAAAAByoQthwOEYGtGy4AAABT+9CA3nQAAixIACDgcRpeAXGYB3hAqFAAAB_JOAAH8XAABUDgAANhQAExYWw4xBYzK77IuAABqHUG4Cix0AAIISAAAAJDQD5UAKyYAAW4bAABhMgAA7CwAAAxBYzK77IuAABqHQm4Cix0AANYWhQfAAA6Ac2olouCyaEqAAsUNDUABppsABLomOIAKwFgKkLGZXVblC8BHZAnP7mwa6Kg4lkD0GjsAAMQshw6AAABUmAAABTGwBgjIABGQAAJhIrhkAACGxcONXv_FwaT1J8AP2Kg4gZOOgAAxCyHDoAAv78AVNQGBcUQChUAAQoSGoACXDYABRBF_oaAAcIkABIa8AqGP_1pOa5Tv4XAAA1DmjcBRY6AAFSPAAAeETUSLgsyjKgF7kCcAPAVKwAsubGkAKdkRVAADggXBGCYfhcBAyoAAGoAB8jYAAzBEvRSAB3wsEsEwnCxmGqi4NJjE+AGqZCoABaGjsAArBAn90pAAFS_v51FHQIRNYaLPILgIGVAABEagTwNgrWbAAf_KgAGGiwO4o7NodjhgI3Y1IeBWDCVDgP8XANRIg_ylDUSIAFqEQACpiYAAJYMABEyBBDgXGXAKnIgpIqciAC3J0AQAN6NAABLBgACHwA4yAJiwAAA8NAAHhoAAAAAAAAJDQIocC6y4BVpEFJFWkQAXbOgADpjQAAAqhwbA4D_FwCrCIKSKsIgAPAZAAKkGgAIMEQACVYC4OAxhcAh4iHJ_dKEPEQAHgMgADzFQAALg4AjT4DHFwCIiIP7pQiIiqAdABHDIAA9A8AAFUOAAEpBtDQKRyFwAEECtR0AEWMgAD0DwAAVQ4G2BoFNKi4IIKTNjkE3BRVUA6AKvHQAB6B4AAKocHOGdnEC2Xz4IiFwG0SIA4cTHGuga2MG4ACpBoAAKocAARCBtEqD0VKmFgApIEUiP+GQBKkoAARYsAAFIOAASxAaF4ApVUXCEyiMiIitJNimwUaCHmDIABUg0AAFUOBCjYOgXjbQhcGk_4fPwC0hMFVe6EF_DIABUg0AAFUOL8xwwAFxEWPABXKqaOQsBMDiUoD_RkAQBKAAEWLAABSDgA_rxQGwBuC4CgwAmAKtmwUf+oQeWMgAFSDQAAVQ4ABqMDoSA2SSWL6aaQB54_AIAERZKtWUIGeHDMABUg0AAFUOAmhxGWIYPgScoXhpFhHjvwS0B_4iOJVAYkYLwAFSDQAAVQ4M78xQTMBHRspALGcDAMAMOAMRsAARULjDQxCPBcAAMkSAACWDAABQgDZ8AGOgAY0AHFgBAkAAAAAAAAAAALcFBbeNHwAmLBMDAMBgHWVAKKHgBRQ8H+V4JNEQAAggoAAAAmZAGAwDrKgFFDwAooeD_K8EmiIAAQQUAAC4GAACpAX04AkNAGAwCwNgAAA94REEScnAAAsCgAAACQ0AYDAa0qAGIRMcgYhXQlYRAABrCgAAtwAkNB6iQDtKgE_jwApAeD+a8EqCIAAmgcAAALo160WBxJcA1MeAHdjwV2qiPCJGAASwSFHID8AAdCGRIAfEwBPB4AEqNAAKoeAAESLAABSDgD8OPwLEw+mXAYbHgDbI8FdqoYEcRntmoACSKGw62EA3ocB42EiHBhPIYRVLgInjwBE8eCu1URGQIwABWiwAAlAAchDcHAJQ1FQANh4ABoPA9XihAAACeFgAAwwlDCeQwiqXARPHgCJ48FdqoiEgRgACeFgAAihwADkIAlDQVAA0HgAGg8D1eKEAAAJwWAACEHGGABi4Ew4AYZUAiYeAETDwf7XgesRCEAAEIABMOARQ6ChVLQbACpHgAVI8FEAZBEAAXomAACKHACCQhFDuvlxPQ8FwAOx4AB2PH_mDfLQqAABeiYAAIocIYIodJU+CNhcBT0eP5pQU9Hiu10F5kCMAAAACKHAIodJU+CihcBpceKSGlx4rtB_snAuxxGBVw2A4gABFDgDAEJcwRdy42B1BcBG8eKSEbx4rtdPurEhAAAAAihwB8b4UhYghkE7CoDThMAacJgA_8VAAAAAQg4AOxcABKwJGktmwWdLgJ7jxSQnuPT0ukmojWiJGG0AjIAARQ4g7MBSFwihwBAShcvAkJQaSCErpxsPVEIlpAnCMTZzMtJBdBQAARQ4paUA9LwD2iEUOAMgXBpD8jx_oWAchdrofFPg6gDPy4AAIocABIaJuPgOWVAYmPgB8w8F3_a8GfiIAAMxcAAAJMgPyY_QLg2jujx2UkKGDwXa6AhA2MzBrgysOnAAA6GoNEJ+H1MhaG0DofOykh1seK7XQK+OIwP1MwIBLGcUnIADVjQAWmIOJAfkxFpV302ZyWRw_KSHtC4kl2ulUGIcSsjMAkCxmAAEIOHwCYcCA_XwhAtuplElHjsAyUPFEu10qhRhxGHEAfwZWQXgAAAmBbYEQ9ASpQvDKDCPHYBkAeKJQVi_XSqE+HEYcQCAxkEkP5NQA2bGPBxOH4DVKF4AAj52AMUID5RIktV0JCWQA3KXGk0gGChYlcEznb8nMScAQcwhBwCZi4BPY8AJ7Hge0EIJEQAESg4AAIQcAENCBwOccZAAA7HgAHY8If6OwFAAAiUHAABCDhDw4+BA2+EDQMAdYiAh4XAEPC4AByAAHAKAAA8DACIXgaBreDwAXNgugAPRNgq10G0nQAAcAoAADwMBoAhLghCoejQPtKgyikjpuATSHgu10H8mQAAAACEKBlUaP3lzHyheGUKQdNwDJ48F2uhMsyAADwJAAAmCgADy4AkNLrjR_kuTSULwyikjpuAVFHgu10H8mQAAAAAAJLgDM38KVoEaJamsoXhlFJHTcAqKPBdroP5MgcgADpiIAADCXcKhThGiWptKF4ZRRx03AKkjwXa6D+zIAAAogJNGgZHRzlrOI0S1o5QvrNlCEHTcAumPFEu10I0mWZhoAAAAEIUA0m0SRoH6lRZRPR03AJoDwXf9rwP3MkJFQACGhYAADwAWXAExJdsaJagUoXhlGkHTcAliPNENi7XQcKZBFAAAAAASXAExKDhrAo0FCSoMops0bgD7B4+YS7XQzSZHnD4AAAAMwAYXLNjRLUIlC8sozI6bgErR5ohsXa6B3TBuEUABZBcAAACS6DBrqo0S1ixcrDKU5OGoB6ge_0xWy7XQzSZA9AAP8WNwADMBDFyVI0S18RcrDKTSUHDcAiUPYQQi7XQcGZAAAQevKwAHmC+ACsvOBax2NEtbwXKwyk0Rhw3AJrDwXa6D_TIY_zbgAAkgBaNgD5YQUEy1BYF6EwGGTIAIoADkAAYgkAAG4uABi6g40DnSoMo4I0dn7UYIDHSBHIAAADASAkgBaNgAFowAMuG42s6NEtfcXKwyrLSJ41Lv7iIBygSKXf4qRBdszYwigABJAC0bAKDh4CBNVYFXjACS49caBtZUGUqQbADhB4w1muggQigAF9koAAASXHWWMwpDRslqyC5WGEEkYN66PQNMQJzrWa6DKjBuEUAAv8lABd2YFbLwcGiAjRLVrlC8MpjE6eNQCaQ8F2ug_kyLCWfyowAIEyhN4iJkbGSmPOFQs+jRLVwFysMoGE6WNQFcGwdBjLluuhMQ8nEy00nytXFoAAIQoIODWJxolrFi5WWEfKdLGoAG0YPhdrodoMg4nEKTLQtEyOwB_x2AFMha0aNEtYsXKywg1ABmjB8LtdDtBl_ZiOMuWzmCyFoW2QQgAAAajTvm0gRoJVlRZQAR03ANRDwXYZrwWHMgtoD+C6+kUAAPCUPQ0bJabIuVlhB0nSxqANRLjB8LNdAYhttIB8SheURs5k0E6mwkhivgGdUgD9cASnhCFiFDRLbFFwYRLxsAAQf_rQAKWK4ZQCoiEEkWgF6FhQJi_+NDqy5RRcrLCNaMG5zReAUn1FoCYgAJ_KF5xJItAY4LAA9Gl1holpdi5WGEYMYN6SVQFIVa6GbjIOKdnLeBFloBJQvMJJFoAnBQ2MBkyHB42S0fBUrDCMGMG9JKoTRSMkVgAdljMGjRnAAhBcrONJGIDqhQ2Tp3cjc6DLJIHRIFgsDmyID05cAb0GgA84VAACEACe4kTMDH04DHk4To0gmBoMCwO4HgBiADEAAiCwAA4AoAAFwMXJ+Yxo6UjZeXk46dn8DAmY7Hh5PDw8TEhoa"
noncomputable def WL46 (j : ℕ) : ℕ := (dpk j 0 WL46_0)
noncomputable def WD46 : ℕ → ℕ := rdw WL46
noncomputable def ready46_cuts0 : List (ℕ × St × ℕ) := []

theorem ready46_cuts0_ok : CutsOk ready46_cuts0 := cutsOk_nil

theorem ready46_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD46 ready46_cuts0 128 1) (ofCl (RC 0 2 1 1 1 0 0 0) 0) = 29715 := by decide +kernel
#print axioms ready46_parent_cursor

theorem rc46 : Covered (RC 0 2 1 1 1 0 0 0) :=
  rcOfC WD46 ready46_cuts0 ready46_cuts0_ok 29715 ready46_parent_cursor (by decide)
#print axioms rc46
noncomputable def WL47_0 : ℕ := zfNat64 7765 "BgIAADYDAAbAYAAAAAAAMBAAAAAAAAAAAAAAAAAAAAAAAAADAQAbgYANgMABsBgADcDAABwDgAADAQBgYAAAAAAAAAAAABgIBEMAbgYAAAAA3AwAAAAAYCABCXAAAAAAAAAAAAAYCAFgFAAxEgADAMLGAgBYBQAAWA4AAAwEAAHCAYCAVDBEgiAC4LAAAESCIAALAUAAAYCABCVAMBQEDgDOJAECFgAdZEAAZxIAAAAAMBAAAAAAAAAAAAAAiGAKwcAAAAAAAAAAGAgAJDQ6gcA5RIA5AsAGhIgAHKJAAE0EgAAAEE124d+gOBbosBFwWAGREQALdFgABXCQAARACYKBVYsBBYWAF4EQAKrFgABQCQfnagGqhwAFy4YxIAMgkAQAWABcEQABkEj4A8AAAAYxIAGTMrocAGISAEIA4oiHWpQB7iIJIcQe8RAAFdDgI+KgNMhAHCFgA4REeHSgBYiwSQBeBEXAaAAETRotZIrLKNRChgTSFgDD5EUkBDIsE2SgEfHEZNAAdIsDoApUldDgAALwsBCB4CIRAAfk+PuJQAdQ2AAK+HArocBcYPgAyQgTg5Fg0hLEyKSAh0eCTuJaAEIABXQ4ABiMAGMgAhcAFKgB4sADEgAAAAAAAAAAAARV4BCXAyFESSgD_z0BQIjwAEImAAEY0AAAAAZCgNPQAMpI0HE3Gg6iXBpqupyoMIAABTHgAWgQEGgADgcH9yI0HJhGg_6TFVMHkQeeKNRGkiAAIgUAFbiIAAI0HFyG4YBCrgZCgAmiwA_hYACKPBZACaLAAIkdhyA0AAAYFJXQ4A+A0BvcaAJCkREaaFRKKKQMMzYz8nkMckNAACNB1QxoBlkCcKpy8iCyFmyIiNNDapEUUUgJNPhyQ0ABcgW_SANoQBIWBkK0oNAMQO1FwB2ouAAAACgdAAAcmJOAD0IMFVAEhYGQoBew0AHQCtQ8AC9hoACrQ8AAFKTgOHCV8OSYHAIQKQDwAOYcRgAIQACUCRIIaAAMQFahK6HDlEg+eVAA1jHTaREwAEgiDiAApAPCIwVSqAqskVgCYDlfDlejwEktCtD2CYrIUaIisgJBHj5qUAE4LiojEAAKDhAyFHiEgGIDOEIAAAGIAAcCoAAAwECuhz6xIEMkisrJTSsnqEYaZ4_KyBHSk13BDUDrC5WGUqmGIgLBo2A8vYgbaKV8OBoQPFgMECwApYmRgBJkoSa6AcoqThdtIDwBQ2CoMcwgZCnnBwf+IgNqDwBtQeAD_xEAAFgSAAAyFFiNh4DOx4fSw9jTxMSGhsa"
noncomputable def WL47 (j : ℕ) : ℕ := (dpk j 0 WL47_0)
noncomputable def WD47 : ℕ → ℕ := rdw WL47
noncomputable def ready47_cuts0 : List (ℕ × St × ℕ) := []

theorem ready47_cuts0_ok : CutsOk ready47_cuts0 := cutsOk_nil

theorem ready47_parent_cursor : U (walkCutR TOP BK TOPD BKD PT REG WD47 ready47_cuts0 128 1) (ofCl (RC 0 2 1 1 1 1 0 0) 0) = 7845 := by decide +kernel
#print axioms ready47_parent_cursor

theorem rc47 : Covered (RC 0 2 1 1 1 1 0 0) :=
  rcOfC WD47 ready47_cuts0 ready47_cuts0_ok 7845 ready47_parent_cursor (by decide)
#print axioms rc47
theorem run8 (i0 i1 i2 i3 i4 i5 i6 i7 : ℕ) (h0 : i0 < 1) (h1 : i1 < 3) (h2 : i2 < 2) (h3 : i3 < 2) (h4 : i4 < 2) (h5 : i5 < 2) (h6 : i6 < 1) (h7 : i7 < 1) :
    Covered (rootCl 8 28 1099511627776 COV (fun r => [i0, i1, i2, i3, i4, i5, i6, i7].getD r 0)) := by
  match i0, i1, i2, i3, i4, i5, i6, i7, h0, h1, h2, h3, h4, h5, h6, h7 with
  | 0, 0, 0, 0, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc0
  | 0, 0, 0, 0, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc1
  | 0, 0, 0, 0, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc2
  | 0, 0, 0, 0, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc3
  | 0, 0, 0, 1, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc4
  | 0, 0, 0, 1, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc5
  | 0, 0, 0, 1, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc6
  | 0, 0, 0, 1, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc7
  | 0, 0, 1, 0, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc8
  | 0, 0, 1, 0, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc9
  | 0, 0, 1, 0, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc10
  | 0, 0, 1, 0, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc11
  | 0, 0, 1, 1, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc12
  | 0, 0, 1, 1, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc13
  | 0, 0, 1, 1, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc14
  | 0, 0, 1, 1, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc15
  | 0, 1, 0, 0, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc16
  | 0, 1, 0, 0, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc17
  | 0, 1, 0, 0, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc18
  | 0, 1, 0, 0, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc19
  | 0, 1, 0, 1, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc20
  | 0, 1, 0, 1, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc21
  | 0, 1, 0, 1, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc22
  | 0, 1, 0, 1, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc23
  | 0, 1, 1, 0, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc24
  | 0, 1, 1, 0, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc25
  | 0, 1, 1, 0, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc26
  | 0, 1, 1, 0, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc27
  | 0, 1, 1, 1, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc28
  | 0, 1, 1, 1, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc29
  | 0, 1, 1, 1, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc30
  | 0, 1, 1, 1, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc31
  | 0, 2, 0, 0, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc32
  | 0, 2, 0, 0, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc33
  | 0, 2, 0, 0, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc34
  | 0, 2, 0, 0, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc35
  | 0, 2, 0, 1, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc36
  | 0, 2, 0, 1, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc37
  | 0, 2, 0, 1, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc38
  | 0, 2, 0, 1, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc39
  | 0, 2, 1, 0, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc40
  | 0, 2, 1, 0, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc41
  | 0, 2, 1, 0, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc42
  | 0, 2, 1, 0, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc43
  | 0, 2, 1, 1, 0, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc44
  | 0, 2, 1, 1, 0, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc45
  | 0, 2, 1, 1, 1, 0, 0, 0, _, _, _, _, _, _, _, _ => exact rc46
  | 0, 2, 1, 1, 1, 1, 0, 0, _, _, _, _, _, _, _, _ => exact rc47
  | i + 1, _, _, _, _, _, _, _, hi, _, _, _, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, _, _, _, hi, _, _, _, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 2, _, _, _, _, _, _, _, hi, _, _, _, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 2, _, _, _, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, _, _, _, i + 2, _, _, _, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, _, _, _, i + 1, _, _, _, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, _, _, _, i + 1, _, _, _, _, _, _, _, hi => exact absurd hi (by omega)
theorem run : ∀ idx : ℕ → ℕ, (∀ r < 8, idx r < (badOf (COV.getD r [])).length) → Covered (rootCl 8 28 1099511627776 COV idx) := by
  intro idx h
  rw [rootCl_congr (idx' := fun r => [idx 0, idx 1, idx 2, idx 3, idx 4, idx 5, idx 6, idx 7].getD r 0) (fun r hr => by interval_cases r <;> rfl)]
  have l0 : (badOf (COV.getD 0 [])).length = 1 := rfl
  have l1 : (badOf (COV.getD 1 [])).length = 3 := rfl
  have l2 : (badOf (COV.getD 2 [])).length = 2 := rfl
  have l3 : (badOf (COV.getD 3 [])).length = 2 := rfl
  have l4 : (badOf (COV.getD 4 [])).length = 2 := rfl
  have l5 : (badOf (COV.getD 5 [])).length = 2 := rfl
  have l6 : (badOf (COV.getD 6 [])).length = 1 := rfl
  have l7 : (badOf (COV.getD 7 [])).length = 1 := rfl
  exact run8 _ _ _ _ _ _ _ _ (l0 ▸ h 0 (by norm_num)) (l1 ▸ h 1 (by norm_num)) (l2 ▸ h 2 (by norm_num)) (l3 ▸ h 3 (by norm_num)) (l4 ▸ h 4 (by norm_num)) (l5 ▸ h 5 (by norm_num)) (l6 ▸ h 6 (by norm_num)) (l7 ▸ h 7 (by norm_num))
theorem cert : ∀ g : ℕ → ℝ, (∀ r < 8, 0 ≤ g r) → Pg cN 8 BS TS g :=
  cert_of COV SMAX (by decide) (by decide +kernel) (by decide) 1099511627776 (by decide) run
end AMW.Cert.PC9TinyData
end
noncomputable section
namespace AMW.Cert
theorem PC9Tiny_G_rev (x0 x1 x2 x3 x4 x5 x6 x7 : ℝ) : PC9Tiny.G x7 x6 x5 x4 x3 x2 x1 x0 = PC9Tiny.G x0 x1 x2 x3 x4 x5 x6 x7 := by
  unfold PC9Tiny.G; ring_nf
theorem PC9Tiny_half (y0 y1 y2 y3 y4 y5 y6 y7 : ℝ) (h0 : 0 ≤ y0) (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) (h3 : 0 ≤ y3) (h4 : 0 ≤ y4) (h5 : 0 ≤ y5) (h6 : 0 ≤ y6) (h7 : 0 ≤ y7) :
    (PC9Tiny.cN : ℝ) / PC9Tiny.SA ≤ PC9Tiny.G y0 y1 y2 y3 y4 y5 y6 y7 ∨ y7 < y0 := by
  have hg : ∀ r < 8, 0 ≤ (fun r => [y0, y1, y2, y3, y4, y5, y6, y7].getD r 0) r := by
    intro r hr; interval_cases r <;> simpa
  rcases PC9TinyData.cert _ hg with h | h
  · left
    rw [PC9Tiny.Fg_G] at h
    rw [div_le_iff₀ (by norm_num [PC9Tiny.SA])]
    linarith
  · right; simpa using h
theorem PC9Tiny_cert_full : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ℝ, 0 ≤ x0 → 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → 0 ≤ x4 → 0 ≤ x5 → 0 ≤ x6 → 0 ≤ x7 →
    (PC9Tiny.cN : ℝ) / PC9Tiny.SA ≤ PC9Tiny.G x0 x1 x2 x3 x4 x5 x6 x7 := by
  intro x0 x1 x2 x3 x4 x5 x6 x7 h0 h1 h2 h3 h4 h5 h6 h7
  rcases lt_or_ge x7 x0 with hlt | hle
  · rcases PC9Tiny_half x7 x6 x5 x4 x3 x2 x1 x0 h7 h6 h5 h4 h3 h2 h1 h0 with h | h
    · rw [← PC9Tiny_G_rev]; exact h
    · exact absurd h (not_lt.mpr hlt.le)
  · rcases PC9Tiny_half x0 x1 x2 x3 x4 x5 x6 x7 h0 h1 h2 h3 h4 h5 h6 h7 with h | h
    · exact h
    · exact absurd h (not_lt.mpr hle)
end AMW.Cert
end
noncomputable section
namespace RiemannFail
open Filter
open Zeta23 Zeta23Ext.Bridge Zeta23Ext.BridgeW AMW
private theorem sum_univ_nine' {M : Type*} [AddCommMonoid M] (f : Fin 9 → M) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_eight]; rfl
noncomputable def aW9 : Fin 9 → Fin 9 → ℝ
  | 0, 1 => (12145025938708000000 : ℝ) / 100000000000000000000
  | 0, 2 => (0 : ℝ) / 100000000000000
  | 0, 3 => (8651269219434000000 : ℝ) / 100000000000000000000
  | 0, 4 => (17776096184552000000 : ℝ) / 100000000000000000000
  | 0, 5 => (36889575523970000000 : ℝ) / 100000000000000000000
  | 0, 6 => (90239673332399000000 : ℝ) / 100000000000000000000
  | 0, 7 => (100000000000000000000 : ℝ) / 100000000000000000000
  | 0, 8 => (200000000000000000000 : ℝ) / 100000000000000000000
  | 1, 2 => (22223820732794000000 : ℝ) / 100000000000000000000
  | 1, 3 => (21042948716829000000 : ℝ) / 100000000000000000000
  | 1, 4 => (41416939206756000000 : ℝ) / 100000000000000000000
  | 1, 5 => (46995446251313000000 : ℝ) / 100000000000000000000
  | 1, 6 => (63110424476029000000 : ℝ) / 100000000000000000000
  | 1, 7 => (19520653335201000000 : ℝ) / 100000000000000000000
  | 1, 8 => (100000000000000000000 : ℝ) / 100000000000000000000
  | 2, 3 => (31202320231433000000 : ℝ) / 100000000000000000000
  | 2, 4 => (47970464688707000000 : ℝ) / 100000000000000000000
  | 2, 5 => (49931791573808000000 : ℝ) / 100000000000000000000
  | 2, 6 => (70456915128268000000 : ℝ) / 100000000000000000000
  | 2, 7 => (63110424476029000000 : ℝ) / 100000000000000000000
  | 2, 8 => (90239673332399000000 : ℝ) / 100000000000000000000
  | 3, 4 => (34428833097063000000 : ℝ) / 100000000000000000000
  | 3, 5 => (61973173188925000000 : ℝ) / 100000000000000000000
  | 3, 6 => (49931791573808000000 : ℝ) / 100000000000000000000
  | 3, 7 => (46995446251313000000 : ℝ) / 100000000000000000000
  | 3, 8 => (36889575523970000000 : ℝ) / 100000000000000000000
  | 4, 5 => (34428833097063000000 : ℝ) / 100000000000000000000
  | 4, 6 => (47970464688707000000 : ℝ) / 100000000000000000000
  | 4, 7 => (41416939206756000000 : ℝ) / 100000000000000000000
  | 4, 8 => (17776096184552000000 : ℝ) / 100000000000000000000
  | 5, 6 => (31202320231433000000 : ℝ) / 100000000000000000000
  | 5, 7 => (21042948716829000000 : ℝ) / 100000000000000000000
  | 5, 8 => (8651269219434000000 : ℝ) / 100000000000000000000
  | 6, 7 => (22223820732794000000 : ℝ) / 100000000000000000000
  | 6, 8 => (0 : ℝ) / 100000000000000
  | 7, 8 => (12145025938708000000 : ℝ) / 100000000000000000000
  | _, _ => 0
noncomputable def bW9 : Fin 8 → ℝ
  | 0 => (28195867368000000 : ℝ) / 100000000000000000000
  | 1 => (50516979727000000 : ℝ) / 100000000000000000000
  | 2 => (69185101351000000 : ℝ) / 100000000000000000000
  | 3 => (80158024056000000 : ℝ) / 100000000000000000000
  | 4 => (80158024056000000 : ℝ) / 100000000000000000000
  | 5 => (69185101351000000 : ℝ) / 100000000000000000000
  | 6 => (50516979727000000 : ℝ) / 100000000000000000000
  | 7 => (28195867368000000 : ℝ) / 100000000000000000000
noncomputable def W9 : WCert 9 := ⟨aW9, bW9⟩
theorem aW9_0_0 : aW9 0 0 = 0 := rfl
theorem aW9_0_1 : aW9 0 1 = (12145025938708000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_0_2 : aW9 0 2 = (0 : ℝ) / 100000000000000 := rfl
theorem aW9_0_3 : aW9 0 3 = (8651269219434000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_0_4 : aW9 0 4 = (17776096184552000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_0_5 : aW9 0 5 = (36889575523970000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_0_6 : aW9 0 6 = (90239673332399000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_0_7 : aW9 0 7 = (100000000000000000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_0_8 : aW9 0 8 = (200000000000000000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_0 : aW9 1 0 = 0 := rfl
theorem aW9_1_1 : aW9 1 1 = 0 := rfl
theorem aW9_1_2 : aW9 1 2 = (22223820732794000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_3 : aW9 1 3 = (21042948716829000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_4 : aW9 1 4 = (41416939206756000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_5 : aW9 1 5 = (46995446251313000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_6 : aW9 1 6 = (63110424476029000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_7 : aW9 1 7 = (19520653335201000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_1_8 : aW9 1 8 = (100000000000000000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_2_0 : aW9 2 0 = 0 := rfl
theorem aW9_2_1 : aW9 2 1 = 0 := rfl
theorem aW9_2_2 : aW9 2 2 = 0 := rfl
theorem aW9_2_3 : aW9 2 3 = (31202320231433000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_2_4 : aW9 2 4 = (47970464688707000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_2_5 : aW9 2 5 = (49931791573808000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_2_6 : aW9 2 6 = (70456915128268000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_2_7 : aW9 2 7 = (63110424476029000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_2_8 : aW9 2 8 = (90239673332399000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_3_0 : aW9 3 0 = 0 := rfl
theorem aW9_3_1 : aW9 3 1 = 0 := rfl
theorem aW9_3_2 : aW9 3 2 = 0 := rfl
theorem aW9_3_3 : aW9 3 3 = 0 := rfl
theorem aW9_3_4 : aW9 3 4 = (34428833097063000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_3_5 : aW9 3 5 = (61973173188925000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_3_6 : aW9 3 6 = (49931791573808000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_3_7 : aW9 3 7 = (46995446251313000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_3_8 : aW9 3 8 = (36889575523970000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_4_0 : aW9 4 0 = 0 := rfl
theorem aW9_4_1 : aW9 4 1 = 0 := rfl
theorem aW9_4_2 : aW9 4 2 = 0 := rfl
theorem aW9_4_3 : aW9 4 3 = 0 := rfl
theorem aW9_4_4 : aW9 4 4 = 0 := rfl
theorem aW9_4_5 : aW9 4 5 = (34428833097063000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_4_6 : aW9 4 6 = (47970464688707000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_4_7 : aW9 4 7 = (41416939206756000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_4_8 : aW9 4 8 = (17776096184552000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_5_0 : aW9 5 0 = 0 := rfl
theorem aW9_5_1 : aW9 5 1 = 0 := rfl
theorem aW9_5_2 : aW9 5 2 = 0 := rfl
theorem aW9_5_3 : aW9 5 3 = 0 := rfl
theorem aW9_5_4 : aW9 5 4 = 0 := rfl
theorem aW9_5_5 : aW9 5 5 = 0 := rfl
theorem aW9_5_6 : aW9 5 6 = (31202320231433000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_5_7 : aW9 5 7 = (21042948716829000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_5_8 : aW9 5 8 = (8651269219434000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_6_0 : aW9 6 0 = 0 := rfl
theorem aW9_6_1 : aW9 6 1 = 0 := rfl
theorem aW9_6_2 : aW9 6 2 = 0 := rfl
theorem aW9_6_3 : aW9 6 3 = 0 := rfl
theorem aW9_6_4 : aW9 6 4 = 0 := rfl
theorem aW9_6_5 : aW9 6 5 = 0 := rfl
theorem aW9_6_6 : aW9 6 6 = 0 := rfl
theorem aW9_6_7 : aW9 6 7 = (22223820732794000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_6_8 : aW9 6 8 = (0 : ℝ) / 100000000000000 := rfl
theorem aW9_7_0 : aW9 7 0 = 0 := rfl
theorem aW9_7_1 : aW9 7 1 = 0 := rfl
theorem aW9_7_2 : aW9 7 2 = 0 := rfl
theorem aW9_7_3 : aW9 7 3 = 0 := rfl
theorem aW9_7_4 : aW9 7 4 = 0 := rfl
theorem aW9_7_5 : aW9 7 5 = 0 := rfl
theorem aW9_7_6 : aW9 7 6 = 0 := rfl
theorem aW9_7_7 : aW9 7 7 = 0 := rfl
theorem aW9_7_8 : aW9 7 8 = (12145025938708000000 : ℝ) / 100000000000000000000 := rfl
theorem aW9_8_0 : aW9 8 0 = 0 := rfl
theorem aW9_8_1 : aW9 8 1 = 0 := rfl
theorem aW9_8_2 : aW9 8 2 = 0 := rfl
theorem aW9_8_3 : aW9 8 3 = 0 := rfl
theorem aW9_8_4 : aW9 8 4 = 0 := rfl
theorem aW9_8_5 : aW9 8 5 = 0 := rfl
theorem aW9_8_6 : aW9 8 6 = 0 := rfl
theorem aW9_8_7 : aW9 8 7 = 0 := rfl
theorem aW9_8_8 : aW9 8 8 = 0 := rfl
theorem bW9_0 : bW9 0 = (28195867368000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_1 : bW9 1 = (50516979727000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_2 : bW9 2 = (69185101351000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_3 : bW9 3 = (80158024056000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_4 : bW9 4 = (80158024056000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_5 : bW9 5 = (69185101351000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_6 : bW9 6 = (50516979727000000 : ℝ) / 100000000000000000000 := rfl
theorem bW9_7 : bW9 7 = (28195867368000000 : ℝ) / 100000000000000000000 := rfl
theorem W9_B : W9.B = (456111945004000000 : ℝ) / 100000000000000000000 := by
  show (∑ r : Fin 8, bW9 r) = _
  norm_num [Fin.sum_univ_eight, bW9_0, bW9_1, bW9_2, bW9_3, bW9_4, bW9_5, bW9_6, bW9_7]
theorem W9_a_nonneg : ∀ i j, 0 ≤ W9.a i j := by
  intro i j
  unfold W9
  match i, j with
  | 0, 0 => show (0:ℝ) ≤ aW9 0 0; norm_num [aW9_0_0]
  | 0, 1 => show (0:ℝ) ≤ aW9 0 1; norm_num [aW9_0_1]
  | 0, 2 => show (0:ℝ) ≤ aW9 0 2; norm_num [aW9_0_2]
  | 0, 3 => show (0:ℝ) ≤ aW9 0 3; norm_num [aW9_0_3]
  | 0, 4 => show (0:ℝ) ≤ aW9 0 4; norm_num [aW9_0_4]
  | 0, 5 => show (0:ℝ) ≤ aW9 0 5; norm_num [aW9_0_5]
  | 0, 6 => show (0:ℝ) ≤ aW9 0 6; norm_num [aW9_0_6]
  | 0, 7 => show (0:ℝ) ≤ aW9 0 7; norm_num [aW9_0_7]
  | 0, 8 => show (0:ℝ) ≤ aW9 0 8; norm_num [aW9_0_8]
  | 1, 0 => show (0:ℝ) ≤ aW9 1 0; norm_num [aW9_1_0]
  | 1, 1 => show (0:ℝ) ≤ aW9 1 1; norm_num [aW9_1_1]
  | 1, 2 => show (0:ℝ) ≤ aW9 1 2; norm_num [aW9_1_2]
  | 1, 3 => show (0:ℝ) ≤ aW9 1 3; norm_num [aW9_1_3]
  | 1, 4 => show (0:ℝ) ≤ aW9 1 4; norm_num [aW9_1_4]
  | 1, 5 => show (0:ℝ) ≤ aW9 1 5; norm_num [aW9_1_5]
  | 1, 6 => show (0:ℝ) ≤ aW9 1 6; norm_num [aW9_1_6]
  | 1, 7 => show (0:ℝ) ≤ aW9 1 7; norm_num [aW9_1_7]
  | 1, 8 => show (0:ℝ) ≤ aW9 1 8; norm_num [aW9_1_8]
  | 2, 0 => show (0:ℝ) ≤ aW9 2 0; norm_num [aW9_2_0]
  | 2, 1 => show (0:ℝ) ≤ aW9 2 1; norm_num [aW9_2_1]
  | 2, 2 => show (0:ℝ) ≤ aW9 2 2; norm_num [aW9_2_2]
  | 2, 3 => show (0:ℝ) ≤ aW9 2 3; norm_num [aW9_2_3]
  | 2, 4 => show (0:ℝ) ≤ aW9 2 4; norm_num [aW9_2_4]
  | 2, 5 => show (0:ℝ) ≤ aW9 2 5; norm_num [aW9_2_5]
  | 2, 6 => show (0:ℝ) ≤ aW9 2 6; norm_num [aW9_2_6]
  | 2, 7 => show (0:ℝ) ≤ aW9 2 7; norm_num [aW9_2_7]
  | 2, 8 => show (0:ℝ) ≤ aW9 2 8; norm_num [aW9_2_8]
  | 3, 0 => show (0:ℝ) ≤ aW9 3 0; norm_num [aW9_3_0]
  | 3, 1 => show (0:ℝ) ≤ aW9 3 1; norm_num [aW9_3_1]
  | 3, 2 => show (0:ℝ) ≤ aW9 3 2; norm_num [aW9_3_2]
  | 3, 3 => show (0:ℝ) ≤ aW9 3 3; norm_num [aW9_3_3]
  | 3, 4 => show (0:ℝ) ≤ aW9 3 4; norm_num [aW9_3_4]
  | 3, 5 => show (0:ℝ) ≤ aW9 3 5; norm_num [aW9_3_5]
  | 3, 6 => show (0:ℝ) ≤ aW9 3 6; norm_num [aW9_3_6]
  | 3, 7 => show (0:ℝ) ≤ aW9 3 7; norm_num [aW9_3_7]
  | 3, 8 => show (0:ℝ) ≤ aW9 3 8; norm_num [aW9_3_8]
  | 4, 0 => show (0:ℝ) ≤ aW9 4 0; norm_num [aW9_4_0]
  | 4, 1 => show (0:ℝ) ≤ aW9 4 1; norm_num [aW9_4_1]
  | 4, 2 => show (0:ℝ) ≤ aW9 4 2; norm_num [aW9_4_2]
  | 4, 3 => show (0:ℝ) ≤ aW9 4 3; norm_num [aW9_4_3]
  | 4, 4 => show (0:ℝ) ≤ aW9 4 4; norm_num [aW9_4_4]
  | 4, 5 => show (0:ℝ) ≤ aW9 4 5; norm_num [aW9_4_5]
  | 4, 6 => show (0:ℝ) ≤ aW9 4 6; norm_num [aW9_4_6]
  | 4, 7 => show (0:ℝ) ≤ aW9 4 7; norm_num [aW9_4_7]
  | 4, 8 => show (0:ℝ) ≤ aW9 4 8; norm_num [aW9_4_8]
  | 5, 0 => show (0:ℝ) ≤ aW9 5 0; norm_num [aW9_5_0]
  | 5, 1 => show (0:ℝ) ≤ aW9 5 1; norm_num [aW9_5_1]
  | 5, 2 => show (0:ℝ) ≤ aW9 5 2; norm_num [aW9_5_2]
  | 5, 3 => show (0:ℝ) ≤ aW9 5 3; norm_num [aW9_5_3]
  | 5, 4 => show (0:ℝ) ≤ aW9 5 4; norm_num [aW9_5_4]
  | 5, 5 => show (0:ℝ) ≤ aW9 5 5; norm_num [aW9_5_5]
  | 5, 6 => show (0:ℝ) ≤ aW9 5 6; norm_num [aW9_5_6]
  | 5, 7 => show (0:ℝ) ≤ aW9 5 7; norm_num [aW9_5_7]
  | 5, 8 => show (0:ℝ) ≤ aW9 5 8; norm_num [aW9_5_8]
  | 6, 0 => show (0:ℝ) ≤ aW9 6 0; norm_num [aW9_6_0]
  | 6, 1 => show (0:ℝ) ≤ aW9 6 1; norm_num [aW9_6_1]
  | 6, 2 => show (0:ℝ) ≤ aW9 6 2; norm_num [aW9_6_2]
  | 6, 3 => show (0:ℝ) ≤ aW9 6 3; norm_num [aW9_6_3]
  | 6, 4 => show (0:ℝ) ≤ aW9 6 4; norm_num [aW9_6_4]
  | 6, 5 => show (0:ℝ) ≤ aW9 6 5; norm_num [aW9_6_5]
  | 6, 6 => show (0:ℝ) ≤ aW9 6 6; norm_num [aW9_6_6]
  | 6, 7 => show (0:ℝ) ≤ aW9 6 7; norm_num [aW9_6_7]
  | 6, 8 => show (0:ℝ) ≤ aW9 6 8; norm_num [aW9_6_8]
  | 7, 0 => show (0:ℝ) ≤ aW9 7 0; norm_num [aW9_7_0]
  | 7, 1 => show (0:ℝ) ≤ aW9 7 1; norm_num [aW9_7_1]
  | 7, 2 => show (0:ℝ) ≤ aW9 7 2; norm_num [aW9_7_2]
  | 7, 3 => show (0:ℝ) ≤ aW9 7 3; norm_num [aW9_7_3]
  | 7, 4 => show (0:ℝ) ≤ aW9 7 4; norm_num [aW9_7_4]
  | 7, 5 => show (0:ℝ) ≤ aW9 7 5; norm_num [aW9_7_5]
  | 7, 6 => show (0:ℝ) ≤ aW9 7 6; norm_num [aW9_7_6]
  | 7, 7 => show (0:ℝ) ≤ aW9 7 7; norm_num [aW9_7_7]
  | 7, 8 => show (0:ℝ) ≤ aW9 7 8; norm_num [aW9_7_8]
  | 8, 0 => show (0:ℝ) ≤ aW9 8 0; norm_num [aW9_8_0]
  | 8, 1 => show (0:ℝ) ≤ aW9 8 1; norm_num [aW9_8_1]
  | 8, 2 => show (0:ℝ) ≤ aW9 8 2; norm_num [aW9_8_2]
  | 8, 3 => show (0:ℝ) ≤ aW9 8 3; norm_num [aW9_8_3]
  | 8, 4 => show (0:ℝ) ≤ aW9 8 4; norm_num [aW9_8_4]
  | 8, 5 => show (0:ℝ) ≤ aW9 8 5; norm_num [aW9_8_5]
  | 8, 6 => show (0:ℝ) ≤ aW9 8 6; norm_num [aW9_8_6]
  | 8, 7 => show (0:ℝ) ≤ aW9 8 7; norm_num [aW9_8_7]
  | 8, 8 => show (0:ℝ) ≤ aW9 8 8; norm_num [aW9_8_8]
theorem W9_bmin : ∀ r, ((28195867368000000 : ℝ) / 100000000000000000000) ≤ W9.b r := by
  intro r
  unfold W9
  match r with
  | 0 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 0; norm_num [bW9_0]
  | 1 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 1; norm_num [bW9_1]
  | 2 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 2; norm_num [bW9_2]
  | 3 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 3; norm_num [bW9_3]
  | 4 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 4; norm_num [bW9_4]
  | 5 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 5; norm_num [bW9_5]
  | 6 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 6; norm_num [bW9_6]
  | 7 => show ((28195867368000000 : ℝ) / 100000000000000000000) ≤ bW9 7; norm_num [bW9_7]
theorem W9_capacity : ∀ s : ℕ, W9.spanMass s ≤ 2 := by
  intro s
  unfold WCert.spanMass W9
  rcases lt_or_ge s 9 with hs | hs
  · interval_cases s <;> simp (config := { decide := true }) only [sum_univ_nine', aW9_0_0, aW9_0_1, aW9_0_2, aW9_0_3, aW9_0_4, aW9_0_5, aW9_0_6, aW9_0_7, aW9_0_8, aW9_1_0, aW9_1_1, aW9_1_2, aW9_1_3, aW9_1_4, aW9_1_5, aW9_1_6, aW9_1_7, aW9_1_8, aW9_2_0, aW9_2_1, aW9_2_2, aW9_2_3, aW9_2_4, aW9_2_5, aW9_2_6, aW9_2_7, aW9_2_8, aW9_3_0, aW9_3_1, aW9_3_2, aW9_3_3, aW9_3_4, aW9_3_5, aW9_3_6, aW9_3_7, aW9_3_8, aW9_4_0, aW9_4_1, aW9_4_2, aW9_4_3, aW9_4_4, aW9_4_5, aW9_4_6, aW9_4_7, aW9_4_8, aW9_5_0, aW9_5_1, aW9_5_2, aW9_5_3, aW9_5_4, aW9_5_5, aW9_5_6, aW9_5_7, aW9_5_8, aW9_6_0, aW9_6_1, aW9_6_2, aW9_6_3, aW9_6_4, aW9_6_5, aW9_6_6, aW9_6_7, aW9_6_8, aW9_7_0, aW9_7_1, aW9_7_2, aW9_7_3, aW9_7_4, aW9_7_5, aW9_7_6, aW9_7_7, aW9_7_8, aW9_8_0, aW9_8_1, aW9_8_2, aW9_8_3, aW9_8_4, aW9_8_5, aW9_8_6, aW9_8_7, aW9_8_8, if_true, if_false] <;> norm_num
  · have h0 : ∀ i j : Fin 9, ¬ ((i : ℕ) < (j : ℕ) ∧ (j : ℕ) - (i : ℕ) = s) := by
      intro i j ⟨_, h⟩
      have := j.2
      omega
    simp only [h0, if_false, Finset.sum_const_zero]
    norm_num
theorem W9_adm : W9.Adm := ⟨W9_a_nonneg, fun r => le_trans (by norm_num) (W9_bmin r), W9_capacity⟩
private lemma sum8 (f : Fin (9 - 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  show ∑ i : Fin 8, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7
  exact Fin.sum_univ_eight f
theorem cert_wfun_eq (x : ℝ) : AMW.Cert.wfun x = wfun x := rfl
theorem Fw_W9 (g : Fin (9 - 1) → ℝ) :
    Fw W9 g = AMW.Cert.PC9Tiny.G (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) := by
  show (∑ r : Fin 8, bW9 r * g r) + (∑ i : Fin 9, ∑ j : Fin 9, if (i : ℕ) < (j : ℕ) then aW9 i j * wfun (ptsN 9 g j - ptsN 9 g i) else 0) = _
  unfold AMW.Cert.PC9Tiny.G ptsN
  simp only [cert_wfun_eq, sum8, sum_univ_nine', Fin.sum_univ_eight, Fin.isValue, aW9_0_0, aW9_0_1, aW9_0_2, aW9_0_3, aW9_0_4, aW9_0_5, aW9_0_6, aW9_0_7, aW9_0_8, aW9_1_0, aW9_1_1, aW9_1_2, aW9_1_3, aW9_1_4, aW9_1_5, aW9_1_6, aW9_1_7, aW9_1_8, aW9_2_0, aW9_2_1, aW9_2_2, aW9_2_3, aW9_2_4, aW9_2_5, aW9_2_6, aW9_2_7, aW9_2_8, aW9_3_0, aW9_3_1, aW9_3_2, aW9_3_3, aW9_3_4, aW9_3_5, aW9_3_6, aW9_3_7, aW9_3_8, aW9_4_0, aW9_4_1, aW9_4_2, aW9_4_3, aW9_4_4, aW9_4_5, aW9_4_6, aW9_4_7, aW9_4_8, aW9_5_0, aW9_5_1, aW9_5_2, aW9_5_3, aW9_5_4, aW9_5_5, aW9_5_6, aW9_5_7, aW9_5_8, aW9_6_0, aW9_6_1, aW9_6_2, aW9_6_3, aW9_6_4, aW9_6_5, aW9_6_6, aW9_6_7, aW9_6_8, aW9_7_0, aW9_7_1, aW9_7_2, aW9_7_3, aW9_7_4, aW9_7_5, aW9_7_6, aW9_7_7, aW9_7_8, aW9_8_0, aW9_8_1, aW9_8_2, aW9_8_3, aW9_8_4, aW9_8_5, aW9_8_6, aW9_8_7, aW9_8_8, bW9_0, bW9_1, bW9_2, bW9_3, bW9_4, bW9_5, bW9_6, bW9_7]
  norm_num [AMW.Cert.PC9Tiny.SA]
  try ring
theorem cert_AM : ∀ g : Fin 8 → ℝ, (∀ i, 0 ≤ g i) → ((893616123055294719 : ℝ) / 100000000000000000000) ≤ Fw W9 g := by
  intro g hg
  rw [Fw_W9]
  have h := AMW.Cert.PC9Tiny_cert_full (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7) (hg 0) (hg 1) (hg 2) (hg 3) (hg 4) (hg 5) (hg 6) (hg 7)
  simp only [AMW.Cert.PC9Tiny.cN, AMW.Cert.PC9Tiny.SA] at h
  push_cast at h
  exact h
end RiemannFail
end
-- SWAP END certificate
section
/- Mechanical umbrella for the exact attempt016 PC8C5BF certificate and W8 bridge.
   Original attribution, declarations and extraction provenance are retained in
   Attempt016LocalCert and Attempt016W8. Source-only; compilation remains pending.
-/
end
section
/-
Copyright (c) 2026 R. Arun Chandru. Released under Apache-2.0.
Adapted from Samuel Lavery's attempt-016 kernel_limit proof (2026),
Apache-2.0, retaining the imported source's attribution and notices.
Change: expose the uniform bound already proved by gram_close_of,
without a fixed-distance hypothesis. No growing cutoff is substituted
into a theorem whose cutoff was fixed before taking the height limit.

SOURCE ONLY: not yet compiled. No challenge acceptance claim.
-/
noncomputable section
open Matrix RHLinalg Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
namespace Opeth.AMUniformKernel
theorem kernel_limit_uniform (Z : ZeroConfig) :
    ∀ δ > 0, ∀ᶠ T in atTop, ∀ z z' : retained Z (mtParams T) T,
      ‖gram Z (mtParams T) T z z' -
        (Zeta23Ext.Bridge.kfun
          (xret Z (mtParams T) T z - xret Z (mtParams T) T z') : ℂ)‖ ≤ δ := by
  intro δ hδ
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  obtain ⟨T₀, hT₀⟩ := AMW.localHypsCoreAM_eventually hP
  set K : ℝ :=
    (AMW.cAMW (paramsOf stdProfile 1).ϱ / (paramsOf stdProfile 1).w) ^ 2 with hK
  have hK0 : 0 ≤ K := sq_nonneg _
  have hw : 0 < (paramsOf stdProfile 1).w := by linarith [hP.one_le_w]
  filter_upwards [eventually_gt_atTop 0, eventually_w8 hP, AMW.eventually_w32 hP,
    eventually_ge_atTop T₀, (tendsto_L hP).eventually_ge_atTop 1,
    (tendsto_L hP).eventually_ge_atTop
      ((10 * K + 12 * (paramsOf stdProfile 1).w) / δ)]
    with T hT h8 h32 hTT₀ hL1 hLδ
  intro z z'
  have hF := (hT₀ T hTT₀).toCoreW
  have h := gram_close_of hP hT h8 h32 hF Z z z'
  refine h.trans ?_
  set L := (paramsOf stdProfile 1).L T with hLdef
  have hL : 0 < L := by linarith
  have hL4 : L ≤ L ^ 4 := by nlinarith [pow_pos hL 2, pow_pos hL 3]
  have h1 : 10 * K / L ^ 4 ≤ 10 * K / L :=
    div_le_div_of_nonneg_left (by positivity) hL hL4
  have h2 : (10 * K + 12 * (paramsOf stdProfile 1).w) / L ≤ δ := by
    rw [div_le_iff₀ hL]
    have := (div_le_iff₀ hδ).mp hLδ
    linarith
  calc
    10 * K / L ^ 4 + 12 * (paramsOf stdProfile 1).w / L
        ≤ 10 * K / L + 12 * (paramsOf stdProfile 1).w / L := by gcongr
    _ = (10 * K + 12 * (paramsOf stdProfile 1).w) / L := by ring
    _ ≤ δ := h2
end Opeth.AMUniformKernel
end
section
open scoped BigOperators
open Real
noncomputable section
namespace Meshuggah
noncomputable def sincN (t : ℝ) : ℝ := Real.sinc (π * t)
noncomputable def phiC (c t : ℝ) : ℝ := t ^ 2 - (max (t - c) 0) ^ 2
noncomputable def hat (s : ℝ) : ℝ := max 0 (1 - |s|)
end Meshuggah
end
section
open scoped BigOperators
open Real
noncomputable section
namespace Pantera
export Meshuggah (sincN phiC hat)
noncomputable def sep : ℝ := 17 / 20
noncomputable def gammaM : ℝ := 13 / 20
noncomputable def gMaj (u : ℝ) : ℝ := gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2
noncomputable def LMaj : ℝ := 2 * gammaM / sep * (1 + sincN sep)
end Pantera
end
section
open scoped BigOperators ComplexOrder
open Real
noncomputable section
namespace Pantera
noncomputable def LMajBound : Prop := LMaj ≤ 179 / 100
noncomputable def SeparatedBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (y : ι → ℝ) (x : ι → ℝ) (w : ℝ → ℝ),
    (∀ i j, i ≠ j → sep ≤ |y i - y j|) →
    Measurable w → (∀ u, 0 ≤ w u) → (∀ u, w u ≤ gMaj u) →
    ∫ u, w u * (∑ i, ∑ j, x i * x j * Real.cos (2 * π * (y i - y j) * u)) ≤ LMaj * ∑ i, x i ^ 2
end Pantera
end
section
open Real MeasureTheory
namespace Meshuggah.Majorant
noncomputable def cosPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => cosPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : F)
noncomputable def sinPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => sinPoly x n + (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : F)
noncomputable def sincPoly {F : Type*} [Field F] (x : F) : ℕ → F
  | 0 => 0
  | n + 1 => sincPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n + 1).factorial : F)
section Field
variable {F : Type*} [Field F]
lemma cosPoly_succ (x : F) (n : ℕ) :
    cosPoly x (n + 1) = cosPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : F) := rfl
lemma sinPoly_succ (x : F) (n : ℕ) :
    sinPoly x (n + 1) = sinPoly x n + (-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : F) :=
  rfl
lemma sincPoly_succ (x : F) (n : ℕ) :
    sincPoly x (n + 1) = sincPoly x n + (-1) ^ n * x ^ (2 * n) / ((2 * n + 1).factorial : F) :=
  rfl
@[simp] lemma cosPoly_zero (x : F) : cosPoly x 0 = 0 := rfl
@[simp] lemma sinPoly_zero (x : F) : sinPoly x 0 = 0 := rfl
@[simp] lemma sincPoly_zero (x : F) : sincPoly x 0 = 0 := rfl
lemma sinPoly_eq_mul_sincPoly (x : F) (n : ℕ) : sinPoly x n = x * sincPoly x n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sinPoly_succ, sincPoly_succ, ih, pow_succ]; ring
end Field
lemma sinPoly_at_zero (n : ℕ) : sinPoly (0 : ℝ) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sinPoly_succ, ih]; simp
lemma cosPoly_at_zero (n : ℕ) : cosPoly (0 : ℝ) (n + 1) = 1 := by
  induction n with
  | zero => simp [cosPoly_succ]
  | succ n ih => rw [cosPoly_succ, ih]; simp
lemma sincPoly_at_zero (n : ℕ) : sincPoly (0 : ℝ) (n + 1) = 1 := by
  induction n with
  | zero => simp [sincPoly_succ]
  | succ n ih => rw [sincPoly_succ, ih]; simp
lemma cosPoly_abs (x : ℝ) (n : ℕ) : cosPoly |x| n = cosPoly x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cosPoly_succ, cosPoly_succ, ih, pow_mul, sq_abs, ← pow_mul]
lemma sincPoly_abs (x : ℝ) (n : ℕ) : sincPoly |x| n = sincPoly x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sincPoly_succ, sincPoly_succ, ih, pow_mul, sq_abs, ← pow_mul]
lemma hasDerivAt_sinPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => sinPoly y n) (cosPoly x n) x := by
  induction n with
  | zero => exact hasDerivAt_const x (0 : ℝ)
  | succ n ih =>
    have h : HasDerivAt (fun y : ℝ => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        ((-1) ^ n * (((2 * n + 1 : ℕ) : ℝ) * x ^ (2 * n + 1 - 1)) / ((2 * n + 1).factorial : ℝ)) x :=
      ((hasDerivAt_pow (2 * n + 1) x).const_mul ((-1 : ℝ) ^ n)).div_const _
    have h1 : HasDerivAt (fun y : ℝ => (-1) ^ n * y ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))
        ((-1) ^ n * x ^ (2 * n) / ((2 * n).factorial : ℝ)) x := by
      refine h.congr_deriv ?_
      have hc : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul, mul_left_comm,
        mul_div_mul_left _ _ hc]
    exact ih.add h1
lemma hasDerivAt_cosPoly (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cosPoly y (n + 1)) (-sinPoly x n) x := by
  induction n with
  | zero =>
    have h : (fun y : ℝ => cosPoly y (0 + 1)) = fun _ => (1 : ℝ) := by
      funext y; simp [cosPoly_succ]
    rw [h]
    simpa using hasDerivAt_const x (1 : ℝ)
  | succ n ih =>
    have h : HasDerivAt
        (fun y : ℝ => (-1) ^ (n + 1) * y ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1).factorial : ℝ))
        ((-1) ^ (n + 1) * (((2 * n + 1 + 1 : ℕ) : ℝ) * x ^ (2 * n + 1 + 1 - 1))
          / ((2 * n + 1 + 1).factorial : ℝ)) x :=
      ((hasDerivAt_pow (2 * n + 1 + 1) x).const_mul ((-1 : ℝ) ^ (n + 1))).div_const _
    have h1 : HasDerivAt
        (fun y : ℝ => (-1) ^ (n + 1) * y ^ (2 * n + 1 + 1) / ((2 * n + 1 + 1).factorial : ℝ))
        (-((-1) ^ n * x ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ))) x := by
      refine h.congr_deriv ?_
      have hc : ((2 * n + 1 + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
      rw [Nat.factorial_succ (2 * n + 1), Nat.add_sub_cancel, Nat.cast_mul, mul_left_comm,
        mul_div_mul_left _ _ hc, pow_succ ((-1 : ℝ)) n]
      ring
    have h2 := ih.add h1
    rw [← neg_add] at h2
    exact h2
private lemma nonneg_of_hasDerivAt {f f' : ℝ → ℝ} (h0 : f 0 = 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) :
    ∀ x, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt).continuousOn
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hd y).deriv]
      exact hpos y (le_of_lt hy)
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [h0] at h
  exact h
theorem taylor_sign (m : ℕ) :
    (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (cosPoly x (m + 1) - cos x)) ∧
    (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (sinPoly x (m + 1) - sin x)) := by
  have step : ∀ m : ℕ, (∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (cosPoly x (m + 1) - cos x)) →
      ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ m * (sinPoly x (m + 1) - sin x) := by
    intro m hc
    refine nonneg_of_hasDerivAt (f := fun y => (-1 : ℝ) ^ m * (sinPoly y (m + 1) - sin y))
      (f' := fun y => (-1 : ℝ) ^ m * (cosPoly y (m + 1) - cos y)) ?_ ?_ hc
    · simp [sinPoly_at_zero]
    · intro y
      have h : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ m * (sinPoly z (m + 1) - sin z))
          ((-1 : ℝ) ^ m * (cosPoly y (m + 1) - cos y)) y :=
        ((hasDerivAt_sinPoly (m + 1) y).sub (hasDerivAt_sin y)).const_mul _
      exact h
  induction m with
  | zero =>
    have hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ 0 * (cosPoly x (0 + 1) - cos x) := by
      intro x _
      have h1 : cosPoly x (0 + 1) = 1 := by rw [cosPoly_succ, cosPoly_zero]; simp
      rw [h1, pow_zero, one_mul]
      linarith [cos_le_one x]
    exact ⟨hc, step 0 hc⟩
  | succ m ih =>
    have hc : ∀ x : ℝ, 0 ≤ x → 0 ≤ (-1 : ℝ) ^ (m + 1) * (cosPoly x (m + 1 + 1) - cos x) := by
      refine nonneg_of_hasDerivAt
        (f := fun y => (-1 : ℝ) ^ (m + 1) * (cosPoly y (m + 1 + 1) - cos y))
        (f' := fun y => (-1 : ℝ) ^ m * (sinPoly y (m + 1) - sin y)) ?_ ?_ ih.2
      · simp [cosPoly_at_zero]
      · intro y
        have h : HasDerivAt (fun z : ℝ => (-1 : ℝ) ^ (m + 1) * (cosPoly z (m + 1 + 1) - cos z))
            ((-1 : ℝ) ^ (m + 1) * (-sinPoly y (m + 1) - -sin y)) y :=
          ((hasDerivAt_cosPoly (m + 1) y).sub (hasDerivAt_cos y)).const_mul _
        refine h.congr_deriv ?_
        rw [pow_succ]
        ring
    exact ⟨hc, step (m + 1) hc⟩
theorem cos_le_cosPoly (x : ℝ) (n : ℕ) : cos x ≤ cosPoly x (2 * n + 1) := by
  have h := (taylor_sign (2 * n)).1 |x| (abs_nonneg x)
  rw [Even.neg_one_pow (even_two_mul n), one_mul, cosPoly_abs, cos_abs] at h
  linarith
theorem sin_le_sinPoly {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : sin x ≤ sinPoly x (2 * n + 1) := by
  have h := (taylor_sign (2 * n)).2 x hx
  rw [Even.neg_one_pow (even_two_mul n), one_mul] at h
  linarith
theorem sinPoly_le_sin {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : sinPoly x (2 * n + 2) ≤ sin x := by
  have h : 0 ≤ (-1 : ℝ) ^ (2 * n + 1) * (sinPoly x (2 * n + 2) - sin x) :=
    (taylor_sign (2 * n + 1)).2 x hx
  rw [Odd.neg_one_pow (odd_two_mul_add_one n)] at h
  linarith
lemma sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_choice x with h | h <;> rw [h]
  exact sinc_neg x
theorem sincPoly_le_sinc (x : ℝ) (n : ℕ) : sincPoly x (2 * n + 2) ≤ sinc x := by
  rw [← sincPoly_abs, ← sinc_abs]
  rcases eq_or_lt_of_le (abs_nonneg x) with h0 | hpos
  · rw [← h0, sinc_zero]
    exact le_of_eq (sincPoly_at_zero (2 * n + 1))
  · rw [sinc_of_ne_zero (ne_of_gt hpos), le_div_iff₀ hpos,
      mul_comm (sincPoly |x| (2 * n + 2)) |x|, ← sinPoly_eq_mul_sincPoly]
    exact sinPoly_le_sin (le_of_lt hpos) n
end Meshuggah.Majorant
end
section
open Real MeasureTheory
open scoped FourierTransform
namespace Pantera.Majorant
lemma sep_pos : 0 < sep := by unfold sep; norm_num
lemma sep_ne_zero : sep ≠ 0 := sep_pos.ne'
lemma gammaM_nonneg : 0 ≤ gammaM := by unfold gammaM; norm_num
lemma sin_eq_mul_sinc (x : ℝ) : sin x = x * sinc x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinc_of_ne_zero hx]
    field_simp
lemma sinc_sq_le (x : ℝ) : sinc x ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hA : sinc x ^ 2 ≤ 1 := by
    calc sinc x ^ 2 = |sinc x| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (abs_sinc_le_one x) 2
      _ = 1 := one_pow 2
  have hB : sinc x ^ 2 * x ^ 2 ≤ 1 := by
    have h : sinc x * x = sin x := by rw [mul_comm]; exact (sin_eq_mul_sinc x).symm
    rw [← mul_pow, h]
    exact sin_sq_le_one x
  rw [← div_eq_mul_inv, le_div_iff₀ h1, mul_add, mul_one]
  linarith
lemma gMaj_le (u : ℝ) :
    gMaj u ≤ gammaM * (4 * (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹
      + 4 * (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹) := by
  unfold gMaj sincN
  rw [show π * (sep * (u - 1 / 2)) = π * sep * (u - 1 / 2) by ring,
    show π * (sep * (u + 1 / 2)) = π * sep * (u + 1 / 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ gammaM_nonneg
  have h1 := sinc_sq_le (π * sep * (u - 1 / 2))
  have h2 := sinc_sq_le (π * sep * (u + 1 / 2))
  nlinarith [sq_nonneg (sinc (π * sep * (u - 1 / 2)) - sinc (π * sep * (u + 1 / 2)))]
end Pantera.Majorant
namespace Pantera
open Majorant
theorem gMaj_nonneg (u : ℝ) : 0 ≤ gMaj u := mul_nonneg gammaM_nonneg (sq_nonneg _)
theorem continuous_gMaj : Continuous gMaj := by
  have h : Continuous fun u : ℝ =>
      gammaM * (sincN (sep * (u - 1 / 2)) + sincN (sep * (u + 1 / 2))) ^ 2 := by
    unfold sincN
    fun_prop
  exact h
theorem integrable_gMaj : Integrable gMaj := by
  have hne : π * sep ≠ 0 := mul_ne_zero pi_ne_zero sep_ne_zero
  have h1 : Integrable fun x : ℝ => (1 + (π * sep * x) ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.comp_mul_left' hne
  have hm : Integrable fun u : ℝ => (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹ :=
    h1.comp_sub_right (1 / 2)
  have hp : Integrable fun u : ℝ => (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹ :=
    h1.comp_add_right (1 / 2)
  have hB : Integrable fun u : ℝ => gammaM * (4 * (1 + (π * sep * (u - 1 / 2)) ^ 2)⁻¹
      + 4 * (1 + (π * sep * (u + 1 / 2)) ^ 2)⁻¹) :=
    ((hm.const_mul 4).add (hp.const_mul 4)).const_mul gammaM
  refine hB.mono' continuous_gMaj.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gMaj_nonneg u)]
  exact gMaj_le u
end Pantera
namespace Pantera.Majorant
lemma integrable_gMaj_mul_cos (t : ℝ) :
    Integrable fun u : ℝ => gMaj u * cos (2 * π * t * u) := by
  refine integrable_gMaj.mono' (continuous_gMaj.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gMaj_nonneg u)]
  exact mul_le_of_le_one_right (gMaj_nonneg u) (abs_cos_le_one _)
lemma integrable_gMaj_mul_sin (t : ℝ) :
    Integrable fun u : ℝ => gMaj u * sin (2 * π * t * u) := by
  refine integrable_gMaj.mono' (continuous_gMaj.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gMaj_nonneg u)]
  exact mul_le_of_le_one_right (gMaj_nonneg u) (abs_sin_le_one _)
lemma integral_tri_cos_of_ne {a : ℝ} (ha : a ≠ 0) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos (a * t) = (1 - cos (a * sep)) / a ^ 2 := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) sep,
      HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y) / a - cos (a * y) / a ^ 2)
        ((sep - t) * cos (a * t)) t := by
    intro t _
    have hlin : HasDerivAt (fun y : ℝ => a * y) a t := by
      have h := (hasDerivAt_id' t).const_mul a
      rwa [mul_one] at h
    have h1 : HasDerivAt (fun y : ℝ => sep - y) (-1) t := (hasDerivAt_id' t).const_sub sep
    have h2 : HasDerivAt (fun y : ℝ => sin (a * y)) (cos (a * t) * a) t := hlin.sin
    have h3 : HasDerivAt (fun y : ℝ => cos (a * y)) (-sin (a * t) * a) t := hlin.cos
    have h4 : HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y))
        (-1 * sin (a * t) + (sep - t) * (cos (a * t) * a)) t := h1.mul h2
    have h5 : HasDerivAt (fun y : ℝ => (sep - y) * sin (a * y) / a - cos (a * y) / a ^ 2)
        ((-1 * sin (a * t) + (sep - t) * (cos (a * t) * a)) / a
          - (-sin (a * t) * a) / a ^ 2) t := (h4.div_const a).sub (h3.div_const (a ^ 2))
    refine h5.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun t : ℝ => (sep - t) * cos (a * t)).intervalIntegrable _ _)]
  simp only [mul_zero, sin_zero, cos_zero]
  ring
lemma integral_tri_cos (a : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos (a * t) = sep ^ 2 / 2 * sinc (a * sep / 2) ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hd : ∀ t ∈ Set.uIcc (0 : ℝ) sep,
        HasDerivAt (fun y : ℝ => sep * y - y * y / 2) ((sep - t) * cos (0 * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun y : ℝ => sep * y) (sep * 1) t := (hasDerivAt_id' t).const_mul sep
      have h2 : HasDerivAt (fun y : ℝ => y * y) (1 * t + t * 1) t :=
        (hasDerivAt_id' t).mul (hasDerivAt_id' t)
      have h3 : HasDerivAt (fun y : ℝ => sep * y - y * y / 2)
          (sep * 1 - (1 * t + t * 1) / 2) t := h1.sub (h2.div_const 2)
      refine h3.congr_deriv ?_
      rw [zero_mul, cos_zero]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun t : ℝ => (sep - t) * cos (0 * t)).intervalIntegrable _ _)]
    simp only [zero_mul, zero_div, sinc_zero]
    ring
  · have hs := sep_ne_zero
    have hx : a * sep / 2 ≠ 0 := div_ne_zero (mul_ne_zero ha hs) two_ne_zero
    have hcos : cos (a * sep) = 1 - 2 * sin (a * sep / 2) ^ 2 := by
      have h := cos_two_mul (a * sep / 2)
      rw [show 2 * (a * sep / 2) = a * sep by ring, cos_sq'] at h
      rw [h]
      ring
    rw [integral_tri_cos_of_ne ha, sinc_of_ne_zero hx, hcos]
    field_simp
    ring
lemma integral_sin_sub (b : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - b * t)
      = sep * sin (π * sep - b * sep / 2) * sinc (b * sep / 2) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [zero_mul, zero_div, sub_zero, sinc_zero, mul_one, intervalIntegral.integral_const,
      smul_eq_mul]
  · have hs := sep_ne_zero
    have hx : b * sep / 2 ≠ 0 := div_ne_zero (mul_ne_zero hb hs) two_ne_zero
    have hgen : ∀ X Y : ℝ, cos (X - Y) - cos (X + Y) = 2 * sin X * sin Y := by
      intro X Y
      rw [cos_sub, cos_add]
      ring
    have key : cos (π * sep - b * sep) - cos (π * sep)
        = 2 * sin (π * sep - b * sep / 2) * sin (b * sep / 2) := by
      have h := hgen (π * sep - b * sep / 2) (b * sep / 2)
      rw [show π * sep - b * sep / 2 - b * sep / 2 = π * sep - b * sep by ring,
        show π * sep - b * sep / 2 + b * sep / 2 = π * sep by ring] at h
      exact h
    rw [intervalIntegral.integral_comp_sub_mul (f := sin) hb, integral_sin, mul_zero, sub_zero,
      key, sinc_of_ne_zero hx, smul_eq_mul]
    field_simp
lemma integral_half1 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos ((2 * π * u + π) * t)
      = sep ^ 2 / 2 * sincN (sep * (u + 1 / 2)) ^ 2 := by
  unfold sincN
  rw [integral_tri_cos, show (2 * π * u + π) * sep / 2 = π * (sep * (u + 1 / 2)) by ring]
lemma integral_half2 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, (sep - t) * cos ((2 * π * u - π) * t)
      = sep ^ 2 / 2 * sincN (sep * (u - 1 / 2)) ^ 2 := by
  unfold sincN
  rw [integral_tri_cos, show (2 * π * u - π) * sep / 2 = π * (sep * (u - 1 / 2)) by ring]
lemma integral_half3 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - (π - 2 * π * u) * t)
      = π * sep ^ 2 * (u + 1 / 2) * sincN (sep * (u + 1 / 2)) * sincN (sep * (u - 1 / 2)) := by
  unfold sincN
  rw [integral_sin_sub,
    show π * sep - (π - 2 * π * u) * sep / 2 = π * (sep * (u + 1 / 2)) by ring,
    show (π - 2 * π * u) * sep / 2 = -(π * (sep * (u - 1 / 2))) by ring, sinc_neg,
    sin_eq_mul_sinc]
  ring
lemma integral_half4 (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, sin (π * sep - (π + 2 * π * u) * t)
      = -(π * sep ^ 2 * (u - 1 / 2) * sincN (sep * (u + 1 / 2)) * sincN (sep * (u - 1 / 2))) := by
  unfold sincN
  rw [integral_sin_sub,
    show π * sep - (π + 2 * π * u) * sep / 2 = -(π * (sep * (u - 1 / 2))) by ring,
    show (π + 2 * π * u) * sep / 2 = π * (sep * (u + 1 / 2)) by ring, sin_neg,
    sin_eq_mul_sinc]
  ring
noncomputable def FMaj (t : ℝ) : ℝ :=
  2 * gammaM / sep ^ 2 * (max (sep - |t|) 0 * cos (π * t) + sin (π * max (sep - |t|) 0) / π)
lemma FMaj_neg (t : ℝ) : FMaj (-t) = FMaj t := by
  unfold FMaj
  rw [abs_neg, mul_neg, cos_neg]
lemma FMaj_eq_zero {t : ℝ} (ht : sep ≤ |t|) : FMaj t = 0 := by
  unfold FMaj
  rw [max_eq_right (by linarith : sep - |t| ≤ 0)]
  simp
lemma FMaj_of_mem {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ sep) :
    FMaj t = 2 * gammaM / sep ^ 2 * ((sep - t) * cos (π * t) + sin (π * (sep - t)) / π) := by
  unfold FMaj
  rw [abs_of_nonneg h0, max_eq_left (by linarith : (0 : ℝ) ≤ sep - t)]
lemma FMaj_zero : FMaj 0 = LMaj := by
  have hs := sep_ne_zero
  have hp := pi_ne_zero
  have hx : π * sep ≠ 0 := mul_ne_zero hp hs
  unfold FMaj LMaj sincN
  rw [abs_zero, sub_zero, max_eq_left sep_pos.le, mul_zero, cos_zero, sinc_of_ne_zero hx]
  field_simp
lemma continuous_FMaj : Continuous FMaj := by
  have hm : Continuous fun t : ℝ => max (sep - |t|) 0 :=
    (continuous_const.sub continuous_abs).max continuous_const
  have h : Continuous fun t : ℝ => 2 * gammaM / sep ^ 2
      * (max (sep - |t|) 0 * cos (π * t) + sin (π * max (sep - |t|) 0) / π) :=
    continuous_const.mul ((hm.mul (by fun_prop)).add
      ((continuous_sin.comp (continuous_const.mul hm)).div_const π))
  exact h
lemma hasCompactSupport_FMaj : HasCompactSupport FMaj :=
  HasCompactSupport.intro (isCompact_Icc (a := -sep) (b := sep)) fun t ht => by
    apply FMaj_eq_zero
    by_contra hcon
    have h := abs_lt.mp (not_le.mp hcon)
    exact ht ⟨h.1.le, h.2.le⟩
lemma integrable_FMaj_mul_cos (u : ℝ) :
    Integrable fun t : ℝ => FMaj t * cos (2 * π * u * t) :=
  (continuous_FMaj.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_FMaj.mul_right
lemma integrable_FMaj_mul_sin (u : ℝ) :
    Integrable fun t : ℝ => FMaj t * sin (2 * π * u * t) :=
  (continuous_FMaj.mul (by fun_prop)).integrable_of_hasCompactSupport
    hasCompactSupport_FMaj.mul_right
lemma integral_FMaj_cos_half (u : ℝ) :
    ∫ t in (0 : ℝ)..sep, FMaj t * cos (2 * π * u * t) = gMaj u / 2 := by
  have hs := sep_ne_zero
  have hp := pi_ne_zero
  have hcongr : ∀ t ∈ Set.uIcc (0 : ℝ) sep, FMaj t * cos (2 * π * u * t) =
      gammaM / sep ^ 2 * ((sep - t) * cos ((2 * π * u + π) * t))
      + gammaM / sep ^ 2 * ((sep - t) * cos ((2 * π * u - π) * t))
      + gammaM / (sep ^ 2 * π) * sin (π * sep - (π - 2 * π * u) * t)
      + gammaM / (sep ^ 2 * π) * sin (π * sep - (π + 2 * π * u) * t) := by
    intro t ht
    rw [Set.uIcc_of_le sep_pos.le] at ht
    rw [FMaj_of_mem ht.1 ht.2]
    have c1 : cos ((2 * π * u + π) * t)
        = cos (2 * π * u * t) * cos (π * t) - sin (2 * π * u * t) * sin (π * t) := by
      rw [add_mul, cos_add]
    have c2 : cos ((2 * π * u - π) * t)
        = cos (2 * π * u * t) * cos (π * t) + sin (2 * π * u * t) * sin (π * t) := by
      rw [sub_mul, cos_sub]
    have s1 : sin (π * sep - (π - 2 * π * u) * t)
        = sin (π * (sep - t)) * cos (2 * π * u * t)
          + cos (π * (sep - t)) * sin (2 * π * u * t) := by
      rw [show π * sep - (π - 2 * π * u) * t = π * (sep - t) + 2 * π * u * t by ring, sin_add]
    have s2 : sin (π * sep - (π + 2 * π * u) * t)
        = sin (π * (sep - t)) * cos (2 * π * u * t)
          - cos (π * (sep - t)) * sin (2 * π * u * t) := by
      rw [show π * sep - (π + 2 * π * u) * t = π * (sep - t) - 2 * π * u * t by ring, sin_sub]
    rw [c1, c2, s1, s2]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_half1 u, integral_half2 u, integral_half3 u, integral_half4 u]
  · unfold gMaj
    field_simp
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
theorem integral_FMaj_mul_cos (u : ℝ) : ∫ t, FMaj t * cos (2 * π * u * t) = gMaj u := by
  have hsupp : Function.support (fun t : ℝ => FMaj t * cos (2 * π * u * t))
      ⊆ Set.Ioc (-sep) sep := by
    intro t ht
    rw [Function.mem_support] at ht
    have hF : FMaj t ≠ 0 := left_ne_zero_of_mul ht
    have hlt : |t| < sep := by
      by_contra hcon
      exact hF (FMaj_eq_zero (not_lt.mp hcon))
    exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2.le⟩
  have hcont : Continuous fun t : ℝ => FMaj t * cos (2 * π * u * t) :=
    continuous_FMaj.mul (by fun_prop)
  have hneg : ∫ t in (-sep)..0, FMaj t * cos (2 * π * u * t)
      = ∫ t in (0 : ℝ)..sep, FMaj t * cos (2 * π * u * t) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := sep)
      (f := fun t : ℝ => FMaj t * cos (2 * π * u * t))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [FMaj_neg, mul_neg, cos_neg]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
    ← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (-sep) 0)
      (hcont.intervalIntegrable 0 sep), hneg, integral_FMaj_cos_half]
  ring
lemma integral_FMaj_mul_sin (u : ℝ) : ∫ t, FMaj t * sin (2 * π * u * t) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => FMaj t * sin (2 * π * u * t)) volume
  simp only [FMaj_neg, mul_neg, sin_neg, integral_neg] at h
  linarith
noncomputable def FMajC (t : ℝ) : ℂ := (FMaj t : ℂ)
lemma continuous_FMajC : Continuous FMajC :=
  Complex.continuous_ofReal.comp continuous_FMaj
lemma integrable_FMajC : Integrable FMajC :=
  (continuous_FMaj.integrable_of_hasCompactSupport hasCompactSupport_FMaj).ofReal
theorem fourier_FMajC (u : ℝ) : 𝓕 FMajC u = ((gMaj u : ℝ) : ℂ) := by
  have hc := integrable_FMaj_mul_cos u
  have hs := integrable_FMaj_mul_sin u
  have hpt : ∀ t : ℝ, Complex.exp (((-2 * π * t * u : ℝ) : ℂ) * Complex.I) • FMajC t
      = ((FMaj t * cos (2 * π * u * t) : ℝ) : ℂ)
        - ((FMaj t * sin (2 * π * u * t) : ℝ) : ℂ) * Complex.I := by
    intro t
    rw [smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show -2 * π * t * u = -(2 * π * u * t) by ring, cos_neg, sin_neg]
    unfold FMajC
    push_cast
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [hpt]
  rw [integral_sub hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal, integral_FMaj_mul_sin,
    integral_FMaj_mul_cos]
  simp
theorem integral_gMaj_mul_cos (t : ℝ) : ∫ u, gMaj u * cos (2 * π * t * u) = FMaj t := by
  have hF : 𝓕 FMajC = fun u : ℝ => ((gMaj u : ℝ) : ℂ) := funext fourier_FMajC
  have hinv : 𝓕⁻ (𝓕 FMajC) t = FMajC t :=
    MeasureTheory.Integrable.fourierInv_fourier_eq integrable_FMajC
      (by rw [hF]; exact integrable_gMaj.ofReal) continuous_FMajC.continuousAt
  rw [hF, Real.fourierInv_eq'] at hinv
  have hc := integrable_gMaj_mul_cos t
  have hs := integrable_gMaj_mul_sin t
  have hpt : ∀ v : ℝ, Complex.exp (((2 * π * inner ℝ v t : ℝ) : ℂ) * Complex.I)
        • ((gMaj v : ℝ) : ℂ)
      = ((gMaj v * cos (2 * π * t * v) : ℝ) : ℂ)
        + ((gMaj v * sin (2 * π * t * v) : ℝ) : ℂ) * Complex.I := by
    intro v
    have hin : inner ℝ v t = t * v := by simp
    rw [hin, smul_eq_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      show 2 * π * (t * v) = 2 * π * t * v by ring]
    push_cast
    ring
  simp_rw [hpt] at hinv
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal] at hinv
  have hre := congrArg Complex.re hinv
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    add_zero] at hre
  exact hre.trans (Complex.ofReal_re _)
end Pantera.Majorant
namespace Pantera
open Majorant
theorem integral_gMaj_cos (t : ℝ) (ht : sep ≤ |t|) :
    ∫ u, gMaj u * cos (2 * π * t * u) = 0 := by
  rw [integral_gMaj_mul_cos, FMaj_eq_zero ht]
end Pantera
end
section
open Real MeasureTheory
open scoped BigOperators
namespace Pantera
open Majorant
theorem lMajBound : LMajBound := by
  unfold LMajBound LMaj sincN
  have hpos : 0 < π * sep := mul_pos pi_pos sep_pos
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = π * (3 / 20) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hylo : (4712388 : ℝ) / 10000000 ≤ y := by
    rw [hy]
    have h := pi_gt_d6
    norm_num at h
    linarith
  have hyhi : y ≤ (47123895 : ℝ) / 100000000 := by
    rw [hy]
    have h := pi_lt_d6
    norm_num at h
    linarith
  have h2 : (22206 : ℝ) / 100000 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hylo) (sub_nonneg.mpr hylo)]
  have h2' : y ^ 2 ≤ (22207 : ℝ) / 100000 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hyhi) hy0]
  have h4 : y ^ 4 ≤ (4932 : ℝ) / 100000 := by
    have e : y ^ 4 = y ^ 2 * y ^ 2 := by ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2') (sq_nonneg y)]
  have hsin : sin (π * sep) = sin y := by
    rw [hy, ← sin_pi_sub]
    congr 1
    unfold sep
    ring
  have hpoly : Meshuggah.Majorant.sinPoly y (0 + 1 + 1 + 1)
      = y * (1 - y ^ 2 / 6 + y ^ 4 / 120) := by
    rw [Meshuggah.Majorant.sinPoly_succ, Meshuggah.Majorant.sinPoly_succ,
      Meshuggah.Majorant.sinPoly_succ, Meshuggah.Majorant.sinPoly_zero]
    norm_num [Nat.factorial]
    ring
  have hup : sin y ≤ Meshuggah.Majorant.sinPoly y (2 * 1 + 1) :=
    Meshuggah.Majorant.sin_le_sinPoly hy0 1
  have hQ : 1 - y ^ 2 / 6 + y ^ 4 / 120 ≤ (963401 : ℝ) / 1000000 := by linarith
  have key : sin (π * sep) ≤ y * ((963401 : ℝ) / 1000000) := by
    rw [hsin]
    exact hup.trans ((le_of_eq hpoly).trans (mul_le_mul_of_nonneg_left hQ hy0))
  have hr : sin (π * sep) / (π * sep) ≤ 3 / 17 * ((963401 : ℝ) / 1000000) := by
    rw [div_le_iff₀ hpos]
    refine key.trans (le_of_eq ?_)
    rw [hy]
    unfold sep
    ring
  rw [sinc_of_ne_zero hpos.ne']
  have hc : 2 * gammaM / sep = 26 / 17 := by
    unfold gammaM sep
    norm_num
  rw [hc]
  linarith
end Pantera
namespace Pantera.Majorant
noncomputable def quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * cos (2 * π * (y i - y j) * u)
lemma quadForm_eq {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) :
    quadForm y x u = (∑ i, x i * cos (2 * π * y i * u)) ^ 2
      + (∑ i, x i * sin (2 * π * y i * u)) ^ 2 := by
  unfold quadForm
  rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show 2 * π * (y i - y j) * u = 2 * π * y i * u - 2 * π * y j * u by ring, cos_sub]
  ring
lemma quadForm_nonneg {ι : Type} [Fintype ι] (y x : ι → ℝ) (u : ℝ) : 0 ≤ quadForm y x u := by
  rw [quadForm_eq]
  positivity
lemma continuous_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) : Continuous (quadForm y x) := by
  have h : Continuous fun u : ℝ => ∑ i, ∑ j, x i * x j * cos (2 * π * (y i - y j) * u) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => by fun_prop
  exact h
lemma integrable_gMaj_mul_term (a c : ℝ) :
    Integrable fun u : ℝ => gMaj u * (c * cos (2 * π * a * u)) := by
  have h := (integrable_gMaj_mul_cos a).const_mul c
  have e : (fun u : ℝ => gMaj u * (c * cos (2 * π * a * u)))
      = fun u : ℝ => c * (gMaj u * cos (2 * π * a * u)) := by
    funext u; ring
  rw [e]
  exact h
lemma quadForm_expand {ι : Type} [Fintype ι] (y x : ι → ℝ) :
    (fun u : ℝ => gMaj u * quadForm y x u)
      = fun u : ℝ => ∑ i, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) := by
  funext u
  simp only [quadForm, Finset.mul_sum]
lemma integrable_gMaj_mul_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ) :
    Integrable fun u : ℝ => gMaj u * quadForm y x u := by
  rw [quadForm_expand]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_gMaj_mul_term (y i - y j) (x i * x j)
theorem integral_gMaj_mul_quadForm {ι : Type} [Fintype ι] (y x : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → sep ≤ |y i - y j|) :
    ∫ u, gMaj u * quadForm y x u = LMaj * ∑ i, x i ^ 2 := by
  classical
  have hval : ∀ i j, ∫ u, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u))
      = if i = j then LMaj * x i ^ 2 else 0 := by
    intro i j
    have e : (fun u : ℝ => gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)))
        = fun u : ℝ => x i * x j * (gMaj u * cos (2 * π * (y i - y j) * u)) := by
      funext u; ring
    rw [e, integral_const_mul]
    split_ifs with hij
    · subst hij
      rw [sub_self, integral_gMaj_mul_cos, FMaj_zero]
      ring
    · rw [integral_gMaj_cos _ (hsep i j hij), mul_zero]
  rw [quadForm_expand]
  calc ∫ u, ∑ i, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u))
      = ∑ i, ∫ u, ∑ j, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) :=
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          integrable_gMaj_mul_term (y i - y j) (x i * x j)
    _ = ∑ i, ∑ j, ∫ u, gMaj u * (x i * x j * cos (2 * π * (y i - y j) * u)) :=
        Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
          integrable_gMaj_mul_term (y i - y j) (x i * x j)
    _ = ∑ i, ∑ j, if i = j then LMaj * x i ^ 2 else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hval i j
    _ = ∑ i, LMaj * x i ^ 2 := Finset.sum_congr rfl fun i _ => by simp
    _ = LMaj * ∑ i, x i ^ 2 := (Finset.mul_sum _ _ _).symm
end Pantera.Majorant
namespace Pantera
open Majorant
theorem separatedBound : SeparatedBound := by
  intro ι _ y x w hsep hw hw0 hwg
  have hDnn := quadForm_nonneg y x
  have hgD := integrable_gMaj_mul_quadForm y x
  have hwD : Integrable fun u : ℝ => w u * quadForm y x u := by
    refine hgD.mono' (hw.mul (continuous_quadForm y x).measurable).aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 u) (hDnn u))]
    exact mul_le_mul_of_nonneg_right (hwg u) (hDnn u)
  have h1 : ∫ u, w u * quadForm y x u ≤ ∫ u, gMaj u * quadForm y x u :=
    integral_mono hwD hgD fun u => mul_le_mul_of_nonneg_right (hwg u) (hDnn u)
  rw [integral_gMaj_mul_quadForm y x hsep] at h1
  exact h1
end Pantera
end
section
/-
Concrete majorant for Samuel Lavery's attempt-016 AM window.

The imported AM definitions/bounds retain their original Apache-2.0 and
transitive notices in Attempt016Base. The two-sinc Fourier identities and
Taylor inequalities below are reused from Simple673/Distinct839, with an
explicit changed amplitude 7/10. No old-profile domination is assumed.

Source-only draft: no compilation or kernel-acceptance claim.
-/
noncomputable section
open Real MeasureTheory
open scoped BigOperators
namespace Opeth.AMMajorant
noncomputable def scaledMajorant (s : ℝ) : ℝ := (14 / 13) * Pantera.gMaj s
lemma rho_pos : 0 < AMW.rhoAM := by
  unfold AMW.rhoAM
  exact one_div_pos.mpr AMW.K0AM_pos
lemma rho_le : AMW.rhoAM ≤ (109 / 100 : ℝ) := by
  have h := AMW.G.rhoAM_bounds.2
  norm_num at h ⊢
  linarith
lemma pi_coarse : (157 / 50 : ℝ) ≤ π ∧ π ≤ 22 / 7 := by
  have h := AMW.G.pi_bounds15
  constructor <;> linarith [h.1, h.2]
lemma scaledMajorant_eq (s : ℝ) :
    scaledMajorant s = (7 / 10) *
      (sinc (π * (17 / 20) * (s - 1 / 2)) +
        sinc (π * (17 / 20) * (s + 1 / 2))) ^ 2 := by
  simp only [scaledMajorant, Pantera.gMaj, Pantera.gammaM,
    Pantera.sep, Meshuggah.sincN, mul_assoc]
  ring
lemma sinc_lower (z : ℝ) :
    1 - z ^ 2 / 6 + z ^ 4 / 120 - z ^ 6 / 5040 ≤ sinc z := by
  have h := Meshuggah.Majorant.sincPoly_le_sinc z 1
  norm_num [Meshuggah.Majorant.sincPoly] at h
  nlinarith only [h]
lemma cos_core_upper (s : ℝ) :
    cos (sqrt 2 * s) ≤ 1 - s ^ 2 + s ^ 4 / 6 := by
  have h2 : (sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : (sqrt 2 : ℝ) ^ 4 = 4 := by
    calc (sqrt 2 : ℝ) ^ 4 = ((sqrt 2) ^ 2) ^ 2 := by ring
      _ = 4 := by rw [h2]; norm_num
  calc cos (sqrt 2 * s) ≤ Meshuggah.Majorant.cosPoly (sqrt 2 * s) 3 :=
      Meshuggah.Majorant.cos_le_cosPoly (sqrt 2 * s) 1
    _ = 1 - s ^ 2 + s ^ 4 / 6 := by
      norm_num [Meshuggah.Majorant.cosPoly, mul_pow, h2, h4] <;> ring
lemma profile_upper {s : ℝ} (hs : |s| ≤ 1 / 2) :
    AMW.rhoAM * AMW.vAM s ≤
      (109 / 100) * (213743119 / 200000000 - s ^ 2 + s ^ 4 / 6) := by
  have hv0 : 0 ≤ AMW.vAM s := le_trans (by norm_num) (AMW.vAM_ge_core hs)
  have hv : AMW.vAM s ≤ 213743119 / 200000000 - s ^ 2 + s ^ 4 / 6 := by
    rw [AMW.vAM_eq]
    linarith [cos_core_upper s, (abs_le.mp (AMW.abs_pAM_le s)).2]
  exact (mul_le_mul_of_nonneg_right rho_le hv0).trans
    (mul_le_mul_of_nonneg_left hv (by norm_num))
private lemma frequency_powers :
    (π * (17 / 20) : ℝ) ^ 2 ≤ 357 / 50 ∧
    31684 / 625 ≤ (π * (17 / 20) : ℝ) ^ 4 ∧
    (π * (17 / 20) : ℝ) ^ 6 ≤ 364 := by
  set d : ℝ := π * (17 / 20)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hlo : (2669 / 1000 : ℝ) ≤ d := by
    dsimp [d]; linarith [pi_coarse.1]
  have hhi : d ≤ (187 / 70 : ℝ) := by
    dsimp [d]; linarith [pi_coarse.2]
  have h2lo : (178 / 25 : ℝ) ≤ d ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hlo)
      (show 0 ≤ d + 2669 / 1000 by positivity)
    nlinarith only [h]
  have h2hi : d ^ 2 ≤ (357 / 50 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ 187 / 70 + d by positivity)
    nlinarith only [h]
  have h4lo : (31684 / 625 : ℝ) ≤ d ^ 4 := by
    have h := mul_nonneg (sub_nonneg.mpr h2lo)
      (show 0 ≤ d ^ 2 + 178 / 25 by positivity)
    nlinarith only [h]
  have h6hi : d ^ 6 ≤ (364 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr h2hi)
      (show 0 ≤ (357 / 50 : ℝ) ^ 2 + (357 / 50) * d ^ 2 + (d ^ 2) ^ 2 by
        positivity)
    nlinarith only [h]
  exact ⟨h2hi, h4lo, h6hi⟩
lemma sinc_sum_lower {s : ℝ} (hs : |s| ≤ 1 / 2) :
    29 / 20 - (5 / 4) * s ^ 2 ≤
      sinc (π * (17 / 20) * (s - 1 / 2)) +
        sinc (π * (17 / 20) * (s + 1 / 2)) := by
  set d : ℝ := π * (17 / 20)
  set x : ℝ := s ^ 2
  have hx0 : 0 ≤ x := sq_nonneg s
  have hx1 : x ≤ 1 / 4 := by
    have h := abs_le.mp hs
    dsimp [x]
    nlinarith [h.1, h.2]
  have hd := frequency_powers
  change d ^ 2 ≤ 357 / 50 ∧ 31684 / 625 ≤ d ^ 4 ∧ d ^ 6 ≤ 364 at hd
  have hT :
      2 - d ^ 2 / 6 * (1 / 2 + 2 * x) +
          d ^ 4 / 120 * (1 / 8 + 3 * x + 2 * x ^ 2) -
          d ^ 6 / 5040 * (1 / 32 + (15 / 8) * x + (15 / 2) * x ^ 2 + 2 * x ^ 3)
        ≤ sinc (d * (s - 1 / 2)) + sinc (d * (s + 1 / 2)) := by
    calc
      _ = (1 - (d * (s - 1 / 2)) ^ 2 / 6 + (d * (s - 1 / 2)) ^ 4 / 120 -
              (d * (s - 1 / 2)) ^ 6 / 5040) +
          (1 - (d * (s + 1 / 2)) ^ 2 / 6 + (d * (s + 1 / 2)) ^ 4 / 120 -
              (d * (s + 1 / 2)) ^ 6 / 5040) := by dsimp [x]; ring
      _ ≤ _ := add_le_add (sinc_lower _) (sinc_lower _)
  have hm2 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd.1 (show (0 : ℝ) ≤ 6 by norm_num))
    (show 0 ≤ 1 / 2 + 2 * x by positivity)
  have hm4 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd.2.1 (show (0 : ℝ) ≤ 120 by norm_num))
    (show 0 ≤ 1 / 8 + 3 * x + 2 * x ^ 2 by positivity)
  have hm6 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd.2.2 (show (0 : ℝ) ≤ 5040 by norm_num))
    (show 0 ≤ 1 / 32 + (15 / 8) * x + (15 / 2) * x ^ 2 + 2 * x ^ 3 by positivity)
  have hC :
      (2 - 119 / 200 + 7921 / 150000 - 13 / 5760) +
          (-119 / 50 + 7921 / 6250 - 13 / 96) * x +
          (31684 / 37500 - 13 / 24) * x ^ 2 - (13 / 90) * x ^ 3
        ≤ sinc (d * (s - 1 / 2)) + sinc (d * (s + 1 / 2)) := by
    nlinarith only [hT, hm2, hm4, hm6]
  have hlast : 0 ≤ (31684 / 37500 - 13 / 24 : ℝ) - (13 / 90) * x := by
    linarith only [hx1]
  have hprod := mul_nonneg (sq_nonneg x) hlast
  change 29 / 20 - (5 / 4) * x ≤ _
  nlinarith only [hC, hx0, hprod]
theorem normalized_profile_margin {s : ℝ} (hs : |s| ≤ 1 / 2) :
    AMW.rhoAM * AMW.vAM s + 1 / 1000 ≤ scaledMajorant s := by
  set x : ℝ := s ^ 2
  set S : ℝ := sinc (π * (17 / 20) * (s - 1 / 2)) +
    sinc (π * (17 / 20) * (s + 1 / 2))
  have hx0 : 0 ≤ x := sq_nonneg s
  have hx1 : x ≤ 1 / 4 := by
    have h := abs_le.mp hs
    dsimp [x]
    nlinarith [h.1, h.2]
  have hS : 29 / 20 - (5 / 4) * x ≤ S := sinc_sum_lower hs
  have hp : 0 ≤ 29 / 20 - (5 / 4) * x := by linarith
  have hS0 : 0 ≤ S := hp.trans hS
  have hsquare := mul_nonneg (sub_nonneg.mpr hS)
    (add_nonneg hS0 hp)
  have hq := mul_nonneg (sub_nonneg.mpr hx1)
    (show 0 ≤ (579 / 400 : ℝ) - (2189 / 2400) * (x + 1 / 4) by linarith)
  have hv := profile_upper hs
  have h4 : s ^ 4 = x ^ 2 := by dsimp [x]; ring
  rw [h4] at hv
  change AMW.rhoAM * AMW.vAM s ≤ (109 / 100) * (213743119 / 200000000 - x + x ^ 2 / 6) at hv
  rw [scaledMajorant_eq]
  change AMW.rhoAM * AMW.vAM s + 1 / 1000 ≤ (7 / 10) * S ^ 2
  nlinarith only [hv, hsquare, hq]
theorem normalized_profile_le_scaled_majorant {s : ℝ} (hs : |s| ≤ 1 / 2) :
    AMW.rhoAM * AMW.vAM s ≤ scaledMajorant s := by
  linarith [normalized_profile_margin hs]
end Opeth.AMMajorant
end
section
/-
Actual finite-height separated Gram bound for the attempt-016 AM window.

Copyright (c) 2026 R. Arun Chandru. Apache-2.0.
The AM objects and their proofs retain Samuel Lavery's Apache-2.0 and
transitive notices in Attempt016Base. Generic Poisson/sum-of-squares
manipulations are adapted from Kristian Muri Knausgard's Apache-2.0
Distinct839/ZeroKernel/{Window,Separated}.lean. This module changes the realized
window, domination, and normalization explicitly to the actual AM family.

SOURCE ONLY: not compiled. No entrywise limiting-kernel approximation,
new analytic hypothesis, numerical oracle, or original Simple673 local
inequality is used. The whole finite-height matrix is bounded directly.
-/
noncomputable section
open Real Filter Topology MeasureTheory Zeta23
open scoped BigOperators
namespace Opeth.AMSeparatedGram
private lemma re_paperFT_ofReal {g : ℝ → ℝ} (hg : Continuous g)
    (hs : HasCompactSupport g) (r : ℝ) :
    (paperFT (fun u => (g u : ℂ)) r).re = ∫ u, g u * cos (r * u) := by
  have hint : Integrable (fun u : ℝ =>
      (g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (Complex.continuous_ofReal.comp hg).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    · refine hs.mono fun u hu => ?_
      rw [Function.mem_support] at hu ⊢
      intro h0
      apply hu
      rw [h0, Complex.ofReal_zero, zero_mul]
  have h := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at h
  rw [paperFT_def, ← h]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have e : Complex.I * (r : ℂ) * (u : ℂ) = ((r * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  show ((g u : ℂ) * Complex.exp (Complex.I * (r : ℂ) * (u : ℂ))).re =
    g u * cos (r * u)
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
private lemma VPhiR_eq_integral {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (r : ℝ) :
    AdmWindow.VPhiR v r = ∫ u, v u ^ 2 * cos (r * u) :=
  re_paperFT_ofReal hW.sq_continuous hW.sq_hasCompactSupport r
private lemma integrable_sq_mul_cos {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (r : ℝ) :
    Integrable (fun u => v u ^ 2 * cos (r * u)) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hW.sq_continuous.mul (continuous_cos.comp (continuous_const.mul continuous_id))) ?_
  refine hW.sq_hasCompactSupport.mono fun u hu => ?_
  rw [Function.mem_support] at hu ⊢
  intro h0
  apply hu
  rw [h0, zero_mul]
private lemma finite_sum_le_hasSum {f : ℤ → ℝ} {S : ℝ} (d : ℕ)
    (hf : HasSum f S) (h0 : ∀ k, 0 ≤ f k) :
    ∑ k : Fin d, f ((k : ℕ) : ℤ) ≤ S := by
  classical
  have he : ∑ k : Fin d, f ((k : ℕ) : ℤ) =
      ∑ k ∈ (Finset.range d).map Nat.castEmbedding, f k := by
    rw [Finset.sum_map]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ℤ)) d
  rw [he]
  exact sum_le_hasSum _ (fun k _ => h0 k) hf
private lemma poisson_square {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) (T : ℝ) {ι : Type} [Fintype ι]
    (γ z : ι → ℝ) :
    HasSum (fun k : ℤ =>
        (∑ i, z i * AdmWindow.vHatR v (γ i - (T + k * (2 * π / L)))) ^ 2)
      (L * ∑ i, ∑ j, z i * z j * AdmWindow.VPhiR v (γ i - γ j)) := by
  have h : HasSum (fun k : ℤ => ∑ i, ∑ j, z i * z j *
        (AdmWindow.vHatR v (γ i - (T + k * (2 * π / L))) *
          AdmWindow.vHatR v (γ j - (T + k * (2 * π / L)))))
      (∑ i, ∑ j, z i * z j * (L * AdmWindow.VPhiR v (γ i - γ j))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (hW.hasSum_vHatR_mul T (γ i) (γ j)).mul_left (z i * z j)
  convert h using 1
  · funext k
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
private lemma cosine_integral {v : ℝ → ℝ} {L w c : ℝ}
    (hW : AdmWindow v L w c) {ι : Type} [Fintype ι] (γ z : ι → ℝ) :
    ∑ i, ∑ j, z i * z j * AdmWindow.VPhiR v (γ i - γ j) =
      ∫ u, v u ^ 2 * ∑ i, ∑ j, z i * z j * cos ((γ i - γ j) * u) := by
  have hint : ∀ i j,
      Integrable (fun u => z i * z j * (v u ^ 2 * cos ((γ i - γ j) * u))) :=
    fun i j => (integrable_sq_mul_cos hW (γ i - γ j)).const_mul _
  calc
    _ = ∑ i, ∑ j, ∫ u, z i * z j * (v u ^ 2 * cos ((γ i - γ j) * u)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [VPhiR_eq_integral hW, integral_const_mul]
    _ = ∫ u, ∑ i, ∑ j, z i * z j * (v u ^ 2 * cos ((γ i - γ j) * u)) := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hint i j]
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
private lemma change_scale (f : ℝ → ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u, f u = L * ∫ s, f (L * s) := by
  rw [Measure.integral_comp_mul_left f L, smul_eq_mul,
    abs_of_pos (inv_pos.mpr hL), ← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul]
theorem scaled_separated_bound (ι : Type) [Fintype ι] (y z : ι → ℝ)
    (w : ℝ → ℝ) (hsep : ∀ i j, i ≠ j → 17 / 20 ≤ |y i - y j|)
    (hw : Measurable w) (hw0 : ∀ s, 0 ≤ w s)
    (hwM : ∀ s, w s ≤ AMMajorant.scaledMajorant s) :
    (∫ s, w s * ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s))
      ≤ (1253 / 650) * ∑ i, z i ^ 2 := by
  have hsmall : ∀ s, (13 / 14 : ℝ) * w s ≤ Pantera.gMaj s := by
    intro s
    have h := hwM s
    unfold AMMajorant.scaledMajorant at h
    linarith
  have hs : ∀ i j, i ≠ j → Pantera.sep ≤ |y i - y j| := by
    simpa only [Pantera.sep] using hsep
  have h := Pantera.separatedBound ι y z (fun s => (13 / 14) * w s) hs
    (measurable_const.mul hw) (fun s => mul_nonneg (by norm_num) (hw0 s)) hsmall
  have hscale :
      (∫ s, ((13 / 14 : ℝ) * w s) *
        ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s)) =
      (13 / 14 : ℝ) *
        ∫ s, w s * ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun s => by ring)
  rw [hscale] at h
  have hmass : Pantera.LMaj ≤ (179 / 100 : ℝ) := Pantera.lMajBound
  have hn : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm := mul_le_mul_of_nonneg_right hmass hn
  linarith
noncomputable def realizedWeight (P : Params) (T s : ℝ) : ℝ :=
  AMW.rhoAM * AMW.MAM * AMW.WAM P T (P.L T * s) ^ 2
theorem realizedWeight_nonneg (P : Params) (T s : ℝ) :
    0 ≤ realizedWeight P T s :=
  mul_nonneg (mul_nonneg AMMajorant.rho_pos.le AMW.MAM_pos.le) (sq_nonneg _)
theorem realizedWeight_measurable {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T) : Measurable (realizedWeight P T) := by
  have hW := AMW.admWindow_WAM hP T h8
  exact (continuous_const.mul
    ((hW.continuous.comp (continuous_const.mul continuous_id)).pow 2)).measurable
theorem realizedWeight_le {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T) (s : ℝ) :
    realizedWeight P T s ≤ AMMajorant.scaledMajorant s := by
  have hW := AMW.admWindow_WAM hP T h8
  have hL := hW.L_pos
  have hw : 0 < P.w := by linarith [hP.one_le_w]
  by_cases hs : |s| ≤ 1 / 2
  · have hsq : AMW.WAM P T (P.L T * s) ^ 2 =
        (AMW.vAM s / AMW.MAM) * Taper.phi P.ϱ (P.L T) P.w (P.L T * s) ^ 2 := by
      rw [AMW.WAM, AMW.phiW_sq_eq hP.taper hw hL, AMW.hW,
        mul_div_cancel_left₀ s hL.ne']
    have ht0 : 0 ≤ Taper.phi P.ϱ (P.L T) P.w (P.L T * s) :=
      Taper.phi_nonneg hP.taper _
    have ht1 : Taper.phi P.ϱ (P.L T) P.w (P.L T * s) ≤ 1 :=
      Taper.phi_le_one hP.taper _
    have hv : 0 ≤ AMW.vAM s := (by norm_num : (0 : ℝ) ≤ 681 / 1000).trans
      (AMW.vAM_ge_core hs)
    have he : realizedWeight P T s = AMW.rhoAM * AMW.vAM s *
        Taper.phi P.ϱ (P.L T) P.w (P.L T * s) ^ 2 := by
      rw [realizedWeight, hsq]
      field_simp [AMW.MAM_pos.ne'] <;> ring
    rw [he]
    exact (mul_le_of_le_one_right (mul_nonneg AMMajorant.rho_pos.le hv)
      (pow_le_one₀ ht0 ht1)).trans (AMMajorant.normalized_profile_le_scaled_majorant hs)
  · have hfar : P.L T / 2 ≤ |P.L T * s| := by
      rw [abs_mul, abs_of_pos hL]
      have := lt_of_not_ge hs
      nlinarith
    have hzero := hW.support (P.L T * s) hfar
    rw [realizedWeight, hzero, zero_pow (by omega : 2 ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (Pantera.gMaj_nonneg s)
noncomputable def realKernel (P : Params) (T γ γ' : ℝ) : ℝ :=
  ((AMW.atAM P T).a T * P.L T ^ 2)⁻¹ *
    ∑ k : Fin (P.d T),
      AdmWindow.vHatR (AMW.WAM P T)
        (γ - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / P.L T))) *
      AdmWindow.vHatR (AMW.WAM P T)
        (γ' - (T + (((k : ℕ) : ℤ) : ℝ) * (2 * π / P.L T)))
theorem realKernel_form_le {P : Params} (hP : P.Valid) (T : ℝ)
    (h8 : 8 * P.w ≤ P.L T) (ha : 0 < (AMW.atAM P T).a T)
    (ι : Type) [Fintype ι] (γ z : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 17 / 20 ≤
      |P.L T * (γ i - T) / (2 * π) - P.L T * (γ j - T) / (2 * π)|) :
    (∑ i, ∑ j, z i * realKernel P T (γ i) (γ j) * z j) ≤
      (AMW.rhoAM * AMW.MAM * (AMW.atAM P T).a T)⁻¹ *
        (1253 / 650) * ∑ i, z i ^ 2 := by
  have hW := AMW.admWindow_WAM hP T h8
  set L := P.L T with hLdef
  set a := (AMW.atAM P T).a T with hadef
  have hL : 0 < L := hW.L_pos
  have hc : 0 < a * L ^ 2 := by positivity
  set F : ι → ℤ → ℝ := fun i k =>
    AdmWindow.vHatR (AMW.WAM P T) (γ i - (T + k * (2 * π / L))) with hFdef
  set y : ι → ℝ := fun i => L * (γ i - T) / (2 * π) with hydef
  have hA : (∑ i, ∑ j, z i * realKernel P T (γ i) (γ j) * z j) =
      (a * L ^ 2)⁻¹ * ∑ k : Fin (P.d T), (∑ i, z i * F i ((k : ℕ) : ℤ)) ^ 2 := by
    have hpt : ∀ i j, z i * realKernel P T (γ i) (γ j) * z j =
        ∑ k : Fin (P.d T), (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) := by
      intro i j
      simp only [realKernel, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      dsimp [F, a, L]
      push_cast
      ring
    rw [Finset.mul_sum]
    calc
      _ = ∑ i, ∑ j, ∑ k : Fin (P.d T), (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpt i j
      _ = ∑ i, ∑ k : Fin (P.d T), ∑ j, (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k : Fin (P.d T), ∑ i, ∑ j, (a * L ^ 2)⁻¹ *
          ((z i * F i ((k : ℕ) : ℤ)) * (z j * F j ((k : ℕ) : ℤ))) :=
        Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [sq (∑ i, z i * F i ((k : ℕ) : ℤ)), Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
  have hB : (∑ k : Fin (P.d T), (∑ i, z i * F i ((k : ℕ) : ℤ)) ^ 2) ≤
      L * ∑ i, ∑ j, z i * z j * AdmWindow.VPhiR (AMW.WAM P T) (γ i - γ j) :=
    finite_sum_le_hasSum (P.d T) (poisson_square hW T γ z) (fun k => sq_nonneg _)
  have hD : (∑ i, ∑ j, z i * z j * AdmWindow.VPhiR (AMW.WAM P T) (γ i - γ j)) =
      L * ((AMW.rhoAM * AMW.MAM)⁻¹ *
        ∫ s, realizedWeight P T s *
          ∑ i, ∑ j, z i * z j * cos (2 * π * (y i - y j) * s)) := by
    rw [cosine_integral hW γ z,
      change_scale (fun u => AMW.WAM P T u ^ 2 *
        ∑ i, ∑ j, z i * z j * cos ((γ i - γ j) * u)) hL]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun s => ?_)
    have harg : ∀ i j, (γ i - γ j) * (L * s) = 2 * π * (y i - y j) * s := by
      intro i j
      dsimp [y]
      field_simp <;> ring
    simp only [harg, realizedWeight]
    change _ = (AMW.rhoAM * AMW.MAM)⁻¹ *
      (AMW.rhoAM * AMW.MAM * AMW.WAM P T (L * s) ^ 2 * _)
    field_simp [AMMajorant.rho_pos.ne', AMW.MAM_pos.ne'] <;> ring
  have hE := scaled_separated_bound ι y z (realizedWeight P T) hsep
    (realizedWeight_measurable hP T h8) (realizedWeight_nonneg P T)
    (realizedWeight_le hP T h8)
  rw [hA]
  calc
    _ ≤ (a * L ^ 2)⁻¹ * (L * (L * ((AMW.rhoAM * AMW.MAM)⁻¹ *
        ((1253 / 650) * ∑ i, z i ^ 2)))) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hc.le)
      refine hB.trans ?_
      rw [hD]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hE (inv_nonneg.mpr
            (mul_nonneg AMMajorant.rho_pos.le AMW.MAM_pos.le))) hL.le) hL.le
    _ = _ := by
      dsimp [a]
      field_simp [hL.ne', ha.ne', AMMajorant.rho_pos.ne', AMW.MAM_pos.ne']
      <;> ring
lemma normalization_limit_identity : AMW.rhoAM * AMW.MAM * AMW.aInf = 1 := by
  rw [AMW.aInf_eq]
  change (1 / AMW.K0AM) * AMW.MAM * (AMW.K0AM / AMW.MAM) = 1
  field_simp [AMW.K0AM_pos.ne', AMW.MAM_pos.ne']
/-- The finite-height normalization tends to one; retain explicit slack51/50. -/
theorem eventually_normalization {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 0 < (AMW.atAM P T).a T ∧
      (AMW.rhoAM * AMW.MAM * (AMW.atAM P T).a T)⁻¹ ≤ (51 / 50 : ℝ) := by
  have ht : Tendsto (fun T => (AMW.atAM P T).a T) atTop (𝓝 AMW.aInf) := by
    convert AMW.tendsto_aW hP using 1
    funext T
    rw [AMW.atAM_a hP T] <;> rfl
  have hnear : (50 / 51 : ℝ) * AMW.aInf < AMW.aInf := by
    nlinarith [AMW.aInf_pos]
  filter_upwards [ht.eventually (lt_mem_nhds hnear)] with T hT
  have ha : 0 < (AMW.atAM P T).a T :=
    lt_trans (mul_pos (by norm_num) AMW.aInf_pos) hT
  refine ⟨ha, ?_⟩
  have hr : 0 < AMW.rhoAM * AMW.MAM := mul_pos AMMajorant.rho_pos AMW.MAM_pos
  have hh := mul_le_mul_of_nonneg_left hT.le hr.le
  have hi := normalization_limit_identity
  rw [inv_eq_one_div, div_le_iff₀ (mul_pos hr ha)]
  nlinarith only [hh, hi]
theorem eventually_realKernel_form_le {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 0 < (AMW.atAM P T).a T ∧
      ∀ (ι : Type) [Fintype ι] (γ z : ι → ℝ),
        (∀ i j, i ≠ j → 17 / 20 ≤
          |P.L T * (γ i - T) / (2 * π) - P.L T * (γ j - T) / (2 * π)|) →
        (∑ i, ∑ j, z i * realKernel P T (γ i) (γ j) * z j) ≤
          (63903 / 32500) * ∑ i, z i ^ 2 := by
  filter_upwards [Zeta23.ThmD.eventually_w8 hP, eventually_normalization hP] with T h8 hnorm
  refine ⟨hnorm.1, ?_⟩
  intro ι _ γ z hsep
  have h := realKernel_form_le hP T h8 hnorm.1 ι γ z hsep
  have hn : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm' := mul_le_mul_of_nonneg_right hnorm.2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1253 / 650) hn)
  calc
    _ ≤ _ := h
    _ ≤ (51 / 50 : ℝ) * ((1253 / 650) * ∑ i, z i ^ 2) := by
      simpa only [mul_assoc] using hnorm'
    _ = (63903 / 32500) * ∑ i, z i ^ 2 := by ring
/-- Exact identification with the retained matrix used by the AM counting consumer. -/
theorem gram_re_eq (Z : ZeroConfig) {P : Params} (hP : P.Valid) (T : ℝ)
    (ha : 0 < (AMW.atAM P T).a T)
    (u v : Zeta23Ext.Bridge.retained Z (AMW.atAM P T) T) :
    (Zeta23Ext.Bridge.gram Z (AMW.atAM P T) T u v).re =
      realKernel P T (u.1 : ℂ).im (v.1 : ℂ).im := by
  have hc : 0 ≤ Zeta23Ext.Bridge.aL2 (AMW.atAM P T) T := by
    unfold Zeta23Ext.Bridge.aL2
    exact mul_nonneg ha.le (sq_nonneg _)
  rw [Zeta23Ext.Bridge.gram_apply Z (AMW.atAM P T) T
    (Zeta23Ext.Bridge.phiHatReal_atAM hP T) hc, Complex.ofReal_re]
  simp only [Zeta23Ext.Bridge.aL2, Zeta23Ext.Bridge.atAM_L,
    Zeta23Ext.Bridge.atAM_phiHatR_eq hP T] <;> rfl
theorem eventually_gram_form_le (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι]
      (e : ι → Zeta23Ext.Bridge.retained Z (Zeta23Ext.Bridge.mtParams T) T)
      (z : ι → ℝ),
      (∀ i j, i ≠ j → 17 / 20 ≤
        |Zeta23Ext.Bridge.xret Z (Zeta23Ext.Bridge.mtParams T) T (e i) -
          Zeta23Ext.Bridge.xret Z (Zeta23Ext.Bridge.mtParams T) T (e j)|) →
      (∑ i, ∑ j, z i *
        (Zeta23Ext.Bridge.gram Z (Zeta23Ext.Bridge.mtParams T) T (e i) (e j)).re * z j)
        ≤ (63903 / 32500) * ∑ i, z i ^ 2 := by
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  filter_upwards [eventually_realKernel_form_le hP] with T hT
  intro ι _ e z hsep
  have hs : ∀ i j, i ≠ j → 17 / 20 ≤
      |(paramsOf stdProfile 1).L T * ((e i).1.val.im - T) / (2 * π) -
        (paramsOf stdProfile 1).L T * ((e j).1.val.im - T) / (2 * π)| := hsep
  have h := hT.2 ι (fun i => ((e i).1 : ℂ).im) z hs
  have heq : ∀ i j,
      (Zeta23Ext.Bridge.gram Z (Zeta23Ext.Bridge.mtParams T) T (e i) (e j)).re =
        realKernel (paramsOf stdProfile 1) T ((e i).1 : ℂ).im ((e j).1 : ℂ).im :=
    fun i j => gram_re_eq Z hP T hT.1 (e i) (e j)
  simpa only [heq] using h
end Opeth.AMSeparatedGram
end
section
open scoped BigOperators ComplexOrder
open Real
noncomputable section
namespace Meshuggah
end Meshuggah
end
section
open Zeta23.ZeroSide.RankTraceMult
namespace Meshuggah.Gram
end Meshuggah.Gram
end
section
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace Meshuggah.Gram
@[simp] lemma sincN_zero : sincN 0 = 1 := by simp [sincN]
section RealEntries
variable {τ : Type*} [Fintype τ]
end RealEntries
namespace GramData
variable {ι : Type*} {y : ι → ℝ} {lab : ι → Fin 2} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}
end GramData
end Meshuggah.Gram
end
section
noncomputable section
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg Polynomial
open scoped ComplexOrder BigOperators
open Zeta23.ZeroSide.RankTraceMult
namespace Meshuggah.Gram
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {σ : Type*} [Fintype σ] [DecidableEq σ]
section Blocks
variable {β : Type*} [Fintype β] [DecidableEq β] (f : ι → β)
noncomputable def blockOf (G : Matrix ι ι 𝕜) (k : β) : Matrix {i // f i = k} {i // f i = k} 𝕜 :=
  G.submatrix Subtype.val Subtype.val
@[simp] lemma blockOf_apply (G : Matrix ι ι 𝕜) (k : β) (a b : {i // f i = k}) :
    blockOf f G k a b = G a b := rfl
end Blocks
end Meshuggah.Gram
end
section
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
namespace Meshuggah.Gram
theorem eigenvalues_le_of_real_form {τ : Type*} [Fintype τ] [DecidableEq τ] {A : Matrix τ τ ℂ}
    (hA : A.IsHermitian) {B : τ → τ → ℝ} (hAB : ∀ a b, A a b = (B a b : ℂ)) {c : ℝ}
    (hform : ∀ x : τ → ℝ, ∑ a, ∑ b, x a * B a b * x b ≤ c * ∑ a, x a ^ 2) (k : τ) :
    hA.eigenvalues k ≤ c := by
  have h1 : ‖hA.eigenvectorBasis k‖ = 1 := hA.eigenvectorBasis.orthonormal.1 k
  have h2 := EuclideanSpace.norm_eq (hA.eigenvectorBasis k)
  rw [h1] at h2
  have heig := hA.eigenvalues_eq k
  set v : τ → ℂ := ⇑(hA.eigenvectorBasis k) with hv
  have h3 : ∑ a, ‖v a‖ ^ 2 = 1 := Real.sqrt_eq_one.1 h2.symm
  have hnorm : ∑ a, (v a).re ^ 2 + ∑ a, (v a).im ^ 2 = 1 := by
    have h6 : ∀ a, (v a).re ^ 2 + (v a).im ^ 2 = ‖v a‖ ^ 2 := fun a => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun a _ => h6 a, h3]
  have heq : hA.eigenvalues k
      = ∑ a, ∑ b, (v a).re * B a b * (v b).re + ∑ a, ∑ b, (v a).im * B a b * (v b).im := by
    rw [heig]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, hAB, Finset.mul_sum,
      map_sum, RCLike.re_to_complex]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im]
    ring
  have hre := hform fun a => (v a).re
  have him := hform fun a => (v a).im
  calc hA.eigenvalues k
      = ∑ a, ∑ b, (v a).re * B a b * (v b).re + ∑ a, ∑ b, (v a).im * B a b * (v b).im := heq
    _ ≤ c * ∑ a, (v a).re ^ 2 + c * ∑ a, (v a).im ^ 2 := add_le_add hre him
    _ = c := by rw [← mul_add, hnorm, mul_one]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : Type*} [Fintype β] [DecidableEq β]
  {y : ι → ℝ} {lab : ι → Fin 2} {κ : ι → ι → ℝ} {η : ℝ} {G : Matrix ι ι ℂ}
end Meshuggah.Gram
end
section
/-
Actual AM separated-block spectral bound.

The AM definitions and proofs retain the attribution and licenses in
Attempt016Base and AMSeparatedGram. The only spectral conversion used
here is Kristian Muri Knausgard's generic real-form eigenvalue lemma;
no multiplicity-weighted old-window operator is imported as a premise.

SOURCE ONLY: not compiled. One eventual height works for every separated
principal block of the same actual retained Gram matrix.
-/
noncomputable section
open Matrix Filter Topology Zeta23
open Zeta23Ext.Bridge
open scoped BigOperators
namespace Opeth.AMSeparatedSpectrum
open Classical
/-- Actual retained AM Gram entries are real, without any limiting error. -/
theorem gram_entry_eq_re (Z : ZeroConfig) {P : Params} (hP : P.Valid)
    (T : ℝ) (ha : 0 < (AMW.atAM P T).a T)
    (u v : retained Z (AMW.atAM P T) T) :
    gram Z (AMW.atAM P T) T u v =
      ((gram Z (AMW.atAM P T) T u v).re : ℂ) := by
  have hc : 0 ≤ aL2 (AMW.atAM P T) T := by
    unfold aL2
    exact mul_nonneg ha.le (sq_nonneg _)
  simp only [gram_apply Z (AMW.atAM P T) T (phiHatReal_atAM hP T) hc,
    Complex.ofReal_re]
theorem eventually_submatrix_eigenvalues_le (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (e : ι → retained Z (mtParams T) T),
      (∀ i j, i ≠ j → 17 / 20 ≤
        |xret Z (mtParams T) T (e i) - xret Z (mtParams T) T (e j)|) →
      ∀ k : ι,
        ((gram_isHermitian Z (mtParams T) T).submatrix e).eigenvalues k ≤
          (63903 / 32500 : ℝ) := by
  have hP : (paramsOf stdProfile 1).Valid :=
    paramsOf_valid taperProfile_stdProfile one_pos le_rfl
  filter_upwards [AMSeparatedGram.eventually_normalization hP,
    AMSeparatedGram.eventually_gram_form_le Z] with T hnorm hform
  intro ι _ _ e hsep k
  have hreal : ∀ i j : ι,
      ((gram Z (mtParams T) T).submatrix e e) i j =
        ((gram Z (mtParams T) T (e i) (e j)).re : ℂ) :=
    fun i j => gram_entry_eq_re Z hP T hnorm.1 (e i) (e j)
  exact Meshuggah.Gram.eigenvalues_le_of_real_form
    ((gram_isHermitian Z (mtParams T) T).submatrix e) hreal
    (fun z => hform ι e z hsep) k
theorem eventually_submatrix_eigenvalues_le_two (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (e : ι → retained Z (mtParams T) T),
      (∀ i j, i ≠ j → 17 / 20 ≤
        |xret Z (mtParams T) T (e i) - xret Z (mtParams T) T (e j)|) →
      ∀ k : ι,
        ((gram_isHermitian Z (mtParams T) T).submatrix e).eigenvalues k ≤ 2 := by
  filter_upwards [eventually_submatrix_eigenvalues_le Z] with T hT
  intro ι _ _ e hsep k
  exact (hT ι e hsep k).trans (by norm_num)
theorem eventually_principal_eigenvalues_le_two (Z : ZeroConfig) :
    ∀ᶠ T in atTop, ∀ S : Finset (retained Z (mtParams T) T),
      (∀ i j : S, i ≠ j → 17 / 20 ≤
        |xret Z (mtParams T) T i.1 - xret Z (mtParams T) T j.1|) →
      ∀ k : S,
        ((gram_isHermitian Z (mtParams T) T).submatrix
          (Subtype.val : S → retained Z (mtParams T) T)).eigenvalues k ≤ 2 := by
  filter_upwards [eventually_submatrix_eigenvalues_le_two Z] with T hT
  intro S hsep k
  exact hT S Subtype.val hsep k
end Opeth.AMSeparatedSpectrum
end
section
/-
Concrete close-pair lower bound for Samuel Lavery's attempt-016 AM kernel.
The imported definitions and rational constants retain their Apache-2.0
and transitive notices in Attempt016Base. This argument uses the full sinc
formula, including all removable-pole points, and does not use Simple673.K.

Source-only draft: no compilation or kernel-acceptance claim.
-/
noncomputable section
open Real MeasureTheory
open scoped BigOperators
namespace Opeth.AMClosePair
lemma KMT_eq_integral (t : ℝ) :
    AMW.KMT t = ∫ s in (-(1 : ℝ) / 2)..(1 / 2),
      cos (sqrt 2 * s) * cos (2 * π * t * s) := by
  have hp : ∀ s : ℝ, cos (sqrt 2 * s) * cos (2 * π * t * s) =
      (cos ((sqrt 2 - 2 * π * t) * s) +
        cos ((sqrt 2 + 2 * π * t) * s)) / 2 := by
    intro s
    rw [sub_mul, add_mul, cos_sub, cos_add]
    ring
  have hi₁ : IntervalIntegrable (fun s : ℝ => cos ((sqrt 2 - 2 * π * t) * s))
      volume (-(1 : ℝ) / 2) (1 / 2) :=
    (by fun_prop : Continuous fun s : ℝ => cos ((sqrt 2 - 2 * π * t) * s)).intervalIntegrable _ _
  have hi₂ : IntervalIntegrable (fun s : ℝ => cos ((sqrt 2 + 2 * π * t) * s))
      volume (-(1 : ℝ) / 2) (1 / 2) :=
    (by fun_prop : Continuous fun s : ℝ => cos ((sqrt 2 + 2 * π * t) * s)).intervalIntegrable _ _
  simp_rw [hp]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hi₁ hi₂,
    AMW.integral_cos_mul_sinc, AMW.integral_cos_mul_sinc]
  rfl
lemma KMT_ge_at_sep {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 17 / 20) :
    AMW.KMT (17 / 20) ≤ AMW.KMT t := by
  rw [KMT_eq_integral, KMT_eq_integral]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous fun s : ℝ =>
      cos (sqrt 2 * s) * cos (2 * π * (17 / 20) * s)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun s : ℝ =>
      cos (sqrt 2 * s) * cos (2 * π * t * s)).intervalIntegrable _ _)
  intro s hs
  have hsabs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hs2 : s ^ 2 ≤ 1 / 4 := by nlinarith [hs.1, hs.2]
  have hc0 : 0 ≤ cos (sqrt 2 * s) := by
    linarith [AMW.cos_sqrt2_ge (s := s)]
  have harg0 : 0 ≤ 2 * π * t * |s| := by positivity
  have harg1 : 2 * π * (17 / 20) * |s| ≤ π := by
    have h := mul_le_mul_of_nonneg_left hsabs
      (show 0 ≤ 2 * π * (17 / 20 : ℝ) by positivity)
    nlinarith only [h, pi_pos]
  have harg : 2 * π * t * |s| ≤ 2 * π * (17 / 20) * |s| := by
    have h := mul_le_mul_of_nonneg_right ht1
      (show 0 ≤ 2 * π * |s| by positivity)
    nlinarith only [h]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi harg0 harg1 harg
  have he (a : ℝ) (ha : 0 ≤ a) :
      cos (2 * π * a * s) = cos (2 * π * a * |s|) := by
    calc cos (2 * π * a * s) = cos |2 * π * a * s| := (Real.cos_abs _).symm
      _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * π * a)]
  rw [he (17 / 20) (by norm_num), he t ht0]
  exact mul_le_mul_of_nonneg_left hc hc0
lemma normalized_KMT_at_sep_ge :
    (1 / 5 : ℝ) ≤ AMW.KMT (17 / 20) / AMW.K0AM := by
  set z : ℝ := π * (17 / 20)
  set y : ℝ := π * (3 / 20)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hzlo : (8 / 3 : ℝ) ≤ z := by
    dsimp [z]; linarith [AMMajorant.pi_coarse.1]
  have hzhi : z ≤ (187 / 70 : ℝ) := by
    dsimp [z]; linarith [AMMajorant.pi_coarse.2]
  have hylo : (471 / 1000 : ℝ) ≤ y := by
    dsimp [y]; linarith [AMMajorant.pi_coarse.1]
  have hyhi : y ≤ (33 / 70 : ℝ) := by
    dsimp [y]; linarith [AMMajorant.pi_coarse.2]
  have hy2 : y ^ 2 ≤ (33 / 70 : ℝ) ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hyhi)
      (show 0 ≤ 33 / 70 + y by positivity)
    nlinarith only [h]
  have hy3 : y ^ 3 ≤ (33 / 70 : ℝ) ^ 3 := by
    have h := mul_nonneg (sub_nonneg.mpr hyhi)
      (show 0 ≤ (33 / 70 : ℝ) ^ 2 + (33 / 70) * y + y ^ 2 by positivity)
    nlinarith only [h]
  have hcos : (22 / 25 : ℝ) ≤ cos y := by
    nlinarith only [Real.one_sub_sq_div_two_le_cos (x := y), hy2]
  have hsin : (9 / 20 : ℝ) ≤ sin y := by
    have h := Meshuggah.Majorant.sinPoly_le_sin hy0 0
    norm_num [Meshuggah.Majorant.sinPoly] at h
    nlinarith only [h, hylo, hy3]
  have hgam : (4 / 5 : ℝ) ≤ AMW.gamAM := by
    linarith [AMW.G.gamAM_bounds.1]
  have hgam0 : 0 ≤ AMW.gamAM := by linarith
  have hgz : (4 / 5 : ℝ) * (8 / 3) ≤ AMW.gamAM * z :=
    mul_le_mul hgam hzlo (by norm_num) hgam0
  have hprod : ((4 / 5 : ℝ) * (8 / 3)) * (9 / 20) ≤
      (AMW.gamAM * z) * sin y :=
    mul_le_mul hgz hsin (by norm_num) (mul_nonneg hgam0 hz0)
  have hnum : (14 / 5 : ℝ) ≤ cos y + 2 * AMW.gamAM * z * sin y := by
    nlinarith only [hcos, hprod]
  have hden0 : 0 < 2 * z ^ 2 - 1 := by
    have h := mul_nonneg (sub_nonneg.mpr hzlo)
      (show 0 ≤ z + 8 / 3 by positivity)
    nlinarith only [h]
  have hdenhi : 2 * z ^ 2 - 1 ≤ (32519 / 2450 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr hzhi)
      (show 0 ≤ 187 / 70 + z by positivity)
    nlinarith only [h]
  have hD : AMW.mD (17 / 20) ≠ 0 := by
    change 1 - 2 * z ^ 2 ≠ 0
    intro he
    linarith only [hden0, he]
  have hcosz : cos z = -cos y := by
    have he : z = π - y := by dsimp [z, y]; ring
    rw [he, Real.cos_pi_sub]
  have hsinz : sin z = sin y := by
    have he : z = π - y := by dsimp [z, y]; ring
    rw [he, Real.sin_pi_sub]
  have heq : AMW.KMT (17 / 20) / AMW.K0AM =
      (cos y + 2 * AMW.gamAM * z * sin y) / (2 * z ^ 2 - 1) := by
    rw [AMW.KMT_eq_ND hD]
    change (AMW.K0AM * ((cos z - 2 * AMW.gamAM * z * sin z) / (1 - 2 * z ^ 2))) /
      AMW.K0AM = _
    rw [hcosz, hsinz]
    rw [show (1 : ℝ) - 2 * z ^ 2 = -(2 * z ^ 2 - 1) by ring]
    field_simp [AMW.K0AM_pos.ne', ne_of_gt hden0] <;> ring
  rw [heq, le_div_iff₀ hden0]
  nlinarith only [hnum, hdenhi]
lemma kernel_eq_KMT_add_correction (t : ℝ) :
    AMW.kfunAM t = AMW.KMT t / AMW.K0AM +
      AMW.rhoAM * ∑ n ∈ Finset.range 12, (AMW.cAM (n + 1) : ℝ) * AMW.Tj n t := by
  unfold AMW.kfunAM
  rw [AMW.K0AM_eq, AMW.KfunAM_eq_sinc, Finset.sum_range_succ',
    AMW.cAM_zero, AMW.ωAM_zero, one_mul]
  have hk : (sinc ((sqrt 2 - 2 * π * t) / 2) + sinc ((sqrt 2 + 2 * π * t) / 2)) / 2 =
      AMW.KMT t := rfl
  rw [hk]
  have hs : ∀ n ∈ Finset.range 12,
      (AMW.cAM (n + 1) : ℝ) *
        ((sinc ((AMW.ωAM (n + 1) - 2 * π * t) / 2) +
          sinc ((AMW.ωAM (n + 1) + 2 * π * t) / 2)) / 2) =
      (AMW.cAM (n + 1) : ℝ) * AMW.Tj n t := by
    intro n _
    rw [AMW.term_sinc]
    rfl
  rw [Finset.sum_congr rfl hs]
  unfold AMW.rhoAM
  ring
lemma Tj_abs_le (n : ℕ) (t : ℝ) : |AMW.Tj n t| ≤ 1 := by
  unfold AMW.Tj
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h := abs_add_le (sinc (π * (t - ((n : ℝ) + 1))))
    (sinc (π * (t + ((n : ℝ) + 1))))
  linarith [Real.abs_sinc_le_one (π * (t - ((n : ℝ) + 1))),
    Real.abs_sinc_le_one (π * (t + ((n : ℝ) + 1)))]
lemma correction_abs_le (t : ℝ) :
    |AMW.rhoAM * ∑ n ∈ Finset.range 12, (AMW.cAM (n + 1) : ℝ) * AMW.Tj n t|
      ≤ 749 / 10000 := by
  have hs : |∑ n ∈ Finset.range 12, (AMW.cAM (n + 1) : ℝ) * AMW.Tj n t| ≤ 13743119 / 200000000 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun n _ => ?_) AMW.sum_abs_cAM_succ
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Tj_abs_le n t)
  rw [abs_mul, abs_of_pos AMMajorant.rho_pos]
  have h := mul_le_mul_of_nonneg_left hs AMMajorant.rho_pos.le
  nlinarith only [h, AMMajorant.rho_le]
lemma kernel_ge_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 17 / 20) :
    (1251 / 10000 : ℝ) ≤ AMW.kfunAM t := by
  have hbase := div_le_div_of_nonneg_right (KMT_ge_at_sep ht0 ht1) AMW.K0AM_pos.le
  have hcorr := (abs_le.mp (correction_abs_le t)).1
  rw [kernel_eq_KMT_add_correction]
  linarith [normalized_KMT_at_sep_ge]
theorem kernel_ge_one_eighth {t : ℝ} (ht : |t| ≤ 17 / 20) :
    (1 / 8 : ℝ) ≤ AMW.kfunAM t := by
  by_cases ht0 : 0 ≤ t
  · have h := kernel_ge_nonneg ht0 ((le_abs_self t).trans ht)
    linarith
  · have htneg : t < 0 := lt_of_not_ge ht0
    have h := kernel_ge_nonneg (neg_nonneg.mpr htneg.le)
      ((neg_le_abs t).trans ht)
    have he : AMW.kfunAM (-t) = AMW.kfunAM t := by
      unfold AMW.kfunAM
      rw [AMW.KfunAM_neg]
    rw [he] at h
    linarith
theorem kernel_square_ge {t : ℝ} (ht : |t| ≤ 17 / 20) :
    (1 / 64 : ℝ) ≤ AMW.kfunAM t ^ 2 := by
  have h := kernel_ge_one_eighth ht
  nlinarith [sq_nonneg (AMW.kfunAM t - 1 / 8)]
end Opeth.AMClosePair
end
section
open scoped BigOperators
namespace Pantera.Transfer
end Pantera.Transfer
end
section
open scoped BigOperators
open Finset
namespace Pantera.Transfer
end Pantera.Transfer
end
section
open scoped BigOperators
namespace Meshuggah.Transfer
end Meshuggah.Transfer
end
section
open scoped BigOperators
open Finset
namespace Meshuggah.Transfer
end Meshuggah.Transfer
end
section
open scoped BigOperators
open Finset
namespace Meshuggah.Transfer
end Meshuggah.Transfer
end
section
open scoped BigOperators
open Finset
namespace Pantera.Transfer
end Pantera.Transfer
end
section
open scoped BigOperators
open Finset
namespace Pantera
namespace Transfer
end Transfer
end Pantera
end
section
/-
Copyright (c) 2026 R. Arun Chandru. Released under Apache-2.0.
Adapted from Samuel Lavery's attempt-016 band_close/block_defect proofs
and Kristian Muri Knausgard's Simple673 finite-neighbour count, both 2026,
Apache-2.0. Preserve the imported developments' attribution and notices.
Changes: full defect on a spectrum bounded by two; charge entry errors
only on the actual fourteen-neighbour band, not all ordered pairs.
SOURCE ONLY: not yet compiled; not a completed challenge proof.
-/
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace Opeth.AMSparseDefect
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem defect_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    0 ≤ defect hA := by
  rw [defect, rtrace_specMap]
  exact sum_nonneg (fun i _ => Psi_nonneg _)
theorem offdiag_le_defect_of_spectrum_le_two {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hcap : ∀ i, hA.eigenvalues i ≤ 2) :
    offDiagSqOn A univ ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  have hsum : ∑ i, Psi (hA.eigenvalues i) =
      ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
    sum_congr rfl (fun i _ => by simp [Psi, hcap i])
  have hfrob := frobSq_specMap hA (fun t => t - 1)
  rw [specMap_sub_one] at hfrob
  rw [hsum, ← hfrob]
  exact offDiagSqOn_le_frobSq_sub_one A
end Opeth.AMSparseDefect
end
section
/-
Copyright (c) 2026 R. Arun Chandru. Released under Apache-2.0.
Uses the attributed AM band certificate interface in Attempt016Base and
the linear-error comparison in AMSparseDefect. No certificate premise is
silently replaced by a numerical sample or by a different kernel.
SOURCE ONLY: compilation and concrete certificate instantiation pending.
-/
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
end
section
open Finset
namespace Meshuggah.Gram
variable {ι : Type*}
structure IsCloseMatching (y : ι → ℝ) (d : ℝ) (σ : ι → ι) : Prop where
  invol : ∀ i, σ (σ i) = i
  close : ∀ i, σ i ≠ i → |y i - y (σ i)| < d
lemma IsCloseMatching.id (y : ι → ℝ) (d : ℝ) : IsCloseMatching y d (fun i => i) :=
  ⟨fun _ => rfl, fun _ h => absurd rfl h⟩
lemma IsCloseMatching.addPair [DecidableEq ι] {y : ι → ℝ} {d : ℝ} {σ : ι → ι}
    (hσ : IsCloseMatching y d σ) {i j : ι} (hi : σ i = i) (hj : σ j = j) (hij : i ≠ j)
    (hd : |y i - y j| < d) :
    IsCloseMatching y d (fun x => if x = i then j else if x = j then i else σ x) := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · by_cases hxi : x = i
    · subst hxi
      simp [hij.symm]
    · by_cases hxj : x = j
      · subst hxj
        simp [hxi]
      · have h1 : σ x ≠ i := fun h => hxi (by rw [← hσ.invol x, h, hi])
        have h2 : σ x ≠ j := fun h => hxj (by rw [← hσ.invol x, h, hj])
        simp [hxi, hxj, h1, h2, hσ.invol x]
  · by_cases hxi : x = i
    · subst hxi
      simpa using hd
    · by_cases hxj : x = j
      · subst hxj
        simp only [if_neg hxi, if_true]
        rw [abs_sub_comm]; exact hd
      · simp only [if_neg hxi, if_neg hxj] at hx ⊢
        exact hσ.close x hx
theorem exists_maximal_matching [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (d : ℝ) :
    ∃ σ : ι → ι, IsCloseMatching y d σ ∧
      ∀ i j, σ i = i → σ j = j → i ≠ j → d ≤ |y i - y j| := by
  classical
  obtain ⟨σ, hσmem, hσmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun σ : ι → ι => IsCloseMatching y d σ)
    (fun σ => (Finset.univ.filter fun i => σ i ≠ i).card)
    ⟨fun i => i, by simp [IsCloseMatching.id]⟩
  have hσ : IsCloseMatching y d σ := by simpa using hσmem
  refine ⟨σ, hσ, fun i j hi hj hij => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  set τ : ι → ι := fun x => if x = i then j else if x = j then i else σ x with hτ
  have hτm : IsCloseMatching y d τ := hσ.addPair hi hj hij hlt
  have hlt' : (Finset.univ.filter fun x => σ x ≠ x).card
      < (Finset.univ.filter fun x => τ x ≠ x).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i, ?_, ?_⟩
      · simp [hτ, hij.symm]
      · simp [hi]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hxi : x ≠ i := fun h => hx (h ▸ hi)
      have hxj : x ≠ j := fun h => hx (h ▸ hj)
      simpa [hτ, hxi, hxj] using hx
  exact absurd (hσmax τ (by simpa using hτm)) (not_le.2 hlt')
noncomputable def matchLabel [DecidableEq ι] (σ : ι → ι) (i : ι) : Option (Sym2 ι) :=
  if σ i = i then none else some s(i, σ i)
lemma matchLabel_eq_none [DecidableEq ι] {σ : ι → ι} {i : ι} :
    matchLabel σ i = none ↔ σ i = i := by
  unfold matchLabel
  split_ifs with h <;> simp [h]
lemma matchLabel_eq_some [DecidableEq ι] {σ : ι → ι} {i : ι} {z : Sym2 ι} :
    matchLabel σ i = some z ↔ σ i ≠ i ∧ s(i, σ i) = z := by
  unfold matchLabel
  split_ifs with h <;> simp [h]
lemma matchLabel_partner [DecidableEq ι] {σ : ι → ι} (hσ : ∀ i, σ (σ i) = i) {i : ι}
    (hi : σ i ≠ i) : matchLabel σ (σ i) = some s(i, σ i) := by
  rw [matchLabel_eq_some, hσ i]
  exact ⟨fun h => hi h.symm, Sym2.eq_swap⟩
lemma eq_or_eq_of_matchLabel [DecidableEq ι] {σ : ι → ι} {i l : ι}
    (h : matchLabel σ l = some s(i, σ i)) : l = i ∨ l = σ i := by
  rw [matchLabel_eq_some] at h
  rcases Sym2.eq_iff.1 h.2 with h1 | h1
  · exact Or.inl h1.1
  · exact Or.inr h1.1
end Meshuggah.Gram
end
section
/-
Copyright (c) 2026 R. Arun Chandru. Released under Apache-2.0.
The actual AM definitions, finite defect and pinching theorem are those
of Samuel Lavery's attributed attempt-016. The maximal matching and its
labels are from Kristian Muri Knausgard's Distinct839 development.

This file combines actual AM close pairs with the same-matrix separated
remainder. It does not assert or replace the local certificate premise.
SOURCE ONLY: not yet compiled; no completed challenge proof is claimed.
-/
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace Opeth.AMMatching
open Meshuggah.Gram
variable {ι : Type} [Fintype ι] [DecidableEq ι]
/-- Each close pair contributes twice the desired local floor, with only
four times the entrywise error. Both ordered off-diagonal entries of the
actual matrix are retained. Neither a diagonal normalization nor a PSD
premise is needed for the existing Hermitian minimum-defect theorem. -/
theorem close_pair_block_bound {x : ι → ℝ} {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c δ : ℝ} (hc : c ≤ 1 / 64) (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    {i j : ι} (hij : i ≠ j) (hnear : |x i - x j| ≤ 17 / 20) :
    2 * c - 4 * δ ≤ blockDefect hG {i, j} := by
  classical
  have hkij : (1 / 64 : ℝ) ≤ wfun (x i - x j) :=
    AMClosePair.kernel_square_ge hnear
  have hkji : (1 / 64 : ℝ) ≤ wfun (x j - x i) :=
    AMClosePair.kernel_square_ge (by simpa only [abs_sub_comm] using hnear)
  have heij := wfun_sub_le_norm_sq (hclose i j hij)
  have heji := wfun_sub_le_norm_sq (hclose j i hij.symm)
  have hoff : offDiagSqOn G {i, j} = ‖G i j‖ ^ 2 + ‖G j i‖ ^ 2 := by
    simp [offDiagSqOn, hij, hij.symm]
  have hmin : 2 * c - 4 * δ ≤ min 1 (offDiagSqOn G {i, j}) := by
    apply le_min
    · linarith
    · rw [hoff]
      linarith
  have hd := block_defect_of_isHermitian
    (hG.submatrix (Subtype.val : ({i, j} : Finset ι) → ι))
  rw [offDiagSqOn_submatrix] at hd
  exact hmin.trans hd
end Opeth.AMMatching
end
section
/-
Concrete counting consumer for the attempt-016 AM operator.

The imported AM tail, retained-set, and actual-zeta interfaces retain the
Samuel Lavery / Zeta23 attribution and licenses in Attempt016Base.
The sole open hypothesis below is explicitly the eventual defect bound
for that same AM retained Gram matrix. No claim is made that it has been
discharged here, or that the proposed rational has been accepted.

Source-only draft: no compilation or kernel-acceptance claim.
-/
noncomputable section
open Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
end
section
/-
Actual AM operator-to-counting composition.

The AM definitions and analytic results retain the licenses and notices
in Attempt016Base and the imported AM modules. This file discharges the
same-operator, uniform-kernel, separated-spectrum, and retained-set inputs.
Its only certificate inputs are the displayed actual eight-point local
certificate, admissibility, and its exact pressure sum.

SOURCE ONLY: not compiled; the concrete extracted certificate has not yet
been instantiated here. No challenge acceptance claim is made.
-/
noncomputable section
open Filter Topology Zeta23
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
open scoped BigOperators
end
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace OpethN
theorem card_near_le_k (ℓ k : ℕ) (i : Fin ℓ) :
    (univ.filter fun j : Fin ℓ =>
      i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + k ∧ (j : ℕ) ≤ (i : ℕ) + k).card ≤ 2 * k := by
  have h1 : (univ.filter fun j : Fin ℓ =>
        i ≠ j ∧ (i : ℕ) ≤ (j : ℕ) + k ∧ (j : ℕ) ≤ (i : ℕ) + k).card
      ≤ ((Icc ((i : ℕ) - k) ((i : ℕ) + k)).erase (i : ℕ)).card := by
    refine card_le_card_of_injOn (fun j : Fin ℓ => (j : ℕ)) ?_ ?_
    · intro j hj
      have hj' := (mem_filter.mp (mem_coe.mp hj)).2
      refine mem_coe.mpr (mem_erase.mpr ⟨fun h => hj'.1 (Fin.ext h.symm), mem_Icc.mpr ?_⟩)
      have := hj'.2
      show (i : ℕ) - k ≤ (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + k
      omega
    · intro a _ b _ hab
      exact Fin.ext hab
  have h2 : ((Icc ((i : ℕ) - k) ((i : ℕ) + k)).erase (i : ℕ)).card ≤ 2 * k := by
    rw [card_erase_of_mem (mem_Icc.mpr ⟨by omega, by omega⟩), Nat.card_Icc]
    omega
  exact h1.trans h2
section Sparse
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem band_close_n (n : ℕ) {x : ι → ℝ} (hx : Function.Injective x)
    {m : ℕ} (hS : (univ.image x).card = m) (hcard : Fintype.card ι = m)
    (G : Matrix ι ι ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ) :
    (∑ r : Fin m × Fin m,
      if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
        wfun ((univ.image x).orderEmbOfFin hS r.1 -
          (univ.image x).orderEmbOfFin hS r.2) else 0)
      ≤ offDiagSqOn G univ + 4 * ((n - 1 : ℕ) : ℝ) * δ * m := by
  classical
  set e := Equiv.ofBijective _ (sRank_bijective hx hS hcard) with he
  set R : ι → ℕ := fun i => (sRank x hS i : ℕ) with hR
  set C : ι → ι → Prop := fun i j =>
    i ≠ j ∧ R i ≤ R j + (n - 1) ∧ R j ≤ R i + (n - 1) with hC
  set F : ι → ι → ℝ := fun i j =>
    if C i j then wfun (x i - x j) else 0 with hF
  have hsum : (∑ r : Fin m × Fin m,
      if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
        wfun ((univ.image x).orderEmbOfFin hS r.1 -
          (univ.image x).orderEmbOfFin hS r.2) else 0) =
      ∑ i, ∑ j, F i j := by
    rw [Fintype.sum_prod_type, ← e.sum_comp]
    apply sum_congr rfl
    intro i _
    rw [← e.sum_comp]
    apply sum_congr rfl
    intro j _
    simp only [he, Equiv.ofBijective_apply, sRank_val, hF, hC, hR,
      ne_eq, (sRank_injective hx hS).eq_iff]
  have hnear (i : ι) : (univ.filter (C i)).card ≤ 2 * (n - 1) := by
    have hinj : (univ.filter (C i)).card ≤
        (univ.filter fun j : Fin m => sRank x hS i ≠ j ∧
          (sRank x hS i : ℕ) ≤ (j : ℕ) + (n - 1) ∧
          (j : ℕ) ≤ (sRank x hS i : ℕ) + (n - 1)).card := by
      apply card_le_card_of_injOn (fun j : ι => sRank x hS j)
      · intro j hj
        have hj' := (mem_filter.mp (mem_coe.mp hj)).2
        refine mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, ?_⟩)
        exact ⟨fun h => hj'.1 (sRank_injective hx hS h), hj'.2⟩
      · intro a _ b _ hab
        exact sRank_injective hx hS hab
    exact hinj.trans (card_near_le_k m (n - 1) (sRank x hS i))
  have hterm (i j : ι) : F i j ≤
      (if i ≠ j then ‖G i j‖ ^ 2 else 0) +
        (if C i j then 2 * δ else 0) := by
    change (if C i j then wfun (x i - x j) else 0) ≤
      (if i ≠ j then ‖G i j‖ ^ 2 else 0) + (if C i j then 2 * δ else 0)
    by_cases hc : C i j
    · simp only [if_pos hc, if_pos hc.1]
      exact sub_le_iff_le_add.mp (wfun_sub_le_norm_sq (hclose i j hc.1))
    · simp only [if_neg hc, add_zero]
      split_ifs <;> positivity
  have hcount (i : ι) :
      (∑ j, if C i j then 2 * δ else 0) ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hc : ((univ.filter (C i)).card : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnear i
    have h2δ : (0 : ℝ) ≤ 2 * δ := mul_nonneg (by norm_num) hδ
    have h := mul_le_mul_of_nonneg_right hc h2δ
    nlinarith only [h]
  rw [hsum]
  calc
    (∑ i, ∑ j, F i j) ≤ ∑ i, ∑ j,
        ((if i ≠ j then ‖G i j‖ ^ 2 else 0) +
          (if C i j then 2 * δ else 0)) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hterm i j))
    _ = offDiagSqOn G univ + ∑ i, ∑ j,
        (if C i j then 2 * δ else 0) := by
      simp only [sum_add_distrib, offDiagSqOn, ne_eq, ite_not]
    _ ≤ offDiagSqOn G univ + ∑ _i : ι, 4 * ((n - 1 : ℕ) : ℝ) * δ :=
      add_le_add le_rfl (sum_le_sum (fun i _ => hcount i))
    _ = offDiagSqOn G univ + 4 * ((n - 1 : ℕ) : ℝ) * δ * m := by
      rw [sum_const, card_univ, hcard, nsmul_eq_mul]
      ring
theorem pressure_le_n {n : ℕ} {x : ι → ℝ} {m : ℕ}
    (hm : n ≤ m) (hS : (univ.image x).card = m)
    (W : WCert n) (hb : ∀ r, 0 ≤ W.b r) {R : ℝ}
    (hspan : ∀ i j, x i - x j ≤ R) :
    blkPress W.b x univ ≤ W.B * R := by
  classical
  have hmem (k : ℕ) (hk : k < m) : sortedOn x univ k ∈ univ.image x := by
    rw [sortedOn_eq hS, sortedExt_of_lt _ hk]
    exact Finset.orderEmbOfFin_mem _ hS _
  unfold blkPress
  rw [hS]
  calc
    (∑ r : Fin (n - 1), W.b r *
        (sortedOn x univ (m - (n - 1) + r) - sortedOn x univ r))
        ≤ ∑ r : Fin (n - 1), W.b r * R := by
      apply sum_le_sum
      intro r _
      have hr := r.isLt
      obtain ⟨i, _, hi⟩ := mem_image.mp (hmem (m - (n - 1) + r) (by omega))
      obtain ⟨j, _, hj⟩ := mem_image.mp (hmem r (by omega))
      apply mul_le_mul_of_nonneg_left _ (hb r)
      rw [← hi, ← hj]
      exact hspan i j
    _ = W.B * R := by rw [← sum_mul]; rfl
theorem remainder_bound_n {n : ℕ} (hn : 2 ≤ n) {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ i, hG.eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG := by
  classical
  set m := Fintype.card ι with hmdef
  have hcard : Fintype.card ι = m := rfl
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  have hB : 0 ≤ W.B := WCert.B_nonneg hW
  have hk : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hk0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  by_cases hm : n ≤ m
  · have he := block_energy_band hn W hW hCert hm x hx hS
    have hb := band_close_n n hx hS hcard G hδ hclose
    have hp := pressure_le_n hm hS W hW.b_nonneg hspan
    have hd := Opeth.AMSparseDefect.offdiag_le_defect_of_spectrum_le_two hG hcap
    rw [← hk] at he
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG
    nlinarith only [he, hb, hp, hd]
  · have hmk : m ≤ n - 1 := by omega
    have hmk' : (m : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hmk
    have hcm := mul_le_mul_of_nonneg_left hmk' hc
    have hbr : 0 ≤ W.B * R := mul_nonneg hB hR
    have hdm : 0 ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ * (m : ℝ) := by positivity
    have hd := Opeth.AMSparseDefect.defect_nonneg hG
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG
    nlinarith only [hcm, hbr, hdm, hd]
theorem block_remainder_bound_n {n : ℕ} (hn : 2 ≤ n) {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (B : Finset ι)
    (hcap : ∀ i, (hG.submatrix (Subtype.val : B → ι)).eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (B.card : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c ≤ blockDefect hG B := by
  classical
  have hxB : Function.Injective (fun i : B => x i) := fun i j h =>
    Subtype.ext (hx h)
  have hcloseB : ∀ i j : B, i ≠ j →
      ‖G.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) i j -
        (kfun (x i - x j) : ℂ)‖ ≤ δ := fun i j hij =>
    hclose i j (fun h => hij (Subtype.ext h))
  have h := remainder_bound_n hn hxB (hG.submatrix (Subtype.val : B → ι)) hc W hW hCert
    hδ hcloseB hcap hR (fun i j => hspan i j)
  simpa only [Fintype.card_coe, blockDefect] using h
end Sparse
section Matching
open Meshuggah.Gram
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem matching_defect_bound_n {n : ℕ} (hn : 2 ≤ n) {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) (hcPair : c ≤ 1 / 64)
    (W : WCert n) (hW : W.Adm)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ S : Finset ι,
      (∀ i j : S, i ≠ j → 17 / 20 ≤ |x i - x j|) →
      ∀ k : S, (hG.submatrix (Subtype.val : S → ι)).eigenvalues k ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c ≤ defect hG := by
  classical
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  obtain ⟨σ, hσ, hσsep⟩ := exists_maximal_matching x (17 / 20)
  let S : Option (Sym2 ι) → Finset ι :=
    fun z => univ.filter (fun i => matchLabel σ i = z)
  have hpinch : (∑ z, blockDefect hG (S z)) ≤ defect hG :=
    pinching_partition hG (Option (Sym2 ι)) (matchLabel σ)
  have hblock (z : Option (Sym2 ι)) :
      (c - 4 * k * δ) * ((S z).card : ℝ) -
        (if z = none then W.B * R + k * c else 0) ≤ blockDefect hG (S z) := by
    cases z with
    | none =>
      rw [if_pos rfl]
      have hfixed (i : S none) : σ i = i :=
        matchLabel_eq_none.mp ((mem_filter.mp i.property).2)
      have hsep : ∀ i j : S none, i ≠ j → 17 / 20 ≤ |x i - x j| := by
        intro i j hij
        exact hσsep i j (hfixed i) (hfixed j)
          (fun h => hij (Subtype.ext h))
      have hb := block_remainder_bound_n hn hx hG hc W hW hCert
        hδ hclose (S none) (hcap (S none) hsep) hR hspan
      linarith only [hb]
    | some z =>
      rw [if_neg (Option.some_ne_none z), sub_zero]
      by_cases hne : (S (some z)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have hiLabel : matchLabel σ i = some z := (mem_filter.mp hi).2
        obtain ⟨hiMove, hiPair⟩ := matchLabel_eq_some.mp hiLabel
        subst z
        have hpair : S (some s(i, σ i)) = {i, σ i} := by
          ext l
          change l ∈ univ.filter (fun j => matchLabel σ j = some s(i, σ i)) ↔
            l ∈ ({i, σ i} : Finset ι)
          simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
          constructor
          · exact eq_or_eq_of_matchLabel
          · intro hl
            rcases hl with rfl | rfl
            · exact matchLabel_eq_some.mpr ⟨hiMove, rfl⟩
            · exact matchLabel_partner hσ.invol hiMove
        have hij : i ≠ σ i := fun h => hiMove h.symm
        have hb := Opeth.AMMatching.close_pair_block_bound hG hcPair hδ hclose hij
          (hσ.close i hiMove).le
        rw [hpair]
        have hcard : ({i, σ i} : Finset ι).card = 2 := by simp [hij]
        rw [hcard]
        have hkδ : δ ≤ k * δ := le_mul_of_one_le_left hδ hk1
        norm_num only [Nat.cast_ofNat]
        linarith only [hb, hδ, hkδ]
      · have hempty : S (some z) = ∅ := not_nonempty_iff_eq_empty.mp hne
        rw [hempty, card_empty, Nat.cast_zero, mul_zero]
        exact blockDefect_nonneg hG ∅
  have hcardsNat : (∑ z : Option (Sym2 ι), (S z).card) = Fintype.card ι := by
    simpa only [S, mem_univ, filter_true, card_univ] using
      (sum_card_fiberwise_eq_card_filter (univ : Finset ι)
        (univ : Finset (Option (Sym2 ι))) (matchLabel σ))
  have hcards : (∑ z : Option (Sym2 ι), ((S z).card : ℝ)) =
      (Fintype.card ι : ℝ) := by
    exact_mod_cast hcardsNat
  have hcharge : (∑ z : Option (Sym2 ι),
      if z = none then W.B * R + k * c else 0) = W.B * R + k * c := by
    simp
  calc
    (c - 4 * k * δ) * (Fintype.card ι : ℝ) - W.B * R - k * c =
        ∑ z : Option (Sym2 ι), ((c - 4 * k * δ) * ((S z).card : ℝ) -
          (if z = none then W.B * R + k * c else 0)) := by
      rw [sum_sub_distrib, ← mul_sum, hcards, hcharge]
      ring
    _ ≤ ∑ z, blockDefect hG (S z) := sum_le_sum (fun z _ => hblock z)
    _ ≤ defect hG := hpinch
end Matching
end OpethN
end
noncomputable section
open Filter Topology
open Zeta23 Zeta23.ZeroSide Zeta23.ThmD Zeta23Ext.Bridge
namespace OpethN.Counting
open Classical
noncomputable def ActualDefectEstimate (Z : ZeroConfig) (n : ℕ) (c B : ℝ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * ((retained Z (mtParams T) T).card : ℝ) -
        B * spanOf (xret Z (mtParams T) T) Finset.univ - ((n - 1 : ℕ) : ℝ) * c
      ≤ Dcirc Z (mtParams T) T
theorem defect_to_dyadic (Z : ZeroConfig) (H : PaperInputs Z) {n : ℕ} (hn : 2 ≤ n)
    {c B : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hB : 0 ≤ B)
    (hdef : ActualDefectEstimate Z n c B) :
    ∀ ε > (0 : ℝ), ∀ᶠ T in atTop,
      ((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 - B) / (1 - c) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  have hk0 : 0 < k := by linarith
  have hmu : 0 < 1 - c := sub_pos.mpr hc1
  set C : ℝ := 4 * k + 2 + c + B with hCdef
  have hC : 0 < C := by
    dsimp [C]
    linarith
  set δ : ℝ := min (c / (8 * k)) ((1 - c) * ε / C) with hδdef
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hc0 (by positivity)) (div_pos (mul_pos hmu hε) hC)
  have hδcap : δ ≤ c / (8 * k) := min_le_left _ _
  have hδeps : δ ≤ (1 - c) * ε / C := min_le_right _ _
  have hbudget : C * δ ≤ (1 - c) * ε := by
    have h := (le_div_iff₀ hC).mp hδeps
    linarith only [h]
  have hcoef : 0 ≤ c - 4 * k * δ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * k)).mp hδcap
    nlinarith only [h, hc0]
  filter_upwards [hdef δ hδ, deleted_strips Z H δ hδ,
    span_retained_le Z H δ hδ, tail_passage Z H (eventually_h7 Z) δ hδ,
    (Zeta23.Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop (k * c / δ)]
    with T hd hstrip hspan htail hNlarge
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ)
  set m : ℝ := ((retained Z (mtParams T) T).card : ℝ)
  set R : ℝ := spanOf (xret Z (mtParams T) T) Finset.univ
  set D : ℝ := Dcirc Z (mtParams T) T
  change (c - 4 * k * δ) * m - B * R - k * c ≤ D at hd
  change n0 - δ * N ≤ m at hstrip
  change R ≤ (1 + δ) * N at hspan
  change (AMW.HW - δ) * N + D ≤ n0 at htail
  change k * c / δ ≤ N at hNlarge
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hn0N : n0 ≤ N := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    change (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ)
    exact_mod_cast h
  have hn := mul_le_mul_of_nonneg_left hstrip hcoef
  have hR := mul_le_mul_of_nonneg_left hspan hB
  have herr := mul_le_mul_of_nonneg_left hn0N
    (show 0 ≤ 4 * k * δ by positivity)
  have hδ2N : 0 ≤ 4 * k * δ * δ * N := by positivity
  have hD : c * n0 - B * N - (4 * k + c + B) * δ * N - k * c ≤ D := by
    nlinarith only [hd, hn, hR, herr, hδ2N]
  have hend : k * c ≤ δ * N := by
    have h := (div_le_iff₀ hδ).mp hNlarge
    nlinarith only [h]
  have hHW : (6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 : ℝ) * N ≤ AMW.HW * N := by
    have h : (6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 : ℝ) ≤ AMW.HW := by
      calc
        _ = (6721290091768038344368273523390880473594 / 10 ^ 40 : ℝ) := by norm_num
        _ ≤ AMW.HW := AMW.HW_ge
    exact mul_le_mul_of_nonneg_right h hN0
  have hmain : ((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 : ℝ) - B - C * δ) * N ≤ (1 - c) * n0 := by
    dsimp [C]
    nlinarith only [hD, htail, hend, hHW]
  have hid : (1 - c) * ((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 - B) / (1 - c)) = 6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 - B := by
    field_simp
  have hcoeff : (1 - c) * ((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 - B) / (1 - c) - ε) ≤
      (6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 : ℝ) - B - C * δ := by
    rw [mul_sub, hid]
    linarith only [hbudget]
  have hscaled : (1 - c) * (((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 - B) / (1 - c) - ε) * N) ≤ (1 - c) * n0 := by
    calc
      _ = ((1 - c) * ((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 - B) / (1 - c) - ε)) * N := by ring
      _ ≤ ((6721290091768038344368273523390880473594 / 10000000000000000000000000000000000000000 : ℝ) - B - C * δ) * N :=
        mul_le_mul_of_nonneg_right hcoeff hN0
      _ ≤ _ := hmain
  exact le_of_mul_le_mul_left hscaled hmu
end OpethN.Counting
end

/-
ADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS

This comment supplements, and does not replace, the source and modification
notices retained above. The Knausgard NOTICE below is reproduced verbatim;
its descriptions and historical claims refer to the upstream project.
The inherited MIT portions retain their MIT terms. Original contributions
and the Apache-licensed portions are offered under Apache-2.0.

Knausgard directory NOTICE
Source: https://github.com/kristianmk/839/blob/0e961ea199b425010843bc8044676d4ad29fe031/lean/NOTICE

NOTICE for the directory lean/

Lean 4 proofs for the paper "More than 83.9% of the zeros of the Riemann zeta function are
distinct and more than 67.34% are simple and on the critical line"
Copyright 2026 Kristian Muri Knausgård

The files in this directory are licensed under the Apache License, Version 2.0 (see LICENSE).
They were drafted with AI assistance, as stated in README.md.

This directory builds on, and contains material derived from, the Lean library

    Zeta23, https://github.com/anthropics/formal-math (directory zeta23),
    commit fbdc36bbf17d20af3fd0447c6d1a8a02773c9844,
    Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0.

The library itself is not included. Derived from it are:

1. upstream_relax.patch. A patch to fourteen files of the library: lines of the library and
   changes to them. The changes are described at the top of the patch and in README.md.

2. Definitions in the statement files. Challenge839.lean, Challenge673.lean,
   ChallengeFurther.lean and Challenge889.lean repeat, character for character, definitions of
   the library's Challenge.lean and Zeta23/Statement.lean (IsNontrivialZero, zeroMult, zerosIn,
   Ncount, Ndist, N0simple, Nsimple, and N0mult, which is the library's N0), so that the theorems
   here are about the same objects as the library's theorems.

3. Proof text. Some proofs here follow proofs of the library and reuse lines of them; the files
   say so in their comments. A comparison of the 212 files of the five developments with the
   library found lines identical to lines of the library in 35 of them, 149 lines of 11132
   (lines of 60 characters or more). The files with more than three such lines, and the library
   files they follow:
     Distinct839/Window/TVWindow.lean          Zeta23/XiPrime/QuarticWindow/ModWindow.lean
     Distinct839/WindowMoments/Ramp.lean       Zeta23/XiPrime/QuarticWindow/Moments.lean
     Distinct839/Gram/Threshold.lean           Zeta23/ZeroSide/RankTraceMult.lean
     Distinct839/Assembly/Threshold.lean       Zeta23/ZeroSide/RankTraceMult.lean
     Further/Threshold.lean                    Zeta23/ZeroSide/RankTraceMult.lean
     Distinct839/Assembly/Instance.lean        Zeta23/Assembly/SeamMult.lean
     Simple673/Assembly/Instance.lean          Zeta23/Assembly/SeamMult.lean
     Further/Line/Instance.lean                Zeta23/Assembly/SeamMult.lean
     Further/Dist/Instance.lean                Zeta23/Assembly/SeamMult.lean
     Line889/Assembly/Instance.lean            Zeta23/Assembly/SeamMult.lean
     Distinct839/Assembly/Final.lean           Zeta23/XiPrime/Assembly.lean
     Simple673/Assembly/Final.lean             Zeta23/XiPrime/Assembly.lean

The NOTICE file of the library is reproduced below, as its licence requires.

--------------------------------------------------------------------------------
Zeta23 — a Lean 4 formalization of critical-line zero-proportion theorems
Copyright 2026 Anthropic, PBC

This product is licensed under the Apache License, Version 2.0 (see LICENSE).

This product includes software derived from PrimeNumberTheoremAnd
(https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
Copyright the PrimeNumberTheoremAnd contributors, licensed under the Apache License, Version 2.0.
The derived files are the ones under Zeta23/FromPNTPlus/; each carries its upstream notice
(source file, upstream commit, original copyright line) and a description of the local modifications.
Some of those files in turn derive from mathlib (https://github.com/leanprover-community/mathlib4),
Copyright the mathlib contributors, Apache License, Version 2.0; their original headers are preserved.

This product depends on, but does not include, Lean 4 (https://github.com/leanprover/lean4) and
mathlib4 with its standard dependency set — fetched by the build tool from their public repositories at the
revisions pinned in lake-manifest.json: batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient and
plausible are released under the Apache License, Version 2.0; Cli (leanprover/lean4-cli) is released under the
MIT License (Copyright (c) 2021 Marc Huisinga). None of these dependencies is included in this repository.
--------------------------------------------------------------------------------

AMTOPA/zeta-exact-pressure LICENSE
Source: https://raw.githubusercontent.com/AMTOPA/zeta-exact-pressure/7253fdcab9366af45b8c8caf44e408c0af44a1a7/LICENSE

MIT License

Copyright (c) 2026 AMTOPA

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

teal-sea/zeta-lab LICENSE
Source: https://raw.githubusercontent.com/teal-sea/zeta-lab/aa6af68acd48466e9b005b80aaf608036de44c99/LICENSE

MIT License

Copyright (c) 2026 Thomas Lince

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Apache License, Version 2.0 (one copy for the Apache-licensed portions)
Source: https://github.com/kristianmk/839/blob/0e961ea199b425010843bc8044676d4ad29fe031/lean/LICENSE

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/