import StructuralS1RM20261018.PhaseA1.QuantizedComponent
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.PCell AMW.Cert.Pyr AMW.Cert.PyrD
namespace StructuralS1RM20261018.LocalGeometry
def leftCell : Cl := ⟨[26112, 28545, 29184, 29666, 29666, 29184, 28545, 57729], [75995, 39936, 45301, 44151, 44151, 45301, 57659, 96765], [54657, 83841, 113507, 143173, 172357, 200902, 287745, 57729, 87395, 117061, 146245, 174790, 261633, 58850, 88516, 117700, 146245, 233088, 59332, 88516, 117061, 203904, 58850, 87395, 159753, 57729, 119361, 90177], [104540, 133724, 163390, 193056, 222240, 250785, 347550, 78725, 108391, 142272, 171456, 203904, 292551, 79846, 113727, 142911, 175359, 264006, 84543, 113727, 146175, 228311, 84061, 116509, 184160, 86843, 154494, 125310]⟩
def rightCell : Cl := ⟨[26112, 60721, 29184, 29666, 29666, 29184, 28545, 26112], [53902, 94169, 45301, 44151, 44151, 45301, 36510, 102463], [86833, 116017, 145683, 184715, 230016, 258561, 284673, 89905, 119571, 158603, 203904, 232449, 258561, 58850, 88516, 117700, 146245, 172357, 59332, 88516, 117061, 143173, 58850, 87395, 113507, 57729, 83841, 54657], [140106, 169290, 198956, 228622, 257806, 286351, 384896, 123353, 153019, 182685, 211869, 240414, 334912, 84333, 113999, 143183, 171728, 274191, 84815, 113999, 142544, 245007, 84333, 112878, 215341, 81811, 176309, 131008]⟩

def canonicalGap (P : ℕ → ℝ) (rev : Bool) (r : ℕ) : ℝ :=
  if rev then
    [P 9-P 8, P 8-P 7, P 7-P 6, P 6-P 5, P 5-P 4, P 4-P 3, P 3-P 2, P 2-P 1].getD r 0
  else
    [P 1-P 0, P 2-P 1, P 3-P 2, P 4-P 3, P 5-P 4, P 6-P 5, P 7-P 6, P 8-P 7].getD r 0

structure Domain (P : ℕ → ℝ) : Prop where
  left : InCell 8 AMW.Cert.PC9QB6M.PR leftCell (canonicalGap P false)
  right : InCell 8 AMW.Cert.PC9QB6M.PR rightCell (canonicalGap P true)
  separated : ∀ r < 9, (17 : ℝ)/20 ≤ P (r+1)-P r
  orderedLeft : P 1-P 0 ≤ P 8-P 7
  orderedRight : P 9-P 8 ≤ P 2-P 1

theorem canonical_span (P : ℕ → ℝ) (rev : Bool) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ 8) :
    gsum (canonicalGap P rev) i j =
      if rev then P (9-i)-P (9-j) else P j-P i := by
  have hi : i ≤ 8 := hij.trans hj
  cases rev <;> interval_cases j <;> interval_cases i <;>
    norm_num [canonicalGap, gsum_range, Finset.sum_range_succ] at * <;> ring

theorem numeric0 : eL0 AMW.Cert.PC9QB6M.TS leftCell 0 = 26112 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 0 = 26112 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 0 = 75995 ∧
    tI AMW.Cert.PC9QB6M.TS 0 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 0 = 1 := by decide +kernel
theorem range0 (P : ℕ → ℝ) (h : Domain P) :
    (26112 : ℝ)/SC ≤ P 1-P 0 ∧ P 1-P 0 ≤ (75995 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 0) (by decide)
  rcases numeric0 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 1 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric1 : eL0 AMW.Cert.PC9QB6M.TS leftCell 1 = 83841 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 1 = 83841 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 1 = 133724 ∧
    tI AMW.Cert.PC9QB6M.TS 1 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 1 = 3 := by decide +kernel
theorem range1 (P : ℕ → ℝ) (h : Domain P) :
    (83841 : ℝ)/SC ≤ P 3-P 0 ∧ P 3-P 0 ≤ (133724 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 1) (by decide)
  rcases numeric1 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 3 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric2 : eL0 AMW.Cert.PC9QB6M.TS leftCell 2 = 113507 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 2 = 113507 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 2 = 163390 ∧
    tI AMW.Cert.PC9QB6M.TS 2 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 2 = 4 := by decide +kernel
theorem range2 (P : ℕ → ℝ) (h : Domain P) :
    (113507 : ℝ)/SC ≤ P 4-P 0 ∧ P 4-P 0 ≤ (163390 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 2) (by decide)
  rcases numeric2 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric3 : eL0 AMW.Cert.PC9QB6M.TS leftCell 3 = 143173 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 3 = 143173 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 3 = 193056 ∧
    tI AMW.Cert.PC9QB6M.TS 3 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 3 = 5 := by decide +kernel
theorem range3 (P : ℕ → ℝ) (h : Domain P) :
    (143173 : ℝ)/SC ≤ P 5-P 0 ∧ P 5-P 0 ≤ (193056 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 3) (by decide)
  rcases numeric3 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric4 : eL0 AMW.Cert.PC9QB6M.TS leftCell 4 = 172357 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 4 = 172357 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 4 = 222240 ∧
    tI AMW.Cert.PC9QB6M.TS 4 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 4 = 6 := by decide +kernel
theorem range4 (P : ℕ → ℝ) (h : Domain P) :
    (172357 : ℝ)/SC ≤ P 6-P 0 ∧ P 6-P 0 ≤ (222240 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 4) (by decide)
  rcases numeric4 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric5 : eL0 AMW.Cert.PC9QB6M.TS leftCell 5 = 200902 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 5 = 200902 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 5 = 250785 ∧
    tI AMW.Cert.PC9QB6M.TS 5 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 5 = 7 := by decide +kernel
theorem range5 (P : ℕ → ℝ) (h : Domain P) :
    (200902 : ℝ)/SC ≤ P 7-P 0 ∧ P 7-P 0 ≤ (250785 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 5) (by decide)
  rcases numeric5 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric6 : eL0 AMW.Cert.PC9QB6M.TS leftCell 6 = 258631 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 6 = 287745 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 6 = 347550 ∧
    tI AMW.Cert.PC9QB6M.TS 6 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 6 = 8 := by decide +kernel
theorem range6 (P : ℕ → ℝ) (h : Domain P) :
    (287745 : ℝ)/SC ≤ P 8-P 0 ∧ P 8-P 0 ≤ (347550 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 6) (by decide)
  rcases numeric6 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 0 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric7 : eL0 AMW.Cert.PC9QB6M.TS leftCell 7 = 28545 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 7 = 28545 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 7 = 39936 ∧
    tI AMW.Cert.PC9QB6M.TS 7 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 7 = 2 := by decide +kernel
theorem range7 (P : ℕ → ℝ) (h : Domain P) :
    (28545 : ℝ)/SC ≤ P 2-P 1 ∧ P 2-P 1 ≤ (39936 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 7) (by decide)
  rcases numeric7 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 2 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric8 : eL0 AMW.Cert.PC9QB6M.TS leftCell 8 = 57729 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 8 = 57729 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 8 = 78725 ∧
    tI AMW.Cert.PC9QB6M.TS 8 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 8 = 3 := by decide +kernel
theorem range8 (P : ℕ → ℝ) (h : Domain P) :
    (57729 : ℝ)/SC ≤ P 3-P 1 ∧ P 3-P 1 ≤ (78725 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 8) (by decide)
  rcases numeric8 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 3 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric9 : eL0 AMW.Cert.PC9QB6M.TS leftCell 9 = 87395 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 9 = 87395 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 9 = 108391 ∧
    tI AMW.Cert.PC9QB6M.TS 9 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 9 = 4 := by decide +kernel
theorem range9 (P : ℕ → ℝ) (h : Domain P) :
    (87395 : ℝ)/SC ≤ P 4-P 1 ∧ P 4-P 1 ≤ (108391 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 9) (by decide)
  rcases numeric9 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric10 : eL0 AMW.Cert.PC9QB6M.TS leftCell 10 = 117061 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 10 = 117061 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 10 = 142272 ∧
    tI AMW.Cert.PC9QB6M.TS 10 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 10 = 5 := by decide +kernel
theorem range10 (P : ℕ → ℝ) (h : Domain P) :
    (117061 : ℝ)/SC ≤ P 5-P 1 ∧ P 5-P 1 ≤ (142272 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 10) (by decide)
  rcases numeric10 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric11 : eL0 AMW.Cert.PC9QB6M.TS leftCell 11 = 146245 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 11 = 146245 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 11 = 171456 ∧
    tI AMW.Cert.PC9QB6M.TS 11 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 11 = 6 := by decide +kernel
theorem range11 (P : ℕ → ℝ) (h : Domain P) :
    (146245 : ℝ)/SC ≤ P 6-P 1 ∧ P 6-P 1 ≤ (171456 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 11) (by decide)
  rcases numeric11 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric12 : eL0 AMW.Cert.PC9QB6M.TS leftCell 12 = 174790 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 12 = 174790 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 12 = 203904 ∧
    tI AMW.Cert.PC9QB6M.TS 12 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 12 = 7 := by decide +kernel
theorem range12 (P : ℕ → ℝ) (h : Domain P) :
    (174790 : ℝ)/SC ≤ P 7-P 1 ∧ P 7-P 1 ≤ (203904 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 12) (by decide)
  rcases numeric12 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric13 : eL0 AMW.Cert.PC9QB6M.TS leftCell 13 = 232519 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 13 = 261633 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 13 = 292551 ∧
    tI AMW.Cert.PC9QB6M.TS 13 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 13 = 8 := by decide +kernel
theorem range13 (P : ℕ → ℝ) (h : Domain P) :
    (261633 : ℝ)/SC ≤ P 8-P 1 ∧ P 8-P 1 ≤ (292551 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 13) (by decide)
  rcases numeric13 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 1 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric14 : eL0 AMW.Cert.PC9QB6M.TS leftCell 14 = 29184 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 14 = 29184 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 14 = 45301 ∧
    tI AMW.Cert.PC9QB6M.TS 14 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 14 = 3 := by decide +kernel
theorem range14 (P : ℕ → ℝ) (h : Domain P) :
    (29184 : ℝ)/SC ≤ P 3-P 2 ∧ P 3-P 2 ≤ (45301 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 14) (by decide)
  rcases numeric14 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 2 3 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric15 : eL0 AMW.Cert.PC9QB6M.TS leftCell 15 = 58850 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 15 = 58850 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 15 = 79846 ∧
    tI AMW.Cert.PC9QB6M.TS 15 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 15 = 4 := by decide +kernel
theorem range15 (P : ℕ → ℝ) (h : Domain P) :
    (58850 : ℝ)/SC ≤ P 4-P 2 ∧ P 4-P 2 ≤ (79846 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 15) (by decide)
  rcases numeric15 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 2 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric16 : eL0 AMW.Cert.PC9QB6M.TS leftCell 16 = 88516 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 16 = 88516 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 16 = 113727 ∧
    tI AMW.Cert.PC9QB6M.TS 16 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 16 = 5 := by decide +kernel
theorem range16 (P : ℕ → ℝ) (h : Domain P) :
    (88516 : ℝ)/SC ≤ P 5-P 2 ∧ P 5-P 2 ≤ (113727 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 16) (by decide)
  rcases numeric16 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 2 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric17 : eL0 AMW.Cert.PC9QB6M.TS leftCell 17 = 117700 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 17 = 117700 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 17 = 142911 ∧
    tI AMW.Cert.PC9QB6M.TS 17 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 17 = 6 := by decide +kernel
theorem range17 (P : ℕ → ℝ) (h : Domain P) :
    (117700 : ℝ)/SC ≤ P 6-P 2 ∧ P 6-P 2 ≤ (142911 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 17) (by decide)
  rcases numeric17 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 2 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric18 : eL0 AMW.Cert.PC9QB6M.TS leftCell 18 = 146245 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 18 = 146245 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 18 = 175359 ∧
    tI AMW.Cert.PC9QB6M.TS 18 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 18 = 7 := by decide +kernel
theorem range18 (P : ℕ → ℝ) (h : Domain P) :
    (146245 : ℝ)/SC ≤ P 7-P 2 ∧ P 7-P 2 ≤ (175359 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 18) (by decide)
  rcases numeric18 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 2 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric19 : eL0 AMW.Cert.PC9QB6M.TS leftCell 19 = 203974 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 19 = 233088 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 19 = 264006 ∧
    tI AMW.Cert.PC9QB6M.TS 19 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 19 = 8 := by decide +kernel
theorem range19 (P : ℕ → ℝ) (h : Domain P) :
    (233088 : ℝ)/SC ≤ P 8-P 2 ∧ P 8-P 2 ≤ (264006 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 19) (by decide)
  rcases numeric19 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 2 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric20 : eL0 AMW.Cert.PC9QB6M.TS leftCell 20 = 29666 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 20 = 29666 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 20 = 44151 ∧
    tI AMW.Cert.PC9QB6M.TS 20 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 20 = 4 := by decide +kernel
theorem range20 (P : ℕ → ℝ) (h : Domain P) :
    (29666 : ℝ)/SC ≤ P 4-P 3 ∧ P 4-P 3 ≤ (44151 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 20) (by decide)
  rcases numeric20 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 3 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric21 : eL0 AMW.Cert.PC9QB6M.TS leftCell 21 = 59332 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 21 = 59332 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 21 = 84543 ∧
    tI AMW.Cert.PC9QB6M.TS 21 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 21 = 5 := by decide +kernel
theorem range21 (P : ℕ → ℝ) (h : Domain P) :
    (59332 : ℝ)/SC ≤ P 5-P 3 ∧ P 5-P 3 ≤ (84543 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 21) (by decide)
  rcases numeric21 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 3 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric22 : eL0 AMW.Cert.PC9QB6M.TS leftCell 22 = 88516 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 22 = 88516 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 22 = 113727 ∧
    tI AMW.Cert.PC9QB6M.TS 22 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 22 = 6 := by decide +kernel
theorem range22 (P : ℕ → ℝ) (h : Domain P) :
    (88516 : ℝ)/SC ≤ P 6-P 3 ∧ P 6-P 3 ≤ (113727 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 22) (by decide)
  rcases numeric22 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 3 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric23 : eL0 AMW.Cert.PC9QB6M.TS leftCell 23 = 117061 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 23 = 117061 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 23 = 146175 ∧
    tI AMW.Cert.PC9QB6M.TS 23 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 23 = 7 := by decide +kernel
theorem range23 (P : ℕ → ℝ) (h : Domain P) :
    (117061 : ℝ)/SC ≤ P 7-P 3 ∧ P 7-P 3 ≤ (146175 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 23) (by decide)
  rcases numeric23 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 3 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric24 : eL0 AMW.Cert.PC9QB6M.TS leftCell 24 = 174790 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 24 = 203904 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 24 = 228311 ∧
    tI AMW.Cert.PC9QB6M.TS 24 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 24 = 8 := by decide +kernel
theorem range24 (P : ℕ → ℝ) (h : Domain P) :
    (203904 : ℝ)/SC ≤ P 8-P 3 ∧ P 8-P 3 ≤ (228311 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 24) (by decide)
  rcases numeric24 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 3 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric25 : eL0 AMW.Cert.PC9QB6M.TS leftCell 25 = 29666 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 25 = 29666 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 25 = 44151 ∧
    tI AMW.Cert.PC9QB6M.TS 25 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 25 = 5 := by decide +kernel
theorem range25 (P : ℕ → ℝ) (h : Domain P) :
    (29666 : ℝ)/SC ≤ P 5-P 4 ∧ P 5-P 4 ≤ (44151 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 25) (by decide)
  rcases numeric25 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 4 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric26 : eL0 AMW.Cert.PC9QB6M.TS leftCell 26 = 58850 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 26 = 58850 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 26 = 84061 ∧
    tI AMW.Cert.PC9QB6M.TS 26 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 26 = 6 := by decide +kernel
theorem range26 (P : ℕ → ℝ) (h : Domain P) :
    (58850 : ℝ)/SC ≤ P 6-P 4 ∧ P 6-P 4 ≤ (84061 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 26) (by decide)
  rcases numeric26 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 4 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric27 : eL0 AMW.Cert.PC9QB6M.TS leftCell 27 = 87395 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 27 = 87395 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 27 = 116509 ∧
    tI AMW.Cert.PC9QB6M.TS 27 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 27 = 7 := by decide +kernel
theorem range27 (P : ℕ → ℝ) (h : Domain P) :
    (87395 : ℝ)/SC ≤ P 7-P 4 ∧ P 7-P 4 ≤ (116509 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 27) (by decide)
  rcases numeric27 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 4 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric28 : eL0 AMW.Cert.PC9QB6M.TS leftCell 28 = 145124 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 28 = 159753 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 28 = 184160 ∧
    tI AMW.Cert.PC9QB6M.TS 28 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 28 = 8 := by decide +kernel
theorem range28 (P : ℕ → ℝ) (h : Domain P) :
    (159753 : ℝ)/SC ≤ P 8-P 4 ∧ P 8-P 4 ≤ (184160 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 28) (by decide)
  rcases numeric28 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 4 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric29 : eL0 AMW.Cert.PC9QB6M.TS leftCell 29 = 29184 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 29 = 29184 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 29 = 45301 ∧
    tI AMW.Cert.PC9QB6M.TS 29 = 5 ∧ tJ AMW.Cert.PC9QB6M.TS 29 = 6 := by decide +kernel
theorem range29 (P : ℕ → ℝ) (h : Domain P) :
    (29184 : ℝ)/SC ≤ P 6-P 5 ∧ P 6-P 5 ≤ (45301 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 29) (by decide)
  rcases numeric29 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 5 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric30 : eL0 AMW.Cert.PC9QB6M.TS leftCell 30 = 57729 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 30 = 57729 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 30 = 86843 ∧
    tI AMW.Cert.PC9QB6M.TS 30 = 5 ∧ tJ AMW.Cert.PC9QB6M.TS 30 = 7 := by decide +kernel
theorem range30 (P : ℕ → ℝ) (h : Domain P) :
    (57729 : ℝ)/SC ≤ P 7-P 5 ∧ P 7-P 5 ≤ (86843 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 30) (by decide)
  rcases numeric30 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 5 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric31 : eL0 AMW.Cert.PC9QB6M.TS leftCell 31 = 115458 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 31 = 119361 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 31 = 154494 ∧
    tI AMW.Cert.PC9QB6M.TS 31 = 5 ∧ tJ AMW.Cert.PC9QB6M.TS 31 = 8 := by decide +kernel
theorem range31 (P : ℕ → ℝ) (h : Domain P) :
    (119361 : ℝ)/SC ≤ P 8-P 5 ∧ P 8-P 5 ≤ (154494 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 31) (by decide)
  rcases numeric31 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 5 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric32 : eL0 AMW.Cert.PC9QB6M.TS leftCell 32 = 28545 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 32 = 28545 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 32 = 57659 ∧
    tI AMW.Cert.PC9QB6M.TS 32 = 6 ∧ tJ AMW.Cert.PC9QB6M.TS 32 = 7 := by decide +kernel
theorem range32 (P : ℕ → ℝ) (h : Domain P) :
    (28545 : ℝ)/SC ≤ P 7-P 6 ∧ P 7-P 6 ≤ (57659 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 32) (by decide)
  rcases numeric32 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 6 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric33 : eL0 AMW.Cert.PC9QB6M.TS leftCell 33 = 57729 ∧
    eL AMW.Cert.PC9QB6M.TS leftCell 33 = 57729 ∧
    eU AMW.Cert.PC9QB6M.TS leftCell 33 = 96765 ∧
    tI AMW.Cert.PC9QB6M.TS 33 = 7 ∧ tJ AMW.Cert.PC9QB6M.TS 33 = 8 := by decide +kernel
theorem range33 (P : ℕ → ℝ) (h : Domain P) :
    (57729 : ℝ)/SC ≤ P 8-P 7 ∧ P 8-P 7 ≤ (96765 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.left (n := 33) (by decide)
  rcases numeric33 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P false 7 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric34 : eL0 AMW.Cert.PC9QB6M.TS rightCell 0 = 26112 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 0 = 26112 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 0 = 53902 ∧
    tI AMW.Cert.PC9QB6M.TS 0 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 0 = 1 := by decide +kernel
theorem range34 (P : ℕ → ℝ) (h : Domain P) :
    (26112 : ℝ)/SC ≤ P 9-P 8 ∧ P 9-P 8 ≤ (53902 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 0) (by decide)
  rcases numeric34 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 1 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric35 : eL0 AMW.Cert.PC9QB6M.TS rightCell 1 = 116017 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 1 = 116017 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 1 = 169290 ∧
    tI AMW.Cert.PC9QB6M.TS 1 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 1 = 3 := by decide +kernel
theorem range35 (P : ℕ → ℝ) (h : Domain P) :
    (116017 : ℝ)/SC ≤ P 9-P 6 ∧ P 9-P 6 ≤ (169290 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 1) (by decide)
  rcases numeric35 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 3 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric36 : eL0 AMW.Cert.PC9QB6M.TS rightCell 2 = 145683 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 2 = 145683 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 2 = 198956 ∧
    tI AMW.Cert.PC9QB6M.TS 2 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 2 = 4 := by decide +kernel
theorem range36 (P : ℕ → ℝ) (h : Domain P) :
    (145683 : ℝ)/SC ≤ P 9-P 5 ∧ P 9-P 5 ≤ (198956 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 2) (by decide)
  rcases numeric36 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric37 : eL0 AMW.Cert.PC9QB6M.TS rightCell 3 = 175349 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 3 = 184715 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 3 = 228622 ∧
    tI AMW.Cert.PC9QB6M.TS 3 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 3 = 5 := by decide +kernel
theorem range37 (P : ℕ → ℝ) (h : Domain P) :
    (184715 : ℝ)/SC ≤ P 9-P 4 ∧ P 9-P 4 ≤ (228622 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 3) (by decide)
  rcases numeric37 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric38 : eL0 AMW.Cert.PC9QB6M.TS rightCell 4 = 204533 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 4 = 230016 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 4 = 257806 ∧
    tI AMW.Cert.PC9QB6M.TS 4 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 4 = 6 := by decide +kernel
theorem range38 (P : ℕ → ℝ) (h : Domain P) :
    (230016 : ℝ)/SC ≤ P 9-P 3 ∧ P 9-P 3 ≤ (257806 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 4) (by decide)
  rcases numeric38 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric39 : eL0 AMW.Cert.PC9QB6M.TS rightCell 5 = 233078 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 5 = 258561 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 5 = 286351 ∧
    tI AMW.Cert.PC9QB6M.TS 5 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 5 = 7 := by decide +kernel
theorem range39 (P : ℕ → ℝ) (h : Domain P) :
    (258561 : ℝ)/SC ≤ P 9-P 2 ∧ P 9-P 2 ≤ (286351 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 5) (by decide)
  rcases numeric39 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric40 : eL0 AMW.Cert.PC9QB6M.TS rightCell 6 = 259190 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 6 = 284673 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 6 = 384896 ∧
    tI AMW.Cert.PC9QB6M.TS 6 = 0 ∧ tJ AMW.Cert.PC9QB6M.TS 6 = 8 := by decide +kernel
theorem range40 (P : ℕ → ℝ) (h : Domain P) :
    (284673 : ℝ)/SC ≤ P 9-P 1 ∧ P 9-P 1 ≤ (384896 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 6) (by decide)
  rcases numeric40 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 0 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric41 : eL0 AMW.Cert.PC9QB6M.TS rightCell 7 = 60721 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 7 = 60721 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 7 = 94169 ∧
    tI AMW.Cert.PC9QB6M.TS 7 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 7 = 2 := by decide +kernel
theorem range41 (P : ℕ → ℝ) (h : Domain P) :
    (60721 : ℝ)/SC ≤ P 8-P 7 ∧ P 8-P 7 ≤ (94169 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 7) (by decide)
  rcases numeric41 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 2 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric42 : eL0 AMW.Cert.PC9QB6M.TS rightCell 8 = 89905 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 8 = 89905 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 8 = 123353 ∧
    tI AMW.Cert.PC9QB6M.TS 8 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 8 = 3 := by decide +kernel
theorem range42 (P : ℕ → ℝ) (h : Domain P) :
    (89905 : ℝ)/SC ≤ P 8-P 6 ∧ P 8-P 6 ≤ (123353 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 8) (by decide)
  rcases numeric42 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 3 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric43 : eL0 AMW.Cert.PC9QB6M.TS rightCell 9 = 119571 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 9 = 119571 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 9 = 153019 ∧
    tI AMW.Cert.PC9QB6M.TS 9 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 9 = 4 := by decide +kernel
theorem range43 (P : ℕ → ℝ) (h : Domain P) :
    (119571 : ℝ)/SC ≤ P 8-P 5 ∧ P 8-P 5 ≤ (153019 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 9) (by decide)
  rcases numeric43 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric44 : eL0 AMW.Cert.PC9QB6M.TS rightCell 10 = 149237 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 10 = 158603 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 10 = 182685 ∧
    tI AMW.Cert.PC9QB6M.TS 10 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 10 = 5 := by decide +kernel
theorem range44 (P : ℕ → ℝ) (h : Domain P) :
    (158603 : ℝ)/SC ≤ P 8-P 4 ∧ P 8-P 4 ≤ (182685 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 10) (by decide)
  rcases numeric44 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric45 : eL0 AMW.Cert.PC9QB6M.TS rightCell 11 = 178421 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 11 = 203904 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 11 = 211869 ∧
    tI AMW.Cert.PC9QB6M.TS 11 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 11 = 6 := by decide +kernel
theorem range45 (P : ℕ → ℝ) (h : Domain P) :
    (203904 : ℝ)/SC ≤ P 8-P 3 ∧ P 8-P 3 ≤ (211869 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 11) (by decide)
  rcases numeric45 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric46 : eL0 AMW.Cert.PC9QB6M.TS rightCell 12 = 206966 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 12 = 232449 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 12 = 240414 ∧
    tI AMW.Cert.PC9QB6M.TS 12 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 12 = 7 := by decide +kernel
theorem range46 (P : ℕ → ℝ) (h : Domain P) :
    (232449 : ℝ)/SC ≤ P 8-P 2 ∧ P 8-P 2 ≤ (240414 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 12) (by decide)
  rcases numeric46 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric47 : eL0 AMW.Cert.PC9QB6M.TS rightCell 13 = 233078 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 13 = 258561 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 13 = 334912 ∧
    tI AMW.Cert.PC9QB6M.TS 13 = 1 ∧ tJ AMW.Cert.PC9QB6M.TS 13 = 8 := by decide +kernel
theorem range47 (P : ℕ → ℝ) (h : Domain P) :
    (258561 : ℝ)/SC ≤ P 8-P 1 ∧ P 8-P 1 ≤ (334912 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 13) (by decide)
  rcases numeric47 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 1 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric48 : eL0 AMW.Cert.PC9QB6M.TS rightCell 14 = 29184 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 14 = 29184 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 14 = 45301 ∧
    tI AMW.Cert.PC9QB6M.TS 14 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 14 = 3 := by decide +kernel
theorem range48 (P : ℕ → ℝ) (h : Domain P) :
    (29184 : ℝ)/SC ≤ P 7-P 6 ∧ P 7-P 6 ≤ (45301 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 14) (by decide)
  rcases numeric48 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 2 3 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric49 : eL0 AMW.Cert.PC9QB6M.TS rightCell 15 = 58850 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 15 = 58850 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 15 = 84333 ∧
    tI AMW.Cert.PC9QB6M.TS 15 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 15 = 4 := by decide +kernel
theorem range49 (P : ℕ → ℝ) (h : Domain P) :
    (58850 : ℝ)/SC ≤ P 7-P 5 ∧ P 7-P 5 ≤ (84333 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 15) (by decide)
  rcases numeric49 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 2 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric50 : eL0 AMW.Cert.PC9QB6M.TS rightCell 16 = 88516 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 16 = 88516 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 16 = 113999 ∧
    tI AMW.Cert.PC9QB6M.TS 16 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 16 = 5 := by decide +kernel
theorem range50 (P : ℕ → ℝ) (h : Domain P) :
    (88516 : ℝ)/SC ≤ P 7-P 4 ∧ P 7-P 4 ≤ (113999 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 16) (by decide)
  rcases numeric50 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 2 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric51 : eL0 AMW.Cert.PC9QB6M.TS rightCell 17 = 117700 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 17 = 117700 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 17 = 143183 ∧
    tI AMW.Cert.PC9QB6M.TS 17 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 17 = 6 := by decide +kernel
theorem range51 (P : ℕ → ℝ) (h : Domain P) :
    (117700 : ℝ)/SC ≤ P 7-P 3 ∧ P 7-P 3 ≤ (143183 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 17) (by decide)
  rcases numeric51 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 2 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric52 : eL0 AMW.Cert.PC9QB6M.TS rightCell 18 = 146245 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 18 = 146245 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 18 = 171728 ∧
    tI AMW.Cert.PC9QB6M.TS 18 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 18 = 7 := by decide +kernel
theorem range52 (P : ℕ → ℝ) (h : Domain P) :
    (146245 : ℝ)/SC ≤ P 7-P 2 ∧ P 7-P 2 ≤ (171728 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 18) (by decide)
  rcases numeric52 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 2 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric53 : eL0 AMW.Cert.PC9QB6M.TS rightCell 19 = 172357 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 19 = 172357 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 19 = 274191 ∧
    tI AMW.Cert.PC9QB6M.TS 19 = 2 ∧ tJ AMW.Cert.PC9QB6M.TS 19 = 8 := by decide +kernel
theorem range53 (P : ℕ → ℝ) (h : Domain P) :
    (172357 : ℝ)/SC ≤ P 7-P 1 ∧ P 7-P 1 ≤ (274191 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 19) (by decide)
  rcases numeric53 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 2 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric54 : eL0 AMW.Cert.PC9QB6M.TS rightCell 20 = 29666 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 20 = 29666 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 20 = 44151 ∧
    tI AMW.Cert.PC9QB6M.TS 20 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 20 = 4 := by decide +kernel
theorem range54 (P : ℕ → ℝ) (h : Domain P) :
    (29666 : ℝ)/SC ≤ P 6-P 5 ∧ P 6-P 5 ≤ (44151 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 20) (by decide)
  rcases numeric54 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 3 4 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric55 : eL0 AMW.Cert.PC9QB6M.TS rightCell 21 = 59332 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 21 = 59332 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 21 = 84815 ∧
    tI AMW.Cert.PC9QB6M.TS 21 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 21 = 5 := by decide +kernel
theorem range55 (P : ℕ → ℝ) (h : Domain P) :
    (59332 : ℝ)/SC ≤ P 6-P 4 ∧ P 6-P 4 ≤ (84815 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 21) (by decide)
  rcases numeric55 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 3 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric56 : eL0 AMW.Cert.PC9QB6M.TS rightCell 22 = 88516 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 22 = 88516 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 22 = 113999 ∧
    tI AMW.Cert.PC9QB6M.TS 22 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 22 = 6 := by decide +kernel
theorem range56 (P : ℕ → ℝ) (h : Domain P) :
    (88516 : ℝ)/SC ≤ P 6-P 3 ∧ P 6-P 3 ≤ (113999 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 22) (by decide)
  rcases numeric56 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 3 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric57 : eL0 AMW.Cert.PC9QB6M.TS rightCell 23 = 117061 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 23 = 117061 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 23 = 142544 ∧
    tI AMW.Cert.PC9QB6M.TS 23 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 23 = 7 := by decide +kernel
theorem range57 (P : ℕ → ℝ) (h : Domain P) :
    (117061 : ℝ)/SC ≤ P 6-P 2 ∧ P 6-P 2 ≤ (142544 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 23) (by decide)
  rcases numeric57 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 3 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric58 : eL0 AMW.Cert.PC9QB6M.TS rightCell 24 = 143173 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 24 = 143173 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 24 = 245007 ∧
    tI AMW.Cert.PC9QB6M.TS 24 = 3 ∧ tJ AMW.Cert.PC9QB6M.TS 24 = 8 := by decide +kernel
theorem range58 (P : ℕ → ℝ) (h : Domain P) :
    (143173 : ℝ)/SC ≤ P 6-P 1 ∧ P 6-P 1 ≤ (245007 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 24) (by decide)
  rcases numeric58 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 3 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric59 : eL0 AMW.Cert.PC9QB6M.TS rightCell 25 = 29666 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 25 = 29666 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 25 = 44151 ∧
    tI AMW.Cert.PC9QB6M.TS 25 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 25 = 5 := by decide +kernel
theorem range59 (P : ℕ → ℝ) (h : Domain P) :
    (29666 : ℝ)/SC ≤ P 5-P 4 ∧ P 5-P 4 ≤ (44151 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 25) (by decide)
  rcases numeric59 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 4 5 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric60 : eL0 AMW.Cert.PC9QB6M.TS rightCell 26 = 58850 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 26 = 58850 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 26 = 84333 ∧
    tI AMW.Cert.PC9QB6M.TS 26 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 26 = 6 := by decide +kernel
theorem range60 (P : ℕ → ℝ) (h : Domain P) :
    (58850 : ℝ)/SC ≤ P 5-P 3 ∧ P 5-P 3 ≤ (84333 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 26) (by decide)
  rcases numeric60 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 4 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric61 : eL0 AMW.Cert.PC9QB6M.TS rightCell 27 = 87395 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 27 = 87395 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 27 = 112878 ∧
    tI AMW.Cert.PC9QB6M.TS 27 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 27 = 7 := by decide +kernel
theorem range61 (P : ℕ → ℝ) (h : Domain P) :
    (87395 : ℝ)/SC ≤ P 5-P 2 ∧ P 5-P 2 ≤ (112878 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 27) (by decide)
  rcases numeric61 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 4 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric62 : eL0 AMW.Cert.PC9QB6M.TS rightCell 28 = 113507 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 28 = 113507 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 28 = 215341 ∧
    tI AMW.Cert.PC9QB6M.TS 28 = 4 ∧ tJ AMW.Cert.PC9QB6M.TS 28 = 8 := by decide +kernel
theorem range62 (P : ℕ → ℝ) (h : Domain P) :
    (113507 : ℝ)/SC ≤ P 5-P 1 ∧ P 5-P 1 ≤ (215341 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 28) (by decide)
  rcases numeric62 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 4 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric63 : eL0 AMW.Cert.PC9QB6M.TS rightCell 29 = 29184 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 29 = 29184 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 29 = 45301 ∧
    tI AMW.Cert.PC9QB6M.TS 29 = 5 ∧ tJ AMW.Cert.PC9QB6M.TS 29 = 6 := by decide +kernel
theorem range63 (P : ℕ → ℝ) (h : Domain P) :
    (29184 : ℝ)/SC ≤ P 4-P 3 ∧ P 4-P 3 ≤ (45301 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 29) (by decide)
  rcases numeric63 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 5 6 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric64 : eL0 AMW.Cert.PC9QB6M.TS rightCell 30 = 57729 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 30 = 57729 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 30 = 81811 ∧
    tI AMW.Cert.PC9QB6M.TS 30 = 5 ∧ tJ AMW.Cert.PC9QB6M.TS 30 = 7 := by decide +kernel
theorem range64 (P : ℕ → ℝ) (h : Domain P) :
    (57729 : ℝ)/SC ≤ P 4-P 2 ∧ P 4-P 2 ≤ (81811 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 30) (by decide)
  rcases numeric64 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 5 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric65 : eL0 AMW.Cert.PC9QB6M.TS rightCell 31 = 83841 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 31 = 83841 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 31 = 176309 ∧
    tI AMW.Cert.PC9QB6M.TS 31 = 5 ∧ tJ AMW.Cert.PC9QB6M.TS 31 = 8 := by decide +kernel
theorem range65 (P : ℕ → ℝ) (h : Domain P) :
    (83841 : ℝ)/SC ≤ P 4-P 1 ∧ P 4-P 1 ≤ (176309 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 31) (by decide)
  rcases numeric65 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 5 8 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric66 : eL0 AMW.Cert.PC9QB6M.TS rightCell 32 = 28545 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 32 = 28545 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 32 = 36510 ∧
    tI AMW.Cert.PC9QB6M.TS 32 = 6 ∧ tJ AMW.Cert.PC9QB6M.TS 32 = 7 := by decide +kernel
theorem range66 (P : ℕ → ℝ) (h : Domain P) :
    (28545 : ℝ)/SC ≤ P 3-P 2 ∧ P 3-P 2 ≤ (36510 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 32) (by decide)
  rcases numeric66 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 6 7 (by decide) (by decide)] at hr
  exact hr.2

theorem numeric67 : eL0 AMW.Cert.PC9QB6M.TS rightCell 33 = 26112 ∧
    eL AMW.Cert.PC9QB6M.TS rightCell 33 = 26112 ∧
    eU AMW.Cert.PC9QB6M.TS rightCell 33 = 102463 ∧
    tI AMW.Cert.PC9QB6M.TS 33 = 7 ∧ tJ AMW.Cert.PC9QB6M.TS 33 = 8 := by decide +kernel
theorem range67 (P : ℕ → ℝ) (h : Domain P) :
    (26112 : ℝ)/SC ≤ P 2-P 1 ∧ P 2-P 1 ≤ (102463 : ℝ)/SC := by
  have hr := term_range AMW.Cert.PC9QB6M.hPR AMW.Cert.PC9QB6M.hTS h.right (n := 33) (by decide)
  rcases numeric67 with ⟨ha, hb, hc, hi, hj⟩
  rw [ha, hb, hc, hi, hj] at hr
  rw [canonical_span P true 7 8 (by decide) (by decide)] at hr
  exact hr.2

set_option pp.fullNames true
#print axioms canonical_span
#print axioms range0
#print axioms range67
end StructuralS1RM20261018.LocalGeometry
end
