/- Generated actual scalar checks. Partial pilots only. -/
import StructuralGoal20261016.WindowScalarLine
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowScalarLinePilot
def c0 : WindowConstantSupport.Support :=
  ⟨1,36864,(-4775065357770245891/100000000000000000000:ℚ),(-4775065357770245889/100000000000000000000:ℚ),(-14954807287718617177/20000000000000000000:ℚ),(-37387018219296542941/50000000000000000000:ℚ),(1/1024:ℚ),22107422⟩
theorem constant_check0 : WindowScalarLine.check (.constant c0) 36832 36896 = true := by decide +kernel
theorem constant_bound0 (x : ℝ) (hx : (36832:ℝ)/32768 ≤ x ∧ x ≤ (36896:ℝ)/32768) :
    (22107422:ℝ)/10000000000 ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowConstantSupport.sound constant_check0 hx
def c1 : WindowConstantSupport.Support :=
  ⟨3,86016,(566773748301612103/6250000000000000000:ℚ),(181367599456515873/2000000000000000000:ℚ),(-11720300102951100179/100000000000000000000:ℚ),(-732518756434443761/6250000000000000000:ℚ),(1/1024:ℚ),82024605⟩
theorem constant_check1 : WindowScalarLine.check (.constant c1) 85984 86048 = true := by decide +kernel
theorem constant_bound1 (x : ℝ) (hx : (85984:ℝ)/32768 ≤ x ∧ x ≤ (86048:ℝ)/32768) :
    (82024605:ℝ)/10000000000 ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowConstantSupport.sound constant_check1 hx
def c2 : WindowConstantSupport.Support :=
  ⟨8,274432,(2792027503549062313/100000000000000000000:ℚ),(1396013751774531157/50000000000000000000:ℚ),(91685439635599877/3125000000000000000:ℚ),(2933934068339196067/100000000000000000000:ℚ),(1/1024:ℚ),7778362⟩
theorem constant_check2 : WindowScalarLine.check (.constant c2) 274400 274464 = true := by decide +kernel
theorem constant_bound2 (x : ℝ) (hx : (274400:ℝ)/32768 ≤ x ∧ x ≤ (274464:ℝ)/32768) :
    (7778362:ℝ)/10000000000 ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowConstantSupport.sound constant_check2 hx
def c3 : WindowConstantSupport.Support :=
  ⟨16,516096,(-251352501715630201/20000000000000000000:ℚ),(-314190627144537751/25000000000000000000:ℚ),(3883192977450778887/100000000000000000000:ℚ),(485399122181347361/12500000000000000000:ℚ),(1/1024:ℚ),1569456⟩
theorem constant_check3 : WindowScalarLine.check (.constant c3) 516064 516128 = true := by decide +kernel
theorem constant_bound3 (x : ℝ) (hx : (516064:ℝ)/32768 ≤ x ∧ x ≤ (516128:ℝ)/32768) :
    (1569456:ℝ)/10000000000 ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowConstantSupport.sound constant_check3 hx
def t0 : WindowSupportCertificate.Support := ⟨1,28672,385761515,-458749500,1⟩
theorem tangent_check0 : WindowScalarLine.check (.tangent t0) 28608 28736 = true := by decide +kernel
theorem tangent_bound0 (x : ℝ) (hx : (28608:ℝ)/32768 ≤ x ∧ x ≤ (28736:ℝ)/32768) :
    WindowValueFlow.line (WindowScalarLine.plane (.tangent t0) 28608) x ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowScalarLine.sound tangent_check0 hx
def t1 : WindowSupportCertificate.Support := ⟨1,36864,22801249,71410182,1⟩
theorem tangent_check1 : WindowScalarLine.check (.tangent t1) 36800 36928 = true := by decide +kernel
theorem tangent_bound1 (x : ℝ) (hx : (36800:ℝ)/32768 ≤ x ∧ x ≤ (36928:ℝ)/32768) :
    WindowValueFlow.line (WindowScalarLine.plane (.tangent t1) 36800) x ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowScalarLine.sound tangent_check1 hx
def t2 : WindowSupportCertificate.Support := ⟨4,126976,5753651,-8962353,1⟩
theorem tangent_check2 : WindowScalarLine.check (.tangent t2) 126912 127040 = true := by decide +kernel
theorem tangent_bound2 (x : ℝ) (hx : (126912:ℝ)/32768 ≤ x ∧ x ≤ (127040:ℝ)/32768) :
    WindowValueFlow.line (WindowScalarLine.plane (.tangent t2) 126912) x ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowScalarLine.sound tangent_check2 hx
def t3 : WindowSupportCertificate.Support := ⟨4,135168,5264633,7768409,1⟩
theorem tangent_check3 : WindowScalarLine.check (.tangent t3) 135104 135232 = true := by decide +kernel
theorem tangent_bound3 (x : ℝ) (hx : (135104:ℝ)/32768 ≤ x ∧ x ≤ (135232:ℝ)/32768) :
    WindowValueFlow.line (WindowScalarLine.plane (.tangent t3) 135104) x ≤ WindowKernel.w 24 WindowKernel.d24 x :=
  WindowScalarLine.sound tangent_check3 hx
set_option pp.fullNames true
#print axioms constant_bound0
#print axioms constant_bound1
#print axioms constant_bound2
#print axioms constant_bound3
#print axioms tangent_bound0
#print axioms tangent_bound1
#print axioms tangent_bound2
#print axioms tangent_bound3
end StructuralGoal20261016.WindowScalarLinePilot
