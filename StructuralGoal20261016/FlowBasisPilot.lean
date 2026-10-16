/- Real OBBT flow data; no global floor or zero proportion is claimed. -/
import StructuralGoal20261016.FlowBasisCodec
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.FlowBasisPilot
open FlowBasisCodec
def upper : Fin 10 → Fin 10 → ℤ := ![![0, 765058, 796546, 828034, 859522, 891010, 922498, 953986, 985474, 1016962], ![-31488, 0, 403138, 434626, 466114, 497602, 529090, 560578, 592066, 985474], ![-62976, -31488, 0, 297460, 328948, 360436, 391924, 423412, 560578, 953986], ![-94464, -62976, -31488, 0, 255780, 287268, 318756, 391924, 529090, 922498], ![-125952, -94464, -62976, -31488, 0, 237464, 287268, 360436, 497602, 891010], ![-157440, -125952, -94464, -62976, -31488, 0, 255780, 328948, 466114, 859522], ![-188928, -157440, -125952, -94464, -62976, -31488, 0, 297460, 434626, 828034], ![-220416, -188928, -157440, -125952, -94464, -62976, -31488, 0, 403138, 796546], ![-251904, -220416, -188928, -157440, -125952, -94464, -62976, -31488, 0, 765058], ![-283392, -251904, -220416, -188928, -157440, -125952, -94464, -62976, -31488, 0]]
def edges0 : List Edge := [(0, 7), (2, 1), (4, 1), (5, 1), (6, 3), (8, 5), (8, 7), (9, 7)]
def coefficient0 : Fin 10 → ℤ := ![8368619520000000000000, -31329852482483404800000, 17390996152890857881600, -10951768532748632064000, 13136706536029172531200, -13136706536029172531200, 10951768532748632064000, -17390996152890857881600, 18595611433212071116800, 4365621529271333683200]
def target0 : ℤ := (-3321130684399778562834432000)
theorem checked0 : checkBasis edges0 upper coefficient0 0 target0 = true := by decide +kernel
theorem bound0 (x : Fin 10 → ℝ) (hx : ∀ i j, x j-x i ≤ (upper i j : ℝ)) :
    (target0 : ℝ) ≤ ∑ i, (coefficient0 i : ℝ)*x i := by
  simpa using checkBasis_sound edges0 upper coefficient0 0 target0 checked0 x hx
def edges1 : List Edge := [(2, 0), (2, 1), (3, 0), (4, 3), (6, 1), (6, 5), (8, 5), (8, 7), (9, 5)]
def coefficient1 : Fin 10 → ℤ := ![-2211760060570699038720, -26059946051429300961280, 25449650370160673423360, -5548507599876941414400, 6655465355623027179520, -6655465355623027179520, 5548507599876941414400, -8810821196156879503360, 9421116877425507041280, 2211760060570699038720]
def target1 : ℤ := (2154674697444881969876828160)
theorem checked1 : checkBasis edges1 upper coefficient1 0 target1 = true := by decide +kernel
theorem bound1 (x : Fin 10 → ℝ) (hx : ∀ i j, x j-x i ≤ (upper i j : ℝ)) :
    (target1 : ℝ) ≤ ∑ i, (coefficient1 i : ℝ)*x i := by
  simpa using checkBasis_sound edges1 upper coefficient1 0 target1 checked1 x hx
def edges2 : List Edge := [(2, 0), (2, 1), (2, 3), (2, 5), (4, 3), (6, 3), (8, 5), (8, 7), (9, 7)]
def coefficient2 : Fin 10 → ℤ := ![-1582852391749892505600, -6742249147287905894400, 71031093219037798400000, -68696409194959033139200, 4763002752494868889600, -4763002752494868889600, 3970805279321997312000, -6305489303400762572800, 6742249147287905894400, 1582852391749892505600]
def target2 : ℤ := (-17549066058849243718536396800)
theorem checked2 : checkBasis edges2 upper coefficient2 0 target2 = true := by decide +kernel
theorem bound2 (x : Fin 10 → ℝ) (hx : ∀ i j, x j-x i ≤ (upper i j : ℝ)) :
    (target2 : ℝ) ≤ ∑ i, (coefficient2 i : ℝ)*x i := by
  simpa using checkBasis_sound edges2 upper coefficient2 0 target2 checked2 x hx
def edges3 : List Edge := [(2, 0), (2, 1), (3, 1), (3, 4), (3, 5), (6, 4), (8, 5), (8, 7), (9, 4)]
def coefficient3 : Fin 10 → ℤ := ![-1334802100702017945600, -5685664925019940454400, 5317350128162393292800, 28986736737559565107200, -28318685277503355289600, -4016588099317995929600, 3348536639261786112000, -5317350128162393292800, 5685664925019940454400, 1334802100702017945600]
def target3 : ℤ := (-6153508757365276134919372800)
theorem checked3 : checkBasis edges3 upper coefficient3 0 target3 = true := by decide +kernel
theorem bound3 (x : Fin 10 → ℝ) (hx : ∀ i j, x j-x i ≤ (upper i j : ℝ)) :
    (target3 : ℝ) ≤ ∑ i, (coefficient3 i : ℝ)*x i := by
  simpa using checkBasis_sound edges3 upper coefficient3 0 target3 checked3 x hx
set_option pp.fullNames true
#print axioms bound0
#print axioms bound1
#print axioms bound2
#print axioms bound3
end StructuralGoal20261016.FlowBasisPilot
