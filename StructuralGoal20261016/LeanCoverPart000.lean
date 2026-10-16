/- Complete frozen subtree. Only the final composition covers the full domain. -/
import StructuralGoal20261016.LeanCoverBase
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralGoal20261016.LeanCoverBase
open StructuralW10Unconditional20261016
open StructuralW10Cert20261016
namespace StructuralGoal20261016.LeanCoverPart000
-- Frozen tree path r000
def initialCell : Cl := ⟨[27852, 27852, 27852, 27852, 27852, 27852, 27852, 27852, 27852], [88480, 88480, 88480, 88480, 88480, 88480, 88480, 88480, 88480], [55704, 83556, 111408, 139260, 167112, 194964, 222816, 250668, 55704, 83556, 111408, 139260, 167112, 194964, 222816, 55704, 83556, 111408, 139260, 167112, 194964, 55704, 83556, 111408, 139260, 167112, 55704, 83556, 111408, 139260, 55704, 83556, 111408, 55704, 83556, 55704], [116332, 144184, 172036, 199888, 227740, 255592, 283444, 311296, 116332, 144184, 172036, 199888, 227740, 255592, 283444, 116332, 144184, 172036, 199888, 227740, 255592, 116332, 144184, 172036, 199888, 227740, 116332, 144184, 172036, 199888, 116332, 144184, 172036, 116332, 144184, 116332]⟩
def T0 : ℕ := ~"--.CZ=T.0_>rnN3mu!|HqWB'R}il[50)mb4(xd{H'q4L{Q3hzEK.#"
def treeChunk (n : ℕ) : ℕ := T0
def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455
def D0 : ℕ := ~"4!+ute7-`mUt4g`Y/7?Zph%EHp`}Q_[n,.$?__2S5MGC<X]X}9T(2M='Y!Y`Hc9PAVPidjdZM8Q)5*=+!G0v;@g.3--E!<W,^rV4Murw[CK,P&>b/8E/`u}o2_]wM[F'@Iltnh[povdnCO6nhShR1=}[R+uZ*DuAN8YVYDG&AYP7H+n;y?o[gkJ:|26b=$e&Sds#J1I,xnk??H57f>E1~s.pYPUBw5d`pGbYN"
def payloadChunk (n : ℕ) : ℕ := D0
def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
def leafCheck := ForcedCoverage2.dispatch payload
theorem checked : FixedGeometry.walk SL read leafCheck 128 1 (FixedGeometry.Cell.ofCl initialCell) = 14 := by
  decide +kernel
theorem covered : CovBy 9 PR (Pg cN 9 BS TS) initialCell := by
  apply FixedGeometry.walk_sound hSL cN read leafCheck (ForcedCoverage2.dispatch_sound payload) 128 1 (FixedGeometry.Cell.ofCl initialCell)
  rw [checked]
  decide
#print axioms covered
end StructuralGoal20261016.LeanCoverPart000
end
