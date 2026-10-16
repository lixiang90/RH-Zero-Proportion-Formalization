"""Adapt capacity, band and separated remainder payments to actual new Fw.

All local-floor premises use the shared WindowGapEnergy.Fw definition. This
module establishes the algebraic/combinatorial consumer, not the new floor.
"""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
core=(ROOT/'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
cb=(ROOT/'StructuralResearch20261016/Coboundary.lean').read_text(encoding='utf-8')
cbc=(ROOT/'StructuralResearch20261016/CoboundaryCounting.lean').read_text(encoding='utf-8')
def section(source,start,end):
 a=source.index(start);return source[a:source.index(end,a)]
fw=section(core,'lemma Fw_windowGaps','section BlockPressure')
fw=fw.replace(' rw [hq]', ' simp only [wfun] at hq\n rw [hq]')
pairs=section(core,'lemma window_pairs_le_band','theorem block_energy_band')
band=section(core,'theorem band_close_n','theorem pressure_le_n')
sumblock=section(cb,'theorem block_energy_band_of_sum','theorem block_energy_band_summed')
sumblock=sumblock[:sumblock.rfind('/--')] if '/--' in sumblock else sumblock
sepblock=section(cb,'theorem block_energy_band_separated','/-- Existing sparse Gram payment')
remainder=section(cb,'theorem remainder_bound_separated_summed','theorem remainder_bound_separated_coboundary')
remainder=remainder[:remainder.rfind('/--')] if '/--' in remainder else remainder
block=section(cbc,'theorem block_remainder_bound_separated','/-- Close pairs')
def adapt(s):
 s=re.sub(r'\bFw\b','WindowGapEnergy.Fw',s)
 s=s.replace('OpethN.band_close_n','band_close_n')
 return s
head='''/- SPDX-License-Identifier: Apache-2.0
New-kernel capacity, band and separated remainder payments.
Adapted from BridgeW/OpethN in the attributed Core and the repository's
Coboundary module. Every energy premise uses shared WindowGapEnergy.Fw.
No local-floor or improved zero-proportion theorem is asserted here.
-/
import StructuralGoal20261016.WindowGapEnergy
import StructuralResearch20261016.Coboundary
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
open OpethN
namespace StructuralGoal20261016.WindowDiscreteEnergy

def kfun (x : ℝ) : ℝ := WindowKernel.k 24 WindowKernel.d24 x
def wfun (x : ℝ) : ℝ := WindowKernel.w 24 WindowKernel.d24 x
theorem kfun_neg (x : ℝ) : kfun (-x) = kfun x := by
 unfold kfun WindowKernel.k
 rw [WindowKernel.K_neg]
theorem wfun_neg (x : ℝ) : wfun (-x) = wfun x := by
 unfold wfun WindowKernel.w
 change kfun (-x)^2 = kfun x^2
 rw [kfun_neg]
theorem wfun_sub_comm (a b : ℝ) : wfun (a-b) = wfun (b-a) := by
 rw [← wfun_neg, neg_sub]
theorem wfun_nonneg (x : ℝ) : 0 ≤ wfun x := sq_nonneg _
theorem abs_kfun_le_one (x : ℝ) : |kfun x| ≤ 1 := WindowKernel.k24_abs_le_one x
theorem wfun_sub_le_norm_sq {g : ℂ} {t δ : ℝ}
 (h : ‖g-(kfun t : ℂ)‖ ≤ δ) : wfun t - 2*δ ≤ ‖g‖^2 := by
 have hk : ‖(kfun t : ℂ)‖ = |kfun t| := Complex.norm_real _
 have htri : abs (‖g‖-|kfun t|) ≤ δ := by
   rw [← hk]
   exact (abs_norm_sub_norm_le g _).trans h
 have hsq := sq_sub_two_mul_le_sq (abs_nonneg _) (abs_kfun_le_one t) (norm_nonneg g) htri
 rw [sq_abs] at hsq
 exact hsq

variable {n : ℕ}
'''
traits='''
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def SeparatedSummedCertificate {n : ℕ} (W : WCert n) (c C sep : ℝ) : Prop :=
 ∀ {m : ℕ}, n ≤ m → ∀ y : Fin m → ℝ, StrictMono y →
   (∀ i j, i ≠ j → sep ≤ |y i-y j|) →
   c*((m : ℝ)-((n-1 : ℕ) : ℝ))-C ≤
     ∑ i ∈ range (m-(n-1)), WindowGapEnergy.Fw W (windowGaps n (sortedExt y) i)

theorem summed_of_pointwise {n : ℕ} (hn : 2 ≤ n) (W : WCert n) {c sep : ℝ}
 (hfloor : ∀ g : Fin (n-1) → ℝ, (∀ i, sep ≤ g i) → c ≤ WindowGapEnergy.Fw W g) :
 SeparatedSummedCertificate W c 0 sep := by
 intro m hm y hy hsep
 have hwin : ∀ i ∈ range (m-(n-1)),
     c ≤ WindowGapEnergy.Fw W (windowGaps n (sortedExt y) i) := by
   intro i hi
   have hi' := Finset.mem_range.mp hi
   apply hfloor
   intro r
   have hr := r.isLt
   have hhi : i+((r : ℕ)+1) < m := by omega
   have hlo : i+(r : ℕ) < m := by omega
   change sep ≤ sortedExt y (i+((r : ℕ)+1))-sortedExt y (i+(r : ℕ))
   rw [sortedExt_of_lt y hhi, sortedExt_of_lt y hlo]
   have hp := hsep ⟨i+((r : ℕ)+1),hhi⟩ ⟨i+(r : ℕ),hlo⟩
     (by intro h; have := Fin.mk.inj_iff.mp h; omega)
   rw [abs_of_nonneg (sub_nonneg.mpr (hy.monotone (by
     change i+(r:ℕ) ≤ i+((r:ℕ)+1)
     omega)))] at hp
   exact hp
 have hs := Finset.sum_le_sum hwin
 rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
 have hc : ((m-(n-1) : ℕ) : ℝ) = (m : ℝ)-((n-1 : ℕ) : ℝ) := by
   rw [Nat.cast_sub (by omega : n-1 ≤ m)]
 rw [hc] at hs
 simpa only [sub_zero, mul_comm c] using hs

'''
sepblock=sepblock.replace('(sorted_separated hS hsep)',
 '(StructuralResearch20261016.Coboundary.sorted_separated hS hsep)')
tail='''
#print axioms summed_of_pointwise
#print axioms remainder_bound_separated_summed
#print axioms block_remainder_bound_separated
end StructuralGoal20261016.WindowDiscreteEnergy
end
'''
out=ROOT/'StructuralGoal20261016/WindowDiscreteEnergy.lean'
out.write_text(head+adapt(fw)+traits+adapt(pairs)+adapt(band)+adapt(sumblock)+adapt(sepblock)+adapt(remainder)+adapt(block)+tail,
 encoding='utf-8',newline='\n')
print(out.relative_to(ROOT),out.stat().st_size)
