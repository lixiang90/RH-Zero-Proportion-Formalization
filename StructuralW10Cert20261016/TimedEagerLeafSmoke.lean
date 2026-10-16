/- A closed real subtree only. No global W10 floor is asserted. -/
import StructuralW10Cert20261016.ForcedCoverage2
import StructuralW10Cert20261016.EagerLeaf

elab "#w10_timing" label:str : command => do
  let tick ← IO.monoMsNow
  Lean.logInfo m!"W10_TIMING {label.getString} {tick}"

set_option Elab.async false
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralW10Cert20261016.TimedEagerLeafSmoke
-- original subtree r0110001000111110011001
def initialCell : Cl := ⟨[27852, 50025, 27852, 27852, 79677, 27852, 27852, 49267, 50637], [49289, 81554, 59308, 59228, 169563, 59260, 48659, 81975, 82461], [77877, 105729, 133581, 213258, 241110, 277809, 359784, 442245, 77877, 105729, 185406, 213258, 241110, 310495, 392956, 55704, 135381, 163233, 191085, 240352, 311402, 107529, 135381, 163233, 212500, 263137, 107529, 135381, 184648, 235285, 55704, 104971, 155608, 77119, 127756, 99904], [130843, 190151, 223467, 303144, 330996, 358848, 408115, 458752, 140862, 195615, 275292, 303144, 330996, 380263, 430900, 118536, 225267, 253119, 280971, 330238, 380875, 197415, 225267, 253119, 302386, 353023, 197415, 225267, 274534, 325171, 107919, 189894, 245494, 130634, 213095, 164436]⟩
def SL : List ℕ := [0, 0, 9, 10, 11, 12, 13, 14, 15, 16, 0, 0, 1, 17, 18, 19, 20, 21, 22, 23, 9, 1, 0, 2, 24, 25, 26, 27, 28, 29, 10, 17, 2, 0, 3, 30, 31, 32, 33, 34, 11, 18, 24, 3, 0, 4, 35, 36, 37, 38, 12, 19, 25, 30, 4, 0, 5, 39, 40, 41, 13, 20, 26, 31, 35, 5, 0, 6, 42, 43, 14, 21, 27, 32, 36, 39, 6, 0, 7, 44, 15, 22, 28, 33, 37, 40, 42, 7, 0, 8, 16, 23, 29, 34, 38, 41, 43, 44, 8, 0]
theorem hSL : SLok 9 PR SL := by decide +kernel
def T0 : ℕ := ~"0Y_]6R'x|Ry/WDr}Wt}<.2<@|IXegI!>QS-z&6q=CYe_+%-/Do2b~1&1uk<jTvn1](abGI=0:&4-moTM)LMpsDH2xN@^,#>CUfg-lkFY24lO,=I%|s*^:v&PLfSO!erz4:tzw'e;x"
def T1 : ℕ := ~"V|t?BC1hLJ`2u2K=#Ahp*koqWu_F0,,<}fyJ.D6bWp3Sif^ZDY]5$%B0;sUI?>b6?eX->wLjcWmpt*5_._ZeH*WuU6~LJW&oOutIp4[kZDe+e-V=5R8YcxGcIgm`e.JB-f"
def treeChunk (n : ℕ) : ℕ := (if n < 1 then T0 else T1)
def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455
def D0 : ℕ := ~"#[^l7AcT8Ra%$~u$aMLkt*Sco*@D&B5qYB%>Em}#l(xGfOa>Mb.V+9QbtXRZBmH6UTVfK4>];Gp1oi4eEv3IQNECxvcs2[wo8:Qf~ef0pV$jCv2'9|BS:/57F1TALPa3*Qk/;E{@9<KzCQt<!m5jjP6KlQYtL5*QJUkQ)G)qli%3+:Fn$7@>7Q@#wc3OlS`;Yui3Oyq?pr9,^1I+$J=HDe&p=H-b)B0&dQ|:n{G0fiyX>=<g.M,U^$'|Y{'YQ>0(]5;<orgiGAA#:wWe_2H3;fB1EG7OpAvp@Us{s/szRWHIXVH8aKv=Ah6D](Y>_Cr]`cY_(2EjM4(flmV:hm,(ng8aHG)8H<@+qi25r=E#g:Oyb3l1v3i)Yp,;#!LJ^eD*#+fl[=D'i[_*@m[fro^roJ(1etX7nrY3$/T{v#XbiKTY^78E.zi3TrG<VF}sRI+30kq)kFx>ICZiI,SeVSkgX0^O$YaJ=>w~R:*s2Z<QF1<N%iQ*;[D[vZS:<+IW1rv$qjE1j42A:u9=_6kjRJN%;l3O]8KX:?lLz).+pemUEQU*w}k@=pm@CxK44m)WtWdR??,`j)[,[gn>CZu7o.K-dtOw*YU6!-LV|6qm?Cu*_@!Rg-{rnG^F4)-EyE&4;{R;e&e,?{{w;MP3g_JZbpxK@tp2KLYxtsW,3U@[R8S$fxB=hzZ|(I=e#$ebf0giJJ0o.wwA*b2rhaGK'L!+*^qS?/pI:loMhf+c|LMcL!Xmk}D8_=wJ=7u]RD#]7q}9*R|9(u`2H^`e551Wza'0Fr/y=+w586bvmeIg'?Zdq6>4h6sI*ZYEOVS.|]se3{6wiVt~Q/ViNu?OcXWXzlI<L2lt1d|%7_YlY48Gv:S(ZS%wBftaaT|@WI5)>/my=1BZ+PY{$SdwhNQF$`tdXqU!i1d:t,IKqp9,M5IgTHIv'NRP6yKd>ITJw.G,Tw8+ek<??J95;M_grkpNn8Msdu.dj+5CWo1iRkKy%KCmRYiA&!=OC9<aLrbt!h6NWaM|4P/to*F'OAYW6mo@nV*K`imS.IZ!P_~`#@/Y$maU9:Q|z4;5ln*@z%eC=C=*2?>{Cgd]4l=;yr|+$zBF>IwZ'@g1D[QxHHl;;sKB=QPFqq#8A4&5>j$'@yE}xV!u8Q(E'~snY[m7~d%4q>Da<-1QjzyliFZrE]wFXqq{sy:iQ7/m^iMR~QOHfFnsX,Dh_g-r!?N0hK&p)mR!0t10!@'hvjV6vZr145Cq1Fgb#>+5Z^6khycE#Q@:"
def payloadChunk (n : ℕ) : ℕ := D0
def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
def leafCheck := EagerLeaf.dispatch payload
#w10_timing "certificate_begin"
theorem checked : ForcedCoverage2.walk SL read leafCheck 128 1 initialCell = 64 := by
  decide +kernel

#w10_timing "certificate_end"

theorem covered : CovBy 9 PR (Pg cN 9 BS TS) initialCell := by
  apply ForcedCoverage2.walk_sound hSL read leafCheck (EagerLeaf.dispatch_sound payload) 128 1 initialCell
  rw [checked]
  decide
#w10_timing "soundness_end"
#print axioms covered
end StructuralW10Cert20261016.TimedEagerLeafSmoke
end
