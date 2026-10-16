import StructuralW10Unconditional20261016.StreamingDual
import StructuralW10Unconditional20261016.FixedGeometry
/- A closed real subtree only. No global W10 floor is asserted. -/
import StructuralW10Cert20261016.ForcedCoverage2
import StructuralW10Cert20261016.FastPruefer

elab "#w10_timing" label:str : command => do
  let tick ← IO.monoMsNow
  Lean.logInfo m!"W10_TIMING {label.getString} {tick}"

set_option Elab.async false
noncomputable section
open StructuralW10Cert20261016
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralW10Unconditional20261016.StreamingDual128Smoke
-- original subtree r10000100010000101010010101101
def initialCell : Cl := ⟨[53405, 84441, 27852, 27852, 58918, 27852, 27852, 27852, 53405], [83123, 214665, 59345, 58982, 176339, 59014, 162711, 52275, 84578], [137846, 165698, 193550, 252468, 280320, 336602, 388877, 473455, 112293, 140145, 199063, 226915, 254767, 305754, 390332, 55704, 114622, 142474, 170326, 198178, 251583, 86770, 114622, 142474, 170326, 223731, 86770, 114622, 142474, 195879, 55704, 83556, 136961, 55704, 109109, 81257], [272705, 300557, 328409, 387327, 415179, 443031, 470883, 524288, 247152, 275004, 333922, 361774, 389626, 417478, 470883, 118327, 232043, 259895, 305185, 333037, 386442, 204191, 232043, 277333, 305185, 358590, 204191, 249481, 277333, 330738, 190563, 218415, 271820, 190563, 243968, 136853]⟩
def SL : List ℕ := [0, 0, 9, 10, 11, 12, 13, 14, 15, 16, 0, 0, 1, 17, 18, 19, 20, 21, 22, 23, 9, 1, 0, 2, 24, 25, 26, 27, 28, 29, 10, 17, 2, 0, 3, 30, 31, 32, 33, 34, 11, 18, 24, 3, 0, 4, 35, 36, 37, 38, 12, 19, 25, 30, 4, 0, 5, 39, 40, 41, 13, 20, 26, 31, 35, 5, 0, 6, 42, 43, 14, 21, 27, 32, 36, 39, 6, 0, 7, 44, 15, 22, 28, 33, 37, 40, 42, 7, 0, 8, 16, 23, 29, 34, 38, 41, 43, 44, 8, 0]
theorem hSL : SLok 9 PR SL := by decide +kernel
def T0 : ℕ := ~"0^F{qJR_tToL8japuHg[7bwoB*<?!xT8l/C|9.A^iE`&Abucs:5KL)kKyHy38pS/!2E/]-0?4eP239,sxfW$,`h+2$wDt;=#+yq_9[CS?GoZ~IR4$dUk#W'Z+{W*xE1Xj^A>&CjN%"
def T1 : ℕ := ~"5sU''Y^jtEk0_@]I*E;&^)4qoZb^QeCb&%yk[Dp+LS{)/nl2jiTFd5M)s'I15YawuUAv0l8{dH)^glnoeSST='JGy4?'BHhG|w.6LtsZ8NUzqG<ZU(4td*-p4h>y4$yu3h.VdTkAu"
def T2 : ℕ := ~"M+gU^T*a{#F&+grgR@7^cM<{$Z}F~YE}O,@7*C=GXc1^ewD;V_E!!qKd6/M|ByiS#*'tI=,MmrvHXA;x:8Rz`+]L6F2uo>Lw61w:T9_fF[teooZU6N=z6fuu'G3Gtj!U@+Z/,4l0E"
def T3 : ℕ := ~"%$Oz%q`cVo]aFfH+wtzDv$VTr&S19eOiB}..-iRta3|q8lD/sz{_=]Na2`3E#[*LF~}Z2LiWY>;XD%X;qv:C%ZNpiTh]~l=W:{-@/,^=kq9upjW14cAh#1qlV]U4{etj[4V;,oC"
def T4 : ℕ := ~"%K.j{}h*|oHZcM6&ox>hzt-X:_7CTy?TDY}l9F4)A(HPq/4YXjQQXJum(|AQ.z#t.l!M7L>pE.Ui5ao?&n2`!8OZ'52?)J]]h$_qGI1N!eP_Gm.$aHBUf7lFMnFqfWQaF4`#5th"
def T5 : ℕ := ~"#09.#frm@;*yB)(Iw,yUl&ey7#=!A2h{iV_8lXSgP#w~kZSJ@Szr.WOGj>s)s`|y^BtsEY}}3+h]N~dl=V8_}.Uj4gV`qV^SArCV~eO#VIC>`VN37uHI'(umE0Z_Azy<0&nv8nCGsJ"
def T6 : ℕ := ~"&Fgo0P-kUdSc[wB?f(.H^3W<jg1;dB5_F%5@Wz*?8&=YyKQ6?(7::8Xko~[v(tNV/v]k2L3}FIC#sH~$..W6'l<hGOf5CnDBnQ#mD`=SF*,TnD-QfeE?!W,7@9|Ig_hU:COYeh1"
def T7 : ℕ := ~"#=$H.2jbcAE)kR0::K[$NhG^B'*#@I$8m5yoAy2P+=wQ_Oe~ti$z*.ifA7PlhXD//vS6S8Gr8=NL,!~[WrV}VY1IIB,[:?cNSp*k0K'6xd;%wLUj4id~I:2$rLn.(UQnA5+"
def treeChunk (n : ℕ) : ℕ := (if n < 4 then (if n < 2 then (if n < 1 then T0 else T1) else (if n < 3 then T2 else T3)) else (if n < 6 then (if n < 5 then T4 else T5) else (if n < 7 then T6 else T7)))
def read (pos : ℕ) : ℕ := Nat.land (Nat.shiftRight (treeChunk ((pos-1)/32)) (28*((pos-1)%32))) 268435455
def D0 : ℕ := ~"#Y_q>wyZ:MYg`E0v~nIJf|[?v85:vS/F9f~[<<W&cVqEe=9'f>`)>)H7eVJVzvVq59UuJMxlK|P/N2<{@OqA)z4Y<zaj&vetIP(h1;+XY;nFLxS2rxZ9hb~]wDb?[b-V|GRK6=3W''+HHt:X7[4}pR`0cJ'E6Iv4,RTn-s!t>:+=mF,[g<IT:1q8uvEEqiP2N`5.LhanplK`<1}<iUo!cOlFVNuJg,)f-.kK&Hk?5xoU90*ocD2MG|^3(=%+XG_#tsnb?7CCYrXFZ<}{'P_?'S`.2c/;~H{^8#aunjG-u:8[pLEvYkhint_Q>0-L.9>PtEA&X?7[1WBx2XQkZ|)eDS4T~f5`u[Vhzu$v)E5K9y[#/n)Q9HwMA18Zk[it@|Y!9l=&KKvH<p<f>HJmB@bu}2!n2$#~/|QP[HwA95iF[^NFwdNJ0VLec-whJ~5Syt@<g`mJOJvpHyx]/E%<{z1iFM_8*KI#hZ65lZ^Vuz34>WZ4X*LwGVe6;HzRLB|F1X1@?({,'4gHEU5AOCMqeJB/M2&{(Bi:b-~~fKtlp3X&}QYzYiM$_%*A}AZ^Bb.?K%6TBjy/<RefNoDyS=AYhhSED2Df4eUS-hl0'*8SkXU5*iw>l8xs,&H_WhFGZzEu!V`V]p+fl+|](LfR64>AU)Gqsd{kxk}ly}|5`dTC9SI's?9b#.8d=UfO@2eV>%h|~l&BSxzl)I%{ervVkHdie|&$%q+>jqGS@M^`F;DWv.uPHQ^m/<|q`wz?PL3?!.tS2wc9t5d-Hfn0-Y7x3(OnzcL2`_m,C`,QBt)GEV(m9PS1AVb;g2EnE=pIFnm_~]|:T4-KcH[a`dxC;&HKEWmjR$U`o)4vgVs]-Lu4[qZF|s4g-C%Nw?0=RNvfdbf/2Ky:kMF3[E^[FCk_{5;h<A'xi59[m+K:n,HLZ!<OoZT-LK5ctPr>sw/TY+qayUSZD7=pPf}cTXC%P03T2_-V*1.[6U4vUFrteeL8/3-R(')@.-gN%m5I1u!G`6;Y+~Gk6)h[RX+hD4TV5b-Z&qq^6[W[Y*HfbAA]H6B&5[WD7/VTm1K~M)ea!e&opRK^?vcv,dN5f+hPl[j'{AX7;L,ZE~|FyRI1z%:b~NX9eMcXaM-V$`g#TW^-]uh:u>;wdUnvW#v<23*[aD}s(G)!@@BKuQd9m~KDu{pab_Q+~ybtT*M*L=`+Ku%7(O<GLpn7>0gJcs(*jaz8YK<OG2c)WI+7ym&?zMiN9CXY%Nf<[c3~lkK=35d{Nd(uz*e'lS)wQPIkq(.JL/.>tvm)o{lb!wo^EWMP[T'33DLP5wCJJWBNS8<Vh^:MLN4$@y~zrCq<@HzJg_|/IM&o8r]:Rc8jw"
def D1 : ℕ := ~"&nF;?R$wM@zCdzhI&_`;'8'6&z6FB+=s:2<x<8Z]uCs8g+',07_!ma,|lfIh|$RN>fy?2$/f,kQtiOU<RMl$x0N8-4mQ?$Lh5Vx!RF_q<%USA46?|s,Ye]H>eb!Y;}W.7PBk{C/o**H{d;E{q.!-Xg1zthp%[YK,;p(~&g)%jJi7LPJx`l<}3ORghgu7~woLo]C<4<luwQ^R8yb6<7sVr;ET_L:|_^#'{A4d.!Vl_9r_2HQC9@hM6+xZu_1F*&x:)`xMtiH3&=Nsrb>!t7*qZR(VJ--$qWFwa7amiIg/ncPRZ(j]sExkoFo3fi4.285%tyRuzdlPVvc5vkibkBLW21Y'IOhMO',FrYggw#|37P-<{PZuc&GXB=Ulu`iG$qf(.gZE^<F)ruGu]eJ<q(F:#~Kt=boB)RWZ14EN3yOfv2x)30yf1u4%A)l_(Qczraufj-0nQXvjRV.Lbse@_f|wZl4BSgRKCs#4?sQW&F+dZ<2#Z<mFt0DA8bcN)_xO|hMyt:aW=sE{8@@piJg%9>xaay7H7.j>$P+z/_PS(g8M.Z22.[w1J`rP]+qdex}a5{iV%hRXhnwx:B._JSnXb/CXOdNN0{fx~=%+I|5nZv1z={X}Zt1KJR*'!$T`W<,(S^WV|*V[x@%VoTs]=Oe@ZE9HoR#:xL?YucoTpZn<{3hsf@VI,[{UmRl5_z@$9g/)T$hGSEw[kW;8v;lyF[zHq_g{W4=c>ct6s#X3%!(xRXH%Qq-nEfzTGo#|u50LVlktM8]I|Za|L!{1tQ1Z1@^ntv%*Q$qGP#daJk`O~,wx__SX2{33BX-Ht9/CE)ZlKb{qtcY_WfgzvDBIYDaYWkSXLDJ~U}q6+_#eSp&N5*r&i40d#MGI4S*-'Phl8oP^[[f/q(fZA7jYt+XByJpVh%k@bdCF0,~|qKJ#[Dr})R2rBkcln=!;1r$kHIN0qEtju.*h1j:5_DLSeX&![33E;u)?T-Fuf1kB{-+pZh}&}(RgEP(beJ1*'@%p.'Q&)wMA?)<N/(S8<.G(R$$g7<UB[(hMwk;O;_K)1_{i<1ChnEDXmcf)RA!'EzGd):JA&~,=9f7zk:Ed*?LFQ6|jLCEpj:>7>k7$%'Ea'6E/('/~.]s7CTFg%1!q?1G+Qq~1AeeYWh-n47F}?q4KjSs^j<g47vJ8&:6T~j)+%=s(#dj,828%5CwJ9^G.oW8:qWtq^zET2fn`zYP1gfk5^hyA71xIJvLtI30qa~/AXiS3~Yp_*wwRC8u754_d2p(t3$?G;<@bF.x1Q[V=r:&=xATd%U%,z,HjW;+fw7i=k"
def D2 : ℕ := ~"7*qd1GtdQ/zw>}8o.FbPM.o_~K:q-%m+R1!l2[@S@wZ@HSq'550]?3!HW;>B8V0],aL>9Pd#&G}QFVyr918P]S#G&lcT$tw,M=`w;Ut9j5><0D.(]/MgM/0fs.&L*-R&I(w'NQ7nqIUCPs7.^FS`t)P[z_&@(>wgp[Pa3ObsHZZ3vk=1:^8,D|<>Bz6yKciJc8BHmwlF!tdB--no;l7PSW`Q,6}u(|l]Y8nAziI&Bjmw$%eHlw't8E#zgsvwiCd6m+|VAv:[/KX_#)&}#iMAB(CIX]TeG5PrfvMs^Y<9?]D413QGYRK|{M$zq';#),AK1E/Bc^;'}8B8_(BM@-6&Th5q@B{{1%/#5{vkpTXP^3T|eGX&j-6q[{qgNw1#[BuT.CN[mU+RhTkxjzDMV%@-Z~K9Dy<#bLCH5N3;~TDj_cr:WnXlBaWP@6y5f*l7m*n*S2!$h-G%GA-qIIr/2|3n09q_m5yQ>`r*Q,'4a!@JDfv7*0PO='Y/1D[C<r7uj7x#`?BIuyCq(qJuo_6i<Itd[-s[{0{JVRehb$4$;*N|^9tczt@quB,(k4-e5,MS]OXmrr':tySZ#`V#!@n99Uvd,]/Y3Q'u}21C>-{_xJK46S$'!d1%`,&rkJ`_.B%'bQHrPMy0'd_!u7XCj7<e'vU)ca*'8m5!d*;TswMZn?mPYmZY*pZ+02C!bi;5B[Wlf8cYo+,'/YeQB2j^Xd,k4SCUk9LbjI!yumGPunxdn:/,vC72N)Y3nCQ}k`lMIG/'_5TZi@iFew}Wy5KOvRo=^8DaW2@0lH,-?r=+'ybRt[u<b*Le@Yv!7X;*5bTEYI$rLGU}1?6JQzTKs@-gE}nzbZ6KKSP33B*-LndqxF}!gV4x<!B8uWFfgeL-E#Cu*v=lHG5d!V!=hIVBC>:o%}XD83l3wi0{FYwPB!G?5npef;|k(eDr[mHY]kZG,p-7%vkCH1r(tn;C`(w&NXj]lAsWB6,`OgOpxW@g`qlT4(rP{:wUB4/dZoUiDKWHmR|Sq*P3i-m|tpG(5_EE>8JZWDHK_p=.&22rUSmA;|BgO=x3Kh-cHX~S],|PI/oq>Igka%,p)85TZfPPDg=px(2-]A,zf%UC!t^kaOu/LhMGp{ph,Oul[3Ak5gfZ6;E=Ew:(CbGUy0Moi?Ty5K^O^&::5IyK};0p.V[T9V0b_h1?q/B:@L3:|5g8MN%XTR`S82Mm#[IQnRA[j15gX(}4[2ClP-1ah)qp~[xWH{s`WU~mFjrW*4F.VK=sl<x=:ElM0C:<xJ)=7sf;~9lO<'t&Mg/5O1i!}{#ib(u?Ea,4CV}F/W*,Ji4Um{ll]oO9krXMgHBm!/&L;qg1+mz1o,c-XG!+~LClMqK6$dA/w~pHl3c(o5DSn_+?0Ba2Ai&vZDau@ytu<GeGmTuSOVRJS;iA-EPpW9|c]jafCLW+R4Ai9VB;;y(GX|$D,Z`l@[v:E9eQ?4B{ky6&-|3]CXt&bqXXPCO'px"
def D3 : ℕ := ~"#H?|eTyNSK?cv(`8$As'|P1/P(4s4x)uWD^56hu.fGNzQ-Ca%(D2wZ}ss+FtCF:ot}}mVX)ju|@2zU'tIf%C)md^VY8O+I*A5FBA+6rBOq(Sq<7AMmP?E{U{~+T-%k&&4+,X7n[`/P}m1%r8I^|C)*ty0xfou)bIZ{+nbX8$7w7d&sZR#NaIo2z-sv!>*Aw1VVnCSv^fKLoK(UO{b:Mi0NslpUg:xE6QF&*[ux'V-O2wWG&l48xS1md^1D?fL2<(.1@*z+pD}|v[@ty,l3UQ,2`-9.0(=4D?eL95!>gXc7``f@Y<qWDu;LjVc!r-mj;8Z%JFzIo^B~REl(LkJ76U-GNz_eD~sv2arR;2{5BJ-O>zs~)5g,U:VX~{PN_[=}_KtUiKV&)6tqm+X_Gmk$D_l8zmjiDW4&-M18)EROhj)N@x}Fx1^&P22hj.Qf,uL]u-mT73'og?%uT@B+!<xDWFTuEs##bK|s.DFhwIy,zRk&Q<R%[Cjwc2jN;ls~~C8>QF#(cLiK|p:]]_G1jw!]]6<V[#A8/VwgW51Kv>#{BvQOJ-{y~AVX2LNC5.k2>goU}VP*I`!{)._lWBzP!B*id%,@]6pPd-+U}qf4Ii/@:EPAOq5TjKQ)S+pHyAQk7SO)ti4u%@}kwT'NHo|N_`n'<#N7dAk:Pn~N2F2}|=Xzj0M{vyIzu_M<IY1%ubdUfC11D.vVShRZ^M(,8f`Hx'q,Un+k9aPaygyfYJ:>#L7B7R/LyCP$B_VyJq)>aj}Uf4yT@8GT^!8#3{OweE8n6NRS-t@.2Hg'gqC1,3ZC,;c2kNa_A5#xXZ}DU!ks_{=Ng|pSIx_^XNAR$0C@~t1'FkM;H*/:;SE*<DSaG0J^S,48YN}i]I2;v%UA=hjrZeEP_pmo!80MNkZm?J7u;Rr)IhS_TbJgsz*&u&ukFpY@1w_V7dS^USPw.j)4lhJ+p@du;S5RMBq=$TM'hxD|O=J32'-fiKRQ^d:Bdvw:4-l%V]g.4|7U{`$ws<n6d;*k*][w&Oo*bqhPnQ>NB.Yk8_?D2[S?7hEn[<2T;4^9%n/J}?vt6Gc`}BLKmzK^GbmNyI.@NwY)QJ?aZ`P|m,eRWCG0.H9eB=)kgY.LuGTgaAqV*r<-W2{MQR{pOH8+F_s,5{vH(/%KUIXu)+b+8$|K|3aH'3Z%GSWcv]4D'^qr{yB@g}m-!01w985cI5}Gv(3-y0#?;mdzWL*lH~+~E|O=Hy8Zf%a3+%>+i2FhDfX<7]kkF[9iqTa/LhTi)kV(,[b[xMrn'j+:yb_5/dzvyT8yPfZ5,]'p>#Ey&bNss-1fOM<YN;p{,Qu)rAQ6*u2n|Rv+?I=@eWo`z.H$M#:5c`MB%bY'o<W&2M2wTY[3>o_!%S,s~E9lg>;Aqf^/yM88sH)j5eE:3Ct2q?KZ1<&`;5xmskQ.*Z3;b,Ke[OrWQ%K*t&O'tp"
def payloadChunk (n : ℕ) : ℕ := (if n < 2 then (if n < 1 then D0 else D1) else (if n < 3 then D2 else D3))
def pick : ℕ → ℕ → ℕ
  | 0, w => Nat.land (Nat.shiftRight w 11) (2 ^ (Nat.land w 2047) - 1)
  | n+1, w => pick n (Nat.shiftRight w (11 + Nat.land w 2047))
def payload (n : ℕ) : ℕ := pick (n%32) (payloadChunk (n/32))
def leafCheck := StreamingDual.dispatch cN payload
#w10_timing "certificate_begin"
theorem checked : FixedGeometry.walk SL read leafCheck 128 1 (FixedGeometry.Cell.ofCl initialCell) = 256 := by
  decide +kernel

#w10_timing "certificate_end"

theorem covered : CovBy 9 PR (Pg cN 9 BS TS) initialCell := by
  apply FixedGeometry.walk_sound hSL cN read leafCheck (StreamingDual.dispatch_sound cN payload) 128 1 (FixedGeometry.Cell.ofCl initialCell)
  rw [checked]
  decide
#w10_timing "soundness_end"
#print axioms covered
end StructuralW10Unconditional20261016.StreamingDual128Smoke
end
