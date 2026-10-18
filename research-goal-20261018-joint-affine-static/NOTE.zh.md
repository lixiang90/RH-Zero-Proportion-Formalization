# 原 FS 的联合 affine 能量接口：只读推导

本包只读固定新source；不查询B/C数据、不算核、不分类、不pair scan、
不做LP/优化或Lean。父任务报告C首个真实相容例同时满足两个ordered条件；
这提示纯几何外包不够，不构成能量反例。本包不重算该case。

## 1. 从实际mtermTI抽出显式有理直线

固定source SHA f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。
来源为TVal (9769)、mterm_minV (9774)、mterm_okI (10563)、mtermTI
(10603)，而非将失败的tau版mcheckGX_sound当前提。

记Q=32768，R=1024，D=10^9，V=10^10，SA=10^20。
一个原state C与原FS的第e项给出原L0=eL0、L=eL、U=eU、
(k,m,p,r)。必须保留原mtermTI的hok/mokI与L0<=L，且s在[L/Q,U/Q]。
定义下面全部由原整数见证确定的数：

  v_e = mvT top bk f L (uc L U) k m p r
  cp_e = mcpT f L0 k m p r, cn_e = mcnT f L0 k m p r
  d_e = (mslT f k m p r - 2*D*mwT k m)/(D*R)
  beta_e = v_e/(V*R) + (cp_e-cn_e)/(Q*D*R) - d_e*L0/Q.

减法在cast到Int/Rat/Real后进行，绝不能用截断Nat.sub。
由mtermTI存在Dactual满足D*Dactual>=mslT-2D*mwT，且其实际term下界为

  Q*v_e + Q*V*Dactual*(s-L0/Q) + 10*(cp_e-cn_e)
     <= Q*V*R*wfun(s).

因为s>=L/Q>=L0/Q，可以用Dactual的有理下界替换。利用V=10D后得到

  beta_e + d_e*s <= actual wfun(s).

这是可直接证明的新薄lemma形状：给原mtermTI的analytic/finite guards，
结论为固定有理line的区间有效性；不要求原main floor检查在tau成功，
不需新w值、w'值或更高Taylor表。mcheckGX_sound (10174)已包含所有
需要的per-term输入及求和代数，但其直接结论是固定目标Pg，不暴露此line。
需要抽取中间推理，不能用其整个定理逆推出任意line有效。

## 2. 原cell上的实际窗口 affine

令a_e为TS的整数质量，b_r为BS整数压力，均按SA归一化。由34个a_e>=0
及term_range，得到对任意h在原InCell(C)内：

  A_C(h) = [sum_r b_r*h_r + sum_e a_e*(beta_e+d_e*span_e(h))]/SA
          <= F9(h).

展开为A_C=C_C+sum_r alpha_C,r*h_r，其中
C_C=sum_e a_e*beta_e/SA，
alpha_C,r=(b_r+sum_{e:i_e<=r<j_e} a_e*d_e)/SA。
pressure不丢，也不能在两个window相加时重复扣掉基线c9。
两原FS足以确定这些有限有理系数；原dual flows不是构造line所必需。

合法域仍是各自原state和原point范围。joint DBM可能把有效s区间收紧，
但不能把收紧后的L/U/L0喂回gptF/mcp/mcn或mokI，尤其anchor可能落在
新窄区间外，Nat.sub(p-L0)和TVal_mono的额外anchor条件会改变。
正确做法是保留原line的原区间证明，再由jointContains推出s仍在原区间。
不把某child FS无条件外推至parent，也不取两child line的max跨越合法域。

## 3. 九gap联合问题：比单窗tau判定弱的正确目标

physical h0..h8，左右使用各自原FS与原state，并用id/rev映射局部gap；
反射只置换gap和跨度，不改变actual F9。令A_L(h)、A_R(h)为两个嵌入后
的有理affine。则在共同合法域D内

  A_L(h)+A_R(h) <= E_L(h)+E_R(h).

目标是对每个覆盖pair/chart证A_L+A_R>=2c，其中
c=(c9+tau)/2=893766123055294719/10^20；无须逐pair证明
E_L>=tau或E_R>=tau。两者的析取是充分但过强的条件。
在共享七gap上先相加，把两侧相反符号的系数抵消，再统一取linear下界，
可避免两个window各自最坏位置无法同时实现造成的损失。

例如转换X_i=20Q*p_i后，sum gamma_r*h_r是十point potentials的divergence
线性形式。若D中每条有向edge满足Xj-Xi<=U_e，给出mu_e>=0且
div(mu)恰为负的目标potential系数，则

  C+sum gamma*h >= C-sum mu_e*U_e.

非零divergence残差须用已证各potential/gap范围另付款，不能删去。
足够的实际证书是非负有理mu、精确balance/constant等式和最终有理
下界>=2c；不用证明LP optimality。D来自两原states与sep，可忽略ordered
使域更宽；若使用ordered四point式，需真正的linear-inequality dual接口，
不可伪装成一条DBM edge。这里没有求出任何mu或新下界。

## 4. 原flows能复用什么，不能保证什么

MulOKg (9133)实际给出在原cell内非负slack

  B_C(h)=Cp-Cm+sum_r (P_r-S_r)*(Q*h_r-L_r) >=0.

由原A_C可取更保守的affine

  Aflow_C(h)=A_C(h)-B_C(h)/(Q*D*R*SA) <= A_C(h) <= F9(h).

这正对应source把原dual加入后再以Ng/gap_lo逐坐标付款的缩放。
左右两套flows可按物理跨度/反射嵌入并相加；每个原nonnegative move
仍有效。原state reference L的差异必须进入constant，不能强制同一L。
它们提供可复用的sound dual起点和可重建的九gap residual，不保证达到2c。
简单把两个已经支付完widths的local lower number相加只给已有基线。

若在共同域对raw A_L+A_R做精确joint DBM下界，允许的证书至少包含
原flow组合，且还可利用跨窗口/sep关系。即使不重新优化flows，先合并
两个Aflow的共享gap residual再统一付一次box/DBM支持，也可能减少两次
独立付款；是否达到目标是新有限算术义务，未执行、未获证。
不应为了复用flows而宣称Aflow在点值上强于raw A；它反而减去非负slack，
只是便于从较弱box域取得可证下界的dual表示。

## 5. 相关性在source哪一步损失

- TVal本来保留actual w1(p/Q)与完整原区间tangent。mterm_minV先用点
  slope上界支付anchor到L0的部分，后用slope下界替换Dactual，已经丢掉
  slope精确值；本文不恢复这部分，也不假设新导数包。
- constant kernel mass用整个原[L,uc L U]的lb，已丢该项的s依赖。
- mcheckGX_sound的S1→S2将span严格改写成gap求和，这一步是等式，不丢失。
- S3/gap_lo (8945)把每个剩余gap系数的负部独立付width，再用main
  inequality关闭。原MulOKg能保留部分单窗span关系，却没有把两window的
  shared gap和joint DBM一起最小化。该层正是本次可恢复的信息。
- 已经取完各window scalar lower number后无法凭数值反推被丢的coeff；
  但原FS、state、P/S/Cp/Cm仍在source，足够重建它们，无须新kernel样本。

## 6. baseline clipping接口及一个不应夸大的点

无论A如何抽取，原全域c9证明给出
E_L+E_R>=max(c9,A_L)+max(c9,A_R)。一个小而sound的有限dual接口是
给theta_L,theta_R在[0,1]，证明在joint域

  theta_L*A_L+theta_R*A_R+(2-theta_L-theta_R)*c9 >=2c.

因为max(c9,A)>=theta*A+(1-theta)*c9，它即可推出目标。theta=1,1
是直接联合affine；theta=1,0退化为单窗A_L>=tau。一般有理theta配合
joint dual只是候选certificate，无需在Lean证明优化器找到最优值。

然而对本文忠实抽出的同一原FS line，原mcheck成功的flow+gap_lo/main
链本身可抽出更强后果：Aflow_C>=c9于原cell，且A_C>=Aflow_C。
因此保持完整原cell的实际joint域内，max(c9,A_C)事实上等于A_C；
clipping在这种faithful提取上不自动创造新增益。若用其他更简化line或
尚未带出这个中间后果，clipping仍是合法备用接口，但不能宣传为已证
的新相关性。真正待检的是共同域的联合linear minimum能增加多少。

## 7. 最短actual连接与当前未完成事项

所需新可靠性证明仅为：mtermTI到signed rational line；34term正权求和
及原state域桥；两朝向/两窗口九gap coefficient等式；joint DBM dual
balance/cost（及残差如有）的soundness；固定pair/prod树覆盖；实际平均
WCert10及separated counting/matching。原PVI/LBSound/TVal合法区间不重采。
不可省的有限义务是每个欲关闭joint region的真实有理下界证书及完整覆盖。

本推导没有这些新finite witnesses，更未证明source<2MB或完整kernel链
<3200s。若后续授权一次数值机会关，应先固定使用哪种affine抽取/原flow
付款，再评价当前C见证对，不能用反复换line/精度掩盖失败；该建议不是
当前授权。本包到静态接口和scope为止，不启动新family或proofbatch。
