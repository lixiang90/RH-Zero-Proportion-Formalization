# 原 flow 如何精确证明抽出的 A_FS >= c9

此为joint-affine-static的独立纸面addendum。旧frozen note不改。
没有读取或代入C point，没有新数值/核查询、优化、pair或Lean。

固定源为Solution.lean，SHA
f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。
使用9133 MulOKg、9340附近Ng、10155 mcheckGX、10174的S1–S5证明、
10603 mtermTI。以下全部有限sum/整数都指同一原numeric叶的原state/FS。

## 定义与前提

Q=32768，R=1024，D=10^9，V=10^10，SA=10^20，
kappa=Q*V*R=335544320000000000（原SLOPE），V=10D。
g为任意原InCell内点；z_r=Q*g_r-L_r，H_r=U_r-L_r。
原box guard L_r<=U_r给0<=z_r<=H_r。H是普通有符号差，与原Nat.sub相同。

第e项的a_e为TS整数质量，b_r为BS整数。按原mtermTI定义v_e、cp_e、
cn_e、m_e=mslT、w_e=mwT；这些都含FS内部R混合权，不含外部a_e。
L0_e=sum_{i_e<=r<j_e} L_r，来自eL0定义；term_range给s_e>=L0_e/Q。
原hok/PVI/LBSound等保证joint-affine-static所列原有理line：

  ell_e(s)=v_e/(V*R)+(cp_e-cn_e)/(Q*D*R)
           +(m_e-2D*w_e)*(s-L0_e/Q)/(D*R) <= actual wfun(s).

所有减法先cast为signed，不能把负slope或cp-cn截为Nat零。
各a_e>=0，故

  A(g)=[sum b_r*g_r+sum a_e*ell_e(s_e)]/SA <= F9(g).

原flow/ydec给P_r,S_r,Cp,Cm及MulOKg，即

  B(g)=Cp-Cm+sum_r(P_r-S_r)*z_r >=0.

定义Aflow(g)=A(g)-B(g)/(Q*D*R*SA)。于是Aflow<=A；不需新的flow。

## 精确代数恒等式

设sum_e:r in e表示原跨度含第r个gap，定义signed整数

  K_r=D*R*b_r+sum_e:r in e a_e*(m_e-2D*w_e)-P_r+S_r，

以及signed整数常数

  T=V*R*sum_r b_r*L_r+Q*sum_e a_e*v_e
       +10*sum_e a_e*(cp_e-cn_e)+10*(Cm-Cp)。

由span_e(g)-L0_e/Q=sum_e:r in e z_r/Q，有限求和交换及V=10D，严格有

  kappa*SA*Aflow(g)=T+10*sum_r K_r*z_r。

这一等式不是重新评价函数；即使形式上的参考gap L/Q本身不在nonadjacent
cell内也无妨，只是展开affine constant，未在参考点调用任何核定理。

原Ng f bs TS FS P S r定义的Nat subtraction正是

  N_r=max(2D*sum_e:r in e a_e*w_e+P_r
              -(D*R*b_r+sum_e:r in e a_e*m_e+S_r),0)
      =max(-K_r,0)。

不用假设K_r>=0；cast(Nat.sub x y)=max(x-y,0)处理两符号情况。
对任意0<=z<=H、N=max(-K,0)都有K*z>=-N*H：K非负时左边>=0；
K负时z<=H反向相乘。这就是source的gap_lo/S3，不能把负部支付符号倒转。
因此

  kappa*SA*Aflow(g)>=T-10*sum_r N_r*H_r。

## 与原main margin逐项完全相同

定义原mcheckGX main inequality的signed margin M0=RHS-LHS(cN)。
把其Nat加乘分别cast并移项，得到精确恒等式

  M0=T-10*sum_r N_r*H_r-kappa*cN。

这里T中的+10(Cm-Cp)对应原flow付款；term cp/cn与flow Cp/Cm不可混淆。
式中Q*sum a*v、V*R*sum b*L分别就是原32768*isum与
10240000000000*isum；所有constant和factor均来自同一source checker。
由原成功numeric check M0>=0，及kappa、SA>0，推出

  A(g)>=Aflow(g)>=cN/SA+M0/(kappa*SA)>=c9。

所以对本文忠实抽出的line，max(c9,A)=A在每个原cell内，非仅“可能”。
这一结论使用原完整main inequality及flow；若只知term guards不知main成功，
只能断A<=F9而不能断A>=c9。若换line/符号/舍入/缺flow或删cell约束，也不能
自动继承本结论。本包没有重新编译这个新中间lemma，只给完整源式推导。

## signed/Nat转化的必需守卫

- L<=U用于width Nat.sub；InCell用于0<=z<=U-L。
- L0<=L<=s*Q和mokI的active-anchor范围来自原term_range/mtermTI。
  active point p>=L0，故mcp/mcn的Nat.sub(p,L0)正确代表有符号差；
  若对应mw=0则该项为零，不需要无关point的额外不等式。
- mcp/mcn各自非负，但相减必须先cast；msl-2Dmw及K同理。
- Ng的截断恰好是max(-K,0)，不是近似等式；P/S不需有大小关系。
- 原hPR/hTS、尺寸、PVI/LBSound/mokI、MulOKg都保留；两窗口映射到共同
  physical gap时，各自原L0/P/S和constant不可互换。joint收紧不重解码points。

## 对下一固定C-potential诊断的纯逻辑含义（尚未执行）

若以后获授权，只把已存在并满足两原states的同一精确potential代入A_L/A_R，
那是有限有理affine评价，不是新kernel函数点。若该值之和<2c，则这个固定
pair的原二FS共同affine模型不可能证明全域sum>=2c：该点已经在其合法
joint域内，任何sound joint linear dual下界都不超过该点值。
上面的结论还给max(c9,A_L)+max(c9,A_R)=A_L+A_R，故baseline clipping
及其theta凸组合也救不了该固定模型；减去任何非负flow slack同样不能。
这不否定实际能量下界，更不否定所有可改FS/非线性方法。
反之一个点值>=2c只通过必要机会关，不证明共同域的minimum或新比例。
本授权未包含这次affine算术执行，本包到纸面逻辑为止。
