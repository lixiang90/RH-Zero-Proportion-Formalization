# 固定 N2 Below 后的 μ 加权曲率余项：独立纸面接口

本文件只审数学接口，未计算曲率、跨度闭包、矩阵、p*、任何新FS/点/核值，也未执行LP或Lean。固定 N2 已终止且冻结327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f。其 G1322606/cells278,665/rev-id 只是当前 pooled 原组件模型的 Below，尚非 actual F 反例。以下新增前提并未消除。

## 1. 保留原组件的量化支付

原 source：`record-source-audit/snapshot/Solution.lean` SHA f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。Q=32768、D=10^9、V=10^10=10D、R=1024、κ=QRV。物理跨度 s，以原 PT 整数锚 p 表示 q=p/Q，原 l0=L0/Q。

一个 anchor 的量化资料为 v、dlN、duN，dl=dlN/D、du=duN/D。原源码 PVI/TVal 给出 v/V≤w(q)、dl≤w1(q)≤du，并给原适用区间的切线下界。N 原组件是

ell(s)=v/V+dl(s-l0)-du(q-l0)，

κ ell(s)=E+S B(X)，X=20Q·positions，S=(R/2)dlN，E=QRv-10R(dlN L0+duN(p-L0))。

由于原 guards 给 s≥L/Q≥l0、q≥L/Q≥l0，有

w1(q)(s-q)-[dl(s-l0)-du(q-l0)]
 = (w1(q)-dl)(s-l0)+(du-w1(q))(q-l0)≥0。

因此若另证 m≥0 且 w2(t)≥m 对 t∈hull({q},I) 成立，则

w(s)≥ell(s)+(m/2)(s-q)^2，s∈I。

必须保留原 L0、量化 derivative 区间及 E/S。不能改成未经原源码证明的裸点切线，也不能在 joint domain 收窄后重写原 L0。

**关键区间门槛**：原 q 可能不在两窗 joint feasible-span 区间 I 中。只在 I 有 w2≥m 不够；必须覆盖从原 q 到每个 s 的整段，即 hull({q},I)。q 仍是原 PT 点，不允许择新核锚。若没有已证正曲率，则直接使用原 ell 下界，付款取0；这不等于假设该段 w2≥0。

## 2. 原 raw dual 的统一支付

固定 N2 包内确有 valid raw dual，但外部独审仍另行。每 raw 行 a_r·z≤d_r，μ_r≥0，完整52坐标 b+Σμ_r a_r=0，raw baseline cost D0=-Σμ_r d_r。z包括10位置（gauge0）和42共享 T。

对正曲率已经证明的 anchor 行，实际点 T_e=κw(s_e) 满足更强的

a_r·z≤d_r-κ m_r(s_e-q_r)^2/2。

所以实际 raw objective O=b·z 满足

O≥D0+Σ_r c_r(s_e-q_r)^2，c_r=μ_r κ m_r/2≥0。

几何行、constant-component 行以及未获得正曲率的 anchor 行仍只有原 raw bound，不附加平方。不能为同一个已汇入 row 的 external a 再乘一次；原 grouped T mass 已由 full52 dual 平衡承担。

需要支付的缺口是 target-D0。**不是** target-某个 Below primal objective；valid primal/dual 未必目标相等。当前 packet 无须假定二者相等即可合法。

## 3. 同物理 span 的 weighted variance/clamp

对每 physical span e 汇集其所有正 c_r，令 C_e=Σc_r。

- C_e=0：该组贡献0，不能除以0。
- C_e>0：qbar_e=(Σc_r q_r)/C_e，V_e=Σc_r q_r²-(Σc_r q_r)²/C_e。

恒等式 Q_e(s)=Σc_r(s-q_r)²=C_e(s-qbar_e)²+V_e。若已证明真实 span s∈[L_e,U_e]，则

Q_e(s)≥V_e+C_e dist(qbar_e,[L_e,U_e])²。

区间可来自原两cell/分离的严格有理几何闭包，但这份纸面包没有计算闭包。闭区间接触保留；clamp 使用闭区间。qbar仅代数中心，不是新的 w/derivative 采样点。各组常数相加是一条保守 uniform 支付，尚未测量能否达到缺口。

## 4. 保留跨度相关性的二次网络

令 positions t∈R^10，B_e为实际正向 span incidence。Q(t)=Σ_r c_r(B_e t-q_r)²。若固定有理 t* 满足所有位置的精确法方程

Σ_r c_r(B_e t*-q_r)B_e=0，

则精确展开得

Q(t)=Q(t*)+Σ_r c_r(B_e(t-t*))²≥Q(t*)。

只核9个非gauge位置亦足够，但必须明确每 incidence 坐标总和0，剩余第0方程由总和恢复。无需一般数值PSD证书；非负平方权即可。正权子图可不连通，需逐连通分量的gauge/一致性处理，不能把 singular normal system 当无解。根尚未授权本包计算该系统或 t*。

t*不必在原几何域内，因为这里给整个位置空间的更宽域下界。它也不是新 kernel anchor，不在t*取w值。现有 Below primal 位置通常不满足该法方程，不能把在那里计算的 Q 值直接当 uniform 付款。若只近似驻点，展开还有2r·(t-t*)，r为法方程残差；必须明确另付该项或拒绝。不能静默丢弃。

若使用整数 X=20Q t，平方系数必须改成 c_r/(20Q)²，锚为20p_r；漏掉这个缩放会把付款放大。保持物理变量公式即可避免混淆。

## 5. 当前实际 source 的解析接缝与缺口

实际 source 的 source-only定位：

- 5971–5972：w1AM、w2AM的实际公式。
- 7573–7603：CellA.w1_enc、W2L_eq、w2_nonneg，使用K0/K1/K2实际interval包。
- 7613–7622：Cert.wfun/w1/w2与实际函数对应，HasDerivAt wfun/w1。
- 7635、7696–7701：convOk/cellConv_sound目前导出 w2≥0。
- 9769–9775、10500、10539–10559：TVal/PVI/ivIn/mokI的原锚/导数/区间合同。
- 10603–10616：mtermTI原整数消费接口。

CellA.w2_nonneg 的证明实际已经建立

W2L.v≤(k1AM(x)²+kfunAM(x)*k2AM(x))*DZ²。

因w2AM=2*(...)，可在相同 `c.ok=true`、`E2L>0`、`E3L>0` 和物理interval membership前提下薄化为

w2AM(x)≥2*W2L.v/DZ²。

原现成 theorem 只消费 W2L.nonneg 以导出0；本包没有新增Lean theorem，也没有计算任何W2L。若未来提供有理m，还须精确核 m*DZ²≤2W2L.v。因子2与DZ²不可遗漏。PVI/TVal本身只证明切线和点导数，不能直接提供正m。不能迁移旧24mode核的二阶表到此source的核。

因此下一个可审计量化包必须给：固定原 active anchor rowID/μ/原q；每个声称正m的 source CellA区间和完整ok/E2/E3/量化下界见证；证明覆盖hull(q,I)；原raw52/成本；exact非负c与variance或stationary identity。没有这些前提，本纸面公式不消除全域缺口。这里没有决定或运行任何新量化实验。
