# 固定 s1R 源的原 FS 非线性余项：只读静态审查

本包只读固定原源并推导符号公式；没有提取任何新 FS、评价任何点或核、计算曲率数值、生成矩阵、运行优化/扫描/Lean，也没有证明新的零点比例。它是备选数学接口，不是已执行的新家族。

绑定源：`research-goal-20261018-record-source-audit/snapshot/Solution.lean`，原始 UTF-8 1,818,411 B，SHA256 `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。所有下列行号指此原源。旧冻结包、I 合同及治理状态不改。

## 1. 实际函数和原有接口

- 132--149：当前 13 项 `cAMn/cAM/vAM`，不是旧核；373--375：积分 `KfunAM`、归一化 `kfunAM`、`wfunAM = kfunAM²`。416--418 给同一实际函数的 13 项 sinc 表达。
- 5951--5984：`KfunAM/K1AM` 的导数；`kfunAM'=k1AM`、`k1AM'=k2AM`；`wfunAM'=w1AM=2kk'`、`w1AM'=w2AM=2((k')²+kk'')`。这些是全实轴导数命题。
- 7613--7620：证书 `wfun/w1/w2` 是上述实际 s1R 函数的别名；证书 `kD=-1` 不构成曲率结论。
- 8133--8134：`LBSound top bk` 在指定闭区间内给 `lb/V <= wfun`。
- 9769--9773：`TVal` 同时含 anchor 位于 `[L,U]`、双侧导数界、以及 `v_p+w'(p/Q)(s-p/Q)<=w(s)`。它没有量化正二次余项。
- 10488--10550：`TVal_congr/TVal_mono`、`PVI`、`ivIn`、`tval_of_ivIn` 保留原 anchor word 与原有效区间。
- 10553--10614：`mokI -> mterm_okI/mtermTI`；9774--9829 的 `mterm_minV` 选择真实导数，但最终只输出线性 lower，舍去下述余项。

## 2. 一项原 FS 的精确余项分解

记 `Q=32768, D=10^9, V=10^10=10D, M=1024`。固定一项的原 `L0,L,U,Uc=uc L U`、原 FS `(kind,lambda,p,r)`；令

`lc=mwc kind lambda, l1=mw1 kind lambda, l2=mw2 kind lambda`。

保留原 guards：`L0<=L`、`lambda<=M`、`mokI=true`、`s in [L/Q,U/Q]`；因此 `lc+l1+l2=M`（8929），每个 active anchor `q=p/Q` 均满足 `L0/Q<=L/Q<=q<=U/Q`，且相应原 `TVal` 有效。只有 active（权非零）anchor 可使用其 `TVal`，不能以零权 payload 衍生新 tangent。

对每个 active anchor 定义

```
ell0 = L0/Q
v_p = lo32(f p)/V
dlo_p = (lo32(hi32(f p))-2D)/D
dhi_p = (2D-hi32(hi32(f p)))/D
d_p = w1(p/Q)
b = lb top bk L Uc / V
ell_p(s) = v_p+dlo_p*(s-ell0)-dhi_p*(p/Q-ell0)
```

`dlo_p <= d_p <= dhi_p` 由 `TVal`，所有减法在 cast 后是实数/有符号减法。8835--8843、8941--8944、9261--9265 及 10579--10594 的 Nat-sub cast 身份给出原 I 中混合仿射式恰为

```
alpha(s) = (lc*b+l1*ell_p(s)+l2*ell_r(s))/M.
```

这与原 `mvT/(VM)+(mcpT-mcnT)/(QDM)+sigma*(s-L0/Q)` 相同，其中 `sigma=(mslT-2D*mwT)/(DM)`；并非换 anchor、移动 `L0` 或按新联合区间重解 FS。

定义

```
B_p(s) = w(s)-v_p-d_p*(s-p/Q)
E_p(s) = (d_p-dlo_p)*(s-ell0)+(dhi_p-d_p)*(p/Q-ell0).
```

逐项精确恒等式是

```
w(s)-alpha(s)
 = [lc*(w(s)-b)+l1*(B_p(s)+E_p(s))+l2*(B_r(s)+E_r(s))]/M.
```

每个右项非负：`w-b` 用原 `LBSound` 及 `U<=Uc`；`B_p` 用原 `TVal`；`E_p` 用原双侧导数界、`s>=ell0`、`p/Q>=ell0`。这是所需新薄代数 lemma 的完整数学内容，源码尚无此打包 lemma。`mtermTI` 的存在导数不能被不经这层代数就反推成任意新 affine。

对整窗，pressure 部分在 `F9-A_C` 中精确抵消；10638--10649 的同一 `BS/TS/SA` 给

```
F9(g)-A_C(g) = (1/SA)*sum_e a_e*(w(span_e(g))-alpha_e(span_e(g))).
```

外部 `a_e` 是原 TS 权重，不能再次混入 FS `l1,l2`。反射仅映射 span 与 gap coefficient；原 anchor、`L0` 和 guards 不重解。

## 3. 最低新增解析成本的非线性信息：原组件包络

原 guards 分别已证 `w>=b` 以及对每个 active anchor `w>=ell_p`。故

```
rho_env(s)=max(b, active ell_p(s), active ell_r(s))-alpha(s) >= 0
w(s)-alpha(s) >= rho_env(s).
```

只有一项时按有效组件取 max；常数 `b` 始终由原 `LBSound` 有效，即便 `lc=0`。这恢复的是混合前组件信息，不等于在同一混合后 `A_L+A_R` 上更换 dual。I 点检验若对固定混合后 A 给负值，不会逻辑排除此不同的 piecewise-linear 模型。本包不作点检验，也不宣称此包络有任何实际增益。若未来使用，需要单独 gate、全域 coverage 和 branch/source 预算。

## 4. 可从现有区间证明抽出的定量曲率

5742--5829 的 `CellA` 已定义实际 `k,k',k''` 包络；7418--7434 的 `K0_enc` 用 `c.ok`，7485--7503 的 `K1_enc` 另需 `0<E2L`，7510--7540 的 `K2_enc` 再需 `0<E3L`，全都保留原闭区间 `[c.LN/Q,c.UN/Q]`。

令 `Z=DZ`、`a=(mabs c.K1).v`、`q=(c.K0.mul c.K2).lo.v`。`W2L` 的 5827--5829 定义及 7577 的等式给 `c.W2L.v=a²+qZ`。现有 7578--7602 的 `w2_nonneg` 证明实际先得到

```
a² <= (k'(x))²*Z²,
qZ <= k(x)k''(x)*Z².
```

因此在同一 `ok/E2L/E3L/closed interval` guards 下，能新增更强的薄 lemma

```
2*c.W2L.v/Z² <= w2AM(x).
```

这个定量式本身不需 `W2L.nonneg=true`；若要 `mu>=0`，必须另有该比较或更强有理数比较。原 7635 `convOk` 和 7696--7700 `cellConv_sound` 只导出非负；不能凭 bool true 宣称统一严格正曲率。旧 `chainOk/rgOk` 的 8764--8778、8792--8812、8915--8924 仅传播 `w2>=0`。要跨 chain 得到有理 `mu`，仍须证明每个覆盖 cell 的上述定量下界 `>=mu`，且完整覆盖原 segment。本包没有评价任何 cell 的该表达式。

若原完整闭区间上已认证 `w2>=mu>=0`，可由 5977--5984 的导数（或 7619--7620 别名）及二次修正函数的导数单调性新增薄 calculus lemma：

```
eps_p=w(p/Q)-v_p >= 0,
B_p(s) >= eps_p + mu/2*(s-p/Q)^2.
```

不需要假定全局凸，也不需要第三阶导数。可仿 8848--8911 的 MVT/monotone/tangent 证明对 `w(x)-mu*x²/2` 操作。`eps_p>=0` 来自 `PV`（9857），不是由一个孤立 `TVal` 自动得到。

### 不得越过的延伸区别

9994--10016 的 `tcheckZC/PZC` 允许凸 core 加两类外延；10059--10075 用 `rg_conv` 只证 core。10076--10115 的 derivative-order 外延和 10128/10130/10143/10145 的 `zsideF` 外延不同。后者可能靠近似点值的 slack 证明 `B_p>=0`，并不证明真实 tangent 或整段强凸。由 `TVal` alone 不能推出 `B_p>=eps_p+mu*(s-p/Q)^2/2`。

若新增量化 core 曲率且保留外部 derivative-order guards，可另证 saturated 余项

```
B_p(s) >= eps_p + mu/2*(clamp(s,za,zb)-p/Q)^2
```

（core 含 anchor），因为外侧 `B_p` 沿离开 core 的方向不减。这也不能直接用于只有 zside 的外延；那一部分必须仍用 `B_p>=0`，或另证新的 residual side guard。

## 5. 平方恒等式：成立但不能擅自丢交叉项

用实际 `k=kfunAM`、`a=k(q)`、`b=k1AM(q)`、`z=s-q`，375 及 5971 给纯代数恒等式

```
B_p(s) = eps_p + (k(s)-a)^2
                 + 2*a*(k(s)-a-b*z).
```

最后一项一般没有确定符号。`w=k²` 或 `w>=0` 不足以删去它；`TVal` 也不够。一个充分的附加局部 guard 是沿整个 `[q,s]` 有 `a*k2AM(x)>=0`，它令最后一项非负，从而得到 `B_p>=eps_p+(k(s)-a)^2`。可用原 K0/K2 包络证明这样的 guard，但尚未判定任何原 anchor/cell 满足它。若引入符号或绝对值上界，必须明确保留负误差项；不能把形式平方当免费正增益。

## 6. 真正的共享-span 补偿：weighted variance

若未来对同一物理 span `s` 的若干原 active anchors，各自已证完整适用域上的非负定量曲率，记

```
gamma_j = a_e*l_j*mu_j/(SA*M) >= 0.
```

两窗余项之和便至少包含 `1/2*sum_j gamma_j*(s-q_j)^2`（以及未丢弃的非负项）。当 `Gamma=sum gamma_j>0`，恒等式

```
sum gamma_j*(s-q_j)^2
 = Gamma*(s-qbar)^2 + sum gamma_j*(q_j-qbar)^2,
qbar=(sum gamma_j*q_j)/Gamma
```

将共享 span 的不兼容 anchor 转成有固定正项的 variance。两 anchor 的固定项为 `gamma1*gamma2/(gamma1+gamma2)*(q1-q2)^2`。这是可以跨越“混合后 A 的可行低点”障碍的具体数学信息；不需要把两个窗口的独立最小位置假设成可同时实现。所有 gamma、anchor separation、曲率适用域与实际增益均未评价，不能预判它足够付款。若无统一正曲率或 anchors 相同，它可能给零收益。

## 7. 所需额外命题和交付边界

最小复用链为：原 FS 组件/余项代数身份 → guarded quantitative `w2`（或另一 residual side guard）→ generic quadratic tangent → shared-span variance → 原实际联合目标与完整 coverage/counting。源已有实际函数导数和 K0/K1/K2 包络；后三个 thin lemma 及新目标 coverage 尚未形式化。不能用 Python 的 lower/model 数值代替这些解析和 Lean 义务。

当前原单源仅余 `2,000,000-1,818,411=181,589 B`。可复用 lemma 加少量 per-span 参数有可能比逐 pair 矩阵轻，但这里没有 source 尺寸或 Lean/nanoda 运行验证。任何 residual 新数据/点检验/新 family 执行均需另行 gate；本包不会自动触发。
