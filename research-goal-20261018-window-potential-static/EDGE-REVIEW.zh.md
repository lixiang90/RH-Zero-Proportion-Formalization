# 联合仿射边权与累计势函数：独立因子及计数审查

本文件只作符号与既存接口交叉核对，不执行 J、FS/点/矩阵/核、图搜索、势函数求解、优化或 Lean。旧 `CONTRACT.zh.md`、`INDEPENDENT.zh.md` 与 `independent-files.json` 不改。

审查的扩展文为 `JOINT-EDGE-EXTENSION.zh.md` SHA256 `0f8f4721de9de2297e35d72bac5fe7b5148f31035856e9c396cc1fb94b0b9540`。固定实际 s1R 源 SHA256 `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`；宏观004 SHA256 `b36cf3d32cae2a232dea169f7c90af5948d93f38040b4c3577bcc5793e848fea`。这些只标识当前版本，绝不预判 J 尚未执行的结果。

## 1. 有效 dual 的正确方向及 below-target 结论

记 `k=kappa*SA>0`、`d0=kappa*(Nc-N9)`、`T=4*kappa*Nc=4*k*c`。原155行统一写为 `a_r*X<=rhs_r`，I 的原仿射身份为 `C+b*X=2*k*(A_i+A_j)`；原解析 guards 必须保证各自 `A<=F`。

若有整数 `d>0,n_r>=0` 且全十坐标满足 `d*b+sum n_r*a_r=0`，则

```
d*(C+b*X) >= d*C-sum n_r*rhs_r = N,
2*k*(F_i+F_j) >= N/d.
```

这里不需声称 primal 可行、LP optimum 或 `N>=d*T`。即使 below-target，非负乘子、全 balance 和原 guards 核过后，N/d 仍为有效 joint lower；负乘子或 balance 失败不能记录为有效 bound。rank/full-basis 只是构造该 dual 的一种方式，不能代替显式证书检查。

## 2. 12、24、2 的缩放

从 joint lower 得

```
F_i+F_j-2*c >= (N-d*T)/(2*k*d).
```

若实际归一化 normal 的 determinant 检查及原 small-minor 前提给 `d in {1,2,3,4}`，则 `12/d` 为整数，且

```
24*k*(F_i+F_j-2*c) >= (12/d)*(N-d*T).
```

原 scalar floors 同时给 `F_i+F_j-2c >= (Mi+Mj-2d0)/k`，故另一下界恰为 `24*(Mi+Mj-2d0)`。二者取 max 合法：

```
W_ab=max(24*(Ma+Mb-2d0), (12/d)*(N-d*T)),
F_a+F_b-2*c >= W_ab/(24*k).
```

无有效 dual 时只能保留 baseline。不能在 d 不整除12或 normal 被重新缩放时使用 floor 除法替代精确除法。det<=4 只适用原153个 incidence normals 加至多两个原 Ordered（各为两个 incidence 的差）；新增 energy row、重新归一化或新 side condition 都需重审。权重 n 的 numerator 不受4限制。

## 3. 有向 star 链与累计能量

沿用 2374 个 id/rev 标签，物理转移 `((i*1187+j)*4+chart)` 仍映射 `2*i+chart//2 -> 2*j+chart%2`；局部反射不反向这条边。严格 Empty 的边可删除；其余保守未解及 paid 边不能因为没有成功 joint dual 就删除。

star 取形式能量 `tau=2c-c9`。真实窗口 a 的 baseline 给

```
tau+F_a-2c >= Ma/k.
```

因此双向 star 边权为 `24*Ma`，约束 `Qstar=0` 便等价于 `-24Ma<=Qa<=24Ma`。star 无需几何可实现，因为这些是为代数闭链强加的数值约束。

若所有允许有向边均有 `Q_b-Q_a<=W_ab`，沿 `star,a0,...,a(L-1),star` 先由 Q 相消得 `sum W>=0`，再由各 pair lower 得

```
2*sum_r F_r+2*tau-2*(L+1)*c >= 0,
sum_r F_r >= L*c-(tau-c).
```

加强后的 W 属于 pair 能量下界，不能代入原 `Phi=(q-M+2d0)/(2k)` 的单窗推导。单对真实能量或 affine 平均小于 c，均不自动否定可摊销累计模型。

## 4. K 旧环只提供一个固定的必要门

原 K 九边负环已由独立 receipt `2b21a5a0a8c1a628a2aa14c8f7530de34d5ba9714adb30998013a1951e405d14` 逐边核过。若未来仅用固定 J 家族的全部有效 bounds 强化这九条边后，精确 sum W 仍严格负，则这个固定加强后的外图 Q 模型矛盾；不需启动全图 Q 求解。

若 sum W 非负，只通过该环必要关，不能宣称图无负环或存在 Q。成功时仍需全部 paid、全部 sparse 保守边及全部 star 约束的完整证书；失败也不证明实际多窗环可实现或实际能量反例。本次没有计算任何加强后 W。

## 5. paid 隐式族的 suffix 公式

对给定旧向量 D，目标 b 的所有 paid 入边约束右端的最小值确为

```
24*(Mb-2d0)+min_{a:Ma>=2d0-Mb}(D_a+24*Ma).
```

source 集合是全部2374有向标签；同 Mi 的 id/rev 仍有各自 D。eligible 为空时 minimum 为正无穷，不产生放松。同步算法可写 `Dnew_b=min(Dold_b,RHS(Dold))`；若改顺序更新必须另声明。按原 M 排序的 suffix minimum 只是对这个给定向量的等价 RHS 构造，不自动提供收敛、无负环、Q 存在或资源保证。

## 6. 实际 counting 桥及交付义务

若完整 Q 及真实转移覆盖均成立，对 m>=9 个 17/20 分离排序点，新累计结论给 `(m-8)c-eta<=sum_windows F9`，其中 `eta=tau-c=c-c9`。源 5316 的 `block_energy_band` 在 5330--5345 消耗逐窗 floor；须在这里换累计假设。5346--5357 的 W9 容量/pressure 求和可复用。源 16566 的余项桥及 matching 仍需新的分离累计版本，不能直接填原 pointwise hCert。

匹配中只有 `S none` 是唯一余项块（16644--16662 已给17/20分离），额外 eta 只收此块一次；所有 pair 块仍用原 `c<=1/64` 的 close-pair bound。源 16701--16711 的 None charge 结构可复用。小块 m<9 用非负 defect 单独处理。

在 `0<=c9<=c`、`delta>=0` 下，`0<=eta<=c`，故匹配后强估计

```
(c-32delta)*m-B*R-8c-eta <= Dcirc
```

可保守放宽为 `(c-36delta)*m-B*R-9c<=Dcirc`，恰接源 16720 的 `ActualDefectEstimate Z 10 c B`。这里只是现有误差/端点接口参数10；实际 band、权重和容量仍是 W9。可直接接 16725 的 `defect_to_dyadic` 与 16859--16860 的 `cumulative_of_dyadic`，不把 eta 偷塞入原更强 n=9 类型。

所有 affine 解析 guards、完整几何/能量覆盖、整数 Q 及计数桥尚须进入 Lean。数据、共享 decoder、原状态反射、全 paid/sparse/star 检查和最终 wrapper 均需计入181,589B余量及3200秒整体政策预算。此静态审查不是新 global floor、无条件比例或网站提交通过。
