# 原组件流归一化：独立条件审查

本报告只作精确符号证明与源码接口审查；不提取 FS、不评价任何数值、
不构造或求逆矩阵、不执行 LP/核/Lean。已只读对照 joint 静态说明全部
1--10节：NOTE SHA `1d5c4d98fad774370a38d0a128fce2e3f75ab1c2f0f645c23266f7acaea47ca8`，
其最终 manifest SHA `3b322277203c58be7885b73bf2301024f00bf1e48ac33ae6cfe54aa5daec79ad`。
全部版本也由本目录 manifest 的只读依赖固定。M 的既有局部独审仍独立封存，
本文不改变其原证书、support 或 source，也不选择新 case。

## 1. 先固定 raw 模型，再作正比例列变换

每项 e 的 component 行为

```text
S_ej * n_e · X - T_e <= -E_ej,
n_e = e_v-e_u,     objective T_e coefficient = 2a_e > 0.
```

同一项所有 components 在同一原 cell 上合法，normal n_e 相同。
先给每项选定一个 reference base，记其乘子 μ_e0，其余为 μ_ej。
完整 T-balance 强制

```text
μ_e0 = 2a_e - Σ_(j≠0) μ_ej.
```

消去这68个 base 后，位置 balance 为

```text
b_tilde + Σ_geo μ_r a_r + Σ_extra μ_ej ΔS_ej n_e = 0,
b_tilde = b_position + Σ_e 2a_e S_e0 n_e,
ΔS_ej = S_ej-S_e0.
```

当前 raw pressure、a、S 都是整数，故 b_tilde 为整数且十坐标总和为0。
对 ΔS≠0 定义 γ_ej=|ΔS_ej| μ_ej，则 γ≥0，normalized column 恰为
sign(ΔS_ej) n_e，且恢复 μ_ej=γ_ej/|ΔS_ej|。这是可逆的正对角列变换，
不改变该已选 support 的位置 balance 或非负性；它没有求解新优化问题。

这个结论必须用于原 raw ±1 geometry/Ordered normals，不能将 HiGHS 的
变量/行尺度直接混入，再套整数 minor 界。gauge 删 X0 列不改变实数域，
不是假设 X 或 gap 为整数；最终 checker 应仍核完整10位置及68T balance。

## 2. 小分母结论的精确前提

normalized columns 是有向 incidence columns，加至多两条原 Ordered
columns。每条 Ordered 是两个 incidence columns 的有符号和，故任意
r×r square minor 对这 k≤2 列多线性展开至多2^k项；每项由 incidence
子矩阵的全幺模性为0或±1。因此非零 determinant 的绝对值至多2^k≤4。

若固定 normalized selected support 由 r 个线性独立列组成，取 r 个独立
坐标方程，其整数 RHS 和 Cramer 法则给 γ 及 geometry 乘子的共同分母
|det|≤4；其余坐标方程还必须一致。r=9 的 full-rank basis 是直接情形。
若有更多依赖列，必须明确选择独立 support/free 参数约定并核原全部
方程与质量条件，不能凭 support 条数或“minor≤4”声称解唯一或非负。

这个结论不约束 b_tilde 或 γ 的整数 numerator 大小，更不声称恢复后的
raw μ_ej 也有≤4分母；后者还有 |ΔS_ej| 因子。不同 extra/geometry 可以
有相同 incidence normal，但其原 row、term、cost 和 mass cap 不同，
不能仅按 normal 相同就无条件合并。独立 selected support 里相同列会
造成依赖；若想删除/换列，需要另外证明非负、质量及 Lower 不受损。

## 3. full-rank9 时的 forest 与至多两条 Order

设一个固定 full-rank9 selected support 含 k 条 Ordered（0≤k≤2），
其余9-k条 incidence 列。incidence 列必须自身独立，否则全部列也依赖。
因此保留原 edge labels 的10顶点无向底图是 forest，有 k+1 个连通分量；
孤立点同样计为分量，不能丢弃。

令 η 是这 k 条 Ordered 的乘子，令

```text
q = b_tilde + Σ_order η_s O_s.
```

每个 forest 分量必须满足 Σ_(v in component) q_v=0。因全体坐标总和0，
取其中 k 个独立分量方程解 η；full rank 保证适当 k×k系统非奇异。
其 determinant 等于原 normalized basis determinant 的符号倍（forest
leaf elimination 是整数 unimodular 消元），所以同样≤2^k≤4。
其余分量方程也必须核，不能只选择方便的方程而漏一致性。

给定 η 后，每条 oriented forest edge u→v 的 γ/geometry flow 由 cut 唯一
决定：删该 edge，取含 head v 的一侧 A，则 flow=−Σ_(z in A)q_z。
这给一个不需要一般大矩阵 inverse 的 exact decoder。所有 flow 和 η
仍需逐项检查≥0；forest 本身或 small determinant 不保证非负。

上述 forest 陈述是 full-rank selected basis 的条件结论，不把未选图的
所有 edges 都变成 forest，不适用于将 Ordered 当单条 DBM edge。
若 r<9 或 support 不独立，应回到相应 rank/一致性合同，不能照搬
“k+1分量、k方程”计数。

## 4. ΔS=0 不是可直接相除或任意忽略的列

同项两 component 的 S 相等时，E 较大的 line 在同一原域上处处更强。
若 E_base≥E_extra，把 μ_extra 归并回 base，position balance 不变、
各 T 质量不变、乘子保持非负，dual Lower 不下降；若 E 相等则 cost
精确不变。这个支配删除有简单整数 E 比较的证据。

若 E_extra>E_base，直接将 μ_extra 置零并并回较弱 base 可能降低 bound，
不能自动保持此前的 threshold。可以先把该同S类的最大E作为 reference
base再合并；同S换 base 不改 b_tilde。或者保留零列对应的质量/成本参数。
不能对零 ΔS 除法，也不能只因它不出现在位置 balance 中就忽略 cost。

支配论证只在同一 epigraph term、同一 physical span、共同有效原域内
成立。跨 term 或跨不同合法域，即使 normal 相同也不能照搬。选 reference
base 是 dual 的坐标选择；它不授权改原 FS、anchor、实际核或原 cell。

## 5. base 非负和 cost 仍是必过关

恢复后必须逐项核

```text
μ_extra=γ/|ΔS| >= 0,
μ_base=2a-Σ_extra γ/|ΔS| >= 0.
```

normalized flow 的非负性只给第一式，不能代替第二式。因此它不是一份
可以忘掉 capacity/mass 的普通无容量 min-cost-flow 完整性论证。
最终重建原全部权并核 full78 balance 是最直接的可靠性闭合。

消去 base 后的 raw dual bound 精确为

```text
Σ_e 2a_e E_base
 - Σ_geo μ_r rhs_r
 + Σ_(nonzero extra) γ_ej*(E_extra-E_base)/|ΔS_ej|
 + 原样保留的 zeroΔS extra 成本调整.
```

Ordered RHS 为0；不能把 Order 乘子误计为新的 geometry cost。
归一化只简化 balance 系统及 multiplier 的存储，cost 中仍有 ΔE/|ΔS|，
base 质量也仍有这些除数。因此共同大分母可能转移到重建算术中，没有
消失。可以保存 factorized γ numerator、一个小 d 和可从原 FS 推导的
|ΔS|，避免保存巨大 raw 权，但必须给 exact base/cost checker 的预算。
不能由此宣称最终 Lean 源码≤2 MB 或全流程≤3200秒。

## 6. 独立结论与停止边界

在固定 raw 模型、非零列可逆归一化、独立 selected support、完整一致性、
所有恢复质量非负及 exact raw cost 都保留的前提下，归一化和 forest+
至多两Order decoder 在纸面上成立。zeroΔS 必须按上节单独处理。

本文不证明新 support 存在、最优性、对全部剩余 pair 的效率，也不生成
数值证书或新的 actual Lean 定理。M 已核的固定局部 Lower 仍是自己的
独立有限证据；全域覆盖、实际函数薄桥、最终计数、源码及运行验收都
没有由本静态审查完成。

## 7. 对照 joint 其他接口的补充核对

joint 第4节的 primal tie 符号正确：
`ΔS*n·X=E_base-E_extra`，除以 |ΔS| 后 normal 就是 normalized column。
primal/dual 可行且目标精确相等时，每条正 μ 行必须 tight；若某 base
质量为0，不能仅由另一条 extra 质量为正推出两者 tied。因此九方程
packet 须核各条声称的 tie，或明确继承此前已核的 exact primal face。
canonical max ties 可能改变 base 和 h，不能直接继承旧 Lower；joint
第6节的“解码后重新 full rawcheck”保守条件必须保留。

joint 第7节仅作符号变换的小整数模型也正确：Y=T/512，component 行
除512、objective除1024，给 objective `D*BS pressure+ΣaY`、
target `4QV*Nc`。其 dual 映回 raw 为 component 权乘2、geometry 权乘1024。
这不改变前述 raw 分母限制和完整检查，本文没有执行或选择该变换。

joint 第10节的 derivative interval 备选差式在 s,q≥l0 和 dl≤du 时成立：
`m(s)-ell(s)=(du-dl)*min(s-l0,q-l0)`。凹折线 min 不能错作 epigraph 两行
max；同一实际 anchor 导数才可共享合并。本文仅核符号，不评价收益，
不启动该备选、不证明任何新 κ 增量。

joint 第8--9节全域/交付段是未来待授权合同和预算风险，并非本静态
定理的推论。独审认可其停止边界：完整指定范围 strict EOF、原 guard、
非负/balance/cost、独立 replay、actual Lean、root/counted wrapper 及
source/runtime 缺一不可。Python局部模型成功或本纸面归一化不能代替它们。
