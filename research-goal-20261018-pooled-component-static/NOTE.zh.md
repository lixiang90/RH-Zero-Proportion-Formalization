# 相同物理 span 的组件共享：N 的固定模型修正

2026-10-18，独立静态数学审查。只写本文和哈希依赖；没有执行 FS、点值、枚举、矩阵、秩、LP、核或 Lean。N 尚未执行，本包不改变 root 轮数，不改任何冻结证据。M 的已证局部 Lower 使用较弱的 separate 模型，保持有效；N 应采用下述 pooled 模型，避免把重复 epigraph 变量造成的松弛误当成最强现有组件家族的障碍。

## 1. 同一真实函数值必须共享

两窗中原 term e 映射到物理端点 (u,v)，实际项就是 a_e·w(P_v−P_u)。即使它们来源于不同 cell、FS、anchor、区间与原混合质量，相同物理 span 的实际 w 完全相同。令 C_e 是原常量及原正质量 anchor 的有效 affine 组件集合。对一个 span s 建立一个变量 T_s，保留所有成员 e 的所有原组件行，并取

    T_s ≥ S_ej·span(X)+E_ej   (j∈C_e),
    objective 的 T_s 系数 = 2 Σ_{e∈s} a_e.

仍是 X=20Q·P、实际 T_s=κw(span)。每条组件 row 保留原 term/cell/FS/PT/guard 身份；不得因 normal 或 S/E 相等就丢失来源。所有 a_e>0，故 objective 对每组 T_s 递增，消元后是该组所有组件的 max。实际 kernel 不变，无新 anchor、新采样或新解析假设。

对一个两成员组，设各自 max 为 m_L,m_R，正权 a,b，则未缩放的逐点收益为

    (a+b)max(m_L,m_R)−a m_L−b m_R
      = b(m_L−m_R)  若 m_L≥m_R，
      = a(m_R−m_L)  若 m_R≥m_L。

因此 pooled 目标逐点不小于 separate 目标，在同一完整几何域上的 minimum 也不小于旧 minimum。这是把一窗的有效组件用于同一函数值的另一窗权重的结构增益。它未证明严格的数值增益，也未比较 M 与所有最优 original-mixed dual。

## 2. 42 组、51 个规范变量、full52：纯源码集合论

固定源 `Solution.lean:10639` 的 TS 明列 34 个正权 pair：9 点的全部 36 个 pair，恰缺 (0,2) 与 (6,8)。这两个缺口由本地反射 (i,j)↦(8−j,8−i) 互换，所以四 chart 的 physical pair 集合不变。

两窗在物理点 0..8 与 1..9。公共点 1..8 的 28 个 pair 中，prefix 缺 (6,8)，suffix 缺 (1,3)，故共有 26 个正权 span。两窗 union 是 10 点全部 45 个 pair，去掉 (0,9)、(0,2)、(7,9)，恰 42 个。这个论证只读 TS 的显式源码，没有运行集合枚举。

故模型变量是 X₁..X₉ 加 42 个 T，共 51 个；证书完整余额是 10 个位置坐标加 42 个 T，共 52 个。原组件 row 数不因 pooling 增加，原 155 条 geometry 保留。原来的 full78 名称与固定 68 质量式不能继续当成 N 的维数；原 M full78 消费者依旧正确。

## 3. Group mass 与归一化定理保持成立

对每组 s 选一个 base β_s，令 m_s=2Σ_{e∈s}a_e。dual 的 T 列给 Σ_j μ_sj=m_s。消去 base 后

    h=b+Σ_s m_s S_sβ v_s,
    h+Σ_geo μ_g n_g+Σ_extra μ_ex ΔS_ex v_s=0.

对 ΔS≠0 令 γ=|ΔS|μ、n=sign(ΔS)v_s，仍是原 incidence normal；最多两条 Ordered normal 仍各为两个 incidence 的差。独立 9 列归一化矩阵的 |det|∈{1,2,3,4}、forest+至多两条 Ordered 的解码，以及 raw μ 分母不受 4 限制等结论逐字沿用冻结的 normalization note。独立 basis 每个 **group** 至多一个 extra。

成本仍是

    Σ_s m_s E_sβ − Σ_geo γ_g rhs_g
       +Σ_extra γ_ex(E_ex−E_sβ)/|ΔS_ex|.

必须原样核 group base mass、μ≥0、full52 与原 raw cost。ΔS=0 的不同截距、重复行、rank 不足、>9 support 和 free=0 策略均按原静态合同保守处理，不能凭出现这些情况否定家族。base 的 exact μ=0 时，extra μ>0 不蕴含 base/extra tie；tie 只能生成候选 primal，随后全部原 rows 的 exact 检查才可给 Below/最优性。

## 4. 原 cell 强 floor 已经蕴含，无额外 clipping 救援

source `InCell:9078–9081` 是完整 8 gap 与 28 nonadjacent span 上下界；`MulOKg:9133–9135` 本身对 full closed cell 内所有 g 成立。`mcheckGX_sound:10170–10286` 的数值付款只用这些 cell 行、原混合组件、gap width 惩罚与原 flow；没有额外 root/outside 或 Ordered 前提。既有独立 I/J point-free 重建已绑定原 M_i 强余量。

每个原 term 的组件 max 不小于原 R=1024 的非负 convex mixture。pooled T 又不小于每个 term 的组件 max。因此在完整原 cell geometry 内，N 每窗的 epigraph energy 已满足

    F_env,i ≥ A_originalFS,i ≥ c9+M_i/(κ SA).

把 c9/M_i 再加入 clipping 并非新的数学收益。若一个声称合法的 N exact primal 单窗低于此强 floor，应排查原 FS/source 身份、geometry 行或缩放实现。合法 exact Below 只否定 **pooled component lower model** 足以证明该目标，不否定真实 F，不证明新比例不可能。仅 support/rank/资源失败则是 inconclusive，不是 Below。

## 5. 全局反射与完整待处理域

P′_r=P₉−P_{9−r} 给 h′_r=h_{8−r}，所以

    (i,j,a,b) ↦ (j,i,1−b,1−a),   chart′=3−2b−a.

它是 involution，固定点是 i=j 且 chart=1 或 2。canonical cell/FS/PT 身份不变，窗口交换；Ordered 条件保同值，9 条 sep 反序。pooled 42 个 T 必须按 physical span (u,v)↦(9−v,9−u) 作 permutation，不能只交换旧两个 34T blocks。normal 的平移项消去，目标与成本不变。

用于减少 discovery 次数时，必须先核待处理集合与扣除证书的 membership。H 的保守算法输出不应未经检查就假定反射封闭；应在 pending∩orbit 中取代表，或为缺席代表提供已闭合依赖。不能简单略过所有 index 大于反射 index 的项而漏域。可运输 exact certificate 并对每成员重新 full52/rawcheck；native status 不是证据。首次 exact Below 可停止该固定模型；若希望声明全域 Lower，须完整指定域 strict EOF、所有扣除都有独审证书，且无 unresolved 或未处理后缀。

## 6. 当前 actual Lean 接口与交付边界

只读审查了 phaseA `203425eb09dc29b3e14d1ab4d25147a6676e29a98ce83886453003b6d7905ab2` 指定的 `CurrentPrefix.lean`、`QuantizedComponent.lean`、`Sparse78.lean`。当前 prefix 是同一 s1R 源至 ptS 加 G_rev；独立组件 ell 的残差、S/E/κ 缩放、常量 lb lower、整数 μ/den 的 full-coordinate balance/cost⇒目标，其数学符号通过纸面审查。没有运行 Lean，generic phaseA 还不等于固定 Data/Physical/Pair 定理已闭合；API/类型/finite table 编译及 axioms 均待正式 gate。N 可复用组件 soundness，有限和消费者须参数化维数或另接 full52。

N 目前只在准备，未运行该 pooled family 的任何数值步骤。本包没有生成 matrix、payload 或 Lean 数据。51 变量较少不构成耗时保证；42 bases 较少也不构成 source 压缩保证，因为单组最多可有 6 个来源组件，旧 3-component tie 描述符预算不可原样沿用。完整全域 cover、dictionary/selector、guard 导航、计数/短对付款、单源 ≤2m 与 Lean+Comparator+nanoda ≤3200s 仍未知。当前不声明新全域 floor、无条件 κ 或可提交结果。
