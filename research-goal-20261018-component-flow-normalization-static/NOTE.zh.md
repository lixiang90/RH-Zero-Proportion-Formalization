# 组件包络证书的 incidence 归一化与交付关口

本包是 2026-10-18 的独立纸面推导；只写本文、静态依赖与文件哈希。没有执行 FS 提取、点值、矩阵、秩、行列式、优化、核、Lean 或新分类。它不修改 M 或此前任何冻结包，不改变 root 轮数或研究方向状态。

固定解析源是 `record-source-audit/snapshot/Solution.lean`，1,818,411 bytes，SHA256 `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。M 的生产 manifest 是 `129c706dcab0aff47ef54a0f249e5d0a49e8f718476faaf453681e73858526d8`。下述定理不依赖原生 LP 状态；实际 M Lower 仍须其独立证书审计。本包不能作为全局新 floor 或新 κ 的声明。

## 1. 固定原始模型及符号

令 Q=32768、R=1024，物理坐标 X=20Q p，规范 X₀=0。每个窗口有 34 个带正系数 a_e 的核项，两窗共有 68 项。令 κ=QRV。沿用 M 的 epigraph 变量 T_e=κ w(s_e)，目标系数 m_e=2a_e；位置部分为整数向量 b，原始目标为

    b·X + Σ_e m_e T_e,           target = 4κ N_c.

这里 N_c 是当前固定 c 的整数分子；T_e 取真实核值时，目标等于 2κ SA(F_L+F_R)。本段只是既有缩放恒等式，不计算新数值。

一项的每个组件 j 都有原始有效不等式

    S_ej v_e·X − T_e ≤ −E_ej,    v_e=e_end−e_start.

常数组件 S=0、E=QR lb。已有 anchor 组件取

    dloN=mid32−2D,       dhiN=2D−hi32,
    E=QR v − 10R[dloN L₀+dhiN(p−L₀)],
    S=(R/2)dloN=512 dloN.

其中 p、L₀、v 都是原 source/PT/FS 记录的整数，不是新采样。组件 lower 的 soundness 来自原 TVal 和原导数上下界，以及 s−L₀/Q≥0、p/Q−L₀/Q≥0；没有使用全局凸性、曲率正性或真实导数端点相等。原混合系数的加权组件平均复原原 affine lower，见 `envelope_model.py:71–100` 的 E/S 与 meanE/meanS 恒等式。本定理不声称 M 严格强于最优的原 mixed-dual 家族：该比较尚未作出。

几何模型为 153 条 DBM incidence 行及至多两条 Ordered 行。每条 Ordered normal 是两个 incidence normal 的差。反射只重映射本地 span/gap，不反向一条 prefix→suffix 的窗口边；四 chart 次序仍是 id/id、id/rev、rev/id、rev/rev。这里全部 incidence 是 X 的原始单位系数 normal；若添加其他 side condition 或能量 normal，以下 small-minor 结论必须重审。

## 2. 质量消元与正确的归一化定理

给定一个 term 的 base 组件 β_e。原始 dual 的 T 列质量条件为

    Σ_j μ_ej=m_e,      μ_ej≥0.

把非 base 的被选组件称为 extra，未选行权重取零，则

    μ_eβ=m_e−Σ_extra μ_ex,
    h=b+Σ_e m_e S_eβ v_e,
    h+Σ_geo μ_g n_g+Σ_extra μ_ex ΔS_ex v_e=0,
    ΔS_ex=S_ex−S_eβ.

h 是整数 full10 向量，坐标和为零。对 ΔS_ex≠0，定义

    α_ex=|ΔS_ex|,
    γ_ex=α_ex μ_ex,
    n_ex=sign(ΔS_ex)v_e.

几何行令 γ_g=μ_g，normal 仍为 n_g。于是余额式变为

    h+Σ_selected γ_k n_k=0,      γ_k≥0.                  (B)

归一化 extra normal 本身就是原 155 行库中同 span 的某个正或负 incidence normal。它与几何行有相同 normal，并不意味着其 rhs 或 dual 成本相同。

**定理。** 若所选 9 个归一化 normal 删除 X₀ 坐标后线性无关，则以坐标为行、所选 normal 为列的 9×9 整数矩阵 A 的非零行列式绝对值 d 属于 {1,2,3,4}。因此 (B) 的唯一解可写 γ_k=n_k'/d，n_k' 为整数；分子没有 ≤4 的限制。

证明：任何 square minor 对至多两条 Ordered 列作多线性展开，最多出现 4 个 incidence minors；有向 incidence 矩阵的 square minors 属于 {0,±1}，故绝对值至多 4。Cramer 定理给结论。注意 raw extra 列是 ΔS v，未归一化的 raw 矩阵不满足此行列式界。原 μ_ex=n_ex'/(d α_ex)，因此 **raw μ 的分母不受 4 限制**。

同一项的两个 extra 归一化列平行，所以独立 9 列中每项至多一个 extra。这个结论只对独立所选列成立，不能凭一个一般 LP support 自动假定。

## 3. Forest 加至多两条 Ordered 的精确解码

设独立 9 列中有 r 条 Ordered，r∈{0,1,2}。其余 9−r 条 incidence 列独立，因此相应的无向边在 10 个顶点上组成 forest；包括孤点在内恰有 r+1 个连通分支。反向平行边和多重副本不能同时留在独立集里。

对每个 forest 分支 C 聚合 (B)，incidence 列完全相消。记

    H_C=Σ_{x∈C}h_x,      Z_Ck=Σ_{x∈C}n_Ordered,k(x).

删除一个分支方程，例如包含顶点 0 的分支，即得 r×r 方程

    Z γ_Ordered=−H.

r=0 不需这个小方程；r=1 或 2 只需一个 1×1 或 2×2 exact solve。forest 的 unimodular 消元给 |det Z|=|det A|≤4；不能仅凭 Z 的每项 ≤2 推出行列式 ≤4。

随后令 f=h+Σ_kγ_Ordered,k n_Ordered,k；每个 forest 分支内 Σf=0。对一条 normal 为 e_v−e_u 的 forest 边，删边后取包含其 target v 的一侧 C_v，则

    γ_edge=−Σ_{x∈C_v} f_x.

若按 rooted subtree 编码，应显式记录该 cut 的 incidence 符号，避免反向边误号。上述式子精确恢复所有 γ；再要求 γ≥0。每项至多一个 extra 时，base mass 非负等价于

    m_e d α_ex ≥ n_ex'.

没有 extra 的项保留全部质量 m_e。这个整数比较无需把所有 α 合并为巨大公共分母。

必须最终原样检查全部 raw μ≥0、68 条质量式、10 个位置余额及原始成本。full78 checker 的依赖边界保持不变；forest 算法只是小证书解码器，不能取代它。也可以直接验证给定整数分子/小分母，而不在可信内核里证明解码器求到了唯一解。

## 4. 正确成本与 primal 活跃方程

原目标常数为零。消去质量后的 dual lower 是

    L=Σ_e m_e E_eβ − Σ_geo γ_g rhs_g
      +Σ_extra γ_ex (E_ex−E_eβ)/α_ex.                 (C)

若 (B)、非负、base mass 与原 full78 全部通过且 L≥4κN_c，即是 Lower。Lower 本身不需要 primal 可行或最优性。不得把 extra 的 (E_ex−E_eβ)/α_ex 换成同 normal 的某个几何 rhs；其成本来源不同。

若还要重建保存的活跃 primal 方程，则几何行是 n_g·X=rhs_g，而 extra/base tie 是

    ΔS_ex v_e·X=E_eβ−E_ex,
    n_ex·X=(E_eβ−E_ex)/α_ex.

这与 dual 的同一个 forest+至多两条 Ordered 使用相同规范化矩阵。可以沿 forest 表达各分支的相对 X，再用至多两个 Ordered 方程定分支势；规范 X₀=0。它不需要储存巨大 raw 9×9 inverse。这里没有构造任何实际矩阵或新 primal 点。

## 5. ΔS=0、退化及不可擅自补 basis

若两个组件 S 相同而 E 不同，则 E 较大的组件在整个原 cell 上支配另一个，因为其 affine 值是 S v·X+E。非 extra 的 max 规则应选 E 较大者。把两者同时当作正质量的 active tie 会得到 0=E_base−E_extra≠0，因此该 tie packet 不成立；这只是编码/support 失败，不是物理模型矛盾。

若 S 与 E 均相同，两组件完全相同。可把额外质量移回 base 而不改余额与成本，或在一般原始证书中保留该冗余行，只要质量可行。其归一化列是零，不可放入独立 9 列 basis。不能在删除后未经授权补选其他行以维持 rank9。

秩不足的 support 不自动拥有 spanning tree 或上节方阵。若预先规定 exact RREF 和 free=0，可只做一次这个确定性代数解；一致、非负并经 full78/cost 检查的结果仍是有效 Lower，其余保守 inconclusive。抽出独立 incidence 列仍为 forest，但连通分支可能多于 3；至多两条 Ordered 的 component-balance 方程此时可能超定，必须逐一检查一致性，不能盲用 2×2 solve。primal 若不唯一，也须提前规定自由坐标策略或保存已有 exact 自由坐标，不作自适应 basis/支持搜索。这样的失败不排除整个 component-max 模型。

## 6. 不存 68 个 base 的可审计编码

M 现有 metadata 给出 2 条几何与 7 条 extra 活跃约束。这只是已有记录；本包没有求其 rank 或重建它。可考虑把 9 条活跃 primal 方程作为 packet：几何描述符给 rowID；extra 描述符给 termID 及两个本地组件 ID。由这 9 条方程唯一恢复 X 后，每个没有 extra 的项以固定 tie-break 取 X 处最大组件为 base。有 extra 的项显式指定其两个组件，再按固定次序选择 base 方向。其他项无须逐项储存 base。

若来源是一份 primal/dual 可行且目标相等的证书，正 μ 行在 primal 上必活跃；未分流项唯一的 max 组件可由 X 恢复。对 extra 的两个正组件互换 base 也只是同一质量分解的重参数化。但未被编码的退化 max ties 可能让 canonical base 与原证书不同，从而改变 h 及重建出的 μ。**不能保证新的 canonical packet 自动继承已有 Lower**：必须解码后 full rawcheck；失败即保守 inconclusive，或在下一次冻结格式前为退化项显式加入少量 tie selector。若声称 primal/最优性，还须检查全部 primal 约束；若仅声称 Lower，最后 dual check 已足够，其用于选择 base 的 X 不获得真实核值意义。

原 source 只有 constant 和原 FS 中实际存在的 p/r anchors；不存在或零混合权重而从未取得原 TVal guard 的 anchor 不能凭编码扩充。所有 term/component IDs 都必须从对应 source、FS、cursor 与原 guard 重建并核对。

## 7. 一个可选的小整数等价模型

所有 E 都是 R 的整数倍，S=(R/2)dloN。仅作符号变换，设 Y=T/512，组件行除以 512、目标除以 1024，则

    dloN v·X − Y ≤ −2(E/R),
    objective = D·BS pressure-divergence·X + Σ_e a_e Y_e,
    target = 4QV N_c.

常数组件相应为 −Y≤−2Q lb。新组件 dual 质量是 a_e；若新 dual 为 ν，则映回原模型为 μ_component=2ν_component、μ_geo=1024ν_geo。未来 checker 可以在小整数模型构造，再逐项映回旧 full78 检查。此段不修改 M 的 source、原证书或当前实现，也不把 raw μ 分母错误缩为 ≤4。

## 8. 下一次全域 proof-producing 合同（本轮不执行）

下一步优先完整剩余域的 component-envelope 分类，保持当前 kernel、c、原 anchors、四 chart 与 H remaining，不以另一个任意 seed 或反复固定模板替代全域关口。只有独立证书已经通过的 J Lower/M2417 才可从待处理索引中扣除；扣除须按原 G index 作显式 membership 证书，不能把 native 成功当作通过。

执行前须固定所有输入 pin、需要读取/解码的原 FS/cache 范围、每 case 行/列上限、总 LP 调用上限、每次与总时间/内存/输出限额、终止/续跑策略及 strict EOF。每个待处理 case 最多一个 LP discovery、零重试；native status 只发现候选。按预定 support/base 政策做 exact 归一化恢复，核原 guards、完整 geometry、full78、非负、成本。支持失败或资源终止须留下真实前缀与未处理后缀，不能填充成全域结果。

若 exact feasible primal 的原始 component objective 严格低于 target，首个 **exact Below** 即否定该固定全域 component-max 模型足以证明目标；它不是真实 F 或 RH 新比例的反例。若只是某 support/rank 重建失败，则是 inconclusive。要声称本模型全域成功，必须全部指定域 strict EOF，逐 case 有既有支付/Empty 或新有效 Lower，且全部独立重放通过；不能只由若干成功样本推断。

归一化 forest 编码、9 方程 packet 和 dictionary 都是有待验证的压缩办法，不是此次分类自动闭合的保证。下一关应先基于已保存成功证书作一次固定 packet 的 exact decode 与 byte 预算校验，再决定是否把格式用于全域证据；这一步不需要另一 LP。若全域 discovery 成本可行，固定模板只能作为重用数据的编码，不应默认成为再次类似 J 的受限数学家族。

## 9. Source / runtime 的必要交付门

原单源 1,818,411 B；网站 2,000,000 B 上限仅余 181,589 B，尚未扣新 soundness、decoder、cover、counting、wrapper 和任何 payload。不能用压缩二进制尺寸代替实际 Lean 源码 UTF8 bytes。直接每 case 保存 68 个 2-bit bases 加 9 行 support 必然过大；9 条描述符若各用 9 bits，约 81 bits/case，base64 后仅这部分对 15k 多 case 就已超过余量，尚无证明代码。可尝试固定共享支持、支持 dictionary、同原 cover region 的复用、排序组合编码或共享活跃方程模板，但必须报告真实 dictionary/selector/退化代价，不能假定存在压缩率。

全域 H 的大表也没有已经进入 1.8 MB 基线。还须把 G paid/projection、H Empty 与新增 Lower 的完整覆盖变为源内可验证的 product-cover/层次块或紧凑证据，保留全部原 root/outside/反射/closed 边界；不能仅附多 MB Python bitmap。source 总闭包与 root coverage 的压缩方案、可信 checker、Lean/Comparator/nanoda 总运行时间目前 **未知**。Python 分类完成不解除 ≤3200s 与全单源 ≤2m 的义务；source 预算失败可停止交付路线，不是数学 floor 不存在的证明。

必要 formal 接口至少包括：原 TVal 组件 lower 与 PT guards；原 source FS/cursor 重建；上述质量消元、归一化/forest decoder 或直接证书验证；raw full78 nonneg/balance/cost；全域 product cover 与 root 外 guard；新 floor 到原计数/短对付款及 dyadic/cumulative wrapper；最终 axiom/Comparator/Lean/nanoda 验证。固定 separation=17/20 与短对付款 c≤1/64 也须沿原新 source 链核查，不能使用旧 kernel 的 123/128 payment。若改为累计势函数路线，则需已有 n=10 ActualDefectEstimate 端点桥，不可把它说成 W10 band。

M 固定 pair Lower 是新数学机会：现有 anchors 的完整组件包络可以给出有用的混合 dual，而固定 F9-row seed 的失败或 singular 并未排除任意 mixed dual。但目前没有完整全域 floor、全源压缩、总 runtime 或无条件新 κ，故不称可提交。

## 10. 暂存的导数区间余项备选

只用原 anchor 的 TVal 和 dl≤d_actual≤du，记 q=p/Q、l₀=L₀/Q：

    ell(s)=v+dl(s−l₀)−du(q−l₀),
    m(s)=v+min(dl(s−q),du(s−q)),
    m(s)−ell(s)=(du−dl)min(s−l₀,q−l₀)≥0.

原区间上的常量收益至少 (du−dl)(L−L₀)/Q；未计算其大小。m 是两条线的 min，不能错误编码为 T≥两线（那会变 max）。完整有限证明可按 s≤q/s≥q 分支，或取该凹折线在原区间的 chord 下界。

若同一实际 anchor 导数在多项共用，应先合并共享变量再取 interval min。对非负权重令 A=Σw_e(s_e−l₀e)、B=Σw_e(q−l₀e)，原端点替换损失的统一可恢复项是 (du−dl)min(A,B)。这依赖确为同一 anchor 导数身份，不能仅因相近 p 值共享。当前 M 已成功，备选保持纸面，不启动新 branch、核、采样或 LP。本包不声称任何可量化新 κ 收益。
