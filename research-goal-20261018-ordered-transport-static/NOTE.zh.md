# 两个 Ordered 约束的有限运输合同（纸面）

本包只有静态推导，不运行 G/H、shortest path、transport、LP、核评价、
Lean 或证书搜索，不改变任何原包。它不证明任何具体 pair 已关闭。
G 完整分类与未解数量决定是否值得实施；本包不改变 G 合同。

## 固定行与符号

物理坐标为 X0,...,X9，gauge 可取 X0=0。原 153 个 DBM 行均为
`(e_v-e_u)·X <= w_e`：两份原 cell 的 144 个有向跨度界及 9 个 sep
下界。所有 w_e 为原整数，normal 保持原 ±1 归一化。两 Ordered 行 RHS
均为 0，id normal 定义为

    O0 = -e0+e1+e7-e8,
    O1 = -e1+e2+e8-e9.

四 chart 分别使用 `(O0,O1),(O0,-O1),(-O0,O1),(-O0,-O1)`。
Order 不是单条 DBM edge，而是两条 incidence normal 的差。

以下完整性论证仅适用于：原 153 行可行，且原图强连通。原有限双向
adjacent 界包含连接 0,...,9 的双向链，因此强连通；可行性排除负环。
若原 DBM 已有严格负环，直接用旧证书关闭，无需本规则。

## 为什么恰需 13 种 Order 比例

固定 155-normal 矩阵任意方 minor 的绝对值至多 4：至多两个 Order 行
各展开成两个 incidence 行，每个 incidence minor 为 0 或 ±1。
此界不适用于随意重缩放后的行，也不覆盖能量或新增 side condition。

若加两 Order 后为空，Farkas 给非负乘子、normal 总和 0、严格负成本。
非负 kernel cone 是 pointed；负成本向量分解的极射线中至少一条仍负。
其正支持为 positive circuit，k<=10、normal rank=k-1。取独立的 k-1
坐标列，非零 cofactors 给该一维关系；由 minor 界，除 gcd 后的 primitive
正整数乘子都在 1..4。原 DBM 可行时两 Order 权不能同时为 0。

将两 Order 权的 gcd 约去，比例必在以下固定集合：

    (1,0),(0,1),
    (1,1),(1,2),(1,3),(1,4),
    (2,1),(2,3),
    (3,1),(3,2),(3,4),
    (4,1),(4,3).

正对共 11 个，加两轴共 13 个。除 gcd 后 graph 乘子可以是分数，
不能直接声称这份 graph flow 仍整数。

固定一个比例 (a,b)，令 t=a*O0_chart+b*O1_chart。需要的 graph flow 为

    f_e>=0,  sum_e f_e*(e_v-e_u) = -t,
    cost(f)=sum_e f_e*w_e < 0.

加回两 Order 后 normal 总和为 0；Order RHS=0，故总成本就是 cost(f)。
这是 Empty，不是 Lower。含实际 FS objective b 的 Lower 无此 13 比例界。

原图强连通使整数需求 -t 可行；无负环使无容量最小费用有限。incidence
matrix 的全幺模性保证可取整数最优 flow，其成本不大于前述分数负成本。
因此几何为空时，至少一个比例确有整数负成本 flow。反向则由上面的
Farkas 恒等式直接成立。

## 四 chart 的供需及至多 3x3

写 q=-t，q<0 为供给，q>0 为需求，沿有向路径从供给送到需求。
只在 vertices {0,1,2,7,8,9} 非零。对 id/id，t 的六个系数依次为

    (-a, a-b, b, a, b-a, -b).

其中 a-b、b-a 至多一个为正、至多一个为负，故正负顶点分别至多 3。
rev/rev 为整体反号，供需交换。对 id/rev，六系数为

    (-a, a+b, -b, a, -(a+b), b),

也分别至多 3；rev/id 为整体反号。删掉零供需顶点，轴或 a=b 可退化为
更小运输问题，不能强行保留零供需的非退化假设。

同向总供给为 a+b+|a-b|=2*max(a,b)<=8；异向为 2*(a+b)，13 比例库中
最大为 14。通用保守上界 16 也正确。不能把同向的 8 用于全部四 chart。

## 固定运输计划与 81 个树

无负环时，graph flow 可分解为供需路径及非负成本 cycles；去 cycle
不增成本。令 dist(u,v) 为精确有向 shortest-path 成本。graph 最优费用
恰为以 dist 作成本的 complete bipartite transport 最优值。反向可把
每个 transport shipment 沿其 shortest path 展开，无容量限制。

至多 3 个供给点、3 个需求点。删零后 transport polytope 非空且有界，
线性最小值可在 basic feasible plan 取得。正支持无 undirected cycle，
可加零 shipment 边扩成生成树。因此对 K3,3 的全部

    3^(3-1)*3^(3-1) = 81

棵生成树，按固定供需 leaf-eliminate、保留所有非负解（允许零），
就覆盖至少一个最优 plan。每树至多 5 条 distance 成本项；K2,3 和
K2,2 分别为 12 和 4 棵树。需求只依 chart 和 13 比例，所以可预先
确定可行的 tree plan；它不依 pair 的 DBM RHS。这里未生成或检查任何
plan，也未测其实际 source/time 成本。

## 两种未来实现语义不能混淆

保守证书发现器可以任意给出 flow，只要最终 exact checker 核
f>=0、完整十坐标 balance 及严格负 cost，便可关闭对应 pair/chart。
这不需要信任 shortest-path、transport、tree 枚举或最优性算法。
“没找到负 flow”此时只表示 unresolved，不能称 Ordered 非空。

若要用“13 个精确最小成本均非负”断言非空，则必须另证 shortest-path
值确为最小值、运输树枚举完整且算术精确，再接上述 Farkas 完整性。
零成本或区间接触不是 Empty，始终只以严格负 cost 关闭。

运输输出的 graph flow 未必是 primitive circuit，单边 amount 可能超过
4；不能直接塞进旧每权两位的格式。可保一般整数 flow 并最终核验，
或另抽一条负 primitive circuit 后才使用 1..4 的小权格式。两者均未实施。

最终全域还须逐一覆盖全部必要 product cases、保持原 FS/state/cursor
与四 chart 身份、接实际函数和计数，并通过单文件 2,000,000 B 及全流程
3200 s 限制。本推导不提供这些资源结果，也没有 new floor/new kappa。

纸面交叉核对：joint_gluing_review 同意 13 比例、flow 符号与 primitive
circuit 限定；同向/异向供需界按上述四 chart 修正。没有运行独立算法。
