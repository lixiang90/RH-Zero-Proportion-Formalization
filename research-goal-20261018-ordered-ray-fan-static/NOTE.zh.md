# 两个 Ordered 约束的 5/3-ray 完整性（纸面）

本包是新的静态推导，不改已冻结的 13 比例包或 G 的分类合同。
没有构造树表、求最短路、运行 transport/LP、数据扫描、核评价或 Lean。
它只讨论几何 Empty，既不判断实际某 pair，也不外推联合能量 Lower。

## 原域与费用

固定原 153 个 DBM 行 `X_v-X_u<=w_e`，原整数 RHS 不变，图强连通且
可行，故不存在负环。normal 保持原 ±1 incidence 归一化。两条 Ordered
行 RHS 均为 0，id normal 为

    O0=-e0+e1+e7-e8,  O1=-e1+e2+e8-e9.

四 chart 对它们独立取正负号。令 `t=a*O0_chart+b*O1_chart`，a,b>=0，
并定义

    phi(a,b)=min sum_e f_e*w_e,
    f_e>=0, sum_e f_e*(e_v-e_u)=-t.

强连通确保所有零和需求可行，无负环确保最优费用有限。Farkas 给出
等价关系：155 行为空，当且仅当存在非零 (a,b)>=0 使 phi(a,b)<0。
理由是 graph-only 的负成本关系不可能；若155为空，其负成本关系中的
两 Order 权不全0，graph 部分正好给上面的可行 flow。反向则直接将
graph flow 与 a、b 两 Order 相加。本步不使用 small-minor 或权<=4。

q=-t 的正分量是需求，负分量是供给，路径从供给到需求。去非负 cycle
并换为最短路径，得到 phi 等于固定有向距离 D 上的 transport 最小值。
反向沿路径 routing 给等价性；不存在容量约束。D 可含负条目，但有限。

## 每个开锥内的运输基不变

下述三元供给、需求均为同一多重集 `{x,y,x+y}`，只是赋给不同物理
vertices。先保留三个供给和三个需求位置，即使在边界某质量变成0。
单侧 subset sums 的去重集合为

    S={0,x,y,x+y,2x+y,x+2y,2x+2y}.

任何 transport tree basis 的一条流量，由删该边后的供需总和相减得到，
故是 S 中两个表达式之差。在 x>y>0 内，这些表达式严格依次为

    0<y<x<x+y<x+2y<2x+y<2x+2y;

在 y>x>0 内交换 x、y。除恒等相等的表达式外，没有别的内部符号 wall。
因此同一个开锥内，哪些 tree bases 给非负 primal flow 完全固定。

选一个开锥内点。运输 LP 非空且有界，故存在同时 primal-feasible 和
dual-feasible 的 optimal tree basis；这是标准 LP 最优基存在性，不是
说任一 optimal vertex 的任意补零树都是 dual-feasible。该基的 dual
potentials/reduced costs 只由 D 和所选树决定，不依供需。

于是同基在整个开锥内仍 primal-feasible、dual-feasible，故最优。
到闭锥边界时，它的 tree flow 是质量的线性函数，极限仍非负；相同
dual 仍可行，primal/dual 成本恒等仍成立。所以此基在闭锥上也最优。
这样不需要未经证明地调用边界连续性。保留零质量 vertices 很重要；
若先删除再随意换树，不能直接沿用同基论证。

结论：phi 在每个这样的闭锥上为齐次线性函数。若一点是两条极 ray 的
非负组合，其费用为对应 ray 费用的同一组合；负值必有一条 ray 负。

## 同向 chart：5 条 ray

id/id 下 t 在 vertices {0,1,2,7,8,9} 的系数为

    (-a,a-b,b,a,b-a,-b).

当 a>b>0，正负质量都是 `{a-b,b,a}`。取 x=a-b、y=b，唯一内部 wall
x=y 即 a=2b；外边界为 b=0 与 a=b。当 b>a>0，取 x=b-a、y=a，内部
wall 为 b=2a。两个区域合起来，非负 (a,b) 象限的完整 fan 极 rays 为

    (1,0), (2,1), (1,1), (1,2), (0,1).

rev/rev 是整体反号；供需交换，D 转成相反运输方向，但相同 fan 证明
成立。每个固定 D 都有：若某非负权导致负费用，则这5条中至少一条负。

## 异向 chart：3 条 ray

id/rev 下 t 的六系数为

    (-a,a+b,-b,a,-a-b,b).

正负质量都是 `{a,b,a+b}`，直接取 x=a、y=b；内部只需 wall a=b。
完整 fan 因而只有

    (1,0), (1,1), (0,1).

rev/id 为整体反号，同理。这个更强结果来自 transport 的固定需求结构，
不依赖 155-normal 的 minor 界；它没有否定先前13比例的保守完整性。

## 将来 checker 的正确语义与限制

为了排除某 pair/chart，只需任一上述 ray 给出一份实际 graph flow，
并 exact 核 f>=0、完整十坐标 balance 与严格负 cost。发现器不可信亦
无妨，单个真实负 flow 已足够；未找到仍只能称 unresolved。

若要以“全部5/3ray都没有负成本”声称几何非空，则必须实际获得各 ray
的精确最优费用，并证明 shortest-path/transport/tree 枚举的完备最优性，
再接本纸面 Farkas 论证。错误发现器、浮点状态、未处理样本或仅查少数
任意 paths 都不能支持该非空结论。零成本与闭区间接触不排除。

费用的线性锥分解不约束任意 Lower objective 的大 b；Lower 不适用。
新增 side constraints、能量行、容量、改变 normal 或非零 Order RHS
不在本合同范围，须重审。transport graph amounts 也不自动<=4。

本包没有实际枚举 basis、查某个费用、量化 G 未解收益，或证明运行时间。
完整 source<=2,000,000B 与生成/普通核/导出/Nano 总计3200s仍未知。
没有新全域 floor、零点比例或可提交结论。下一 H 是否实施由 root 在
G 完整结果后决定，不能由本纸面合同自动启动。

独立纸面复核上下文：joint_gluing_review 核查 subset-sum wall、最优
primal-dual basis 的必要条件及闭锥延伸；未执行数学算法或新数值检查。
