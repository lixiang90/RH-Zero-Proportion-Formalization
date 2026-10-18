# I：原两 FS 联合能量的下轮固定机会合同（仅静态）

本包不执行 FS 解码、点值代入、矩阵、inverse、LP、核或 Lean，也没有
准备可自动执行的 producer。只固定数学与代码接口。下一实际 round4
先由 root 做宏观回顾004，审 G/H、source/运行预算，再决定是否给新的唯一 gate；
这里不增加或重置主轮计数，不因文件完成而自动进入 Phase1/2。

## 1. 当前范围及旧 F 成功的限制

H 及独审都完整处理 19,838 条 G 残余，4,460 条 Empty 已核、15,378 个
index 仍保守未解。I 若获授权，只用冻结的 H remaining 流，不改原
F9 profile、c9/tau/c、states、FS、155 normals或测试物理点。

root 对已冻结流的只读观察指出：旧 F pair1/5 的 globalindex4768 已不在
H remaining，即其 Ordered 交域已有 Empty；它不再是“真实可行残余上
联合能量有增益”的证据。旧九行 Lower 仍是合法条件证书，但可在空域
上成立。正支持数9不保证 basis fullrank，更不保证相同 seed 对余下
chart 有效率。因此 Phase2 只是固定无 optimizer 的结构机会，不能借
旧 F 的一次成功省略 rank、balance、cost 或全范围检查。

G sample globalindex2417（prefix0、suffix604、id/rev）保留在 H 中。
其原153边和两 Ordered 均已有独审可行证据。Phase1 只用该已冻结
sample 的原 X_integer_potential、原 X_scale=20Q；不取新点或优化它。

## 2. 最小可靠性命题：原 mtermTI 到实际 affine

固定 source Solution.lean SHA
f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。
使用原 mtermTI(10603)、mterm_minV/TVal(9769起)、mcheckGX_sound
(10170起)及原实际 reversal 定理 PC9QB6M_G_rev。新薄中间定理尚未
在 Lean 实例化；旧 mcheckGX_sound 的整体 floor 结论不能倒推任意 line。
不能 import 另一24mode核的 actual 能量定理来代替本 profile。

Q=32768，Rmix=1024，D=10^9，V=10^10，SA=10^20，kappa=Q*V*Rmix。
对某原 cell 的第e项，保留原 [L,U]、L0=sum原adjacent lower、uc=max(L+1,U)，
原 FS=(kind,lambda,p,r) 及原 PT/lb。p/r 是原 tangent anchors，不是将来
测试的物理点；“point-free”只表示提取器不输入测试 X，不表示删去 anchors。

按原 checker 定义

    v_e=mvT, m_e=mslT, w_e=mwT, cp_e=mcpT, cn_e=mcnT,
    delta_e=m_e-2*D*w_e,
    sigma_e=delta_e/(D*Rmix),
    beta_e=v_e/(V*Rmix)+(cp_e-cn_e)/(Q*D*Rmix)-sigma_e*L0/Q.

所有减法先转 signed Int/Rat，不得用截断 Nat.sub。cp/cn、v、m、w 已含
FS 内部 Rmix 质量，不含外部 TS 整数质量 a_e。原 active anchors、mokI、
PVI/LBSound、L0<=L<=sQ 及 TVal 合法区间保持不动，mtermTI 才给

    beta_e+sigma_e*s <= actual wfun(s).

因此在原 InCell 上，令 b_r 为原 BS，a_e 为原 TS，得到

    A_C(g)=[sum_r b_r*g_r+sum_e a_e*(beta_e+sigma_e*span_e(g))]/SA
          <= actual F9(g).

原 flow、Ng 与 main margin 的已审源式另给 A_C>=c9+Mi/(kappa*SA)。
所以在完整原 cell 内 max(c9,A_C)=A_C，baseline clipping、theta凸组合
不能修复 Phase1 对同一 faithful line 的低于目标点值。减非负 flow slack
只会更弱。本包不改变这些源式，也没有新形式化证明。

## 3. 提取必须与物理点解耦

建议唯一新接口（尚未实现）：

    extract_original_affine(original_cell_id, original_model, original_trace)
      -> {Cstar:Int, J:Vec8 Int, original_state_sha, packed_payload_sha,
          decoded_semantic_sha, consumed_bits, term_components, guards}

它不接收 X、offset、chart 或新的 joint bounds。从 A/B 冻结 trace 核
root/所属stream/position/end/state 身份，只在原 stream、原 state 的 L/U
解码原 FS；nested cuts/游标仍用原 contracts。不应假定48 root的任意位置
都是从一个简单平坦 root_pos1 导航，必须保留137 payload/高层 cuts 身份。
原语义/packed SHA 和 consumed cursor 必须逐项相等，提取后缓存该 cell。

有不含物理测试点的纯整数因式：

    J_r = D*Rmix*b_r + sum_{e:r in e} a_e*delta_e,
    Cstar = Q*sum_e a_e*v_e
            +10*sum_e a_e*(cp_e-cn_e-delta_e*L0_e),
    kappa*SA*A_C(g) = Cstar +10*Q*sum_r J_r*g_r.

pressure 已进 J，不能再另加或漏掉。Cstar 不含物理点，也不把原参考
L/Q 当一个要评价实际核的新点。与旧 F 的 direct_const、direct_gap 可
静态对齐，但旧 helper 不能不加适配直接用于本 sample。

具体旧代码风险：evaluate_once.py 的 evaluate_window(cell,offset,point,...)
在提取 FS 时同时读取 point，系数直接放 coeff[offset+r]，只实现 id。
solve_fixed_once.py assemble 也只构造 id/id 的两份 rows/objective。
这两份旧源保持冻结；不能把新的 id/rev 当成旧调用已支持。

## 4. 四 chart 的唯一嵌入与缩放

physical 九 gap 为 h0,...,h8；off=0/1 对应左/右窗。原 local gap r 取

    id: h[off+r],   rev: h[off+7-r].

原 span(i,j) 对应 id 的 (off+i,off+j)，rev 的 (off+8-j,off+8-i)。
只置换 J/域与正跨度，不 reverse/重解码 FS anchors、L0、v/cp/cn。
借原 actual reversal 定理，原 A_C 对被反射的 local gaps 仍下界相同
physical F9。旧 cell 的 original guards 不能换成收紧后的 joint bounds。

建议分离接口

    embed_affine(original_affine, off, rev)->{constant:Cstar, physicalJ:Vec9 Int}
    joint_integer(left,right,chart)->{C:Int,b:Vec10 Int,target:Int,rows:155}

令 Jphys 是两窗口嵌入后相加，C=2*(CstarL+CstarR)，

    b0=-Jphys0,
    bv=Jphys(v-1)-Jphys(v)  (v=1..8),
    b9=Jphys8.

于是 sum b=0；X_i=20Q*p_i，h_r=(X_{r+1}-X_r)/(20Q)，精确有

    C+b·X=2*kappa*SA*(A_L+A_R),
    target=4*kappa*Nc,
    Nc=893766123055294719, SA=10^20.

两 Order 是 chart 各自取号的原四point normals，不是 DBM edge。
profile、TS/BS、Q/Rmix/D/V/SA、原state和所有integer rounding均固定。

## 5. Phase1：唯一既有点的必要机会关

将来若 root 给专门 gate，仅提取 cell0/604 两份原 FS，并且原样读 G
sample2417。先核样本 SHA、尺度、integer X0=0、全部原153 bounds和两
真实 Ordered；不得用反射前的 id/id 域代替 id/rev。不得修改物理点。
只算一个 exact 整数

    Delta=C+b·X-target,
    (A_L+A_R)-2c=Delta/(2*kappa*SA).

若 Delta<0，则此合法 joint 点直接否定“仅这两份原固定 FS affine
lines 在共同域上统一证明 A_L+A_R>=2c”的目标。任何 sound joint dual
下界不高于该点值；clipping或减原flow slack也不救这个 fixed model。
必须停止本固定两 FS 证书家族，交宏观回顾改选结构；不自动换 anchors、
FS、basis、threshold、核或点。这不是实际 F9<RHS，也不是 RH/零点
比例反例，更不否定新增非线性项或不同有效支持可能改进。

若 Delta>=0，只通过这一必要关，完全不证明该 joint 域的 minimum。
Phase2 仍须下一明确 gate，不能由 Phase1 不失败自动启动。

Phase1 最小输出为两份 point-free affine/原守卫与语义SHA、四朝向映射
中实际使用的 id/rev、同一个原X/SHA、155域验算、C/b/target/Delta 和
signed exact 分数；无需输出新核值或大矩阵，也没有求解器。

## 6. Phase2：单个固定 basis 的无 optimizer 机会（尚未授权）

只允许 seed rowIDs

    [9,29,36,74,84,110,130,153,154].

在每个 chart 按原155 row顺序重建 normals，删除X0列得9x9 B，其rows
是上述固定顺序。rank/determinant/inverse 每chart只核一次，不能把id/id
inverse套给其余chart。此处没有计算这些矩阵或声称它们fullrank。
singular chart 保守unsupported/unresolved，不替换basis。

若 det(B)=delta!=0，令 dabs=abs(delta)、s=sign(delta)。可用整数 adjugate
避免每case保存巨有理数：

    n=-s*adj(B^T)*b_reduced,  mu=n/dabs.

每个欲闭合case都必须核

    n>=0,
    dabs*b + sum_k n_k*rowNormal_k =0  （完整十坐标）, 
    dabs*C-sum_k n_k*rhs_k >= dabs*target.

这才是 Lower。目标已含2窗口因子，不再扣基线或cN。final checker不信
inverse发现器；只信三条exact整数检查。既有small-minor纸面界可给
abs(delta)<=4，但不能代替实际fullrank；n的大小不受4约束。

若将来获得此单次 family 的 gate，遍历H剩余全部15,378，原FS按所需
cell提取一次并缓存，rows RHS按chart/state重建；充分者Lower，其余
保守未解。不能在首未解处停止或自动再跑另一basis/阈值。可只存固定
basis ID/status与原index序列，不逐case复制mu；实际kernel仍需重构
FS/C/b并逐项核，不能把Python成功bitmap作为证明。

## 7. 执行与交付停止条件

node-Mi product 是压缩已有覆盖/交付的方向：完整终止语义上的min可批量
付款，但不会自动提高一个真实可行、未付款 leaf 的 Mi，也不会抬高其
原 faithful A 在固定点的值。它不能绕过2417必要关。若该关为负，需新
实际下界输入或更大 ledger 等宏观方向，不应继续换同一模型的dual。

当前只有本静态合同，没有Phase1/2 producer或执行授权。root round4
宏观回顾必须先问：剩余区域能否被同一可证明族闭合，完整源码<=2MB和
生成/普通核/导出/Nano总3200s是否有现实依据。原source1,818,411B，
181,589B余额还须容纳actual affine lemma、product coverage/counting与
新增decoder；Python包体积或几秒运行时间都不等于网站合规。

先做必要固定点，不先解四矩阵/全15378；Delta<0立即停止该模型。
若未来Phase2获准但source身份/原 guards/反射/游标或任何exact等式失败，
保留失败并停，不修参数掩盖；资源到限只认已提交前缀，不自动重试。
完整Lower+已有G/H也仍须实际薄lemma、两stream product全域归纳、反射、
根外与separation/最终matching/counting，不能把fixed chart/cell局部结果
当无条件κ。所有globalfloor/newκ/提交flags保持false。
