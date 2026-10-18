# H：G 未解集合上的 Ordered 几何 Empty 分类（准备版）

只准备脚本。执行仍须 root 的新不可变 gate，且必须绑定 G 的完整独审
`af09979447c2054f1daaa5a19e6abc59d04decee7752dfc53fe66c0643e30dc6`。
没有调用 inputs、Floyd、assignment/catalog 枚举、核、FS、LP 或 Lean。
原 c9/tau/c、原 cell/FS、G 分类与原 155 行均不改。H 不查能量 Lower。

## 固定范围和数学规则

G 已完整分类 5,635,876 个 case，只有 bitmap 的 19,838 个 unresolved
进入 H。原全局序号仍 `((i*1187+j)*4+chart)`，chart 为 id/id、id/rev、
rev/id、rev/rev。只按该 bitmap 的升序全量走，不在首个未解处停止。
G 的 paid/projection/cycle 不重跑、不扩充；H 的未解也只表示没有证书。

原 graph 是两份完整 cell 的 144 条跨度界及 9 条 sep，边 `(u,v,w)` 仍
表示 `X_v-X_u<=w`，X 是实数 20*32768*p，sep RHS=-17*32768。
两 Order normal（RHS=0）为

    O0=-e0+e1+e7-e8, O1=-e1+e2+e8-e9,

按 chart 对 O0、O1 独立取负。原 source PR 被直接只读解析；不 import
C/G/B producer，也不用 LP 或旧探测点产生新约束。

已冻结的 5/3-ray 纸面定理给同向 rays

    (1,0),(2,1),(1,1),(1,2),(0,1)

和异向 rays `(1,0),(1,1),(0,1)`。同向总供给是 2*max(a,b)，对应
2,4,2,4,2；异向是 2*(a+b)，对应 2,4,2。故每条 ray 都只有至多
4 单位运输，最多 4!=24 个匹配。重复 supply/demand 顶点保留在列表，
permutation 可有重复而不影响完整性。此处没有实际生成该 catalog。

令 t=a*O0_chart+b*O1_chart，q=-t。q<0 是源、q>0 是需求，源到需求
沿原 graph 走。10-vertex integer Floyd 找距离，同时用原 edge-ID 的
非负整数 multiplicity 表示实际 walk，避免展开长 path 列表。每种单位
匹配若费用负，把其 walks 加上 row153 的 a 与 row154 的 b。
若发现原 graph 的负 closed walk，也可直接给 graph-only Empty。

所有候选必须再次 exact 验全部 155 行：rowID 在 0..154、正整数权、
十坐标 weighted normals 总和0、weighted RHS 严格负。这份验算决定
是否输出 Empty，不能相信 Floyd、ray 或 assignment 标签。graph amount
可超过4，不使用两位权重假设。无合格负证书统一 unresolved，不声称
最短路最优性、几何非空或实际低能。没有向 Lower objective 推广5/3规则。

G 首个 sample 的 global index2417 已独立验全部155行可行，所以 H 不
可能全关闭。脚本在这个 index 若发现任何 Empty 候选会明确 assert
失败，不会静默改 tag 来隐藏矛盾。未来推进 floor 仍需实际 affine 联合
付款等另一数学层；H 只是缩小这批几何残余。

## 输出、耐久前缀与独审

`certificates.bin` 开头为5byte `HRC1\n`。每条 record 为

    uint32LE originalGindex; tag:uint8
    tag0: unresolved，无其余payload
    tag1: count:ULEB128(1..155)，随后count个
          rowID:uint8, positiveWeight:ULEB128

rowIDs 严格升序且唯一，ULEB 必须规范编码。显式 index 使顺序、漏项和
重复都可直接核。完整顺序必须与原 G bitmap 的全部 set bits 一致。
row0..152 是原 graph；row153/154 是本 chart 的 O0/O1，bound0。

每256record 缓冲一批，先把证书流和 `remaining-indices.u32.bin` 各自
flush/fsync，再 atomic replace `prefix.json`。初始 magic 也发布0record
前缀。prefix 固定 committed_records/committed_bytes、两流前缀SHA、
counts:{Empty,unresolved}、完整输入 index sequence SHA 与已提交 index
sequence SHA。remaining 流逐个保存 tag0 的 uint32LE originalGindex。
不造 G 的四流/hashchain 大框架；两个流都可由独审完整顺序重建。

资源停止只承认 published bytes/records；未提交 buffer 或其余 suffix
没有类别，不能补 unresolved 后声称完成。硬停止留下的 extra tail 也
不在可接受前缀内。完整时两流必须恰好EOF、records=19838、全部输入
index sequence SHA相同。所有 outputs 用exclusive create，不能重试。

独立 checker 由另一作者放在
`research-goal-20261018-stageH-independent/audit_h.py`，不 import producer，
从原 source/B/G 重建每个155row并核 certificate；它不需要重新运行
Floyd、ray、transport、LP 或核。root gate 固钉该 checker 的最终SHA。

`result.json` 与 published prefix 的 SHA/counts/bytes/index hashes 必须
一致。完整分类成功仍可有 unresolved；它不是新 global floor 或比例。

## 单次执行合同

CLI（本准备阶段未运行）：

```text
C:/Python314/python.exe research-goal-20261018-stageH-ordered-transport/run_once.py --launch-authorized-H --gate <root不可变gate相对路径> --gate-sha256 <完整SHA256>
```

gate 字段模板见 required-gate-fields.json。另需填 prepared_manifest_sha256
和 independent_checker_sha256，二者只能在最终准备包稳定后固定。
wrapper 只开一个 child；硬300s/20,000,000 bytes，child软270s/19,000,000
bytes（输入SHA检查包括在计时内）。guard 到限=inconclusive，只有已发布
前缀可审，不自动恢复、改参数或重试。所有命令/PID/收据/失败持久化。

本包不给执行耗时、关闭数量、完整 source或3200s网站流程的承诺。
没有新FS、kernel、scalar采样、LP、普通Lean、导出或Nano授权。全域
floor、新κ和网站可提交flags保持false；root在G/H精确结果后另决定下一关。
