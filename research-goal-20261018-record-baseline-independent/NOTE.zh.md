# 新纪录原始 floor 的 Stage A 独立数学实参回放

本包独立复核生产包
`research-goal-20261018-record-baseline-replay/files.json`，固定 SHA256
`03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f`。
所读新源仍为 `Solution.lean` 原始 SHA
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
没有更改原始 `cN=893616123055294719`，没有提高阈值或扫描例外对。

独立程序未导入任何 producer Python 模块，也未复制其结果作为算术
输入。唯一共享的执行辅助是我自己之前已独立冻结的 packing decoder：
它按 positional 6bit 整数和解码，不是 producer 的 shift/fold。
source、生产冻结清单、用于对照的原回放/WZ/final summary 与这个
辅助的哈希均在执行前后核对。生产清单中全部文件也逐项检查固定。

一次独立执行真实退出 0，用时约 72.025 秒，没有失败重试。结果在
`independent-replay.json`；它是原有限实参/guard 回放的独立证据，
不是本地 Lean/nanoda/Comparator 通过证据或新的实际 floor。

## 与源语义的对应

输入表、34 正边、8 个 BS、28 PR、BND、TOP/BK/WL 普通 Nat、
PT tree、48 root、70 state/cursor 及118 cuts list 全部从固定**新源**
读取。137 个 packed literal 仍独立验证。BK/WL 的 balanced dispatch
按原应用表达式解析，PT `.nd/.lf` 树重新路由全部2095 literal entries。
实际 active point 用源 `pwD` 重建绝对 24-bit interval 两端，再检查
`ivIn`；没有把 raw delta 字段冒当成绝对区间。

root 输入先按源 `rootCl` 的 bad intervals 和 `tm/matC` 构造；所有
span upper sums 另核不超过 rcM，因此 root 的 A/B 确为 gap sums。
每次 split 使用一个**有符号 9×9 差分约束矩阵**，按新边的 rank-one
图更新重算全部36跨度，再按源 `Nat.sub` 截断。这与 producer 的
col/row 编码实现不同。每个中间偏移的非负前提、完整73字段（含 M=0）
及位置唯一性均检查；未把几何闭包加强成未授权的额外闭包。

branch 的 BND 切点选择、tie 顺序、两子树起始/结束位置和 fuel 都
保持原 source。reflection 仅在 `u7<l0` 时消耗1位，对应源 `Pg`
的第二分支；它没有被记为能量付款。Farkas 分支也保留原判据，原
实际树中没有走到 Farkas 终端。

每个 numeric leaf 独立解码原34项见证、flow multiplier 与消耗位数，
检查 box、全部 active `mokI`、非负质量及1024上限。能量整数余量
直接求值源码打印的 `mcheckP` 内 `Nat.ble` AST，未调用 producer
compact model。辅助函数保持源 `Nat.sub`、`uc`、`mcK`、`mwT`、
`mslK`、`mvKF` 的整数语义。LB 查询另用源 BL8 nibble 规则而非
Python bit_length，降低与 producer 同源简化造成的共同错误风险。

源码 `mcheckP_ok` 把 specialized AST 连接到 `mcheckGX`；
`mtermTI` 把 `mokI`、PVI、LBSound 连接到实际 term 下界；这些是
保留的**源数学证明依赖**。Python 回放证明的是所有实际输入通过
这些消费者的有限条件，不重证 PVI/LBSound 的全域解析证明。

所有70 nested cursor 和48 parent cursor 重新执行 cutwalk 合同：
只有前序已 covered 的 state 可作 cut，73字段、原 cursor、耗尽位置
和非零结果必须一致。fuel=0 不允许绕过为 cut 成功。生产源含 nested
cuts，不是旧 flat walk；本包展开原真实 tree，再独立核这些 cut 合同，
不漏掉 cut 内部 leaf，也不把它们重复算作新 leaf。

## 完整原树对比

- 48 roots，27,234 nodes，13,593 branches；
- **13,046 numeric +595 reflection =13,641 terminal leaves**；
- 443,564 term decodes、189,987 active mokI、15,179 有效 flow entries；
- 48 parent 与70 nested cursor 合同，全部 state/end/依赖顺序一致。

因此网页或任务中的13046应理解为 numeric leaf 数，不能称为全部
terminal 数。本程序没有把13046作为预先的成功断言，而是从原树
重建后与生产结果比较。

所有 root rows、计数、70合同和最小原整数 margin 都逐项相同；最小
margin 为 `65385001396000000`，位于 root11、position27229。
全27,234个事件的 canonical JSONL SHA256 为

`c486090f64a67eccae8de6914688626738e212ebe7ade515d6825efa28abc10e`，

与生产回放完全一致。这个摘要同时绑定每个 node 的 state、split、
cursor/end、leaf kind 与 margin，不只是总数。

原 parser receipt 的 `WD_identity_count=2` 是局部变量被字符串覆盖
造成的历史 metadata 错；该 producer 在原断言中已核dict identity，
后来 consolidated summary 另作纠正。本独立程序直接从新源逐项
核对 `WD0..WD47=rdw WL0..WL47`，结果为48。未修改原历史 receipt。

## 原 root outside guards 独立补齐

完整 COV 连续拼接、八个 SMAX 压力尾、八个 small-gap payment 与
rcM bound 重新核对。对固定源的160个原 true COV 区间，还独立计算
`CellN.WZ` 的原整数实参；没有新增区间或核锚。

WZ 实现使用 Fraction 表示中间有理数并在源规定的每一步向外取整，
与 producer 的整型 IV 类不同。cosP/cosN、sinP/sinN、scP/scN
直接解析新源的 Nat polynomial AST，CE/CJ/FA0 顺序来自13项新窗口，
归一化和误差常数也从新源读取。SZ 的 floor/ceil 先按 signed value
正规化，和源 `SZ.fl/ce` 的分支定义一致；正 coefficient interval
的 mulc 用等价的四角精确乘积实施。所有原 CellA.ok 前置条件检查。

160项 WZ、左右整数、每项 margin 均与生产补充逐整数相同；最小
root guard margin 为 `24036010866362157838000000`。
这补齐原 baseline receipt 明确保留、后来由 root-WZ supplement
关闭的有限 guard 缺口，没有把原历史标记偷偷改成已完成。

## 结论及明确剩余

没有发现这份原 floor 的 walk/leaf/root finite-argument replay 与
固定源消费者之间的实际整数差异。Stage A 的生产原有限回放经过
一份没有 producer imports 的独立实现复核。

源内 LB/PT/WZ 解析有效性、source theorem 的 proof terms、允许三
公理、最终完整 Lean、nanoda、Comparator 时间/内存仍需各自核验；
本回放不等同于全部已有 table proof 的重新内核证明。它也未完成
新阈值的全 sublevel 分类、任何 overlap 付款或新比例。Stage B
仍未执行，网站提交仍不可由本包宣称已准备完成。
