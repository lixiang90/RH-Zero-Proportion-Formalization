# 固定新纪录 Stage B：原见证的一次阈值分类

本包在书面 gate `research-goal-20261016/gates/stageB-20261018.json` 的
授权下执行一次完整分类。Stage A 生产包和独立包先逐项验 SHA；本生产
分类复用 Stage A Python 的 parser、整数模型和完整 walker，**不自称独立
实现**。另一代理的 Stage B 独立审查另行封存，本包不等待或预先代称通过。

唯一新阈值为 `893916123055294719/10^20`，分离为实数 `17/20`。
源内原 cN 仍是 `893616123055294719`。原 printed mcheckP 的 Nat.ble
AST 中 cN 恰出现一次，是左侧加法树中的 `335544320000000000*cN`。
故对完全相同 state、FS 和 flow，精确使用

    M_tau = M_original - 335544320000000000*300000000000000.

未改 source 的 cN、树、cut、点表、FS、flow、核值或任何原 guard；未调用
优化器或 Lean。所有原 leaf 都从完整树展开，未把 Covered(c9) 的 ready
cut 偷换成新阈值成功。所有 active mokI 以及 compact/printed AST 原余量
重新一致，原 48 parent 与 70 nested 的 state、fuel、start/end 均一致。

## 唯一真实执行

执行前保存 implementation.json 和 source SHA；run_once.py 在 Popen 前
保存完整 argv、cwd、命令 SHA 和脚本 SHA。只有一个 child launch，无失败
分类或重试。执行前纯 metadata 检查发现独审 A 的 imports 字段是整数 0，
因此 source 使用整数 0 的 schema 检查；没有改独审输入。

child PID 9352、parent PID 27164；exec 会话 85713。child 35.6964236s，
parent 36.1104046s，exit 0，peak RSS 90,750,976B。外部 parent 对唯一
child 监控 180 秒与 32,000,000B 输出上限；未触发任何上限。

完整原树为 27,234 nodes、13,593 branches、13,641 terminals。其中
13,046 numeric 恰好分为：11,859 closed_numeric_at_tau、1,187 exception。
595 reflection 只因原条件 h7<h0 与有序半域 h0<=h7 矛盾而排除，未支付
任何能量下界；Farkas 为 0。189,987 active mokI 与 443,564 term decode
checks 均与 A 相同。未压缩的 canonical all-node trace SHA 与 A 两实现
严格相同：

    c486090f64a67eccae8de6914688626738e212ebe7ade515d6825efa28abc10e

whole source 与全部被绑定的脚本/闭包输入前后 SHA 相同。原 source
1,818,411B，SHA f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。

## 任意分离 sublevel 的完整外包范围

本包不是 minimizer/KKT 覆盖。数学接口针对任意八 gap h_r>=17/20 且
F9(h)<tau。原 root 外 160 true-COV 仅复用 A 已精确重放的原 WZ guard，
加整个 sep*B 压力得到 c9+sep*B>=tau；未计算新 WZ。八个 SMAX 尾部
使用 b_r*SMAX_r/32768 + sep*(B-b_r)，没有重复第 r 项压力。八个
小 gap <=1/2 的分支在分离域连端点也为空。COV 全部真假段连续性、
边界以及 48 false-interval root products 保持原结构。

有序半域中每个真正 sublevel 点必属于一个 exception 原闭 cell。
由本核 reversal invariance，整个分离 sublevel 属于这些 cell 和它们
反射的并。source 的实际 LB/PT/WZ/reversal 定理是解析依赖，本 Python
包未重新证明其 Lean 证明项，也未代称 kernel/Nano/Comparator 接受。

每个 exception 保存 8 adjacent 与 28 PR 的全部闭上下界，顺序从源取，
单位 1/32768；同时保留 M=0、root/path/stream position、原 witness
语义 SHA、packed payload SHA、nested provenance 及两种整数余量。
未把实数 sep*32768=27852.8 向上取整。为将来的 DBM 松外包，输出明确
记 relaxed_orientation=true：h0<=h7 被丢去使 cell 更宽，而不是假装
它是一条 difference edge。等号 h0=h7 可选 identity 朝向。

exception 表示原见证余量不足，**不表示存在真正低能点**。本包未计算
任何两个例外 cell 的相交性，未得相邻双窗口 floor 或新零点比例。
后续四朝向 pair scan 及新消费者均需另行授权和完整证明。

## 行格式与编码预算

* all-node-events.jsonl.gz：与 A 同 canonical 事件，无新增数学字段。
* numeric-classification.jsonl.gz：13,046 行，每行 root/position/end/path、
  kind、original_margin/tau_margin 十进制字符串、state_sha256 与原
  witness 定位及两种语义 SHA。
* exception-cells.jsonl.gz：上述 exception 行再加连续 exception_id、
  state={L[8],U[8],A[28],B[28],M:0}、coordinate_scale、nested/root
  provenance、separation 及明确的 orientation 松弛标志。
* classification.json：完整计数、PR/pair order、48 roots/70 contracts、
  AST debit identity、所有输入前后 SHA、输出 hash 和预算未知项。

实际 gzip bytes：trace 1,768,819；numeric 2,421,338；exceptions 458,348。
gzip 只是可重放研究数据，不是网站 Lean 源码。为避免把压缩比当证明，
同时计量一种朴素 73 整数十进制 payload 共 579,013B；该测试语法也未
作为合法 Lean 编码实现。baseline 距十进制 2MB 仅余 181,589B，旧三桥
38,361B 也只是迁移参考。完整新 consumer、几何/DBM 证明、新实例与
wrapper、删除替代部分以及 ordinary/export/Nano 运行量都尚未知。
因此完整源码/运行 gate 标 false，禁止因当前 JSON 数据量而启动证明批次。

本包生产数学 pass 已结束。独立 B 审查另存；没有新全局 floor、无条件
新纪录或可提交材料完成的结论。没有改治理计数或旧 frozen 包。
