# D 唯一固定点算术已结束：正 margin，不是全域结论

SPEC.zh.md 为执行前的准备规格，原文保留。实际字段以书面 gate
research-goal-20261016/gates/stageD-affine-point-20261018.json 为准，
SHA 4c1ba012a8fa5c42aeec686ac3836ac4e747061cd8cea5d97c30c44cd2bcd87e。
脚本另强绑已冻结 flow 纸面证明 e3d61af4…64eb，不是新的解析计算。

唯一 child PID 50764、parent PID 53224，child 2.7479612 秒，parent
2.9946435 秒，exit 0；60秒/8MB均未触发。无重试，未改变点/FS/阈值。
执行前 implementation.json 固定 source SHA；launch.json 与 started.json
分别保存实际命令、pid和输入 hash。全部数学输入前后未变。

## exact 结果

在唯一 C potential 上：

    A_L = 152082264558971027263976838343 /
          16777216000000000000000000000000
    A_R = 37495735583468662581496221089 /
          4194304000000000000000000000000
    A_L+A_R-2c = 2167060893220488703515642699 /
                16777216000000000000000000000000 > 0.

c=893766123055294719/10^20。clipped 版本
max(c9,A_L)+max(c9,A_R)-2c 与 raw 版本严格相同：原 flow 证明已给出
本 cell 上 A_FS>=c9+M0/(kappa*SA)，因此在原 cell 内 clipping 冗余。
只按固定点正 margin，不推出整个 cell 或所有例外对的 joint floor。

68 个 term 全部保留原 L0=sum(original adjacent lower)、原 eL/eU、
uc、decoder混合权及active mokI。每一项 beta+sigma*s 与直接 signed
scaled numerator 精确相同，两个 whole affine expression 也相同。
外部 TS a/SA 只乘一次，R=1024 内混合不重复。mcp/mcn先按源 Nat.sub
分别计算再取 signed差；没有对 L0 或原 cell 作联合收紧。

原路径只按已经封存的 A trace 再现原 split，未重新遍历全部树。两份
原 FS/flow 的 packed 与 semantic SHA 全等。compact main margin、
printed AST margin 与原/raised记录一致；全部144 state bounds+9sep
及两 ordered 在同一点上复核通过。没有实际 w 值、核查询或新 tangent。

原 flow 的 Cp/Cm 只用于 certified affine floor，不加到 A 的定义或点值
两次。详细自然数项、34weighted terms、pressure、共同9gap coeff、
whole scaled numerator与原flow/box penalty都在evaluation.json。

## 从已保存余量可见的静态预算

这两个固定 cell 的 M0 是

    74501376990071397846927248000000
    56577247050221517825498512000000.

它们都超过 kappa*(cNum-c9Num)=335544320000000000*150000000000000。
因此按已经冻结的 flow 提取证明，这一特定 pair 中两份原 A_FS 的
逐 cell 强下界各自已至少为 c。这是原余量预算的直接后果，与 C 点值
和任何新 LP 无关；不表示剩余所有 pair 也如此。该比较已报告 root，
没有因此启动新的 pair 筛选或全域计数。freezer只从已保存余量验这条
整数关系，不调用term evaluator或重跑本次算术。

## 作用域

本包是 source 解析 lemma/flow 证明提取之上的有限有理算术诊断，未
通过新的 Lean kernel/Nano/Comparator。它未证明所有例外对的目标，
也未得到新的无条件零点比例。完整消费者、源文件及运行总预算仍未知。
另一代理的独立 68-term 重放另存，不预先代称已经通过。无求解器或
自动后续试验；下一步由root另行决定。

evaluation.json SHA：8137c2f0887db460edbb6c0850b3675cf2ecbb1a0b93285cd187dc751c825dce。
