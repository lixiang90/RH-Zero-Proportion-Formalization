# W9A2 定量 walk 与全域定位准备合同

本包仅准备源码；没有运行 Lean、Comparator、nanoda、LP、核函数、覆盖树或新的数值搜索。
当前官方源为 `research-goal-20261019-w9a2-record/official/proof/Solution.lean`，
1754387 字节，SHA256 `241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7`。
源码及全部旧证据保持不可变。原 transport 两个大输入仅无损恢复并核回原 SHA。

## 定量消费者

`StructuralW9A220261020/Core.lean` 是该官方全源的确定性文本变换。
在原 `AMW.Cert.PC9QB6M` 内提供：

- `qState k`、`qCell k`：冻结 `geometry-audit.json` 的 first24 原始数值叶；73 个字段的 M 仍为 0。
- `qCost k`：相应原 margin 整除 `335544320000000000`；不更换核、锚点或见证。
- `qGoodIncrement=1000000000000`，`qGoodTarget=cN+qGoodIncrement`。
- `qDagIncrement=121390593524`：冻结第 8 margin 给出的首 7 低态备选阈值。
- `qTargetFrom`：按 rank 顺序寻找完全相等的原 St，命中则检查 `cN+qCost k`，否则检查 `qGoodTarget`。
- `QuantGoal g`：原好态 Pg，或某个 k<24 的真实 `InCell qCell k g` 连同该 rank 定量 Pg。

`mcheckP` 只把 floor 参数泛化为 `goalN`；所有其它整数表达式不变。
`mleafP` 的 decoder、质量、激活区间、flow、guards、term ledger 不变。
数值叶将 `qTarget s` 传给原 checker。Farkas 叶仍为空域；reflection 叶放入好态 Pg 的反向分支。
walk、split、状态转移、游标、原 48 个 rc 定理、原打包数字和源数据逐字节保留。
原 `cert` 经 `quant_forget` 回到 cN，故整个原数学与计数链可保留。

只移除过期 `ChallengeDeps.CandidateSpec` import 和与它绑定的三个旧 public wrapper；
原 `ChallengeDeps` import、数学定理、完整 attribution/license 均保留。
最终新 public wrapper 由新的可信 CandidateSpec 和最终新计数结论提供。

## root 外与 reflection 的实际合同

`StructuralW9A220261020/Localization.lean` import Graph；不与 Graph 循环依赖。
`sep=17/20`，`base=cN/SA`，所有数据指向当前 W9A2 Core。

`root_QuantGoal` 在全部 separated 域证明 QuantGoal：

1. 以每个 gap 的真实非负压力及全部 actual wfun 非负性构造下界。
2. 对 `g r >= SMAX r / SC` 的每个 tail，用原 `cN*SC<=BS[r]*SMAX[r]`，再补其它七项 sep 压力，支付好态阈值。
3. `g r <=1/2` 与 sep 直接矛盾；闭边界包含在原 coverChk_sound 的 <=/>= 合同内。
4. 原 true-WZ cover guard 仍只证明 cN；另加全部 sep 压力支付好态阈值。没有伪造提高后的 coverChk 或 WZ 数据。
5. 其它全部配置以原 badOf / idx / incell_root 构造进入原 48 个根，由定量 Data.run 消费全部原 walk。

`ordered_quant` 只用 `g 0<=g 7` 排除每个 Pg 的反向分支。
`scaled_energy` 使用当前 `Fg_G`；`reverse_energy` 使用当前 `PC9QB6M_G_rev`。
`located_state` 为任意 sep 的实际 8-gap 配置选择 id 或 reverse 两朝向，给出：

```lean
∃ v : Fin 49, Graph.StateAt g v ∧
  base + (Graph.cost v : ℝ) / SA ≤ Fw RiemannFail.W9 g
```

G=48 可容纳所有 root 外配置；v<48 时 rank=v/2，odd v 为 reverse。
成本来自 Graph.cost，避免第二份 49 态成本表。
没有 minimizer、scalar model、额外 guard、local energy floor 或数值假设。
`low_DAG_state` 在同一消费者上给首 14 个朝向顶点；没有第二次 walk 或阈值扫描。

## 尚未验证的义务与停止条件

所有 proof 体已写，但未声称普通 Lean 通过。首个编译关必须检查新递归 selector
soundness、泛化 mleaf、全部 48 个定量 rc 的实际 `decide +kernel`、整个 root/reflection/
scaled-energy 构造及实际 located_state。任何 finite check 失败应保留原源与日志；
不能自动换 margin、修改 cell、忽略叶或重跑数值搜索。

普通 Lean 通过之后仍须实际全窗 transition、potential 求和、separated 窗计数、
短对付款和新 unconditional dyadic/cumulative 比例；这些由其它本轮模块负责。
还须全 theorem 的传递公理审计、实际单文件 byte 数、冷检总时限、Comparator、
Lean/nanoda、届时网站最新精确纪录比较、GitHub 字节同步与提交材料。

Core+Localization 当前 raw 合计 1783365 字节；这只留下 216635 字节的纸面余量，
并未包含 Graph/Counting/Final 与 flatten 处理，不是网站大小或时间验收。
没有以原 numerical replay PASS、模块数量或 source-generation 成功冒充新纪录。

## 源码准备中的文件失败

`generate_core.py` 首次在读取未恢复的 geometry 输入时退出；无输出、无数学或 compiler。
`generate_core_v1.py` 在旧 public wrapper anchor 非唯一时断言退出；仍无输出。
`generate_core_v2.py` 仅把该 anchor 扩成唯一完整前缀，随后生成当前 Core。
这两个文件级失败保留，不属于新的求解或编译试验，也没有触发参数重试。
