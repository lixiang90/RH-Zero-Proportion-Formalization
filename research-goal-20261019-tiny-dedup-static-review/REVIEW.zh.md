# Canonical Core 去重的只读可行性审查

结论：源码和依赖层面可行；没有生成备用 Lean 源、没有改冻结输入、没有启动编译/数学重放/网络。若当前冷验证成功，不需要实施备用方案。若因统一预算失败，它可作为减少普通编译冗余的一次独立生产方案，仍须全流程重新验证。

canonical Core 不是旧 Covered 语义：它已经包含强化的 TinyGoal、例外 full-state 定位和提高目标的数字叶检查。其 `PC9QB6M` 命名族需精确替换为 `PC9Tiny`：包括 namespace、Data 和 G_rev/half/cert_full 三个定理名字。两段名字均为7个 UTF-8 字节，所有出现均不在字符串文字中。仅删除原 baseline 实例/公开 wrappers 代码，不改阈值、数据或见证。

审查已经逐段比对：canonical 的强化 concrete checker、COV/137个 packed walk payload/cut witnesses、reflection→actual W9→generic counting tail，经名字替换后与已通过的 Dev/Core 对应段完全相同；不是重新设计证明。canonical 的 LB/PT 表块也与 CurrentPrefix 原表相同。新方案直接保留该表块的真实定义及证明，取代开发分割里 TOP/BK/lbS/TOPD/BKD/lbD/REG/hR/PT/ptS 十个别名。现有 Phase1.Localization、Phase2.Counting、Phase4.Final 只需去除内部 import，namespace、数学陈述和其余正文可保持原字节；原官网 wrapper 无需改。

切点须精确取 `end OpethN.Counting` 后的 `end`，然后保留原完整 THIRD-PARTY LICENSE 尾。不能盲删其间7,496字节：其中含两段 R. Arun Chandru 的 Copyright/Apache-2.0 block notices，必须原字节搬回注释区，两块连同分隔换行共1,404字节。第一版只读审计错误地预期旧尾无版权段，因此失败；原脚本和退出证据均保留，版本化 v1 已把两块计入。该发现没有改变当前生产输入，也不影响当前运行。

字节账本（仅计算，不生成源）：当前 CurrentPrefix+Dev/Core 为1,938,321字节；canonical 原文1,821,568字节。去旧定理代码且保留两块通知及完整许可证后为1,815,476字节，核心净省122,845字节。接现有三桥、沿用当前 header/wrapper/separator 格式，并以 `StructuralS1RTiny20261018.Production.Core` 作为模块标记，静态预测完整单源1,856,418字节，较当前1,979,280字节省122,862字节，距离2MB上限余143,582字节。若另加新的 production 说明注释，其字节应再计入；这些数值不是已生成/编译的候选。

性能边界：去掉了旧 concrete PC9 证明和开发 alias/header 的重复输入，因此可减少 ordinary elaboration 和模块导入开销。但固定 lean4export 是从指定 roots 递归调用 dumpDeps，仅导出类型和证明中实际使用的常数。旧 PC9 checker 很可能已经不在实际导出闭包内；不能把源码缩小6%左右等同于 Comparator、默认 Lean kernel 或 nanoda 同幅提速。本审查没有读取正在运行的结果为完成，没有测量新性能，也没有证明新统一3200秒门。

真正实施仍需要：独立版本化纯文本生成工具、全部数据/见证/通知保留审计、新单源 ordinary 与标准三公理检查、三个官网完整陈述及依赖/primitive 比较、默认 kernel 与 nanoda、统一 generation-through-receipt 的3200秒执行。禁止复用旧用户 olean 或凭静态等价跳过任一门。当前目标仍是无额外数学前提的严格零点比例改进，不以此工程审查替代最终完成。
