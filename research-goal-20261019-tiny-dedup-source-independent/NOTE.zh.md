# 去重源：独立纯文本复核

本包只读取冻结 canonical strengthened Core、Dev Core、三桥原版本与 Production
四模块，及 flatten-v3/v4 的源码和元数据。不 import 或调用任何 producer，不解码
数值见证，不生成 Solution，不执行 Lean、求解、矩阵、核函数、网络或网站操作。

核心标准是逆向全文字节等式：Production.Core 把 PC9Tiny 逆换为同长七字节
PC9QB6M 后，精确等于 canonical Core 从文件头到 `end OpethN.Counting/end` 的
原始字节、旧尾的两块版权注释和完整 third-party license trailer。除此之外没有
删改。旧尾明确退役的实际定理代码列在 receipt，而不靠“unused”字样推断安全。
全部原版权/许可 block 独立扫描并逐字存在；不因退役旧 public wrapper 删除许可。

另独立逐字比较既有 Dev 的强化 concrete checker、COV 后全部 payload/ready/cut/
walk、反射→实际 W9→generic Counting 段。137个 zfNat64 payload 原文本全部相同；
不是重新执行 packing/inverse 或数学检查。表的十个实际定义/证明仍在 canonical
位置；取代 Dev 的旧 prefix aliases，避免把旧 Covered 结论当新强化覆盖。

Localization、Counting、Final 三桥只改 import 行，其他字节完全一致。Final 的
tiny p/q、baseline、pressure、实际 root Ncount/N0star 和所有 premise 与已普通
通过的 Phase4 版本相同；本审计不自行重新证明这些定理。

flatten-v3/v4 generator 的 AST 在仅抽掉 MODULES 常量后全等；wrapper 完全同字节，
三个公开 theorem 陈述仍与官方冻结模板一致。预算通过源字节长度相加独立计算，
不实际拼出候选或运行 generator。实际未来生成和新单源完整验证仍是另一关。

v3网站并行测试源 SHA024902a7…df1a81只读绑定，前后不变。receipt 的纯文本 PASS
不能推出新源 Lean/Comparator/nanoda 已通过，更不能推出性能改善、总3200s通过或
官网接受。原 cold-v0 failure 保留，根代理拥有的 Nano 诊断与本包无任何执行关联。
