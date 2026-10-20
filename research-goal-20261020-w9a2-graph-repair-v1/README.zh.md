# Graph reverse_span 证明行修复 v1

本包只准备源码，不运行 Lean、导出器或任何内核；新编译必须由主线程冻结新 gate 后进行。

实际失败来自主线程 ordinary-v1，gate SHA256 `92def59e80c77b461e3cc301bff748f65e44d53b4c031d745098b156882a3bc5`，父 session 93720 实际退出码 1。Core 先以退出码 0 完成，588.859 秒；随后 Graph 64.25 秒退出码 1。完整 Graph 日志只有一处 error，位于 reverse_span 声明 148:70：反射有限索引展开后，ring 把 `g ⟨7, ...⟩` 与 `g 7` 等当作不同原子。原始日志、命令、子进程、收据和主线程封存的 terminal 清单完整复制于 failed-ordinary-v1-evidence/。

新源码位于 StructuralW9A220261020/Graph.lean，17,366 字节，SHA256 `9877394187460ee686e31561fe8f1ccb5015eb29fa2b7f5c2565071351add00c`。旧 canonical Graph 及 Graph-v0.lean 为 17,334 字节，SHA256 `a2e4f4fcc8068a245aafaff56363060ffcf4e06e1fccb63d57a999cfb68f0783`。唯一变化在源码第 151 行：

```lean
  all_goals norm_num [gsum_range, natGaps, reverse8, Finset.sum_range_succ] <;> simp only [Fin.reduceFinMk] <;> ring
```

插入独立 simp 步骤共增加 32 字节。全部 CRLF 保持，单行正向替换和反向回投均逐字相等；reverse_span 类型原字节不变，其他所有源码字节不变。因此 134 条许可边、2267 项排除、成本、potential、q 数据、StateAt、公开 roots、阈值和其余证明均没有变化。旧 canonical 文件没有写入。

SDK BuiltinSimprocs/Fin.lean 的 reduceFinMk 把字面值 Fin.mk 转换成相同值的 Fin.ofNat。Mathlib 中有显式 `simp only [Fin.reduceFinMk, ...]` 用例。这里必须使用独立 simp：NormNum/Core.lean 的 getSimpContext 仅取 elabSimpArgs 的 ctx，忽略其 simprocs；methods 的 preDefault/postDefault 使用空 simproc 数组。因此仅往 norm_num 参数列表加名称无法从实现静态保证该过程会执行。相关当前文件的 SHA256 和逐行原文位于 proof-rule-evidence.json。

此包不改变之前已普通编译通过的 Prefix 或修复 Core。所有原输入前后哈希一致；没有新数值计算、数学家族、compiler/export/kernel 执行或研究轮计数变更。修复后的 Graph 尚未编译，本包不声称 Comparator、NanoDa、默认内核、3200 秒总验收或网站提交已通过。
