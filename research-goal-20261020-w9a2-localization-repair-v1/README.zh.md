# Localization located_state.hor 证明修复 v1

仅准备同一局部命题的证明，不运行 compiler、exporter 或 kernel。新源在 StructuralW9A220261020/Localization.lean，13,295 字节，SHA256 `f4d32498996dd5f2781cdac1b17531c02757467dc62fae4e5b88d7d675842fd4`。原 canonical Localization 及本包 Localization-v0.lean 保持 13,294 字节、SHA256 `95138259450a504e9db184baa3b1e3b5cd1bdb8e11c8990d4b20a94cc7643a2d`。

实际 ordinary-v3 的 Graph v2 已退出 0（66.812 秒，olean SHA `9bfb52462f64be80158c143ac110fa2b0b23ca8c8577f37ea067280875ab4e0e`）；Localization 随后 16.875 秒退出 1。其完整日志只有一处 error，在原第 262 行：simpa only [reverse8] 之后，反射端点有限索引未归一为数字索引。push_neg 弃用警告不构成该失败。

唯一替换为：

```lean
    have hor : reverse8 g 0 ≤ reverse8 g 7 := by
      change g 7 ≤ g 0
      exact le_of_lt (lt_of_not_ge ho)
```

hor 命题原字节和原不等式证明 term 完全保留，只显式指定 reverse8 定义下两个端点的同一目标。此处不增加假设、分类分支或数值内容。单次文本替换与反向回投精确，全源仅增加 1 字节及 1 行；located_state 类型与其他全部字节不变。完整 root 外覆盖、反射覆盖、StateAt、成本、原数据、阈值和公开 roots 均未改动。旧 canonical 文件没有写入。

失败 job 的 started/terminal 及 Graph、Localization 各自 command/child/log/receipt 共 10 文件保存在 failed-ordinary-v3-evidence/。父 session 46495 的真实退出码 1 来自主线程明确工具观察，repair.json 中清楚区分该来源与所复制的实际 module 收据。读取前后所有原输入 SHA256 与长度相同。

编译新源前需主线程冻结新的 gate；本包没有声称新 Localization 或完整候选已通过普通编译、Comparator、默认内核、NanoDa、3200 秒总验收或网站接受。没有增加研究轮或数学搜索族。
