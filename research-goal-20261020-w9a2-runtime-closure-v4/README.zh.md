# 闭包准备 v4：Package.id? 的真实类型是 Option String

v3 原 exec session 66541、pid 44480 已实际 terminal exit1。其 SDK archive 组件重新核验成功，随后 source/cache 检查走到 Zeta legacy trace 的 `Package.id?` 叶时失败；没有生成完整 closure 或 setup PASS receipt，也没有运行 proof/compiler/export/kernel main。v3 全部字节和失败输出保持冻结。

根因明确：`Lake/Config/Package.lean` 的 `Package.id? : Option PkgId` 对原 Name 调用 `toString (escape := false)`，而 `Lean/Setup.lean` 定义 `PkgId := String`。v3 把包 ID 误当 `Option Name`，多加入了一次 Name 的 `mix 1723`。

v4 唯一代码差异是这一叶的公式：

```text
mix(1723, mix(SDK.string_hash("Zeta23"), 13))
```

`Module.name` 仍使用原来的 Name 逐分量 hash，不改其语义。九项完整 trace inputs、实际 source/imports/options/artifact/depHash 核验及所有其他边界不变。正确类型依据、实际 trace 字段和精确文件 pins 见 `diagnosis.json`；`v3-to-v4.diff` 给出最小改动。

false gate 指向新输出 `tmp/w9a2-20261020/trusted-runtime-closure-v4`，可显式复用 v3 **实际已经写出的 SDK revalidation 组件 receipt**，仍对全部 13,951 个 member 和官方 archive 当前身份重新核验。v3 的“source cache 已处理 10000”只有进度日志，没有逐模块持久完成 receipt，所以 v4 不把该计数作为可复用的 cache PASS；source/cache 检查会重新实际完成。旧整批 exit1 从未升级为 PASS。

本准备包只做文件读取、类型语义静审和 AST 检查；没有调用 SDK hash、Lean、solver、exporter 或独立内核。Root 审本包并另存新的授权 gate 后才可执行一次：

```powershell
C:/Python312/python.exe -u research-goal-20261020-w9a2-runtime-closure-v4/assemble.py --gate <Root 新授权 gate 路径>
```

其输出 schema 保持与 delivery fullchain gate assembler 一致。任何失败会保留真实 terminal 并硬停；source/cache 全闭包和生产全链仍需实际检查，准备包不作 PASS 声明。
