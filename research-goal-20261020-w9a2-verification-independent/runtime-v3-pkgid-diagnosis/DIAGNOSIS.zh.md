# Package.id? 类型诊断及前次静审更正

实际 runtime v3 的来源检查在 Zeta23 Package.id? 叶失败。原因已由源定义确定：Lake/Config/Package.lean 的 id? 返回 Option PkgId，并用 origName.toString；Lean/Setup.lean 明定 `abbrev PkgId := String`。它与 Module.name 的 Name 类型不同。

Init/Data/Hashable.lean 对 Option.some a 定义 hash 为 mixHash(hash a,13)，Lake/Build/Trace.lean 再用 Hash.ofHashable 加外层 mix(1723,...)。故该叶应为 `mix(1723, mix(self.sdk_hash.string("Zeta23"), 13))`。原 v3 错把内层当 Name，额外混入一次 Name.anonymous 的 1723。Module.name 的现有 Name 算法不需要改变，原 trace 数值和缓存数据也不应修改。

我前次 runtime-source-review 对此叶的静态认可漏读了 PkgId 的 String 定义，该项认可由本诊断覆盖。其余类型的哈希公式与来源检查没有因本类型差别而改变。本目录保存五个输入源的 SHA、相关逐行原文及前后读取一致性。

没有改写冻结 v3，没有调用 SDK/DLL/compiler/exporter/kernel/assembler，也未声称新公式已经实际运行通过。修复版须新冻结，继续由主线程执行实际来源控制。
