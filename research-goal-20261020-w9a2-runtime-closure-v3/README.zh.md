# 可信运行时闭包准备 v3：精确 C hash 导出的实际 DLL

v1/v2 及其授权输入和实际输出全部保留且不再修改。本 v3 assembler 和 SDK hash API 尚未执行。实际完成的仅有 `scan_sdk_exports.py` 纯文件 PE 导出表扫描：先对 v2 的官方 SDK member PASS receipt 重核九个 SDK DLL 的字节，然后读它们的 export directory；没有加载 DLL 或运行任何工具 main。

扫描结果：`lean_byte_array_hash`（ordinal 44430，RVA 12851216）和 `lean_string_hash`（ordinal 44720，RVA 12849136）都直接导出于 `bin/libInit_shared.dll`，两者均非 forwarder；其余八个 SDK DLL 没有这两个精确导出名。原始证据 `sdk-export-scan.json` SHA `3a63b32e82c793bdc3d43e2c03413727f8cda01c3e77afb57d518a79564beade`，逐 DLL SHA/导出数/完整排序名称列表 hash 均在其中。

Root 的真实 v2（原 exec session 44009、pid 38328）已经实际核完官方 archive 的 13,951 个选定 member 并写出 PASS 组件 receipt，随后载入 `libleanshared.dll` 后因该库没有上述 byte-array export 而 AttributeError exit1。失败发生于 argtypes 解析，尚未调用任一 hash 函数；没有 proof/compiler/export/kernel main。本 v3 仅把库名和实际 GetModuleFileNameW 核对目标改为已有精确 export 证据的 `libInit_shared.dll`，buffer ABI 与两项允许函数不变。

v3 新增可选的 SDK 组件复用：Root gate 显式接受 v2 的实际 archive-member PASS receipt；程序仍先核官方 archive 当前 SHA，并对 receipt 中每个选定文件的当前 SHA、大小、resolved path 逐个重核，同时要求选定 member 集合精确等于本次源码闭包需要的集合。完成后生成本次新 revalidation receipt。它不复用 v2 的全闭包成功（v2 没有成功），不跳过任何 SDK 文件当前身份核验，也不自动重建依赖。没有该可选 gate 字段时，原流式 tar member 核查路径仍保留。

其他 fixed-source/Mathlib cache/Zeta 完整 trace/五工具旧来源/Windows-Python-WSL 边界合同不变。`v2-to-v3.diff` 给出精确代码变动。新 false gate 的输出为 `tmp/w9a2-20261020/trusted-runtime-closure-v3`，schema 继续与 delivery 的 fullchain gate assembler 兼容。

Root 审冻结准备包并另存新授权 gate 后，可执行一次：

```powershell
C:/Python312/python.exe -u research-goal-20261020-w9a2-runtime-closure-v3/assemble.py --gate <Root 新授权 gate 路径>
```

任何新失败均保存真实 terminal 后停止，不自动重试或修改。完整 source/cache 检查以及两 API 的实际调用仍待该授权执行；本准备包不宣称 runtime closure PASS、生产全链 PASS 或官网接受。
