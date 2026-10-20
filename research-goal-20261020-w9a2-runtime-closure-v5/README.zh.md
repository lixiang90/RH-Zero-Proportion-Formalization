# 闭包准备 v5：一次性覆盖所有导入 Zeta 的旧式与现代 trace

v4 原会话 89749、pid 12340 已实际 exit1：`Package.id?` String 修复越过了此前叶，随后在唯一现代 Zeta 模块被旧式限定拒绝。v1–v4 所有授权字节与实际失败保持冻结。本 v5 assembler 未运行，没有 SDK hash/API、证明、编译器、导出或独立内核执行。

本次先审完整输入族，再准备执行：Zeta23 源码树有 316 文件，当前候选九个 Zeta 根的传递闭包恰好 140 个，正好对应全部 140 个现有 Zeta trace；其他 176 文件没有被导入，不需要新 cache/重建。139 个为旧式，唯一现代模块是 `Zeta23.FromPNTPlus.EulerMaclaurin`，它 `public import Mathlib.NumberTheory.AbelSummation`。全部 140 trace 都是 schema 2025-09-10、九项 inputs；所有声明数据及 sidecar 均存在，sidecar literal 与 trace 一致，没有 source/trace module flag 差异。

`header_info` 现在保存三个独立标志 `is_exported/is_meta/import_all`，原 `header/imports` 名称列表接口不变。新 `TraceHashGraph` 逐式复现固定 SDK 的 public/meta/all/legacy transitive trace 和三个 artifacts 模式，保持导入顺序与重复。SDK direct imports 按 Lake findModules 规则不参与包 trace。

已实际完成两份独立的纯 Python literal 算术审计，均未调用 SDK：本包 `all-imported-zeta-trace-graph.json` 递归 8,821 个非 SDK 包节点，用现有 `.hash` literals 逐项复算所有 140 Zeta 的 imports、module bool 和完整九项输入树 depHash，全部 PASS。唯一现代模块精确得到：

```text
AbelSummation public transitive = 96f70e16101598b7
AbelSummation public artifacts  = baf83acae4c1bb2c
EulerMaclaurin complete depHash = 5a11c1a174c9ac72
```

该算术审计有 61,199 个所读小文件 pins；formal_owner 另写独立 parser/checker 得到相同全量结果。它证明算法与 literal 数据一致，**不替代**最终 assembler 的实际 SDK/数据 byte hash、Git blob、ltar 来源门。

运行时仍先逐文件 `verify_outputs` 核实际数据 byte hash，并把已核 sidecar 值保存到节点供 graph 计算。source visit 按 postorder 插入、outputs 按同序执行，所以检查 Zeta 时递归所需每个 child output_hashes 都已经实际核验。不要把该遍历改成非 postorder。现代 bool 使用 11、旧式 bool 使用 13；Package.id? 保持 Option String，Module.name 保持 Name。

尾部也提前审过全部前提：五旧工具 olean/八源码/固定 Git HEAD/Nano Cargo 和全部 tracked Rust 源/两 native binary/构建证据/Python 当前 loader 路径/应用 PE 普通导入均通过只读检查。默认 sandbox 在第一条 WSL UNC 读取抛 WinError65，审计程序真实退出1，未伪报 PASS。Root 随后实际 `require_escalated` 只读核完旧 ELF receipt 的 17 个 UNC 文件，17/17 当前 SHA 相同（chunk 4f3122）；这是执行权限边界，不是路径或数据错误。最终 metadata setup/fullrunner 按 Root 既定计划在该权限下执行，代码完整检查不放宽。见 `tail-execution-scope.json`。

`all-zeta-shapes-final.json` 是最终完整类型盘点；早期 `all-zeta-shapes.json` 把未缓存文件的 None 也算入 flag difference，保留作原始审计过程，最终盘点已只比较实际 trace，差异为零。

false gate 指向新输出 `tmp/w9a2-20261020/trusted-runtime-closure-v5`，显式复用 v4 实际 SDK 组件 receipt 后仍重核所有 member 与官方 archive 当前 SHA。此前失败整批及仅日志计数的 cache 进度都不升级为 PASS；source/cache 将重新实际全核。输出 schema 与 delivery 的 gate assembler 保持一致。

Root 审本准备包并另存新授权 gate 后，使用允许读取 WSL UNC 的执行权限运行一次：

```powershell
C:/Python312/python.exe -u research-goal-20261020-w9a2-runtime-closure-v5/assemble.py --gate <Root 新授权 gate 路径>
```

只有实际全部检查成功才生成 closure；原外层 handle 的实际 terminal0 与所有 pins 不变仍由 Root 独立核验。本准备包不宣称全闭包、生产全链或官网通过。
