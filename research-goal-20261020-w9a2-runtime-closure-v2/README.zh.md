# 运行时闭包准备 v2：补全官方 SDK Lake 源目录

本目录是新版本；v1 的所有文件及旧实际输出保持原样，不修改运行中的或已经授权的包。尚未运行本 v2 assembler，也未加载 Lean SDK DLL/API、编译证明、导出或运行内核。

Root 实际运行的 v1 是 assembler `2133f9b96d711032549b03eeafa5d52508eca1fd3cbddada15b3ee674aa3c306`、helper `76d5d5add51c61bfa21a7d51bb4ef912dbe1e95a6eac681cc239ffd947c9cd62`，原 exec session 85897、pid 44144、授权 gate SHA `003bdd24baa505e8592467a7f5007ecc31f110fb5e51649d2af740832d39fc55`。其实际 terminal exit1：源码 import 闭包阶段找不到 `Lake.Util.Casing`。还没有进入 SDK archive 核查、SDK hash API、缓存输出检查或 proof 路径。真实 started/terminal/gate pins 见 `previous-failure.json`；2133 原源码保存在 v1 的 `archive-pre-review-v1`。

v2 从已独审的 v1 配置补强版 `550762bc42b133ae6290407526b4bce2d54cd71d432a06ea2038965ebf997aa9` 复制，仅修改 SDK source lookup：同时搜索官方 archive 实际的 `src/lean/` 和 `src/lean/lake/`；Lake 的数据路径仍为 `lib/lean/Lake/...`。对应 `Lake/Util/Casing.lean` 文件已只读确认存在。精确代码 delta 在 `v1-to-v2.diff`。

其他 source/cache/SDK/工具来源合同、固定 Windows/Python/WSL 边界、五个 interpreted 工具 olean、禁止 user cache 与禁止 compiler/export/kernel main 的限制保持同一 scope。两项 SDK hash 导出仍必须在官方 Windows archive 与所需 DLL/lean.h/源和数据逐 member 同 SHA 后才能调用；实际来源/数据检查尚未执行，不能预设 complete。

本版本 false gate 使用全新输出 `tmp/w9a2-20261020/trusted-runtime-closure-v2`，并绑定自身代码和 metadata 输入。Root 完成 review、另存新的 authorized gate 后，可运行一次：

```powershell
C:/Python312/python.exe -u research-goal-20261020-w9a2-runtime-closure-v2/assemble.py --gate <Root 新授权 gate 路径>
```

失败保留真实 receipt 后硬停，不自动重试、重建或改源码。Root 必须独立记录原外层 exec handle 的真实 terminal exit0；后续 fullchain gate assembler 只能在实际 setup 和 ordinary PASS 后生成新的 false proposal。v2 schema 与 v1 相同，`closure.runtime_gate_fragment`、`package_root`、setup receipt pid/argv/script SHA 和完整文件 pins 可直接接 delivery 的 gate assembler。
