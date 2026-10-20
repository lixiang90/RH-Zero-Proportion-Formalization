# W9A2 Windows 本地可信运行时闭包 v1

这是新建的、尚未执行的准备包。没有启动 Lean/Lake、编译用户证明、导出或运行独立内核，也没有修改主轮计数。`gate-template.json` 的 `authorized` 为 false。旧 incomplete 包及其冻结证据保留。

Root 审查并另存新授权 gate 后，可以从项目根运行：

```powershell
C:/Python312/python.exe -u research-goal-20261020-w9a2-runtime-closure-v1/assemble.py --gate <root 的新授权 gate 路径>
```

程序只创建 `tmp/w9a2-20261020/<新目录>`，拒绝复用已有输出目录。失败写实际 `terminal.json` 后硬停；不会重试、重建依赖或生成用户 olean。成功才生成 `closure.json`，并以实际 pid、argv、脚本 SHA、started pin、gate pin 和 `proof_runs=0` 生成 setup receipt。外层真实 exec handle 和 exit0 仍由 Root 独立观察、记录；闭包不替 Root 自行宣称外层 exit0。

源与缓存的合同：

- 用固定 Git commit 的 blob 校验每个实际需要的包源码；只允许与固定 blob 相等的原始字节或 CRLF→LF，HEAD 本身不算来源证明。
- 沿候选、可信 ChallengeDeps、CoreAudit 和固定工具源码头部求传递 import 闭包。包的 olean/server/private/IR 逐个按实际 Lake 输出 hash 核验；源码、trace、hash sidecar、选中的 ltar 和最终 overlay 全部记录 SHA256。
- Mathlib 使用源码中实际的 generation 5 根 hash、路径 components、LF 文本和有序 imports，重算 cache key，核对精确 `.ltar` 头 depHash、当前 trace depHash 和输出字节 LakeHash。该标准本地 cache 合同已向 Root 明确说明；它不是缓存官方密码学签名，也不是独立证明校验。
- Zeta23 只接受固定 legacy 构建配置，检查完整九个 inputs、实际 source hash、每项直接 import 的 transitive/全 artifacts hash、两个 options、module name、package id 和完整 depHash。其 overlay 只由实际传递闭包的数据文件生成；历史根 `ChallengeDeps.olean` 不复制。
- 在调用任何 SDK hash API 前，先验证保存的官方 Windows archive SHA `022576004ed8a4fc81ee8d375419064b54d4475931429d989519fd847ee053f6`，流式逐 member 比对所需 SDK 源码、数据、DLL、lean.exe 以及 `lean.h`。只调用 `lean_string_hash` / `lean_byte_array_hash` 处理 caller-owned buffer；不初始化 Lean 环境或进入其 main/import/check 路径。实际加载 DLL 路径也会核对。
- Comparator 四个旧 olean 和嵌套 `Export/Parse.olean` 精确重用既有实际 CoreAudit PASS receipt 的 SHA；八个工具源码同时核对固定 Git blob 和 frozen runner 的 LF hashes。Native exporter/Nano 使用既有实际 export exit0 和相同二进制 SHA 的来源桥，不把旧候选的成功当作本候选成功。

运行时边界：Windows System32、OS loader/API-set 是已安装系统的可信边界，不把 84 个 OS 递归 delay imports 伪装成应用必需库全集。应用侧普通导入、实际已加载 Python `_decimal.pyd`、`_hashlib.pyd`、`libcrypto-3.dll` 等逐文件核验；Python 已安装标准库文件也记录。WSL ELF loader/启动器采用现存真实 metadata receipt 的 resolved paths 并重新核验文件字节。没有官方沙箱等价性声明。

输出接口：`closure.runtime_gate_fragment` 含 frozen fullrunner 所需的完整 runtime 字段；其 Root review/outer exit 字段仍为 false/null，closure 自 hash 由后续 gate assembler 填写。`closure.package_root`、`candidate_package_libs` 和 `interpreted_tool_libs` 指向全新的干净 overlay；这些路径下的每个运行数据文件都在 `closure.files`。

实际成本边界是读取一次约 583 MB 官方 archive、所需源码与 cache 数据、复制所需包数据到新 overlay，并再次 rehash；没有下载整个 100k cache、没有重建 140 个 Zeta23 依赖。当前候选含 `import Mathlib`，所以其传递闭包接近当前 Mathlib 全体，不能声称只需两个包路径或几个模块。这里不给未经测量的耗时保证。

准备包仅做过 AST、头部解析/重复 imports、dict 输出遍历，以及实际 Statement legacy trace 的纯 Python depHash 结构算术核验。SDK DLL/API、SDK archive 逐 member、所有 cache/source 和 overlay 的真实检查仍待 Root 授权执行；任何断言失败都是尚未关闭的真实 blocker，不能手工把 complete 改成 true。
