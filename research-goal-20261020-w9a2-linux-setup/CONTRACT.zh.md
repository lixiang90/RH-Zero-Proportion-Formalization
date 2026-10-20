# W9A2 Linux 隔离恢复最小合同

本包已准备、未执行 download/mirror/import。采用官方同版 Linux compiler 加当前同 commit
Windows 现有源码与 library data 的 ext4 镜像；不重新 cache 全部100911个 ltar，
不重编140个旧依赖或旧 proof，不修改 Windows 原缓存。
根代理须冻结本包另门后方可执行 setup；任何 Lean import/依赖编译必须等原 Windows
句柄真实终止并另行授权。setup.py 没有任何 lean/lake/cache 调用。

## 成本与路径

compiler 为官方 v4.33.0-rc2 `lean-4.33.0-rc2-linux.tar.zst`，574905502字节，
SHA256 `48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c`。
脚本先读取官方 release metadata，再要求 asset 名称、大小、官方 HTTPS URL 与 digest
全部相同；单次下载失败保留 partial，不自动重试。解包后的 Linux bin/lean 应为
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`。

Windows 存档：`tmp/w9a2-20261020/linux-setup-v0/`；Linux新根固定为
`/var/tmp/rh-zero-w9a2-20261020/runtime-v0`。绝不覆写原 runtime 或有内容的 v0。
本机只读 WSL 探测确认 Ubuntu x86_64/glibc2.35 可用，旧 `/var/tmp/rh-zero-20261015`
与 `/tmp/rh-zero-20261015` 均不存在，新根尚不存在；python3/tar/zstd/curl/git 均在。
当次 `/var/tmp` 可用170039099392字节。脚本另要求至少15GiB余量作为保守 setup
储备；这不是对实际占用的测量或性能保证。

delivery 已独立盘点 Windows Mathlib 有8313个 olean、1825406224字节，Zeta23
有142个 olean、120734520字节；全部 .olean.server/.private 与 .ir 另需复制，
不能把上述约1.95GB当完整镜像大小。现 .ltar 全库约4.85GB，本方案不复制它。
若以后改为源归档恢复，10个普通依赖的固定codeload归档共29354689字节；
本方案直接镜像当前源码，不下载这10包，也不下载Comparator/export/nanoda。
旧140模块累计1750.305秒及旧cache384.432830101秒只是历史成本，不能当新恢复ETA。

## 数据身份与可移植性的准确范围

十包 commit、原codeload URL/SHA/bytes 见 contract.json，对应当前 lake-manifest 与
旧 source-archives.lock。镜像前逐包检查本地 git HEAD；git命令只读且设置
GIT_NO_LAZY_FETCH=1、GIT_OPTIONAL_LOCKS=0。每份复制的 `.lean` 与根配置文件按
Git blob SHA1核回该固定tree；Windows CRLF只在核回原blob后规范化为LF。
源码不是“相同commit名称即假定相同内容”。

`lib/lean` 镜像 .olean、.olean.server、.olean.private、.ir、.ir.sig 及相应hash/trace。
每文件源/目标SHA256、大小及来源写入逐行清单，源在复制前后再核相同；不复制DLL、
SO、object/archive或旧candidate/ChallengeDeps输出。三个已知docs/benchmark源码
symlink只记录Git blob并跳过，不解引用；Lean源码/config symlink会失败停下。
只为mathlib/Zeta23建立指向新根内依赖的links，不复用旧Windows绝对路径。

当前Mathlib缓存属于其固定51e6992e…源与同版toolchain的本地library data；
Cache.Hashing的公式以根配置、模块路径、规范化源及imports为输入，没有平台键。
因此官方同源ltar是可移植数据的合理来源，但本包没有把100911个ltar逐个映射到
现输出，也不虚构这种来源证明。本方案的强证据是固定Git源码与现有data逐字节镜像；
后续完整Lean/nanoda导出仍必须核查实际proof。

已静读安装的同版Lean源码：Environment.readModuleDataPartsOfMod读取.olean及
server/private；readIRPartsOfMod读取.ir.sig/.ir。importModules只显式加载其plugins，
Frontend只在传入ModuleSetup时加载setup.dynlibs。本方案后续采用直接lean调用，
没有 --setup、--plugin 或 Lake动态库配置，所以不尝试加载Windows DLL。
Linux标准库和runtime native extern由完整官方Linux工具链提供。
两端都是x86_64、同githash；这些事实支持一次import试验，尚不能把ABI可用性当已证。

## 已准备的执行命令与停止条件

根另门授权后，在Windows仓库执行：

```
python research-goal-20261020-w9a2-linux-setup/setup.py download
```

该阶段仅下载固定compiler。随后仍在根授权范围内，以Ubuntu执行：

```
wsl.exe -d Ubuntu -- python3 /mnt/e/codex-build/RH-Zero-Proportion-Formalization/research-goal-20261020-w9a2-linux-setup/setup.py mirror
```

mirror先核archive、全部包HEAD与tar路径，然后仅解包和复制；不运行compiler的
--version，也不把setup receipt当import或proof PASS。新根已存在、源blob变化、
缺文件、坏散列、额外symlink、解包/复制失败均原地停下，保留v0，无自动repair/retry。
receipt中的runtime lean_path只指向ext4。所有当前Windows源与data保持不动。

Windows原句柄终止后，根可另门执行唯一 `TrustedImport.lean`：它只import当前
Core的22个非ChallengeDeps imports并#check实际Ncount/N0star，无candidate theorem。
普通import若ABI、IR、part或extern不兼容，立即保留错误；不自动重编依赖。
它若通过只证明这次可信库可被该Linux工具链加载，不能代替后续实际新Core/Graph/
Localization/Counting/Final、公理、Comparator、独立核、源码体积与生产总时间验收。

旧配方不可原样执行：prepare_linux_runtime硬编码旧用户/mnt/c/Users/ip且会覆写
runtime.json；build_dependencies会bootstrap cache再固定4路编译所有Zeta23闭包。
本新方案避开这些动作，依赖compile保持未授权。
