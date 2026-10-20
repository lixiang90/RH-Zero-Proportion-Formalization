# 当前运行时闭包：只读证据与未执行准备

本包没有运行 Lean、export、Comparator、kernel、nanoda main、Rust/C compiler、
installer 或新候选。没有改动冻结v1 runner、旧source草稿或CoreAudit。只读模块查询、
PE字节解析、SHA、git HEAD文件读取以及系统ELF loader的`--list`元数据模式产生证据。
所有完整闭包/执行授权字段保持 false，不能把本包直接当成v1验收运行许可。

`capture_loaded_modules.ps1`只读指定的现有process。当前实际快照来自根已指明的
Lean PID19056：2026-10-20T06:41:43Z，start06:38:35Z，CPU68s，36已加载PE模块。
这证明该进程当时的模块路径；它不证明进程以后已退出，也不证明另一个native
exporter会加载完全相同的模块。快照不是任何证明编译通过收据。

`inspect_runtime.py`只解析文件与hash。review-v0保留最初精确API-contract匹配遗漏
旧revision的诊断。review-v1追加按Windows API-set namespace实际HashedLength
作兼容revision的静态推断，仍明确标成inference，不把它冒称实际loader观察。
review-v1遍历376个PE图像，普通import在此静态模型全部得到候选；84个未解析项
全是广泛OS传递遍历中的delay import，包括空host的可选API-set和HvsiFileTrust、
cmclient、wpaxholder、UpdateAPI、PdmUtilities、AzureAttest等。没有用删掉delay
边的办法把complete改true；root需界定实际可信OS边界与本程序可达加载范围。

当前Lean实际模块包括SDK的libleanshared.dll、libleanshared_1.dll、
libleanshared_2.dll、libInit_shared.dll。native exporter link rsp及静态PE import
另要求SDK的libLake_shared.dll；文件已纳入hash候选，但本包没有启动exporter。
Python静态候选中VCRUNTIME140有Python目录和System32两份；独立当前Python进程的
GetModuleHandle/GetModuleFileName只读查询实际选中`C:/Python312/VCRUNTIME140.dll`，
并选中System32/ucrtbase.dll。controller版本是3.12.5；不要沿用旧C:/Python314。

ELF program/dynamic headers和系统loader的`--list`实际确认当前Nano
SHA `b19804767cb72bf5a317fcfc20e8af7eafdfba789dd6b24bddee2574379ff35a`：
直接NEEDED只有libgcc_s.so.1、libc.so.6，loader实际解析到
`/usr/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2`。evidence里还保存setsid、sh(dash)、
kill、readlink、env及清理工具的传递SO和ld.so.cache，共18个实际文件的resolved
路径/bytes/SHA。这里没有执行这些目标的main，只有loader列依赖；vdso由内核提供，
没有伪造磁盘文件hash。WSL原默认沙盒调用E_ACCESSDENIED后，根授权的require_escalated
只读调用成功；没有安装或重启WSL。

同一Nano SHA已有精确历史来源：

- `verification/gram-defect-single-20261014/independent-kernel.json`的
  tool_provenance.nanoda_binary记录该SHA、固定source commit
  418320295890faed83a96fd97907b12a3b6728c2、Cargo.toml blob SHA
  716d6dde2ac8a5563f0e9a363bee85ce18d0819a34f7b5d865c1e03d3c6d638f，
  并引用three-website-declarations-modular-nanoda.json。
- `verification/analytic-independent-nanoda-driver.json`在前后SHA中同时绑定
  当前Nano和native exporter SHA
  bc718c9ff717b36827799e8edbc86028edaf86bdd26931ce7a8882fd3fbb67d9。
- 现存build-nanoda.sh明确`cargo +1.97.1 build --locked --release`，log结束于
  固定目录nanoda_lib v0.4.13 release完成49.14s。脚本/log/当前Cargo.lock均有hash；
  本包没有据此声称新build或新proof通过。
- 当前native exporter的Lake link trace、rsp、固定8个工具source和当前字节身份
  全已记录；旧receipt与source绑定的证明范围由root复核，不能只填commit字符串。

package HEAD与root原trusted-setup gate逐一相同，只证明当前git身份。为避免与根
唯一compiler争抢大量NTFS metadata，本次没有遍历hash全部package缓存。准备脚本
提供显式`--include-all-package-cache-files`，root可在此前compiler真实terminal后
独立审核再调用。它只做hash，仍不自动证明缓存与源码的生成关系。特别是
olean.server/private、IR、解释执行Comparator/Export overlay都需明确来源与全文件
pins；单独HEAD、单个olean或成功导入不能代替这项绑定。

`build_incomplete_manifest.py`可把这些小证据合为v1 schema候选，始终输出
complete_source_bound_runtime_closure_verified=false，列出确切缺失来源。只有root
另行拿到实际可信setup/导入/必要tool建立门的终端收据，完成源/缓存/当前加载闭包
审查，才可生成新的真正批准manifest与gate。任何setup compiler均需root另gate，
本包不会并发启动。Linux恢复与普通门由independent_math的独立目录负责。

大型PE逐边JSON保留原SHA，并提供确定性gzip运输；原文件本地不删除。它们是审计
元数据，不是上传的Lean源码或数学证书。完整source size与3200秒合同均未改变。
