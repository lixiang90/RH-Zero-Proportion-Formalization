# Windows 可信 native 工具：备用 source-bound setup，未执行

这是旧 Linux native-tools-v2 方法的 Windows 备用实现，当前未启动任何编译器、
exporter、kernel 或debug child。根当前Core编译存活时绝对不运行。模板授权false，
独占观察还要求Windows与Linux无Lean/Lake/Clang进程以及root保存所有旧handle真实
terminal证据。源码、安装目录和输出均使用新目录，不覆盖任何旧binary或receipt。

先采用更小的旧binary证据方案：当前exporter SHA bc718c9f…有
`verification/three-website-declarations-modular-nanoda.json`中真实
export_process_ran=true/exit0，同SDK版本d8b189与固定源码/trace/rsp；Nano b1980476…
有single-20261014的source-pinned真实kernel run。日期和路径变化本身不要求重建。
实际新缺口是解释执行overlay少了Export.Parse：正确同源lib另在
`tmp/Comparator/.lake/packages/lean4export/.lake/build/lib/lean`，应在新gate的tool
overlay添加并验证源/SDK/actual data hashes。Python实际动态stdlib pyd/crypto闭包也
须绑定。普通proof PASS或HEAD本身不能替代缓存来源；不需无条件重编Mathlib/Nano。

只有这些小证据经root复核仍不足，才考虑本备用setup。它从准备中冻结的9份源：
原Comparator五源、lean4export三源与原CoreAudit，完全独立SDK-only项目构建。
所有源SHA按原固定commit的LF字节锁定；CoreAudit SHA保持7e88e84d…原值。外部
Mathlib、Zeta23、候选源码、旧用户olean、包cache、Lake插件、联网require均不在
环境或manifest。`lake --no-cache -v build lean4export coreaudit comparator`是未来
唯一构建批次；第三个原Comparator前端只为使第九源也有完整原生artifact链，验收
仍用锁定CoreAudit，不在setup运行任何前端main。三个exe只在本新目录中生成。

build_native_once.py先完整hash SDK bin/include/lib，清空继承的Lean/C/link环境，
绑定无依赖TOML和empty manifest，再编译三目标。保存每条真实子Popen PID/exit，
所有fresh .olean/server/private/.ir/.c/object/exe/.trace/.rsp，以及前后不变的SDK
头文件/工具/静态库/链接输入。新项目没有外部package，工具import只允许原九模块
和实际使用的固定Lean/Std SDK imports。失败保留failure并停止，零自动retry。

runtime闭包采用实际Windows loader协议，不要求加载全部Windows可选组件：
probe_before_main.py仅创建本setup自己的新child，使用DEBUG_ONLY_THIS_PROCESS
等待自动initial breakpoint，记录GetFinalPathName和EnumProcessModules得到的
实际mapped PE文件，然后在继续用户入口前TerminateProcess并观察owned handle
真的terminal222。不会attach现有进程，也不会执行exporter/CoreAudit main。
Microsoft说明该断点发生在静态DLL映射完成、DLL初始化前；这里据此捕获的是
mandatory loader范围。参见[Initial Breakpoint](https://learn.microsoft.com/en-us/windows-hardware/drivers/debugger/initial-breakpoint)和
[WaitForDebugEvent](https://learn.microsoft.com/en-us/windows/win32/api/debugapi/nf-debugapi-waitfordebugevent)。

源码记录该范围限制：late LoadLibrary不能仅凭初始断点推断。setup额外绑定全部SDK
DLL和根实际Lean进程已观察的late SDK/OS模块；可选OS delay import另列，不把84个
泛OS optional项当成必须全加载的门。完整最终闭包仍需root把实际controller的
stdlib .pyd/crypto、WSL ELF loader/Nano和source-bound包缓存证据合并复核。

`libLake_shared`在旧exporter rsp中是链接输入；当前PE ordinary import图没有它，
不能仅凭-lLake声称它必须动态加载。保守pin SDK该文件可以，但范围必须这样注明。

未来唯一命令形状：

`python -B -X utf8 build_native_once.py --gate <root-new-gate.json> --gate-sha256 <exact-SHA>`

installation.json、terminal.json均fsync并以SHA关联；它们仅说明setup内部步骤。
root还必须拿实际外层handle观察setup parent真exit0且failure不存在；程序不能自行
证明其未来退出。所有输出始终proof_runs=0、official_website_acceptance=false。
这套可信setup在后续完整生产t0之前；真正候选必须随后重新生成并在3200秒全链中
重新绑定native工具/DLL与全部输入，不能以setup成功替代候选普通/双核或官网接受。
