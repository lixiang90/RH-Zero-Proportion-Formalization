本目录只准备一个固定v8-only Windows编译资源门，默认禁用，尚未运行runner、Lean、版本探测、exporter、kernel、网络或UI。它不派生/发现/修复源码，不恢复旧Nano，不执行数学重放或完整验收。模板已填root报告的冻结v8源码5424212b…/1829382B、draft清单7f4496…与独审dc3adb…，runner SHA仍为null且process ownership未提供；root需外部复核/冻结后另写新enabled gate，不能将模板当授权。

未来命令只运行一次原生Lean：-j1 -M6500 --tstack=262144 -DrelaxedAutoImplicit=false -DElab.async=false，并向独占tmp/w9a2-20261020/v8-resource-v1中的新路径输出-o/-i/-c及--json stdout。没有官方--setup；trusted imports由既有libs与缓存CandidateSpec提供。此差异必须保留，不能把Windows观测称作官方Linux 8GB cgroup等价，也不能声称wholepipeline PASS。

窄复用范围由原fullchain-v2 gate 3ebcc3…绑定：重核Lean/Python执行文件和两个小可信模块的source/ordinary terminal/olean直接hash，再把ChallengeDeps.olean（43896B，a9127a…）和CandidateSpec.olean（11184B，ccff10…）逐字复制到新trusted-lib。绝不把旧fullchain-v2/lib加入LEAN_PATH：它含旧Solution.Candidate.olean和Challenge.Candidate.olean。候选输出目录也不加入LEAN_PATH。仅新trusted-lib与原10个干净package-overlay库参与imports；只作少量禁止模块路径检查，不重哈希SDK/DLL/数学package大树。旧runtime closure 4d295c…作为来源引用，不读取其大清单或冒称当前全闭包fresh audit。root须另行明确接受此历史缓存复用边界。

单一monotonic 3200秒时钟从runner入口起覆盖小pins、fresh复制、编译、输出hash与直接输入前后复核。没有自动retry、repair、升级内存限额或任何下一批。仅用保留的本次Popen句柄停止ownchild，不按名称/枚举PID/taskkill或杀其它进程。永久单次owner marker和独占work目录均禁止自动复用。

Windows ctypes GetProcessMemoryInfo只查询ownchild，初始、每30秒及wait后记录PeakWorkingSetSize（峰驻留RSS）、PeakPagefileUsage（峰process commit）和PrivateUsage（当前private commit），每条精简stdout与memory.jsonl落盘。-M6500不是OS硬RSS限。任一已观察peak>=7*1024^3即resource_limit失败并停止ownchild；最终child0但峰值超限也不算成功。阈值检查依赖采样：短时峰值由OS peak计数保留，到下一采样才被发现；这不是硬cgroup封顶。API失败或无法取得最终peak不能记完整资源观测。

成功仅限本次compile/C-generation资源门：actual child wait返回0、三个fresh输出非空、所有直接pins前后不变、末次peak已取得且未达阈值、总时限未超。stdout/stderr原文件保留；started/child/memory/terminal收据fsync，打印terminal SHA。runner内部的parent_exit_code_to_return不是外层真实退出证明。root必须用原工具handle另存actual outer0、同clock总<=3200和打印terminalSHA一致的真实观察，才可认定本次parent退出0。terminal序列化/fsync与外层返回仍须纳入root外层时间判断；内部成功本身不能代替它。任何故障清理/失败证据收集可能超预算，但不能将失败改成成功。

gate-template.json、root-ownership-observation.template.json、root-outer-observation.template.json均是未完成模板。root开启前应静审脚本、冻结新source/runner/review/gate SHA，并确认本W9A2工作区/Lean4.33流程只有这一编译任务。准备文件只作静态审阅，未执行--help或任何导入/语法运行。后续若获授权的入口示意为：

    C:/Python312/python.exe research-goal-20261020-w9a2-v8-resource-preparation-v2/run_resource.py --gate <NEW-root-enabled-gate> --gate-sha256 <exact-new-gate-SHA256>

资源门成功不证明独立双核、官方接受或新的无条件零点纪录完成。所有旧源/收据/网页失败和方向计数保持原样。

本v2是root与formal_owner共同静审要求的两个必要窄修补，原v1保全且未执行：(1) 初次runnerSHA相符后，将runner本身加入immutable直接pins，在finish复核；(2) ownership guard仅接受no_other_W9A2_compiler_processes=true且scope精确为this W9A2 workspace/Lean4.33 pipeline only。root报告13:48:43.9201079Z的CIM只读观察有4个其它Lean进程、本workspace/Lean4.33匹配0；未来实际ownership记录应如实存otherLeanCount，不可声称全机器没有编译，也不声称机器内存隔离。不得停止用户或其它任务进程。新的ownership模板仍为false/null，需root另存新鲜实际记录。其余源码、阈值、预算、argv和cleanup不改；work仍是从未执行的v8-resource-v1，未新开supervisor或恢复路线。
