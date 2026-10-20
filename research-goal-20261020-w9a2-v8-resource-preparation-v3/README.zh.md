这是从冻结resource-preparation-v2复制的第三版纯文本准备包。原v2及其一次真实失败保全。本版未执行Python、AST、runner、Lean、原生工具、memory API、CIM、exporter、kernel、网络、UI或Git。所有模板默认disabled/proposal，runner_sha及新root ownership仍为null/false；root须另行审阅和冻结新enabled gate才能执行。

必要变化只有资源计量和隔离namespace及其证据：新work为tmp/w9a2-20261020/v8-resource-v2，绝不复用已失败的v8-resource-v1；gate schema改w9a2-v8-resource-gate-v2，terminal schema对应v2；metric固定PeakWorkingSetSize、commit_diagnostic_only=true。7*1024^3B停止条件仅检查ownchild PeakWorkingSetSize。PeakPagefileUsage、PagefileUsage、PrivateUsage继续如实采样、保存和展示，但不触发停止，不新设commit cap。

gate精确pin宏观011（9b12107d…）与import-memory-static-independent/files.json（c3db7c1c…），runner要求两个非缺失SHA及固定证据路径，首次核同并加入finish的immutable复核。不接收旧gate schema或缺失metric/commit诊断字段、缺失证据pin。修正依据由这些文件给出：Windows FILE_MAP_COPY整个view的commit记账不能直接等价Linux实际RAM；Lean的-M6500本身按RSS。准备者仅绑定root已冻结证据，没有新host API/探针或独立重做数学核查。

旧v1资源运行实际因预声明peak-commit阈值失败，不能翻为PASS。24个样本、child/outer1、663.234秒、RSS375066624B与commit7728263168B均继续有效；本版只提出经macro011选定的新RSS计量门，尚未获得任何新编译/资源结果。旧失败、旧prepared-v8的false/pending历史快照和所有源码保持不变。

其它执行行为保留冻结v2：fixed exact v8 source5424212b…/1829382B、单个native Lean -j1 -M6500 --tstack=262144 -DrelaxedAutoImplicit=false -DElab.async=false、fresh -o/-i/-c --json、统一3200秒、每30秒ownchild计量、final wait/最后peak、三个非空fresh产物及直接pins前后复核、无重试/repair/自动加限。当前源码同一份v8，不派生新source或改证明/数据。精确raw source diff见exact-runner-diff.json。

可信缓存边界也不变：仅重核并复制两小trusted ChallengeDeps/Spec oleans到新trusted-lib，加既有clean package-overlay；绝不导入旧Solution.Candidate或Challenge.Candidate产物，不把旧fullchain lib加入LEAN_PATH，不复核大runtime树。原runtime closure仅作来源引用，不能称当前全闭包fresh audit。single ownchild retained Popen handle的停止/cleanup逻辑不改，不按进程名或全机器PID杀其它任务。

进程ownership只针对this W9A2 workspace/Lean4.33 pipeline only，不声称全机器没有其它Lean或具有内存隔离。-M6500、OS peak计量与30秒采样均不是硬Linux cgroup约束；Windows RSS门依然不等价官网Linux 8GB cgroup。仍没有官方--setup，仍不是wholepipeline PASS。没有Comparator/default-kernel/Nano数学重放、export、网站上传或推广授权。

原parent真实退出必须由root原工具handle独立记录，内部parent_exit_code_to_return不冒充actual outer0；fsync terminalSHA及同clock总<=3200的外层观测合同保留。root-outer-observation模板改为v8-resource-v2路径和role，新ownership模板仍未填。后续若另获root授权，入口只能是本v3 run_resource.py加NEW enabled gate及其exact SHA；此说明不构成执行许可。
