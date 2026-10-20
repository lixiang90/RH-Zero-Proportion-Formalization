# v9 资源 runner 独立窄审

结论：PASS_STATIC_NARROW_DELTA，未发现本次九处差异改变资源/进程/验收逻辑的阻断。当前准备仍不是执行授权，不能称v9编译或资源通过。

新runner为22785B/SHA068691fce39ed54eb05179c1307fed7b1a68ba5ff1e9570a5c52228e21f445fa。只读全文、差异JSON/patch和禁用模板；准备清单26b1ac45fd85d454c92d41588e028c5444d32324aea30cf2d256fe0612bdd16d的九个成员当前size/SHA均相符。

独立逆投影逐byte核九个新旧span实际内容、顺序和等长性，把新span换回旧span后，与旧v3 runner实际byte array SequenceEqual=true，恢复SHA d47d98607df23d7711176116ce62fa13d85925f5c634af1175cc74ef7b3ad880（tool chunk2585d3）。九处仅涉及v8→v9身份、terminal/gate schema、draft-v9 parent与新固定work路径tmp/w9a2-20261021/v9-resource-v1；其余每个字节不变。

以下关键逻辑经全文静读且由逆投影保持：

- 固定-j1、-M6500、--tstack=262144、relaxedAutoImplicit=false、Elab.async=false，以及-R fresh source、-o/-i/-c三个fresh outputs和--json；没有新增--setup或调整内存上限。
- 从Attempt启动统一3200秒计时，预检/文件pins/编译wait/输出hash/不变检查和失败证据收集保留原deadline逻辑。7GiB stop只看PeakWorkingSetSize；commit仅诊断，不冒称Linux官网8GB cgroup等价或硬OS RSS限制。
- 新独占owner marker/work/source/output；LEAN_PATH只有新trusted-lib加历史十个clean package overlay，不含新输出目录。候选/可信缓存禁止项和两个trusted source/olean/原exit0的精确pins不变。仅复用历史信任，不进行或声称fresh完整runtime闭包审计。
- 只创建一个shell=False、CREATE_NO_WINDOW、stdin关闭的Popen；内存API使用该保留handle，kill/wait也只作用该对象，没有PID枚举、taskkill或重试。
- 成功须实际child returncode为int0、最后own-process peak成功观察、无资源超限、三个新.olean/.ilean/.c各非空、输出hash和所有remembered immutable输入pins复核、deadline检查。final memory query失败或编译异常不能升级成功。

finish中的parent_exit_code_to_return仍只是意图；terminal SHA及真实外层原handle退出必须由root另留观察。deadline终态字段按原代码在terminal写入/print前形成，不能据字段本身扩张为任何未观察的外层结束时间保证。该资源门没有执行独立export/Comparator/Nano，普通Lean编译内部的kernel typechecking也没有被禁用；成功最多是新v9 compiler/C-generation资源诊断，不是数学双核、官网或fullchain通过。

禁用模板保持allow_compiler_execution=false/proposal_only=true/runner_sha256=null；narrow历史cache reuse尚false，source review和ownership为null。未来须root另冻NEW enabled gate，精确绑定7552新源、d5cb manifest、已完成body reviews和当前300秒内W9A2独占观察。原v8失败和旧ordinary PASS均不代替新结果；宏观011/import-memory pins只说明历史RSS指标选择。

本审查没有执行/import/AST/--help runner，没有Lean/compiler、API/进程、数学/数值重放、Git/state/counter操作，没有重新读取/哈希大runtime或再次检查proof源码。源码语义与body投影使用原a8decada/1d947e89独审的既有范围；本包封存即停止。
