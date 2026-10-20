# 固定SDK：内建profiling能提供什么

本报告只读既有同pin Lean 4.33.0-rc2（d8b189…）SDK小文件。没有运行Lean、版本、profile、API、进程查询、compiler、kernel、export或网络；没有生成新proof/source/runner/gate，未改计数或Git。旧19消费者路线、bare InfoTree关闭和cmdlineSnapshots=false均停止；未重新生成这些方向的审计。

现成的文档化低结构开销入口是 **`--profile`**：Shell.lean178的help明确为每个definition/theorem显示elaboration/type checking耗时；405–406仅设置`profiler=true`。`Lean/Util/Profile.lean16–25`登记`profiler`（默认false）和`profiler.threshold`（默认100ms）。36–50的接口通过native `lean_profileit`打印并累计act运行时间；53–56的累计显示接口明确输出到stderr。这条路径与`trace.profiler`的结构化trace系统不同。若将来有独立书面授权，`--profile`和可选的`-Dprofiler.threshold=0`只可作为完成阶段耗时诊断选项；本报告不授权执行，也不保证输出量、资源收益或故障定位。

这个开关**不能据SDK文档宣称“声明开始即stream current-name”**。它报告耗时，只有动作结束才知道耗时；本机已读SDK只有native extern接口，没有本轮可核的time_task实现。异常终止是否刷新最后记录、每个输出记录是否带当前source声明名均不能从现有Lean接口保证。即使最后已完成项可见，也只支持最后完成项的时间/类别，不能把它当作实际失败声明或内存归属。现有InfoTree/snapshot保留仍在，profiler不是内存削减修复；原生计数器自己的额外开销也未测。

**不选`trace.Elab.command`来解决这一目标。** Command.lean464注册该trace；489–505在命令外层`withTraceNode`中以完整`stx`作为消息，489附近的finally才`addTraceAsMessages`。Util/Trace.lean约289–338明确：消息在action完成之后构造，先保留trace状态再addTraceNode；后续约449–473将trace转成MessageData。Language/Basic.lean441–452只对snapshot树按preorder逐步报告已产生的消息。它不是开始时即时、只有一个声明名的可靠流；开启后还可能保留/格式化巨大的命令syntax。

更窄的`trace.Elab.definition.header`（MutualDef252）与`.value`（531）消息只给名字，但仍是同一个完成后trace机制，不能保证正在进行的body在fatal前可见。`.definition.body`（PreDefinition/Main293）会打印type/value，尤其不适用于本次避免巨proof metadata的目的。`trace.profiler`、`.output`与`.serve`也不选：Trace175–214为nested trace，output/serve明确要求保留数据，Frontend400–412从snapshot traceStates导出/服务；并非无保留的进度日志。

**cmdlineSnapshots负结论仅确认，不重开。** Language/Lean648–652在true时清stx/parserState；686–689在true时把历史reported state压成仅env；763在true时不给current command incremental snapshot。false会保留更多状态。它按每命令scope opts读取，因此源设置会影响后续命令，仍不关闭当前InfoTree，也不构成降峰方案。此方向已被宏观010停止，本报告不提出修改。

**decide没有现成安全减内存开关可由此推荐。** Decide75–118的`+kernel`已用mkAuxLemma：AuxLemma43–78以type/privacy/defeq缓存name与levels，checked lemma本来就入env；普通decide还会先Meta whnf再由kernel复算。不能凭去掉`+kernel`就声称更少内存，更不能替换为native验证。此处不设计新的证明切分或更改任何48根。

结论：可确认`--profile`是内建完成阶段耗时诊断；未找到能保证“声明开始时只stream当前名、且不保留巨trace”的已有开关。没有一个已证明的最小源码内存修复可从本次lookup推出。若选择profile诊断，必须由root先书面选择具体路线并重新界定人类“不重复核查”的授权；本报告不生成或启动该门。
