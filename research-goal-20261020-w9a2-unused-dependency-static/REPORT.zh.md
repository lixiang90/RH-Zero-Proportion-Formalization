# a517 源级依赖与重复工作静审

本包只诊断新发生的官网 build timeout。未改 a517、未创建裁剪后的 Lean 源，未运行 Lean、编译器、exporter、kernel、solver 或数学扫描，未修改主轮计数。源级检查之后，仅对既有 `solution.ndjson` 做了一次 Name/声明记录读取；没有求值表达式，流式 SHA 与冻结 1cc0f929…/677296932B 相同。

优先可做的最小变化是删除全部15条独立 `#print axioms`，与 formal_owner 提出的8个显式 noncomputable modifier 分开核对其语义。15条打印命令在原 flat 行17061–17065、17185–17191、17231–17233，共922B（12内部780B、3公开142B）。只删除打印后源码应为1,829,130B；若再仅加8次 ASCII `noncomputable `，增加112B，预测为1,829,242B。本包没有生成这一新源。

这15条均为独立 diagnostic command，flat没有 `#guard_msgs`、`#eval`、`#check` 或 `#reduce` 来消费其消息。SDK `Lean/Elab/Print.lean`240–250只调用 `collectAxioms` 后 `logInfo`。`Lean/Util/CollectAxioms.lean`24–25的runM从空State开始，149–154每次重新runM；其114–118明确说明当前模块elaboration会走声明body，仅imported声明有预计算扩展缓存，beforeExport则另用一次shared State。故多个本文件root的诊断会重复遍历共享的本文件证明依赖，而非复用模块化开发时的import缓存。此处没有逐命令计时，不能把官网3200秒都归给它，也没有可证明的秒数收益下界。

源内打印不是官网数学合同的一部分。已有固定官方 `CONTRIBUTING.md` 的 Acceptance 条目要求精确三定理、exported transitive axiom集和两内核接受，没有要求 `#print`。pinned Comparator `Main.lean` 的 `safeLakeBuild`只等待 `lake build`退出；`compareIt`随后直接export，`verifyMatch`直接运行 `Comparator.compareAt`、`Comparator.checkAxioms`与两内核，不解析源内axiom打印。因此删除全部15条保留所有定义、证明、数据、namespace、option和归属通知时，静态数学与官网合同保持。旧本地collector若依赖这些打印日志，必须由新的明确gate改变收集合同；不能把“没有打印”当作检查公理失败，也不能取消实际export的公理检查。新源SHA及wire digest须另绑定，旧a517记录不升级。

另有一个闭合的旧消费者删除候选集合，共19条、词法跨度合20,010B：

- 旧floor外壳：`PCell.root_cover`、`PC9QB6M.quant_forget/cert_of`、`PC9QB6MData.cert`、`PC9QB6M_half/PC9QB6M_cert_full`、`RiemannFail.cert_AM`，7条6,881B。
- 旧全域floor transfer：`OpethN.remainder_bound_n/block_remainder_bound_n/matching_defect_bound_n`、`OpethN.ActualDefect`三条结论、`Opeth.AMFinal.actual_dyadic/actual_cumulative`，8条12,081B。
- `Localization.base_floor`，159B；没有被新 `located_state` 调用。
- 未用的旧DAG消费者 `Localization.dagThreshold/dag_cost_of_late/low_DAG_state`，3条889B。

`source-def-use.json`列出每条在原flat中的精确行、byte offset/跨度和入边。3516个源声明的词法检查中，这19条的可解析入边都来自该集合内部，未留下外部入边或未解析的候选leaf token。它不是Lean elaborator；跨度包含下一条命令前的trivia，不能直接用来删许可证或文档。若采用此方向，必须逐声明删除并保留scope/options/attributes及全部第三方通知。该集合是可选后续裁剪；Root当前倾向的最小v7不必把它与打印/noncomputable改动同时合入。

现有root export共有74,978个声明。上述19条都没有出现在三公开root所需的导出声明闭包中。这支持“旧消费者不是新根的kernel依赖”，也意味着删除它们不会减少这份既有export中已经没有它们的kernel replay负担；可能节省的只是普通源elaboration/检查和相关序列化活动，收益尚未测量。源码字节数不等于时间占比。

不能误删真正的大证书。`PC9QB6M.Covered`现在就是 `CovBy 8 PR QuantGoal`，48个 `rc0`…`rc47` 各有一次 `decide +kernel`源调用证明增强量化覆盖，新 `Localization.root_QuantGoal`直接复用 `PC9QB6MData.run`。这里的一次是源调用计数，不是对tactic/elaborator/kernel内部实际归约次数的测量。现有export中的 `Covered/QuantGoal/walk/walkC/run/run8`及48个rc全都在；没有证据说同一11,794叶checker在源内被旧版与新版整轮重复计算。旧global-floor外壳是消费这些已命名证明常量，不是第二份全walk证明。`PC9QB6M_G_rev`、`RiemannFail.W9/Fw_W9/W9_adm/W9_B`、`OpethN.band_close_n/pressure_le_n`、`OpethN.Counting.ActualDefectEstimate/defect_to_dyadic`都必须保留，它们邻近旧消费者且确实在root export中。

formal_owner另已静读同版SDK确认 `decide` 有type-index auxlemma cache：旧 `Data.cert`匿名hcov与新Localization具名同type检查可能已经命中，因此不能把两处文本算成必然双倍归约。其8个codegen marker建议及边界在 `research-goal-20261020-w9a2-static-build-cost-formal/files.json` c42347e3…，本报告不重复该检查或声称有时间实测。

官网日志只支持停在 `Building Solution.Candidate`、最终bash124，未到solution export/kernel；最后出现的cached Replayed warning不证明那个依赖耗时。上述诊断均不构成“3200已能通过”、新证明通过或全目标完成。
