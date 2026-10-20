# 同 pin InfoTree 关闭方式的有限静态结论

结论：没有建立一个安全的、只靠现成全文件源码指令关闭后续 InfoTree 收集的方案。公开 API 确实存在，Command 层的 flag 也会跨命令保留；但裸关闭会遇到 frontend 对非空根树的具体假设，不能作为安全候选。按 root 最新指令停止裸 InfoTree=false 路线，不寻找新 hook/wrapper 族，不执行 tiny smoke。

本报告只读固定 v4.33.0-rc2 / d8b189 SDK 源及已保存的官方合同/比较器源码。没有写入 Lean 源、候选或 generator，没有运行 Lean、compiler、版本命令、AST、探针、进程查询、网络或数学检查。没有修改 resource 限制、旧失败、冻结字节或 counter。本任务不据 `interpreter` 标签推断某个声明或 InfoTree 的内存占比。

## 精确 API、类型与作用域

`Lean/Elab/InfoTree/Main.lean:408–409` 定义公开的 `Lean.Elab.enableInfoTree`：具有 `MonadInfoTree m` 实例时，接收 `Bool`（默认 true），返回 `m Unit`；实现只将 `InfoState.enabled` 改为给定 flag。`InfoTree/Types.lean:313–329` 明确该字段控制是否记录树，另有 trees、assignment、lazyAssignment；它不是 `Options` 的注册用户选项。

仅作为精确语法记录，未写入或执行的直接调用为 `run_cmd Lean.Elab.enableInfoTree false`。`BuiltinEvalCommand.lean:274–280` 把 run_cmd 的预期类型固定为 `CommandElabM Unit`；`Command.lean:122–124` 为该 monad 提供 InfoTree 状态实例。`CommandElabM` 是 Context reader、Command.State ref 与 EIO 的 monad（62）；该 API 调用本身只改 infoState，没有调用 addDecl、setEnv、modifyEnv 或改变 kernel 的信任/检查设置。

run_cmd 的求值动作生成阶段在 `BuiltinEvalCommand.lean:230–247` 使用 `withoutModifyingEnv` 避免留下临时求值辅助声明，然后执行 CommandElabM 动作。这里陈述内建实现，不等于已验证该调用可安全用于整个候选。

作用域的关键区别是：

- `Language/Lean.lean:522–539` 在 header 处理结束后初始化 `enabled := true`，不是在每条后续命令开始时无条件恢复 true。
- `Command.elabCommandTopLevel:642–643` 每条命令重置 messages 和树，但显式保留原 `enabled`；`Language/Lean.lean:749–751,772–787` 把实际完整 Command.State 传给下一命令。故 Command 层 false 可以持续到后续命令。
- infoState 属于 Command.State（29），不属于 section/namespace 的 Scope；Scope 仅管理 opts、namespace 等（`Command/Scope.lean:15–23`）。`end` 并不按普通 option 作用域自动恢复这个 flag。新的文件/header 处理才会重新初始化；第三方命令显式调用 API 的行为不在“永远 false”的保证内。
- `run_elab` 预期的是 TermElabM（`BuiltinEvalCommand:282–288`）。`Command.runCore:197,204–216` 将 Command flag 复制到 Core 状态，但回传 trees 等而不回传 enabled；因此不能把 Term/Core 层关闭当作同一个跨命令开关。

## 裸关闭的具体静态障碍

`InfoTree/Main.lean:222–228,283–313` 在 enabled=false 时不增加叶或根 context tree；`InfoState.substituteLazy` 只在已有 trees 上作映射，不会补空根（`InfoTree/Basic.lean:88–92`）。普通后续命令开始时又会清空树。

但 `Language/Lean.lean:697–698` 的命令结果报告路径无条件读取 `infoSt.trees[0]!`。当下一普通命令没有产生树时，这会落入空容器的 getElem! 路径。`PersistentArray.lean:71–79` 最终使用数组的强制索引，`Init/GetElem.lean:103–108` 明确越界会触发 panic，而不是一个正常的“没有 InfoTree”分支。已保存的固定 Comparator `Main.lean:128–129` 又显式给构建子进程设置 `LEAN_ABORT_ON_PANIC=1`。本任务没有执行测试来观察具体退出，但这个可达性障碍足以否定“裸 false 是安全的全文件关闭指令”。不能以可能返回 default 的 panic 行为作为成功方案。

`withEnableInfoTree false action` 是现成的局部 API（`InfoTree/Main.lean:411–417`）：保存 flag，在给定 action 中临时关闭，finally 恢复。它的类型还需要 Monad 与 MonadFinally。它不等于关闭所有后续命令的用户指令。将其接入每条命令需要另一个设计及审查；root 已明确不展开新 wrapper/hook 族，本报告不提供或生成该族，也不承诺任意依赖 InfoTree 的元程序行为或辅助声明完全不变。

## snapshots、-i 与实际可减内容

`internal.cmdlineSnapshots` 是注册 option（`CoreM.lean:55–60`），API 默认 false；普通 CLI frontend 在无完整增量保存时通过 setIfNotSet 默认设为 true（`Frontend.lean:288–290`）。它已用于减少所保存的 command-state metadata：`Language/Lean.lean:686–694` 最小化 reportedCmdState，763 关闭 command incrementality bundle。将它再设 true 不能据此声称新的收益；设 false 会保留更多这类 metadata，不是关闭 InfoTree。

该最小化也没有删除独立的 infoTree snapshot：`Language/Lean.lean:697–713` 仍完成并保存命令树。`trace.Elab.info` 只在 701–709 控制格式化/打印，不控制树的构建。

`-i` 不是开始启用 InfoTree 的开关。`Frontend.lean:387–398` 仅在请求 ilean 时，额外遍历 snapshot 中的树、求 module references 并写 JSON；409–410 刻意不在临近退出时释放 snapshot 图。即使不带 -i，frontend 的命令树构建路径也已存在。源码支持“这里可能保留诊断数据”的定性描述，没有本次 InfoTree bytes、heap profile 或节省量证据，也不能据此解释 93095 的 interpreter memory_exception。

## 合同边界

已保存的官方 CONTRIBUTING 允许单文件 helper declarations，并明确 Lean elaboration 会执行贡献者元程序；direct-submission/schema 与 prepare-candidate 只在所读表面约束字段、UTF8 源大小/路径等，未见对 InfoTree 或 run_cmd 的专门文本禁令。这是对已保存 primary 的有限核对，不是当前部署的额外许可或绕过检查授权。

即使诊断开关没有文本禁令，也必须保持三条声明、完整证明、许可、导出公理审计、Lean 与 nanoda 独立验证；不能通过修改环境、信任级别、proof body、数据或 kernel 检查来换资源。本次有限结论不选择新源、不禁用任何检查，不将现有 soft6500 失败改为 PASS，也不认为它已经等价证明官网 8GB/3200 会失败或会成功。后续路线由 root 书面 review 决定。
