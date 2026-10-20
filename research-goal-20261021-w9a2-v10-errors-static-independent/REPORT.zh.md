# v10 四个 kernel 内存错误的有限独审

实际stdout有且仅有4条severity=error；它们不是反例或数学不等式失败。源为1914823B/SHA86e3f46c…41e14d。本报告只读固定源、已终态stdout和小packet，没有Lean/compiler/decoder/能量/数值重放、源改写、参数族、state/Git或进程动作。

|实际行|具体声明与目标|当前直接依赖|
|---|---|---|
|13611|v10_r37_parent；walkCutR WD37 cuts 128/1，原RC(0,2,0,1,0,1,0,0)、M0→177164|两个cut的全St匹配、原split/leaf计算；父未cut numeric290|
|13793|v10_r43_e0；raw walkCut WD43 [] 107/169，v10_r43_s0→70606|原WD43/checker/该73字段状态；该子树numeric249|
|16954|Graph.edge_potential；∀u v:Fin49, Edge u v→622387738726+potential v−potential u≤5 cost u|Edge/good/badEdges、potentialValues、qCost/qGoodIncrement及整数运算|
|17030|Graph.exclusion_checked；∀u v:Fin49, ¬Edge u v→原完整bounds∧Conflict u v|Edge、witnessRows/sharedSpans、strict Conflict、upper/lower、qCell=toCl(qState)、PR索引与orientation|

前两日志明确说elaborator能归约Decidable、kernel失败于excessive memory；后两在声明kernel检查报同一内存错误。日志不指出某leaf、某大Nat或具体分配，也没有证明这是四个相互独立局部热点。尤其同一进程已保留前文环境/归约内存；较晚的普通finite decide失败仍可能反映累计状态。缺少阶段RSS/归约分配profile，不能据此断言应该继续缩cut或改变numeric阈值。后续声明继续输出不证明失败前的全部根已独立成功，也不是完整源PASS。

Graph两个目标与walk不同：它们直接闭合决定49×49对。qState是24个固定St分支（10667起），qCost是固定24项分支（10693起）；Graph这些有限decide的类型不需要Data.run/旧rc37或原whole-walk proof。exclusion_checked依赖qCell数值边界，并通过17039的edge_from_locations，将共享真实gap的闭区间严格不交矛盾转成Edge。不得把此命题弱化为仅literal表的True。

唯一建议的Graph证明组织：对每个固定i=0..48，各封一份`∀v:State, Edge (Fin.mk i ...) v → 原同一不等式`的row lemma，仍用原ordinary `decide`；exclusion同样各封一份固定u、仍∀v的原完整结论。随后两个原名定理只`intro u; fin_cases u`，49分支逐一引用对应已证明row，不再对整个∀u v目标调用decide。共98个row义务，保持每对检查与所有49状态（含good），最终只做finite cases和opaque theorem引用。单个closed计算从2401对变成最多49对；总计算、保留环境和峰RSS不保证下降。无需新checker、新table、native_decide或新数学数据；没有授权实施或运行。

精确数学边界：保持Edge、cost、potential、witnessRows/sharedSpans、qCell、strict `<`、两个原theorem的全称类型及原参数值全raw不变。不能只证明37条leaf edge而遗漏97条good相关edge，不能删两种orientation，不能把闭边界触碰当冲突。实际依赖仍为：exclusion_checked→edge_from_locations(17039)→Final.actual_summed(17864/17882)；edge_potential→actual_summed的payment(17895)→Counting.summed_of_state。该opaque证明替换不改actual_dyadic(17912)、actual_cumulative(17921)的实际Ncount/N0star函数、无条件范围或weightedKappa。所有root/cut义务仍必须在当前完整源真实通过，Graph行拆分不能补救另两个walk错误。

当前source距2MB余85177B；98份简短row+49分支组合在结构上可用此空间，但未生成、未量测或编译，不能承诺精确体积/性能。若root书面选择该单一组织变化，下一源码关须固定同cap、证明体以外raw保留、尺寸<2MB；任一row/组合失败、依赖旧whole-root/未证假设、大小超cap或实际终态再次资源拒绝即停并回顾，不自动改阈值/加cap/续开参数族。walk两处的进一步有限分块边界由formal_owner互补报告负责；本审查不另派生cut数据或方案。封存即停止。
