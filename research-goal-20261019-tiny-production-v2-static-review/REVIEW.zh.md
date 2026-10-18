# Native fullcold v2：独立静态审查

审查对象是 prepared `f2ab9d281bf39769da08280f40d9369e9b9ffc2f51c57acccbb116999daa9d74`
的全runner、v1→v2差异、configuration、helper、冻结脚本、gate模板和README。
只读/AST/哈希核对，没有import或调用这些producer，没有执行generator、Lean、原生
工具、export、Comparator、nanoda、数学或网络。没有修改任何被审输入。

**结论：本次静读未发现确定的范围削弱或执行路径错误。** 这是源级审查，不保证运行
成功、资源余量、动态安装闭包或最终官网接受，也不产生执行授权。

1. Attempt在所有pin检查和唯一generation之前建立monotonic t0/deadline=t0+3200。
   各child wait使用当前remaining；哈希流每块检查remaining。末端immutable/hash、
   verification、deadline、mirror terminal均fsync并在写后检查remaining。中间的
   verification单独存在不构成成功：必须exit0、三份回执完整且没有failure。
   TERM/KILL清理宽限只记录为失败后的清理，不当作额外证明预算。
2. generation只有一次，通过固定Windows helper在本进程runpy执行冻结v4 generator，
   helper独占PID文件，便于超时仅清理其进程树。旧v3和旧失败包不覆盖；新的draft/
   overlay/lib/mirror须不存在。没有resume、修源或第二次候选编译入口。
3. 全新source allowlist恰ChallengeDeps、CandidateSpec、Challenge.Candidate和完整
   Solution.Candidate，空lib按此顺序全冷编。fresh CandidateSpec取官方模板、已钉
   ledger exactExpression和固定p/q；不修改旧installed trusted常数。
4. LEAN_PATH只有fresh lib和runtime固定package cache；普通阶段和native导出均没有
   用户Dev/prefix或旧ChallengeDeps overlay。package中四种同名trusted/user输出还
   显式拒绝；外部Zeta缓存source/olean按固定receipt逐SHA绑定。原生工具的安装工程
   oleans没有加到proof search path。
5. 动态gate必须绑定root确认terminal0的native安装及prepared SHA。入口还核passed、
   proof_runs=0、无failure、Linux/mirror回执同hash、源/SDK/C闭包状态。九源provenance
   对照锁定归档和原CoreAudit；11个source/config路径、两个ELF、运行时closure的bytes/
   hash和symlink目标均绑定并在后续immutable复核。这里的source→ELF构建因果关系和
   closure完整性依赖已成功且root核验的安装receipt；本proof只重核其实际运行文件，
   不重建安装、不把安装状态当候选proof结果。root报告的86532成功安装不是本审查的
   运行结果；实际执行仍由未来gate指定其精确identity。
6. 原生lean4export的锁定Main确实先initSearchPath(findSysroot)，然后importModules
   CLI给出的module。runner设LEAN_SYSROOT为同SDK、LEAN_PATH以fresh lib优先，调用
   binary `module -- threeRoots primitives`，与Main的参数划分相符；没有把lean --run
   专用参数传原生CLI。supportInterpreter=true的安装配置与动态fresh导入目标一致。
7. 两次导出保持原三个官方roots和完整primitive列表。原CoreAudit源码不变：相同
   compareAt、allowed roots/transitive axioms和env.replay，成功日志三条件必须齐。
   原生执行方式替代解释器，不移除证明、声明、primitive或默认kernel重放。
8. nanoda显式num_threads=0；已锁定源码的≤1分支逐全部声明串行检查。公理白名单三项、
   unsafe=false和unpermitted hard-error均保持。完整Checked行、exit0和observed axioms
   子集都必需，读取同一个已绑定solution export。没有依赖多线程诊断时间冒充串行。
9. 文件限制为RLIMIT_FSIZE=8*1024³ bytes，不声称RAM上限；每阶段time-v记录RSS、
   输出字节与hash，最终记录disk和peak-stage RSS。没有性能保证或官网环境等价保证。

未增加新关：原合同本来要求的成功安装身份、fresh gate、sole owner、全流程真实
terminal/完整回执及官方验收仍须实际满足。本报告只确认当前代码按这些原条件组织，
没有启动任何验证或要求重跑已冻结数学。
