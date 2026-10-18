# nanoda 线程数：锁定源码的静态审查

只读源码分析，未运行 nanoda、benchmark、Lean、export、网络或编译；未改任何配置。锁定 nanoda commit 为418320295890faed83a96fd97907b12a3b6728c2，锁定 Comparator commit 为273294467ce06429e6667ece7f5699f8678c9f4e。

`nanoda/src/util.rs:874–876` 中 num_threads 是 `#[serde(default)] usize`，未设置时默认0。`src/tc.rs:114–151` 在值>1时创建指定数量的 scoped workers，以 AtomicUsize.fetch_add(1) 分发完整 declars 容器的每个索引；所有 worker 都 join，任一 panic 会使检查失败。值≤1时主线程逐项检查全部声明。`src/main.rs:33–46` 只有 check_all_declars 返回后才报告完整 Checked declarations with no errors。

因此增加 num_threads 不删证明、不跳声明、不放宽公理白名单：只改变独立声明的调度。permitted_axioms、unpermitted_axiom_hard_error=true、unsafe_permit_all_axioms=false 必须全部保持。若 root 选择更多线程，仍须完整exit0、完整Checked计数和相同export SHA；不能仅把线程数增加当作PASS。

吞吐提升存在边界：按声明而非按一个声明内部并行；串行读取/解析并未由此变并行，一个极慢声明可能限制总时长。每个 worker 有独立 TypeChecker cache；`src/lib.rs:25` 的线程栈为16,777,216字节，多线程可能增加内存与争用。在未测定实际可用CPU/affinity/cgroup配额前，不能按宿主显示的逻辑核数承诺提速。本审查未读取或测定这些硬件数；root另行检查。

**官网锁定路径的关键区别：** `Comparator/Main.lean:153–166` 的 runNanoda 生成JSON仅写 use_stdin、permitted_axioms、unpermitted_axiom_hard_error、nat_extension、string_extension，未写 num_threads；nanoda默认0随后走串行。捕获的官方 contract 只锁上述commit及公理集合，没有单独num_threads字段。因此该锁定代码不是4线程官方政策，而是缺省串行。网站实际部署若有额外patch/包装，需以其官方可信证据重新核验，不能推定存在。

当前本地 production-v0 明确选择 num_threads=4；这保持了数学重放完整性，却不是锁定官方Comparator生成的相同配置。增加本地线程虽可合法用于完整的独立内核审阅，但不能借其耗时宣称官网相同运行约束已过。建议新入口暂不凭硬件猜测上调线程：记录local与official配置边界，先由root结合实际官网部署和CPU证据决定。若追求锁定官方路径的严格时间复现，应明确用缺省/1线程，而不能默许4或更多线程充作官方时间证明。

旧cold实际未完成nanoda，约352.100秒被统一3200秒deadline终止。没有完整Checked行，不能由该失败推算剩余耗时或预测新线程数必能完成；更不能仅修改计时口径、放宽公理或少导入声明。
