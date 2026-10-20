# 旧v6导出：有限结构审计准备

本轮只读取每份导出前5行，核对已有小收据和exporter源码。677MB/349MB文件的完整SHA只引用原真实exit0收据，本轮没有重新hash或stream。当前stat大小与旧收据相同，但不能以此冒充当前全字节身份验证。

格式是lean4export3.1.0的逐行JSON。首行meta记录Lean版本/commit和exporter/format版本。`in`为名称索引、`il`为宇宙层级索引、`ie`为去重表达式索引；表达式通过子索引形成DAG。匿名名称0、zero level0是预置项。声明记录为def/thm/opaque/axiom/quot或inductive组，含名称、type/value等根索引。依赖先递归导出；表达式按结构去重、子表达式先出。默认剥除mdata，并把let的nonDep规范成false。natVal是十进制字符串，strVal是JSON字符串。源源码和原三根+primitives argv见report/plan。

这不是全部环境导出：原argv显式选择三个公开命题和规定primitives，递归dump其依赖；unsafe默认跳过。因而不存在于该闭包的旧dead消费者、宏decoder、InfoTree、LCNF和C不会由此直接显现。

严格方案只允许solution一次顺序流读（677296932B）；challenge仅现有前5行和小收据，不做第二大文件扫描。120秒总预算、256MiB进程内存、输出≤2MiB，输入过长行/名称表/内存/时间/格式异常均停止并标不完整，不重试。完整SHA可在同一次读取中累加，不能为hash再读一遍。

可重现的默认指标只有全局记录种类/字节数、natVal位数、每个声明的type/value根索引，以及`上一个声明结束→当前声明结束`的序列segment字节、表达式数和literal体积。segment并非该声明独占proofsize：共享DAG节点可能更早输出，递归依赖声明可能先取得节点归账，inductive以一组输出。不得把它拆称type/value精确大小。

格式足以在原则上建立完整DAG并对每个根做unique-reachable遍历；但677MB的节点数未知，O(E)存表与O(所有根闭包大小之和)遍历不能静态保证在256MiB/120秒内完成。重复相加子节点的memo量是展开树成本，会重复共享节点，不能冒称DAG大小。因此本固定方案不做root-reachable精确统计，只留根索引和segment代理。

新增声明只作“已知v6本地声明/namespace匹配”或origin_unresolved标签，没有challenge全名表时不能称精确差集。旧v6导出可以定位静态序列化体积线索，不能变成v8运行profile、Lean137/OOM归因、构建阶段/时间/RSS或数学通过证据。没有实施fullstream、Lean、kernel、export、源码变更、新数值/codec/checker族或新门。
