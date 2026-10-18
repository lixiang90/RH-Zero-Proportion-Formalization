# P：完整剩余 pooled component + 固定曲率关（仅准备）

本包只完成源码、AST、既存元数据与文件/runtime 身份准备。没有执行旧数学恢复、FS 解码、新 case/矩阵、曲率、点值、LP、Laplace 或 Lean。最终独立执行 gate 由 root 另定；prepared manifest 不构成执行授权。

## 固定域与不变量

使用原 H 升序 15,378 个原 G-index，`((i*1187+j)*4+chart)`，四 chart 顺序 id/id、id/rev、rev/id、rev/rev。source/kernel/ledger/c/sep 与 N/N2 一致；candidate 分子仍为 893766123055294719、分母 10^20，sep=17/20。原 source、原 FS/anchor、same-S native pruning、`highs-ds` 和全部 options、固定 normalized support/RREF、raw checker 均从冻结 N 原件导入。没有新阈值、精度、support、solver、相位或锚点规则。

模型仍是 68 原 term 共享相同物理跨度后的 42 个 epigraph；51 个自由变量、full52 平衡。完整155条几何约束、所有原 component rows 均保留。native结果只是发现提示，必须先 durable 保存，再由原 exact reconstruction + raw checker 判定。原 source/FS组件 cache 保留 state/witness/term hash 并同冻结 J cache 对照，不把重启后的 process caches 说成原运行 hint 轨迹续接。

## 首先恢复 N + N2 的 2,375 条

执行时检查所有冻结文件与 runtime 身份；逐原 gzip complete-member 核 canonical JSON、offset/length/压缩与解压 hash、全 EOF。旧 N 的676个完整原case、675条call-intent/native，以及N2的1,699条call-intent/native全部绑定；原调用总数2,374，index全唯一。N2全部2,375条commit须逐行原ordinal/index/前链hash/累计counts/调用数/index hash与proof ref一致，尾部streams长度/hash一致。

每个原数值case从同原FS重建同一model SHA，核原intent/native row映射，再用冻结raw checker重查Lower/Below；有primal时另查全部原行与两窗原M0 floor。原M2417保留已独审数学deduction。原首Below1322606必须同原pair278/665 rev/id、原raw μ、cost和O packet一致，才由已冻结O独审依赖转为`curvature_Lower`。不重新求该pair曲率或LP。原675发布/676durable的历史叙述不改写；P是新已检查恢复前缀。

旧2,374个LP index加入禁止再调用集合；剩余13,003个原index包含J5331088 deduction，因此最多新13,002次LP、累计最多15,376次；各新case至多一次原HiGHS调用，无auxiliary/retry。原N、N2、O文件保持不变。

## 唯一新数学分支：将固定 O 规则用于原 Below

原pooled exactLower直接记`Lower`。仅当同一原reconstruction给出exactBelow，且给定raw dual经原full52/非负/cost重核有效时，才进入固定曲率分支。没有valid原dual则停止为unresolved，不能换一组dual。

`fixed_curvature.py`只泛化O固定305行的包装：从冻结model的原68terms提取正质量anchor、原q/L0/guard/物理跨度，每个物理跨度取全部原member直接bounds交集并加入真实sep长度下界；明确重核chart/span映射。它不调用新FS选择器。CellA和两种付款算法直接使用原O冻结代码。

区间仍是`hull(original q, original-member-bound intersection + sep)`；按O相同规则取第一个完整覆盖的原REG chain及所有闭区间相交的原单元。没有覆盖则该行m=0，不能细分或补anchor。原REG共有266个单元。23个O已独审值按原packet seed直接复用、不重复算；其余每个(L,U)最多计算一次并立即durable保存，整个缓存最多266个已存在单元。没有新kernel/point采样。

正raw锚行权重固定为`c_r = mu_raw * kappa * m_r / 2`，物理位置/原q尺度；不再乘外部a或FS质量。执行相同group variance/clamp与至多一次exact component-gauge Laplace（同O的退化分量/gauge规则），付款取两者max。只比较`raw dual cost + uniform payment >= target`，不把primal deficit当付款要求。full10 stationarity、非负权及原guard/hull均需保存；p*不是新核anchor或能量点。

## 明确停止条件

1. 任意输入/source/runtime/历史raw guard或hash、重复LP、原模型/参数身份失败：保存failure，停止，不修复重跑。
2. 新case无exactLower且无合格exactBelow+有效原dual：保存完整native/exact失败原因与unresolved commit，立即停止。
3. 固定曲率尝试付款不足：保存全部row/cell/variance/network证据，记unresolved并立即停止；不换dual/anchor/interval/support/预算。
4. 任何软资源限到达：保存inconclusive；硬限由sole-child wrapper终止。只有此前完整LF且stream refs有效的commit前缀可接受，未访问suffix不填分类。
5. 只有完整15,378 EOF、无unresolved、全部依赖/付款检查通过才可报`all_range_conditional_Lower_candidate`。这仍不是全域Lean、无条件纪录、网站source/runtime接受或独立全范围审查已完成。

## durability、证据与资源

沿用N2 append-only/fsync链，不调用`os.replace`。每次原组件/native/CellA/curvature/proof/selector gzip member先fsync，再追加canonical commit并fsync；LP intent必须在调用前fsync。新CellA查询也先写独立fsync intent；新exact Below候选在任何曲率工作前先durable。各member保留相对路径、offset/长度与双hash，原始native完整保留。异常后尾部不删；没有自动续跑入口。root gate指定soft/hard时间和closed-output，wrapper只启动一个child并只终止自己的PID。

不作新benchmark。旧N2真实1,699新调用约202秒和单O约14秒含输入/导入成本；它们不证明本剩余完整运行能在某时间/内存/输出预算内完成。Below发生比例、网络分母增长和总源码/runtime未知，不能外推。曲率仅对Below尝试，Lower无需逐case求Laplace。

## M/J source交付接口

当前producer仍可使用已独审M/J数学deduction依赖，不能因此声称最终不需旧大展开源码。`deduction_transfer.py`提供定义-only的后续exact接口，未调用/测试：

- M原同row顺序与μ保持不变，仅将68T坐标映射到42T，再重查full52/非负/cost。
- J给定原raw geometry μ，按每原term的`2*a*(lc,l1,l2)/1024`将原FS展开到constant/positive anchors，再同样重查full52/cost。

准确从旧compact J提取原raw geometry μ的loader、薄Lean消费者与其source预算仍pending。此处不新LP或换FS，也不为了填该接口阻塞主恢复/停止合同。

## source-selector库存接口

每个已闭合case另存selector member：index、closure种类、42base IDs、normalized unknown IDs、curvature正anchor IDs、原REG(chain,ordinal)。deduction保存明确依赖。原μ/m/p*和分母仍保存在完整proof/curvature member，selector不包含其数值。

`selector_inventory.py`只提供未来terminal之后、另获字节处理授权的确定格式UTF-8 Lean数据文字导出接口，不在producer自动调用。导出会核commit链/member hash并精确计数据文字字节；它不实现Lean重建器、generic proof、原source合并、kernel/runtime或网站接受。因此selector文件小不代表最终source gate已过；raw μ/m/p*分母须由尚待实现的重建器恢复并kernel检查。此次不读取/统计其他N2支持模板，执行阶段才按完整原范围处理。

## CLI与gate

准备：`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageP-complete-curvature-preparation/prepare_freeze.py`（仅AST/hash/既存元数据）。

未来执行模板：`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageP-complete-curvature-preparation/run_once.py --launch-authorized-complete-curvature-P --gate <ROOT_GATE_PATH> --gate-sha256 <ROOT_GATE_SHA256>`。必须另有root不可变gate；本SPEC不授予执行权。
