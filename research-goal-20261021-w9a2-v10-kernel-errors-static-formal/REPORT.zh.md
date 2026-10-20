# v10 四个 kernel 检查点的有限静态诊断

范围：读取已完成 stdout.jsonl、冻结 v10、既有 cut packet、同 pin Decide.lean 和有限归档拓扑；未执行 Lean、原 producer、WL decoder、数值模型、export 或 kernel，未改源/门/计数。方向文件与 direction-state 已读；当前主轮 counter4/review13，后续路线由 root 的宏观回顾决定。

实际整份构建据 root 原句柄为 outer1/child1、711.703 秒，不是主动中止。stdout 恰四条 error；这是失败检查点，不是四个声明的独立内存测量。没有每声明 RSS、归约计数或 live-object 证据，不能断言某个表、fuel 或叶数是内存真因，也不能将四条错误当作命题为假。其余声明无 error 不等于已得到可接受的完整 Candidate 或独立内核验收。

## 精确声明和依赖

|位置|声明及实际检查|直接下游|
|---|---|---|
|13611|`v10_r37_parent`：`U (walkCutR … WD37 v10_r37_cuts 128 1) (ofCl (RC 0 2 0 1 0 1 0 0) 0) = 177164`，`decide +kernel`|`rc37`(13613) → `run8` 的 rc37 分支(13873) → `run`(13892) 的完整根覆盖链|
|13793|`v10_r43_e0`：`U (walkCut … WD43 [] 107 169) v10_r43_s0 = 70606`，`decide +kernel`|仅 `v10_r43_c0` 的非零证明引用该等式；随后 CutsOk → `rc43`(13810) → `run8` 的 rc43 分支(13879) → `run`|
|16954|`Graph.edge_potential`：`∀ u v : Fin 49, Edge u v → 622387738726 + potential v - potential u ≤ 5*cost u`，普通 `decide`|Final 在 17895 显式应用该势不等式，支持真实状态路径的求和/望远镜链|
|17030|`Graph.exclusion_checked`：`∀ u v : Fin 49, ¬Edge u v → … ∧ Conflict u v`，普通 `decide`|`edge_from_locations`(17039–17042) 显式取此严格排除证据；Final 在17882应用实际窗口成边定理|

两个 walk error 属于 73 个新游标义务本身：51 个子 cursor、22 个 parent cursor，并非额外一轮数值检查。r37 的两个现有 cut 共覆盖347数值叶，parent 仍正常计算290；r43 的原 raw 子树有249数值叶/499节点/height23，fuel107。固定≤256的拓扑规则并不限制每叶整数/矩阵归约成本，也不限制 kernel 内存；无法从249与256的比较推导可接受性。

源码11207的 `rdw` 按32768位分块选择 packed Nat 再 shift/land；11208的 `node` 根据字低位选择 `leafStep` 或 `splitAx`；11260的 `walkCut` 以 `Nat.rec` 形成 WF，再由 `cutAt` 按位置选择正常 node 或全73字段 `stEq` 的 `kEqE`。parent额外有 `tm` 根规范化。parent的计算式使用 cut 的状态和end数据，不展开子 `Covered` 证明；这些证明仅作为 soundness/`rcOfC` 的独立前提。因此 r37 parent 错误不能简单归因为重放了两个子证明。

同 SDK Decide.lean:88–102，普通 decide 先让 elaborator 归约 instance，返回紧凑 proof 并让 kernel 再检查。105–119 的 `+kernel` 则经 `mkAuxLemma` 立即检查并缓存不透明证明常量；缓存既不替换数学检查，也不限制计算峰值。前两个实际消息明确说 elaborator 能归约但 kernel 内存失败；后两个消息仅说 kernel 内存失败，未提供每阶段消耗。Graph两个检查覆盖49×49个有序对，分别读取 Edge/potential/cost 或 witnessRows/sharedSpans/qCell/方向/strict Conflict，和游标拓扑检查是不同归约形状。它们也可能受同进程先前保留状态影响；没有独立测量不能排除这一点。

## 固定拓扑组合的正、负证据

立即两子树不是可信的收益保证：

* r37 root1，axis1/cut318400/mode1；子 pos9/end177008/fuel127 有636数值叶、1317节点、height83；子pos177008/end177164/fuel127只有1数值叶。保留原cuts后重子仍残余289。把这个636+1机械拆开，未证实足以降低峰值。
* r43失败子pos169，axis5/cut112287/mode0；子pos177/end70388/fuel106有248数值叶、497节点、height22；子pos70388/end70606/fuel106只有1数值叶。248+1同样是明确的不平衡负例。

一个已取得精确局部证据的 r37 组合点：原cut620的直接父为pos612/depth31/fuel97/end92097，axis7/cut82336/mode0；子620/end79718原cut覆盖256叶，另一子79718/end92097有43叶。该祖先共299叶/615节点/height53，其 normalized M0 state SHA为 `98b96ae6a543ff2bff8df39d1c004513d42c6232ec4e89eb52a47d6ad8f5dfb9`。可用包含原cut620的 cut-aware raw walkCut 证明祖先 Covered，只计算43残余；再以祖先hint替换620，保留另一原cut110366，根残余从290降到247。这是一次确定的证明组合，未改变任何叶数阈值、检查器或数值数据；247接近另一失败249，故不承诺资源成功。

root要求的“一次提升两个原cut各自直接父”是可审候选，但本次尚未读取第二cut110366的直接父、状态、end和增量，不推测最终残余或两祖先是否重叠。两cut LCA同样未定位。r43的下一固定候选是沿失败子树的重侧链，跳过1叶分支，取第一个两侧数值叶均>1的分叉；已经知道下一重侧pos177，其直接子位置185与53837，但这两子的数值数、状态/fuel/end以及是否满足规则尚未读取。遵 root 最新停止指令，不追加查询；这些字段保持 unknown，不据此生成源或门。

## 一个受限的后续证明路线及精确边界

建议只在宏观回顾选定后进行定点 compositional Covered 修复：r37采用上述已知祖先提升（或由后续一次明确授权元数据核实的双直接父），r43在固定“第一个真正分叉”两子证明后，以这些子 Covered 构造 CutsOk，用 cut-aware raw walkCut 证明原 `v10_r43_s0` 的 Covered。沿用 `walkCut_ok`/`cutsOk_cons`，不新增 checker、不改图/阈值/精度、不跑 cut-size 参数族。

关键范围：cut-aware游标等式不能直接充当旧 `v10_r43_e0` 的 raw `walkCut []` 等式。若只需要原 `v10_r43_c0 : Covered (toCl v10_r43_s0)`，应在新版本删除未再需要的失败内部 e0，直接用新 Covered 组合替换 c0 的证明；现有源码中 e0 唯一使用点是 c0。c0 的类型、根43的cut状态/end和原根结论可全部保持。若坚持保留原raw e0的等式，则还需真正的 cursor-composition等式证明；当前Covered接口并未提供它，不能以覆盖性偷换等式。

root封存时最新的暂定下一选择：每个实际失败walk只选一个 proper descendant，r37按排除现有两cut后的残余质量接近290的一半、r43按249的一半，平手取最早pos。此处仅确认组合接口可行，不已知选择结果、状态、游标或资源收益。`CutsOk`只要求每个元组有Covered，没有不相交前提；可先用旧cuts证明新祖先/子树Covered，再以`newhint :: oldcuts`和`cutsOk_cons`组合。`cutAt`在新祖先命中即跳过其子树，未命中处仍可用旧hint；重叠不会造成证明循环，因为新hint的Covered证明只依赖旧CutsOk，不依赖新root。该逻辑可行性不替代新提示状态和游标的真实kernel检查，也不授权执行元数据或证明。

Graph的另两个失败不由这项 walk 修复解决。独立代理另给固定49个 opaque u-row lemma后 `fin_cases u` 组合的提案，每行保留∀v/严格Conflict和原数据，详见 `research-goal-20261021-w9a2-v10-errors-static-independent/files.json`。该提案保命题，但当前未实施、未证明资源收益。本报告不另造Graph方案。

任何后续 gate 都必须得到新 proof 的真实 kernel/outer 成功并保完整单文件/双核/官网目标。不得直接把含错误占位的整份失败 Candidate 当作可信缓存，更不能把无 error 的后续声明或这个静态报告当作最终通过。此处到此停止，0新源码、0Lean/数值/内核执行。
