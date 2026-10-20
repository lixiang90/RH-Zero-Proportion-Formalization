# rc10 既有检查器证明分解：准备范围

v9 全部显式普通定义的代码生成入口削减后，固定 -M6500/3200 秒资源构建仍真实失败（terminal6e222b92…e579、outer1、583.671秒、Lean memory_exception）。它不能证明具体失败声明，但使继续盲加 noncomputable 失去依据。停止该族，不增资源、不原样重投。

当前宏观013后第2实际研究轮，只选择一个现有检查器的证明组织问题：rc10 的完整 Covered(强化 QuantGoal) 能否由较小子树的 Covered 和既有 CutsOk/rcOfC 组合。W9A2 旧归档 root10 有906数值叶，end270277；e 是游标而不是步数。旧版70切点对应另一份源和不同WL/几何，禁止直接移植。

先从固定 W9A2 walk-events 归档取 rc10 的位置、轴、切值与结束游标，用现有相同整数几何公式派生根及两个直接子状态，核对已有 state SHA。此操作不读取/解码WL，不重算能量或切线余量，不重新运行原证书检查，只产出未信任提示。M=0、73字段顺序及实际 Lean 状态相等仍须新证明核对。上限30秒、2MB输出，一次执行，不自动重试。

准备一份小的新增 Lean proof pilot 是下一候选关，尚未授权编译。它若被选，必须只使用现有原检查器和当前强化的 Covered，以两个子游标的 decide +kernel、CutsOk_cons 和父 rcOfC 真正组合回同一 rc10；不能通过引用旧rc10成证明，也不能删除原数值检查或引入native_decide。先核对子树大小与字节预算；若极端不平衡、总新增超过8192B或最终单文件超过2MB，停止当前two-child实现选择并另写明确范围。缓存Core只允许开发新引理，不可冒充新单文件资源或官网PASS。

所有冻结源、数值包、收据、旧失败和 DRAFT 历史状态保留。无官网新投、无 export/Comparator/nanoda/旧证明成功collector。完整无条件比例K、全域实际dyadic/cumulative证明、规定公理、官网双核/原资源3200秒、公开promotion及精确Git同步仍是完成门；goal active。

## 同轮基于实际拓扑结果的选择更新

metadata-v1 的原执行820954实际exit0，只得归档几何/拓扑PASS：两个直接子树为905+1数值叶（root独立读归档3a0d94相符）。按前述停止条件，立即停止two-child Lean源码准备；未编译、未把旧70切点移植。v1冻结不改。

root随后仅用现有事件拓扑035c39计算固定规则：将根递归展开至所有前沿子树数值叶≤256，再仅把其中数值叶≥64的前沿节点选为cut。恰五块，数值叶数75、90、196、224、236，共821；另外85仍由父游走真实检查。小叶不各建状态，避免20个前沿节点的无效字节开销。这是同一rc10既有检查器的证明组织选择，不改变数学、阈值、几何、编码或叶算术。

现明确授权新的metadata-v2一次准备/执行：同30秒/2MB上限、同固定归档与源、无WL解码或能量重算；从归档轴/切值传播全部1895个rc10几何状态并核已有state SHA，仅输出root与五块hint的完整状态/pos/end/原fuel(128-depth)/尺寸/高度。parent残余85及可覆盖的821须精确加总。metadata-v2尚非任何Lean证明PASS。此新增执行基于v1有效结果作显式新选择，不是失败自动重试或升资源。

下一候选proof pilot为五条raw walkCut [] cursor（保原fuel/pos、decide +kernel）、各自Covered、CutsOk_cons五次和父rcOfC一次，仍新增≤8192B且最终单文件<2MB。只在状态/接口/字节门明确后另冻结实际compiler关；本段不授权编译。若五块提示/parent不被当前强化检查器接受，停止这份pilot，不把旧rc10当捷径。

## 已选定的单次新增证明执行关

五hint metadata-v2已真实退出0并冻结（清单6fccb81e…c9f），独审21c7d491…9a48。新Pilot.lean5095B/SHAeaa299bb1a6f5b7e6f65851ead6ee0e0d8ac85f941ac1e16f2bba53200bdd0b6已完整静审，五tuple/游标/fragment逐字一致（源审清单5fbe6103…da48），不引用旧rc10/run。完整集成估计1865917B仅是预估，尚无该新单文件资源证明。

root现选择唯一一次新增proof pilot编译，使用已证明且body对应当前v9的Prefix/Core仅作开发导入；fresh复制两份旧olean及两份可信ChallengeDefs，直接身份pre/post hash，不重新跑旧Core、整份v9、export/Comparator/nanoda。新源码五条raw walkCut[] cursor和父walkCutR128 cursor六次decide+kernel必须真实核过，并生成新olean/ilean/C。独审修正runner8930b82e…df49b已无确定阻断：保原3200秒总budget/-M6500/-j1/tstack262144/7GiB PeakWorkingSet，commit只诊断；只按保留句柄wait/停止自有child，实际root原outer0与终态时限/所有直接pins/三个fresh产物均必需。历史10包树不fresh重hash；这不是官网Linux资源、最终单文件、双内核或接受PASS。

成功只允许据新的分块证明另行选最终源码实现关；失败封存真实结果，停止这份pilot，不原样重试、不升资源、不拿旧rc10作捷径。冻结gate后不改直接输入；官网仍quota最后观察0，未上传；所有完整无条件目标保持，counter2/review13不变。
