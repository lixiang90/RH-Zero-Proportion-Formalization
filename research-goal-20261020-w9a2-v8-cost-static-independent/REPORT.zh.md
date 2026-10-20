# 固定 v8 构建成本的有限独立静审

结论：已有材料能区分若干保留或减少的构建工作，但不能把本次939秒、Lean137归因于某个声明、packed解码、48根检查、C生成或OOM。v7/v8的noncomputable修改没有移除主要数学数据和内核检查；两次官网失败也不是受控性能比较。

本审查只读固定v8源码、v6/v7/v8既有投影与静态报告、同pin SDK两个小源文件、官网冻结可见日志。只做字符串/正则结构盘点、直接文件哈希和写本报告；没有Lean、compiler、exporter、kernel、solver、数值重放、网络或进程操作，没有读取大closure或完整export，没有修改proof、state、Git、counter或提出新优化家族。

## 实际结果及版本差异

当前v8仍为1829382B/SHA5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b，当前直接哈希相符。官网观察归档中actual proofDigest为fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4；Solution build显示939秒，Lean137/bash1，没有Solution完成、Solution export或双内核完成。冻结技术日志89317ba7…没有RSS/cgroup OOM证据；七条push_neg deprecation warning不能定位致命类型错误或最后实际执行的命令。

既有独立raw projection dc3adb86…及v7独审记录的范围如下：

| 版本变化 | 精确源码差分 | 保留的工作 |
| --- | --- | --- |
| v6→v7 | 八个checker/walk定义各加noncomputable，共+112B；删十五行独立#print axioms，共−922B；净−810B | 所有证明体、数值数据、48个rc根及公开根不变 |
| v7→v8 | PTT_0..7/PTT/PT十定义各加noncomputable，共+140B | 其他全部字节、135条packed WL、48个rc及表soundness检查不变 |

因此v7的1014秒与v8的939秒只证明两次不同源/不同任务都在Solution build失败，不能把75秒作为十个modifier的净收益，更不能据两次137确定同一个kill原因。没有相同环境重复测量、命令级时间、实际内存曲线或失败时当前声明。

## 可核对的执行路径

**Packed数据先在宏层展开。** 源73–125行的digit64/decode64逐字节处理文本，循环做Nat shift/add，再由宏toString并返回Syntax.mkNumLit。当前135条WL packed定义的payload合计579704个ASCII字符，最大5542；这是输入字符串计数，不是解码后内存、内核项大小或时间下界。本次没有解码任何payload。成功展开后的内核输入是普通Nat numeral，不会在每个decide或独立内核中重新执行radix64宏。宏/decoder在当前源有真实runtime consumer，必须保持可执行；它们不调用被标记的checker或PTT表。源码压缩只减小输入文本，不能推出巨Nat展开、InfoTree或kernel项同等缩小。失败进程是否已展开全部135处未知。

补充root要求的有限caller盘点：WL/WD家族有136条numeral定义（135 packed、1条原十六进制WL31_0）、88个WL…s…平衡selector helper、48个WL根selector及48个WD，共320条普通def。排除这些定义行及quoted string后，源的其余部分只有48条rc0..47定理行引用该家族，引用全部为WD0..47；未发现宏或其他runtime外部consumer。这支持把完整链看成proof-only数据和selector，而不是证明135个literal之外没有其他computable caller。宏decode64仍是生成普通numeral的真正runtime路径，不在此数据链中。本次只做了有限词法引用盘点，没有Lean AST/间接动态调用验证或任何modifier方案；若未来只标135个literal或48个selector而遗漏88个helper，其编译caller边界并未随之闭合。

**48个根检查仍完整存在。** 全部rc0..rc47均直接调用rcOf，源12705–12708的命题仍含closed walk、fuel128及根状态；没有根使用rcOfC。rc后的整数是结果e，不能当作执行步数/叶数。源共72处`decide +kernel`，其中48处属于rc，另24处含pvCheck、winOk、两套表block检查、8个PTT_i_ok、覆盖等；72是语法出现次数，不是72次独立全walk或72个互不相同的重计算。

同pin SDK Decide.lean70–118明确区分普通decide的Meta WHNF与+kernel的mkAuxLemma。+kernel已有按type的module cache，并复用加入环境的lemma；不能简单认定普通elaboration重复两遍所有有限检查，也不能把相同hcov文本视作必然再算一遍。本次没有测缓存命中或归约分配量。

**完整walk在高层按命名证明复用。** 源13081的run8按有限根情况使用rc0..47，13140的Data.run组合run8；Localization.root_QuantGoal在16451行引用Data.run，而不是另生成48个closed walk等式。Data.cert也引用run。此结论只排除这处源码级重复整组检查，不保证表达式或内核内部任意子计算都有全局memo。walkCut/cutAt相关定义仍在源中，但48个根没有选择cut接口；本审查不据此提出改变切分或算法。

**非计算修饰只减少指定的代码生成入口。** 当前共有21条显式noncomputable def，其中18条是v7/v8新增的八个checker/walk和十个PTT定义；FMaj、FMajC、quadForm为既有标记。同pin Basic.lean134–140、186–223显示：非theorem且没有显式modifier的def会尝试compile；noncomputable section本身仅影响编译错误的报告，不普遍跳过代码生成。modifier保留kernel defnDecl的type/value并阻止该入口的compile。因此18处修改保留literal解析、类型检查、透明kernel body、48根归约、PTT_i_ok和其他表检查，也不删除后续InfoTree/快照/序列化工作。

既有runtime-caller边界分别为mcheckP→mleafP→leafStep→node→walkC/walk/walkCut/walkCutR，以及PTT_i→PTT→PT；其他已盘点消费者是定理体/类型。不能把digit64/decode64划入这两个proof-only闭包。v8仍有普通def数据/函数：既有v7词法盘点2269条plain def中仅十条改为显式noncomputable，故同盘点口径剩2259；819条data-like候选中有九条PTT数据被移出，剩810条。此为静态分类，不保证每条成功生成native code。较大剩余例子有qState、TOPD、witnessRows、WL数据，不能因source body较大就断言它是当前热点。

## 当前无法建立的成本结论

本地旧v6普通成功使用-j1/-M13500/-o，没有官网的-i/-c/--setup/--json路径；v8本地两次资源诊断又分别由旧commit门停止、及-M6500下interpreter处memory_exception失败。它们都不能替代本次Linux官网执行路径或给出939秒内的阶段分配。`interpreter`是既有全进程memory检查触发标签，不定位声明；官方137同样不足以确诊OOM。

原有InfoTree/快照保留、最终ilean引用处理和C输出都没有被上述modifier关闭；这些只是尚存的工作路径。本次没有证据表明失败已到C emission或最终ilean遍历，也不重新开启已经停止的InfoTree hook方向。source字节数、packed长度、rc数量、表节点数和单一失败时长均不能提供可靠的秒数/峰值RSS下界或加速保证。

## 下一次只读结构审计的最小指标

以下只是应收集的结构证据，不授权执行新门或修改候选：

1. 固定source/export身份、声明kind/namespace/source span/raw bytes；巨numeral、constructor和application的计数与最大单声明大小分开记录。packed payload字符数与展开后项结构分开，不运行decoder。
2. 对现成v6 export若另门准许单次有界扫描，统计声明type/value的直接constant依赖、表达式DAG共享及aux lemma分布；区分48根、表soundness、数据、runtime宏和三个公开根的可达闭包。记录共享与每根独有部分，不能由文件体积直接估计执行成本。v6 export只能描述v6内核项，不能伪装成v8 C/IR profile。
3. 源级剩余plain def按数据/函数/宏消费者分类；对18个modifier目标记录incoming caller，区分kernel引用与真正runtime调用。仅凭名字出现或较大body，不据此修改noncomputable范围。
4. 将任何推测与缺失证据并列：没有已有命令边界时间/内存、实际C/ilean完成标志或cgroup终止原因时，结构统计只能排序进一步审计的对象，不能裁定137根因。不得为补这些指标自动启动compiler/profile或全树扫描。

本包封存即停止。没有选择下一源码、资源上限或编译批次，也没有将既有失败翻为PASS。
