# rc10 两子树 cut 因子化的有限静态配方

结论：现成接口支持一个具体的单root proof gate：仅将rc10的整次closed walk检查拆成两个直接子树检查，再经CutsOk检查父cursor。它不改变WL、checker、target或完整数学命题。当前尚没有本任务生成的两份精确73字段state/cursor tuple，没有新源或Lean通过；下列是数据准备及单pilot的静态合同。

Root报告v9同cap构建583.671秒、outer1/child3221226505、interpreter memory_exception、RSS6829252608B；本审查未重新观察该进程。该结果不定位rc10、decoder、某叶或OOM。此方向最多试图减小单次闭式归约的最大工作块，不声称减少总保留proof/环境大小、时间或峰RSS；更多命名lemma本身也会增加环境。

只读v9固定源7552…、已有小metadata和解析/几何脚本正文，没有运行脚本、decoder、数值/margin/tangent/energy计算、Lean、export或export扫描；没有实现metadata变换、写proof或改state/Git/counter。原packed-elaborator替换方向已停止，未形成新codec/hook方案。

## 先区分旧70cuts与当前数据

20261018的ready70合同真实存在；packing-parser-v3.json中旧root10有五个ready子合同，(pos,end,fuel)分别为(390,52028,111)、(75500,116289,112)、(105,146546,115)、(154647,196188,112)、(81,226609,118)，旧parent end为235228。它们属于f82a…源。

当前W9A2原源241068…已明确删掉70ready合同并改48个direct rc；source-comparison.json记录packing137→135、PTraw2095→3483、BKD48→144、cursors70→0，geometry端点也变。故不能移植旧70的state/start/end/fuel，更不能复用旧Covered(cN)证明来验收当前QuantGoal。旧组织只作类型/组合模板。

现v9仍由PC9QB6MData.WD10、12832行rc10检查`RC 0 0 1 0 1 0 0 0`，fuel128、pos1、返回e270277。e不是fuel或叶数。已有W9A2 baseline-replay.json对原数据记录root10 height72、1895节点、906数值叶和42反射叶；这些是历史metadata，未在本任务重放。全部48rc根区域与全11794数值叶也不能混作48个计算叶。

## 当前源码已有的数学接口

- 11242–11259：cutAt在pos相等时使用kEqE；kEqE以完整stEq匹配73字段，CutsOk要求每个cut state已有当前`Covered(toCl state)`。其soundness不是任意接受一个位置或只比8个gap。
- 11260–11273：walkCut及walkCut_ok保留原node/split/leaf checker，按fuel证明所有位置的CovK。
- 11274–11278：covered_of_walkCutR适合有外层tm的入口；12709–12712的rcOfC实例化父root。
- 12813–12831：原WL10_0..8、平衡selector和WD10保留；不复制、不重打包、不变更任何原payload。

内部子state已经处于实际递归边界，子目标应为**raw walkCut**，不要无证据再包walkCutR/tm。父root仍用walkCutR。

## 唯一建议的下一关：rc10直接左右两块

先由root另行授权一个仅archive metadata+geometry变换的有限准备：绑定其已观察的walk-events.jsonl.gz（1596457B/SHA1999185a8409c879a987c697d67040f431a0ccaf0dde3181cb8902ffb1d2dbff，本审查未流读该文件），只重建root10的事件geometry，不解WL、不计算energy/tangent/main margin、不寻找新分支或新阈值。

从固定BAD/PR的root10开始，用既有record_math_w9a2.py61–66的split和事件axis/cut传播。检查axis范围、q边界、正序/不重复cursor、左pos=p+8、右pos=left_end、父end=right_end，以及每个root10事件的state_sha256；缺失、cycle或不符立即失败。canonical必须按replay_w9a2.py35–39使用紧凑ASCII JSON **加末尾LF**；state顺序是lo/hi交错72字段，再M=0。不要只哈希72字段、L全列后U全列或无LF的JSON。

M=0有具体源码依据：入口ofCl(RC…)0；cuH末10850保留bc，cuL_eq10854明确输出ofCl(cuB…)s.M；tm11056及tm_ok11058也保留M。geometry split本身不修改M。root的tm先作matC，当前root构造的各span已由相邻gap和给出；变换应与该入口对齐，任何hash不符都停止，不能靠忽略M或放宽state匹配修补。

从pos1事件选两直接孩子：pL=9、pR=eL、eR=270277；两者在父fuel128下各用fuel127。记精确两state为sL/sR，eL从同一事件树取得。当前还缺这些实际tuple，不得把旧root10的ready数字填进来。每个tuple都是不可信proof hint，必须由原Lean计算重新核对。

未来唯一proof-producing pilot的精确义务为：

```
cursor10_L : U (walkCut TOP BK TOPD BKD PT REG WD10 [] 127 9) sL = eL
cursor10_R : U (walkCut TOP BK TOPD BKD PT REG WD10 [] 127 eL) sR = 270277
```

两式分别用原`by decide +kernel`，并检查各end非0。由`walkCut_ok lbS lbD ptS hR WD10 cutsOk_nil 127 p`得到相应CovK，再用cursor equality及非零得到`Covered(toCl sL/sR)`；此处hR仍是原Data环境中的REG soundness，两个新cursor lemma使用独立名字避免遮蔽。本配方未声称已编译语法。

用cutsOk_cons两次建立`CutsOk [(eL,sR,270277),(9,sL,eL)]`，最后检查：

```
U (walkCutR TOP BK TOPD BKD PT REG WD10 cuts 128 1)
  (ofCl (RC 0 0 1 0 1 0 0 0) 0) = 270277
```

再经rcOfC获得与原rc10**相同**的Covered结论，其后run8、Data.run、实际定位、图势、counting、三个公开根全不变。子块必须证明当前QuantGoal；不能引用旧cN floor、旧rc10或导入已成功的whole rc10作为其替代。开发时若root另选已pin Core作缓存，只提供相同定义/通用soundness；新cursor proof依赖必须为上述原+kernel计算及CutsOk，不得偷用旧whole-root结论。

## 大小和停止条件

保留同一份135packed数据。两个73Nat state在各字段十进制不超过13位且M0的条件下，literal主体上界约2×73×15=2190 ASCII B；加两cursor、两Covered薄lemma、CutsOk和父检查，约5KB是合理设计目标，尚非已生成测量。建议硬门为新增raw≤8192B、总raw<2000000B（当前1861120B，余138880B），只替换旧rc10 proof，不能保留它再追加一遍同whole-root检查。

先用既有事件的结构计数报告两子树规模；若一侧接近整个1895节点、构成极端失衡，root应在source准备前停止本两块pilot，不能自动改选更深cut另开分割族。以下任一发生也停该单pilot，不换codec、不细分其他根、不加cap或自动重跑：archive/hash/state/cursor不符；没有两个非空正确子树；metadata字段超预算；任一子或父原+kernel检查失败；source超预算；意外依赖旧whole rc10；同cap单次pilot无实际终态或再次内存失败。不得仅把更早失败或耗时下降称成功。

若pilot实际通过，静态上只增加了可复用的局部覆盖证明并压缩父计算路径；仍需root另审最终单文件投影和完整正式验证。它既不是新的无条件比例定理，也不能保证解决全文件保留项或官网资源限制。本报告封存即停止，没有实施下一关。
