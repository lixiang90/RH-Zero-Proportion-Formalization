# 新 24 模核的整数配置 floor：只读证据库存

2026-10-17。此项只读源码、既有说明及数据元信息，不重新枚举整数
配置，不运行 DP、核函数评价、优化器、Lean 或覆盖搜索。没有修改
已有冻结包。它是证据范围审查，不是一个新的数学证书。

## 结论

在本次核对的现有库存中，**没有找到对全部 pressure 允许的正整数
九 gap 配置的实际新 24 模核统一 floor 证书**。已有的 69 个实际
floor 是 69 个选定 coherent basin 的局部定理；整数中心证明是
一元实际核及其 jet 的界；ternary/DP 文件是有限字母表上的浮点
发现工具或抽样 potential 试验。三类证据不能相互替代成一个全
整数配置定理。本审查不主张通过穷尽全仓库的一切表达式证明了
“不存在任何这类证书”，只记录已检验的相关证据链及其接口。

## 确认采用当前核和 ledger

`WindowGapEnergy.lean:18–23` 定义的 `Fw24` 是当前 `NewLedger.W`
上的实际 `WindowKernel.w 24 d24`。`WindowKernel.lean:121–122`
的 `d24` 引用 `NewWindows.nums24/10^9`。本说明没有把旧 12 模
Core、旧九点 floor 或旧 W10 全树当作新核的整数配置证明。
具体参数 JSON 的 SHA256 是
`61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11`。

## 69 个实际盆地定理的确切范围

`WindowRationalBasinAll.lean:34–48` 已给出全部 `i<69` 的检查及
实际结论，但 `actual` 的参数仍包括 `Region (basin i) g`。
`WindowGramRational.lean:44–46` 定义这个 Region：全部 41 个正权
跨度都须落在该盆选定的整数中心减/加 `21/100` 内。
`:86–108` 用这些局部区间把标量 minorant 转到实际 `Fw24`。
这里没有把 Region 前提消去，也没有从正整数性和 pressure 上界
推导 `∃ i<69, Region (basin i) q` 的定理。

`cover_newwindow_gram.py:50–78` 明确读取旧 W10 的 69 个 inherited
integer-gap patterns，再对当前新核/ledger 重选有理锚。它没有产生
pressure 约束下所有正整数 pattern 的穷尽证书。
`cover_gram_basin_api.py:15–39` 只建立 69 个 tuple 的 lookup；
不在表中就返回 None，而且仍逐一检查全部正权跨度的井 membership。
旧生成/回放 JSON 中的 bridge=false 是当时的历史状态；本审查
**不**用该旧字段否认后来已完成的实际解析桥，而是直接核对当前
实际定理仍具有的 Region 前提。

`WindowGramBasins.lean:1–3,15–20` 的纯代数版本对每一个指定二次
多项式给全实变量下界。其“全实变量”只指该多项式，不能删除
多项式与实际核相连时所需的局部井区间。69 个多项式全部通过也
不是 69 个井以外的实际函数下界。

## 整数中心表的确切范围

`WindowIntegerKernelRecipe.lean:95–128` 使用当前 `nums24`，以
`kI_sound` 和 `wI_sound` 证明 `n<33` 时整数中心实际核 jet 的
有理区间。这使既有整数中心 1–32 的值界可复用，但不是对
九个整数 gap 的压力、41 个边值及其组合做全局最小化的证书。
`“整数”` 一词在这里是核函数的单个输入中心，并非整个整数
配置集合。

`WindowDiscreteEnergy.lean:1–5,61–69` 也没有隐藏 lattice DP：
它证明容量、band 和 separated remainder 的通用桥，
`summed_of_pointwise` 显式把全域 `hfloor` 作为输入。
这个文件名里的 discrete 指后续有限点集能量，并非已经完成的
正整数 gap floor。

## ternary 与 DP 证据的范围

`spectral_wcert_reopt.py:57–84` 的 `discrete_dp` 使用浮点核值和
一个调用者给定的有限 alphabet。其 `memory` 若小于窗口长度会
只计入相应距离范围；即使 memory 覆盖完整九 gap，也只在所选
alphabet 上求候选，不会自动覆盖所有正整数。
`:114–117` 的典型 alphabet 是 `(1.04,1.98,2.92)` 或
`(1.04,1.97,2.915)`，不是正整数配置集合。该文件起首及输出
`:138` 明示无 certified bound，而且原文件使用旧核。

`window_range_ledger_search.py:20–39` 虽把核替换成当前 24 模
profile，却仍使用上述非整数 ternary alphabets、浮点发现与
局部优化；它还重新优化 ledger。`:50–57` 明确区分 sampled
floor、observed upper hint，并保留 global_floor_proven=false。
`window_profile_challenge.py:1,23,41–46` 的 19683 个 ternary
starts 同样只产生全局最小值的局部上界，不是下界证书。

当前 24 模的 `research-goal-20261017-ternary-coboundary/NOTE.txt`
`:3–15,25–30,60–77` 则是固定 29171 个真实 gap 样本的三分类
potential LP。覆盖全部 6561 个 class states/19683 个 class words
不等于覆盖这些连续 classes 内的所有点，更不等于正整数域证明。
它明示尚无逐 closed class 的实际函数 floor；也不能借用原 F 的
global-minimizer-only 排除来替代新的分片目标证明。

额外核对了 joint-cycle 和 phase-lattice 说明，以免漏掉整数点
例子：joint-cycle NOTE:65–90 在 `(1,...,1)` 周围只有一个局部
band 证明；其中浮点 `E=.008601...` 是 **kernel energy**，实际
`F=P+E` 还须加 pressure，不能把 E 误报为 F<c 的整数反例。
phase-lattice NOTE:80–101 的 `(9/4,1,...,1)` 不是全整数配置，
且其低值是辅助 Q 表达式，也不是实际 F 的反例。

## 公共偏移 rounding 的非循环性门槛

根代理已独立审查的公共偏移恒等式为

`F(g) = sum_alpha alpha*F(q) - delta*B + Phi(g)`，

其中所有竞争配置 q 的 gap 为正整数。全局极小点必要式仅为
`Phi(g)<=delta*B`。若另已知每个相关整数 q 都有 `F(q)>=c`，
那么任何 `F(g)<c` 的原域点本来就满足 `F(g)<F(q)`；取凸组合后
自动有 `Phi(g)<delta*B`。因此单独加入该必要式不会排除任何真正
的低能量点，不能把“整数配置能量高”直接说成新排除能力。

可产生 floor 的不同命题是：完整整数配置下界 `F(q)>=L`，加上
实际函数的全域 **下界** `Phi(g)>=m`，从而
`F(g)>=L-delta*B+m`。`Phi<=delta*B` 的方向不能代替后者。
正压力和核平方非负会使 `P(q)>=L` 的尾部自动满足整数 floor，
但剩余 `P(q)<L` 的整数配置仍需完整证明；现有 69 个局部盆和
单个整数中心值表都没有提供这一覆盖步骤。本次未构造或评估
新的全域损失界，也未确认任何 frontier/大祖先收益。

所有证据文件的 byte hashes 与行号见 `inventory.json`。当前仍无
新的无条件零点比例、全域覆盖或网站提交结果；本静态 gate 完成
后停止，不启动局部实验、枚举或新证明批次。
