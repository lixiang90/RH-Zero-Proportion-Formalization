# E：原整cell余量付款加DBM的完整联合floor合同

只读静态审查；不执行E、核值查询、LP、pair或Lean。不改tau/c/FS/核/点，
不修改B/C/D或先前frozen pin。固定域仍是任意九gap h>=sep=17/20，
不是global/local minimum。D的点诊断不是本证明前提；它解释为何C首个
相容pair可被原scalar余量付款，不能把正点值宣传为共享变量新增益。

## 1. 常数与局部实际floor

SA=10^20，kappa=335544320000000000，
c9N=893616123055294719，tauN=893916123055294719，
DeltaN=tauN-c9N=300000000000000，
c=(c9N+tauN)/(2SA)=893766123055294719/SA。
只定义固定付款threshold T=kappa*DeltaN，不改参数或查新核点。

对每个原numeric叶i，Mi为同一原FS/state的signed main margin
RHS-LHS(c9N)，原成功守卫给Mi>=0。已冻结flow-proof纸面lemma完整给出

  Fi(g)>=A_i(g)>=Aflow_i(g)>=c9+Mi/(kappa*SA)

于该原cell的每个点，非只在D点或某个极小点。它使用原mokI/PVI/LBSound、
MulOKg、box/term范围及准确signed/Nat转换，不能只由一个抽象margin数
推出。未实例化为新Lean theorem，后续actual消费者必须真实证明该中间结论。

反射把同一实际F9保持不变并把原cell完整映射；Mi数值不变。paid rule无须
重新对每个朝向计算kernel或margin。反射terminal本身没有Mi付款，它只与
所选ordered半域矛盾。595reflection不能混入numeric付款数组。

## 2. 完整联合floor证明

令E_L=F9(h0..h7)、E_R=F9(h1..h8)。原cert_AM全非负floor给
E_L,E_R>=c9。目标为E_L+E_R>=2c=c9+tau。

若一侧被证明>=tau，另一侧原c9就足够付款。这包括B的非exception
numeric、根外true-COV和SMAX尾部的分离压力余量；不能把“未列入一个
不完整例外表”当这种证明。

更简洁的完整反证形式是：若E_L+E_R<2c，则由另一侧>=c9可分别推出
E_L<tau、E_R<tau。B对所有任意sep sublevel的完整外包给两原exception
cells i,j及各自id/rev，原ordered图表也各自成立。因此只需覆盖该有限
exception乘积的全部四chart：

  (a) 若Mi+Mj>=T，由局部整cell floors有
      E_L+E_R>=2c9+(Mi+Mj)/(kappa*SA)>=c9+tau=2c，矛盾。
  (b) 若Mi+Mj<T，则要求该joint DBM有严格负cycle，也矛盾。

付款允许等号；只有严格小于T进入DBM。这直接证明平均floor c，无须
更强的E_L>=tau或E_R>=tau析取。C把所有binary-tau exceptions都交几何
测试，故C的首个可行pair不否定E。E改变的是已有原witness余量的组合模型，
不是重试同一geometry-only规则，也不改变任何kernel或原见证。

## 3. DBM、ordered与全域覆盖不可省略的条件

两侧36跨度完整闭上下界分别按id/rev与prefix0/suffix1映射为153条
整数rhs difference edges；X=20*32768*p取实数。原state、offset、fuel、
points全部保持；joint DBM与两原states分开。

两ordered条件是四point式，可留在逻辑不变量但从DBM中放松。严格负
cycle即使在松域中也排除实际点；零cycle/闭端点接触不排除。若某个
underpaid pair的DBM可行，须核全部153边并另报两个ordered状态；这只
使此固定外包付款模型未关闭，不是实际F9反例。不能因ordered违反就
擅自删掉该case并继续宣称原机会关已完成。

B的root外补偿仍是原true-COV单项floor+sep*B，以及尾部
b_r*SMAX_r/Q+sep*(B-b_r)。这些已固定检查且不得重复付款第r项压力。
sep>1/2排除原小gap分支。全非负原c9用于反证，未分离域在最终matching
计数中另付款，不声称所有低能自动分离。

## 4. 完整遍历和停止计数

1187 exceptions左右有序乘积、四独立朝向，完整orientation-pair数为
5,635,876。包含i=j；不擅自对称减半。Mi+Mj是朝向无关的固定常数，
故paid pair可一次核后记四个chart已付款，无需运行四次DBM。

完成时须有paid_orientation_pairs+strict_disjoint_pairs+other_negative_cycle_pairs
=5,635,876，三个类别互斥且每pair/chart有唯一身份。若实现按不同顺序
分组，必须说明计数如何展开到四chart，不能把state-pair数当orientation-pair数。
shared28span prescreen只允许严格disjoint，之后153边BF/FW负cycle同C。

第一个underpaid且几何可行的case即停止；timeout/资源限额也停止并标
inconclusive。未遍历项不能计作通过。不得在失败后改tau/sep/line/FS、
换floor舍入方式、追加LP或点查询。本包不给E执行授权。

## 5. 最小actual consumer改动：不必新mincostflow

在已设计product树中，双方到原numeric叶时先验原Mi身份并检查Mi+Mj>=T；
true直接用whole-cell margin-floor lemma关闭，false才调用原DBM几何判定。
任一侧已在tau关闭也可提前结束对侧subtree。原root、split、cursor和
reflection逻辑仍按Stage B/product静态合同；不复制每exception73整数。
Mi可从同一原stream/witness精确重建，不需存另一份FS或求新dual flow。

新的formal核心是strong margin lemma及双方加法，不必实现transshipment
optimizer。当前generic mcheckGX_sound虽然内部left分支证明强floor，
公开type为Pg=(cN<=Fg) or reversed；source-specificCovered也绑定原cN。
所以exactMi方案不能凭更改标签调用旧walk。需提取原S1–S5的中间lemma
（前包已给源式证明）或等价的真实算术proof，保留全部actual guards。

## 6. Nat阈值复用的合法替代与舍入损失

令ni=floor(Mi/kappa)、cN_i=c9N+ni，全部为Nat。mcheckGX对floor参数
唯一线性依赖为kappa*cN_i，其他guard不变，故其新main margin是
Mi-kappa*ni>=0。generic mcheckGX_sound可直接用于这个Nat threshold，
不用新kernel/Taylor分析。其Pg析取需用该侧Ordered消去反射；若要从API
取得无ordered的整cell强floor，仍需抽出其证明体中永远left的薄lemma。

这样能证明Fi>=c9+ni/SA，而非exactMi floor。每项余数
0<=Mi-kappa*ni<kappa，两个window总损失严格<2kappa（margin整数单位）。
因此用ni+nj>=DeltaN付款是另一个更保守合同；exactMi已付款而Nat-floor
规则未付款的pair可能存在，不能静默替换。E当前固定exactMi，依赖strong
flow lemma。若将来提出Nat-floor消费者，必须单独预声明并重新评估它
实际需要的underpaid几何覆盖，不能直接套E exact通过统计。

## 7. 交付边界

E若全部通过，给的是有限证书层面的separated平均floor机会，不自动
成为新Lean或新ζ纪录。仍要实际证明strong lemma、product覆盖、WCert10
容量/压力及matching/counting，并检验单文件2MB、ordinary/export/Nano
完整3200s。现在没有新proofbatch或网站可提交性PASS。

E若失败，也只说明当前原Mi联合付款+松DBM方案未完成；不否定实际floor，
也不等同于新的核函数反例。当前报告不以D点正值或C相容性替代全域证明。
