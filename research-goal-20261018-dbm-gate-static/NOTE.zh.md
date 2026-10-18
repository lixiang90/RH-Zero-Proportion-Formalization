# 固定 DBM 机会关合同的静态审查

只读设计。没有执行pair、核值查询、Lean、solver或分类；不修改已封包。
本审查接受父任务提供的1187例外数作为拟执行合同参数，不独立重放Stage B。
执行仍须等待完整B独审及root另行书面授权。

## 范围、组合与映射

- 1187*1187*4=5,635,876。是有序左右pair，含同一cell的pair；不能只枚举
  i<j，也不自行借反射删掉朝向。重复几何保留不会破坏覆盖。
- prefix位置0..8、suffix位置1..9，共享位置1..8的八vertex，因此共同
  正跨度有choose(8,2)=28个，不能误用七个shared gaps代替全部跨度。
- 每侧36个跨度各有上下两个有向bound，两侧144条，加九条sep下界共153。
  合同应写36*2*2+9，而非可能误解的“72*2bounds*2cells”。重复边也逐条核。
- X_i=20*32768*p_i取实数；原l/u整数变成Xj-Xi<=20u、Xi-Xj<=-20l，
  sep变成Xr-X(r+1)<=-17*32768。无整数gap假设或近似取整。
- 单侧rev把原span(i,j)映射到(8-j,8-i)，之后加prefix0/suffix1偏移。
  不能用整个十点的9-i去反射单个九点窗口。四朝向映射必须独立固定。

## Prescreen和精确判定

共同闭区间严格不交（Lleft>Uright或Lright>Uleft）时，正好给同一
物理跨度的两条反向edge，其权和严格负。乘20后仍严格负。端点接触
不排除；不用epsilon或浮点判别。应记录哪一span和哪两条原edge作理由。

剩余pair可用十vertex Bellman–Ford或Floyd–Warshall精确有符号整数判定。
BF须覆盖所有vertex（例如全距离初始0的虚拟source），而非任意局部可达
搜索。FW diagonal初始化0，重复edge取min。负cycle只作为整数事实：
保存实际原edge序列并核连续性及总和<0，或可独立重算正确closure；
仅凭iteration次数/内部status不够。不能用固定宽度溢出的负数作证据。

可行输出须给十个精确potentials，并重新从原两个state构建全部153条edge，
逐条验证Xj-Xi<=w；不能只验证最短路中被选的edge。平移X0=0无损。
通过的整数potentials也是真实变量的可行解；不需要它们来自真实核极小元。
这只证明几何外包的可行性，不证明任何实际F9<tau。

## Ordered不是DBM约束

分别检查四point inequality：
prefix id为X1+X7<=X0+X8，rev为反向；
suffix id为X2+X8<=X1+X9，rev为反向。
这是两侧源有序半域在各朝向的真实条件，不能当单条difference edge加入。

合同可固定为“第一个精确DBM可行case即停止”，同时输出两ordered
checks及signed slack。若二者均通过，可称ordered geometry也有见证；
仍不能称能量反例。若任一违反，只能称relaxed DBM可行且该potentials
不满足该ordered条件：不能据此判真实ordered交集为空，也不能判其非空。
在当前松外包机会关中仍停止，不额外寻找另一个potentials/删case/改模型。
若想增强ordered可行性判定，属于另授权任务，不能藏在同一次DBM scan内。

## 全域含义、资源与停止

完整B命题必须是任意sep窗口的实际sublevel外包，配以原全域c9基线及
根外分离压力余量；不是minimizer cover。四chart的全部pair负cycle足以
排除双低能窗口。仅测试一部分pair或漏根外区域不够。一个可行松盒只
终止这个固定外包机会关，不否定真实joint下界，也不是新的ζ比例反例。

300s/20MB的bounded read-only机会关是合理的风险受限测试，不是全5.6M
pair将在预算内完成的证据。计时应含输入hash/解析/设置，循环中定期检查；
timeout必须标inconclusive并保存已检查计数，不能当全不可行或发现可行。
不retry、不调顺序寻找更好结果、不改sep/tau/state。首个可行case即停。
20MB应在执行合同明确口径；若是新增raw artifact上限，不得以gzip后大小
替代；若原授权也是RSS上限，不能擅自放宽。无需保存数百万pair的完整
矩阵，保存累计prescreen/负cycle/已处理数与首个见证即可。完整性计数须
区分已处理orientation-pair与尚未处理者，停止时不可写all_pairs_passed。

开跑前/结束时绑定source、B输入、脚本和全部immutable依赖SHA；验证
1187 state身份、shape/原单位、映射表以及B独审status。输出source hash
端点、wall/资源guard、停止原因、pair顺序/索引/朝向、153edge校验结果和
ordered结果。若输出负cycle，则独立审查其edge来源及严格权和。

本审查没有给2MB单文件交付或3200s完整内核链路PASS。即便此机会关
全不可行，后续product consumer/actual joint与计数接口仍须真实证明、
封存和计量；在这些预算未知时不应启动proofbatch。
