# 固定 Stage B 机会关：只设计，不执行分类

本包不运行分类、阈值查询、pair scan、Lean、solver或核值评价。它定义未来
一次固定机会关的输入/输出与停止条件，不是已经完成的外包证书。

## 1. 固定数学目标与输入门槛

唯一阈值 tau=893916123055294719/10^20，原floor
c9=893616123055294719/10^20，sep=17/20。差值整数
DeltaN=300000000000000；不调阈值、分离参数、核或权重。
数学域是任意八gap h_r>=sep 且 F9(h)<tau，绝不要求global/local minimum。
原cert_AM对所有非负gap的floor c9仍是另一条命题。
不声称低能自动推出分离；未分离窗口由最终matching/close-pair计数桥付款。

执行的前置门槛是Stage A独立封存的同一source原floor完整身份重放：
137 packed literals、48root、70nested cut的state/start/fuel/endcursor，
13046 numeric、595reflection、0Farkas，全部原mcheckGX arithmetic/printed
AST与mokI，以及根外160个true-COV/WZ和全部root guards。
这些数字来自本轮团队结果报告；本包不重复运行或把未冻结receipt当依赖。
未来执行者必须首先绑定完整Stage A frozen manifest SHA并独立验证其文件。
原source raw SHA固定f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。

## 2. 根外区域：保留原floor guards，显式补足分离压力

F9=P+sum a_e*w_e，P=sum b_r*h_r，a_e,b_r>=0。对分离域有P>=sep*B。
原true-COV只证明单edge a_adj*w>=c9；故该区域实际上
F9>=c9+sep*B。只需固定有理数验证该下界>=tau，不重查更高阈值WZ。
若使用原每条true-COV的更强下界也必须保持原端点和值，不能新取区间。

原SMAX尾部h_r>=SMAX_r/32768有
F9>=b_r*SMAX_r/32768+sep*(B-b_r)。不得重复计算第r项压力。
对八个r逐项核该固定常数>=tau。原小gap分支h_r<1/2在sep域为空；
1/2、SMAX和COV端点全部按原闭区间覆盖处理，不能留严格/非严格缝隙。
完整true/false COV连续性、bound<KB及root index组合来自Stage A。
若以上任一固定有理guard未获证，必须停止“仅原48root”的分类：不能静默
遗漏根外低能条带，也不自动扩root/查询新WZ。可单独报告是哪一条失败。

上述固定有理余量已经列于record-overlap-static/static-receipt.json。
本包只引用其冻结结果，不重新评价阈值或WZ。本设计的source证明仍须
把原term/linear bounds加上sep压力，不能直接调用原cN版root_cover冒充tau版。

## 3. 原叶只做一次精确threshold扣款，不改标签

原mcheckGX的main inequality对cN唯一线性出现：
SLOPE*cN，SLOPE=335544320000000000（源码10155–10173）。
设Stage A已验证的原main integer margin为M0=RHS-LHS(cN)。
固定同state、FS、moves及tables，M_tau=M0-SLOPE*DeltaN。
只扣一次。其他preconditions与原threshold无关，必须仍全部为真。
M_tau>=0才可标closed_numeric_at_tau；M_tau<0只标exception，
不是实际低能点存在，也不是数学floor失败。禁止直接重标原成功叶。
禁止修改frozen cN、FS、Pruefer/dual moves、PT、原切分或取新见证。

未来Lean消费者应使用带tauCN参数的generic mcheckGX_sound及原guard、
MulOKg、mtermTI证明，结论是该cell的Fg>=tauCN；当前source-specific
Covered/mcheckP/mleafP/walkCut仍绑定cN，不能只改调用参数得到新定理。
分类证明的正确形式是：整个原root中的任意有序分离点，要么已排除，
要么属于输出exception cell。所有nested cut必须按Stage A认证的state
展开成同一批terminal叶；不能把cut的原Covered(cN)当作tau成功而跳过。

13046 numeric每个必须恰好归入closed或exception一次，二者无遗漏。
595reflection在有序半域h0<=h7内不可能：原判断保证h7<h0。
它们不支付tau，也不直接当raised numerical成功叶。Stage A的0Farkas
是预期身份；若出现额外kind/重复terminal/cursor歧义即停止，不自动解释。

## 4. 闭例外外包与反射

保留每个exception的原完整state：8个adjacent L/U及28个PR A/B，合计
36个正跨度的闭上下界，坐标单位1/32768。PR顺序必须来自原source，
不是假定词典顺序。记录原root/stream位置、nested provenance、state SHA、
原witness定位/语义hash和M0/M_tau；不复制或改原witness。

令E_i为这些闭state与h_r>=sep、h0<=h7的交。目标命题是
{h>=sep,F9(h)<tau,h0<=h7} subset union E_i。
由实际F9 reversal invariance，整个分离sublevel被E_i及reverse(E_i)覆盖。
端点相等时可固定选id，不能丢掉h0=h7。为仅DBM消费者，可把h0<=h7
丢去得到更宽闭外包，但必须在metadata记relaxed_orientation=true。
该不等式是p1+p7<=p0+p8的四point关系，不能冒充单条difference约束。
丢掉它只使机会关更粗；若DBM仍不可行则有效，若可行则不说明实际低能。

最小可用于松外包的geometry是七个共享gap的闭projection intervals；
它可筛出部分不相交，但丢弃非相邻跨度相关性。优先保存完整36对state，
以免人为降低唯一机会关的区分力。仅root路径/leaf编号没有几何含义，
不能代替state及已经绑定的重建算法；仅九点边界盒也不够恢复所有PR。

## 5. 两窗口、四朝向与统一整数DBM

十点位置p0..p9，prefix用p0..p8，suffix用p1..p9，共享七gap。
变量X_i=20*32768*p_i仍取实数，平移可令X0=0。原state边界l<=
32768*(pj-pi)<=u映射为Xj-Xi<=20u及Xi-Xj<=-20l。
分离映射为Xr-X(r+1)<=-17*32768；此时全部rhs为整数，无取整点假设。

每个exception状态有id/rev两朝向：
id跨度(i,j)保持；rev跨度映射到(8-j,8-i)，其正距离的l/u不变。
prefix嵌入再加offset0，suffix加offset1。独立处理id/id、id/rev、
rev/id、rev/rev，不能只核同朝向。可利用全局反射减少重复工作，但必须
有精确索引对应，不可凭对称直觉漏两种。若保留ordered条件，其在每个
物理朝向的四point式也要正确映射，不能送进标准10vertex DBM。

DBM只由两套36跨度上下界和九条sep约束组成，至多153条原始有向边。
精确负cycle给不可行证明；cycle权和=0仍可行。浮点feasibility或松弛
后接触一个端点不得当作排除。最终可用循环边编号+严格负整数和作小证据，
无需信任最短路求解算法。每对state四朝向若均得负cycle，则无两个相邻
分离窗口同时低于tau。任何一个DBM可行只代表本松外包机会关未关闭，
不是函数存在低能反例；本授权不再细分、优化见证、加强orientation或改阈值。

## 6. 唯一固定脚本合同与停止门槛

本包没有实现脚本。未来拟议stageB_classify_once.py只做：
固定输入SHA检查→原Stage A证明数据复现/读取校验→上述root余量门槛→
原13046 numeric的单次扣款分类→完整闭state外包输出→统计和source预算。
输出包括closed/exception/root外余量身份、orientation处理及全部input哈希。
不创建新kernel查询，不取新cut，不改变leaf/FS，不自动调用pair scan。
Pair DBM scan须由root另授权；本计划仅把其精确合同写清。

硬停止条件：Stage A身份不全；任一原guard不符；root外余量失败；
count/stream/endcursor不符；阈值扣款与sourceAST不一致；输出超约定资源；
或不能给出完整单文件source预算。均只保存失败位置，不启第二参数方案。
若全部13046在tau均关闭，则得到更强separated九点floor，另行证明与计数。
若有例外，则只有完整外包，不能先称joint floor或比例改进。

## 7. source与运行预算

完整新baseline原文1,818,411B，十进制2MB余额181,589B。
旧三桥证明体38,361B仅为迁移预算参考，不是能直接import的本核定理；
即使按该参考，剩余143,228B仍须容纳classification消费者、例外/DBM证据、
新的WCert10实例、counting与网站wrapper替换。不能只比较gzip数据大小。
保留源内原payload和原witness可避免再复制13046份FS；但raised分类证明
仍有kernel工作成本，新的消费者/证明项绝不免费。直接逐exception重复
72整数和四朝向pair证书可能迅速超额，须在任何后续证明批次前量化。

必要输出预算是baseline实际bytes+新增consumer源码+实际geometry/证据
编码源码+新wrapper减去被替换wrapper，严格<=2,000,000；同时网站整个
ordinary/export/Nano/generation需在现政策3200s预算内。缺少完整计量时
只能标unknown，不能因137payload可读或例外数少便宣布交付可行。

最终若相邻窗口不能同时<tau，原c9全域baseline给
(Fprefix+Fsuffix)/2 >=(c9+tau)/2；仍需本核实际十点容量/pressure、
separated summed/band、matching短对及最终计数桥。现无这些新定理。
本设计不修改governance计数、旧frozen输入或current目标。
