# 复用原 stream 的同步 product 消费者：静态可交付性审查

本包只读已冻结源码和Stage A清单。没有实现消费者、运行分类/pair scan、
生成大证书、优化或编译。结论是存在具体的sound递归接口设计；其成功、
源码合规及网站时限可行性均未知，不把一种表示方法称为新数学改进。

## 1. 具体递归命题

固定实际新核/W9、tau=893916123055294719/1e20及sep=17/20。
物理十点的九gap为h，E0=F9(h0..h7)，E1=F9(h1..h8)。
sigma0,sigma1各取id/rev；x0、x1分别是对应物理窗口经sigma反射后的
八gap。因此实际reversal theorem给F9(x0)=E0、F9(x1)=E1。

一个产品节点持有：两侧原root/bit position/fuel/cursor contract、两套
原St（含原73个Nat字段及M，不只72个geometry端点）、独立joint DBM D。
节点不变量 Inv(h) 包含：h>=sep，x0与x1各在原toCl(St)内，D含物理
十点位置，且Ordered(x0)、Ordered(x1)，即各自第0gap<=第7gap。
具体可证明的soundness为：

  productCheck(node0,node1,D)=true ->
    forall h, Inv(h) -> tau<=E0 or tau<=E1.

等价地，Inv且两个实际窗口均<tau的点集为空。不变量不含极小性。
最外层用既有Stage B根定位余量将两个低能窗口送入原48root之一，再独立
选两朝向，共四chart。最终得到不能同时低于tau；这一步并不自动完成
十点WCert、separated计数、matching和网站statement的证明。

## 2. 递归的有限闭合与分裂规则

1. 任一侧原numeric见证在tau成功：用generic mcheckGX_sound (10174)
   及原mtermTI/MulOKg/PT guards，得到实际该窗口>=tau，整个对侧子树
   均可关闭。新阈值main margin只扣原SLOPE*(tauCN-cN)一次。
2. 任一侧reflection terminal：原u7<l0与该侧Ordered矛盾，关闭该chart；
   不能把它当tau下界，也不能要求joint DBM识别这个四point关系。
3. joint DBM有严格负cycle：实际difference inequalities沿cycle求和
   得0<0，关闭。零cycle不关闭。检查负cycle证据即可，不需信任求解算法。
4. 否则选原左树或右树的一个branch，只按其原split规则产生两孩子；
   joint DBM分别加入映射后的同一branch边，递归两者。孩子的并覆盖
   parent，切点两侧都闭，重叠边界无害。按左右剩余结构fuel之和归纳。
5. 两侧均为tau失败numeric且joint DBM未排除，则返回false。不能把
   “两边原cN成功”或“访问完全部bits”当true。false仅表示这个证书方案
   未关闭，不是实际存在双低能点。

source的cov_splitB (10437) 已对任意谓词P泛型，连同cuB_ok、mat_gen
(9581)提供原child geometry覆盖，不需借用固定floor的splitAx_ok。
反之Covered/CovK/WalkOK在10651–10670固定为Pg(cN)，故walk_ok、
walkCut_ok、covered_of_walkCutR不能直接给上述product谓词。应复用
几何定义/泛型lemma，给新递归soundness，不是重命名原Covered。

## 3. 必须保留 original state 与 joint state 的区别

原dec4F (9843)调用gptF L U解码原点位；ystep/ydec还用原L/A/B计算
dual付款；split切点和child end cursor也取决于原state。故不得把joint
DBM收紧后的projection喂给原decoder或原split。这样做会改变FS/point
及消费位置，失去“复用原13046见证”的身份。product的D只作额外含有
实际点的约束，并可用于负cycle，不修改任一原source state。

原St由原root和原split/normalization确定；D从这两套完整36跨度约束
映射而来，可即时重建，无须把每例外72个端点再写一份Lean literal。
分支只更新被拆一侧原state，另一侧保持；两个子branch的D均可由原states
重建，或用已证单edge closure增量更新。后者仍需新的10vertex soundness
证明，不能把原9vertex Nat偏移cuB的实现无条件当10vertex替身。

原stream是prefix序列，右孩子cursor来自左子树的原结束位置。如果左侧
已在product早关，也不能跳过原语法定位而猜右孩子offset。可用原cN的
已认证cursor合同/纯parser计算end，或附小end索引再显式验证。用tau版
walk返回0计算end会在失败叶截断，不能用于导航。所有nested cut必须
继续按原state/end合同展开，或只作为已证的语法checkpoint；原CutsOk
证明Covered(cN)，不能因此跳过其tau失败叶或产品内部几何。

因此最短的新接口是一个syntax view/导航器加product soundness，而非
直接把两次现有walk的非零结果相乘。导航器需验证fuel/state/end一致；
原137 packed Nat literals与WD48可以原样保留，不新增FS发现算法。

## 4. 四朝向及DBM中的实际边

统一X_i=20*32768*p_i，变量仍为实数。原正跨度(i,j)的l/u映射为
Xj-Xi<=20u、Xi-Xj<=-20l；sep边为Xr-X(r+1)<=-17*32768。
id映射(i,j)，rev映射(8-j,8-i)，prefix再加offset0、suffix加1。
必须处理四个独立chart，而非只id/id。全局反射可减少重复实例，但必须
有精确chart/root对应证明，不能用相同stream名称代替。

Ordered是四point式，不能塞入普通DBM。可在Inv保留它而在D中忽略；
这只让负cycle测试更弱，reflection仍用Inv直接矛盾。若也从Inv去掉它，
595reflection terminal便不再合法关闭，整个原半域覆盖论证就有缺口。

## 5. 为什么能省重复payload，为什么不保证能提交

撰写时父任务报告Stage B生产已PASS：11859 closed、1187 exceptions、
595 reflection，原guards/trace保持Stage A身份。其朴素73整数例外payload
579013B，已经单独超过181589B余额，不能直接复制。此为父任务的上下文
结果，本包未重算分类、未独立审B，也不把仍待独立封存的B结果列作证明。

若所有tau例外在四chart的joint DBM都不兼容，product消费者可直接从
原streams重建state，避免额外保存逐例外72端点或显式完整pair列表。
它与“逐例外pair负cycle”检查的是同一松外包可行性条件，只是允许
在较高branch发现负cycle而共享证据；不会无故获得更强数学结论。

最简source方案是固定的确定性递归+DBM检测，无额外product决策数据；
数学soundness只用整数运算和既有actual checker，错误检测返回false。
但确定性探索可能很慢。另一实现可由不可信elaborator产生branch顺序/
cycle witness，再由小checker/kernel核验；仍不允许native_decide或外部
文件，生成和校验时间都算网站预算。没有这条路径的实现或资源证据。

语法上的最坏范围是四朝向48*48 root组合及近4*13046^2 terminal组合；
若Stage B分类被单独证明并共享，剩余numeric失败对范围降到4*1187^2。
这些都是保守规模表达式，不是已执行的pair数量或时间记录。同步遍历
并不会自动避免这个乘积。一次10vertex Floyd闭包约千级min-plus，
若每节点做一次便可能过预算。只在双失败叶查cycle、增量closure、缓存
tau成功叶可减少重复，但实际访问量、缓存正确性与Lean kernel归约代价
均未测。一个原numeric leaf在很多对侧节点重复展开mcheckGX很危险；
应让其tau成功事实只证一次并共享，不把2D遍历变成重复数值大展开。

Lean闭合证明也不应是一个巨型decide term。可按原root/已证子树分aux
theorem共享；分块能控制内存，却不自动把总ordinary/export/Nano时间
压进3200s。旧W10 OOM/大耗时只能提示风险，不能当本优化source的全树
benchmark，也不能因新源网站已接受就假定额外product工作免费。

当前baseline 1,818,411B，余额181,589B。旧三桥38,361B只是迁移参考；
新增syntax/product/DBM soundness、tau分类共享、WCert10/计数/wrapper
全部真实bytes尚未知。若无需新增大product数据，source有现实省项；
若需要大量schedule/end/cycle缓存，仍可能超过余额。必须在数学机会关
真正关闭后，再测实际单文件bytes、所有新有限义务和整个3200s链路。
本静态意见支持“保留原streams的整体交付设计”，不授权新压缩族或编译。
