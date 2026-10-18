# 固定F合同：两Ordered行加联合affine LP的静态审查

只纸面；没有执行F/LP、代入pair、核查询、优化或Lean。固定对象是E首先
遇到的underpaid pair id/id、exceptions 1/5，不能沿用D另一pair的数值C/b。
实际开跑前须从这两个原FS/state按冻结公式重建C/b并绑定hash/原semantic
身份；本包不重建或读取其数值。只审查合同与证书的数学可靠性。

## 1. 行、坐标、目标与符号

X_i=20*32768*p_i取实数。153条原DBM均为a_k dot X<=d_k，
a=e_v-e_u；再加prefix ordered行
(-1,+1,0,0,0,0,0,+1,-1,0) dot X<=0，
suffix ordered行
(0,-1,+1,0,0,0,0,0,+1,-1) dot X<=0。
这两行对应id/id，符号正确。其他朝向不能直接复用同一符号；本F只固定
当前id/id pair，不扩family。总155行，不把Ordered假装为DBM edge。

全部row的系数和为0，objective b也须精确sum b=0，可设X0=0消平移，
剩9个实变量。前包已给精确整数缩放

  2*SA*kappa*(A_L+A_R)=C+b dot X，
  target=4*kappa*Nc，Nc=893766123055294719。

此处Nc是候选平均floor的scaled numerator；不是原c9N=893616123055294719。
固定两原FS的line有效域仍是完整原states，不因加入order而改L0/points。

若lambda_k>=0、sum lambda_k*a_k=0、sum lambda_k*d_k<0，
则相加所有真实行得到0<0，这是empty的正确Farkas符号。

若mu_k>=0、b+sum mu_k*a_k=0，则
b dot X>=-sum mu_k*d_k，故C-sum mu_k*d_k>=target为正确lower dual。
这两种certificate都不需要信任优化器最优性。不得把a系数balance反号，
也不能把upper-row的cost误加到C。

## 2. 有界性与稀疏断言的正确前提

两个原完整cell各给正跨度双向有限上下界，union覆盖十vertex且连通，
所以设置X0=0后各Xi有上下界；155row的可行域是这个紧DBM域与两闭半
空间的交。若非空则仍紧，linear minimum有限且达到；否则为空，不存在
数学上真正的unbounded分支。solver报告unbounded应标输入/状态未确认，
不能据此得能量结论。

固定9维有理LP非空时，若最优值>=target，存在一个达到最优的非负dual，
其positive support可选<=rank<=9个active rows。可从最优点active行的
normal cone作conic Caratheodory，或从dual basic feasible optimum得到。
这是存在结论，不是浮点输出自动有9项，也不允许任意截掉小权保持margin。
若某个较稠密exact dual本身已过checker，也sound；稀疏性是体积设计而非
正确性前提。强对偶/存在性不用在最终Lean里作为optimizer可靠性假设。

若155row系统不可行，Farkas可选<=10行支持：消X0后系数维数9，
用augmented (a,d)的10维conic表示，或9维Helly/minimal positive circuit。
若实际rank更低还可更少；同样不能用未验证的float稀疏化冒充exact证据。

加入Ordered后矩阵不再只是graph incidence。<=9支持不等于forest；
original <=9edge forest/Pruefer/leaf-supply decoder不能直接套这些rows。
dual权重一般为有理数，不能预设整数或network total-unimodularity。
若最终支持恰都在纯DBM子图，可用其原有flow结构；仍须核完整balance/cost。

## 3. 三种最小可核验输出

Empty：<=10个row IDs和非负整数weights n_k，逐完整十坐标核
sum n_k*a_k=0及sum n_k*d_k<0。任何有理Farkas witness可清正分母为
此整数格式；不必固定normalization。cost严格负已排除全零weights。

Lower：<=9个row IDs、正共同分母K、非负整数weights n_k，核
K*b+sum n_k*a_k=0，K*C-sum n_k*d_k>=K*target。
它直接证明C+bX>=target；等于target可通过。若有更多支持而同样exact
通过也有效。系数完整十坐标检查可避免错误处理X0 gauge；若只检查9项，
必须另严格核所有row和b的translation invariance。

Below：共同正分母q、signed integer z0..z9且z0=0，核全部155条
a_k dot z<=q*d_k，并核q*C+b dot z<q*target。此为lower-model value
低于目标的真正有理可行点，不必达到minimum。它否定的是这个固定两FS
联合affine模型的全域目标，绝不说明实际E_L+E_R<2c。
前包证明原cell上A_i>=c9，所以该点的baseline clipping仍等于A_i。

所有rows都必须从原两states/映射/sep/order定义重新构建；不能只验证LP
压缩后留存的active rows而漏其余约束。原C/E中的relaxed point两order
违例，不可直接当F的Below。需新求得并exact核155行的点才可报告Below。

## 4. 输出解释、预算与scope

一次固定LP仅允许按预声明方案输出上述证书或inconclusive。float status/
objective/residual本身不是数学判据；无法exact恢复certificate就是未决，
不自动换算法/精度/约束/模型retry。恰好等于目标时，近似误差不能当严格
Below，也不能在没有exact dual时标Lower。

Empty或Lower都只关闭这一个原pair/chart，不完成全5,635,876组合覆盖。
后续若考虑全域方案，仍需给全部underpaid pairs的完整覆盖和真实资源预算。
Below也只是必要机会关失败，不是ζ比例反例，更不是原baseline失效。

对单个成功closure，row IDs+少量大整数/共同分母是合理小certificate；
原rows可由stream states重建，避免复制155个十维vectors。新consumer
只需有限行非负加权与exact arithmetic，不必证明LP optimality。不过完整
actual line/域桥、状态导航、pair覆盖、counting及source2MB/全链3200s
仍未知。当前不能因<=9/10支持就宣布整体可提交，也不启动proofbatch。
