# 更强备选：原联合仿射边界与累计势函数结合（仅符号）

K发现的9边负环只排除原Mi给出的scalar外包图势函数。它不排除用原joint
affine在原155行域上的有效Lower加强边权。本说明不执行FS/矩阵/图或q搜索，
也不宣称加强后不存在负环；只保留将来J原固定basis已有计算的全部有效信息。

记k=kappa*SA，d0=kappa*(Nc-N9)，T=4*kappa*Nc。对cell i/j、固定chart，
I的C+bX=2k*(A_i+A_j)，且A_i<=F_i。若J固定basis得到整数n>=0和d=absdet>0，
并精确核全十坐标d*b+sum n_r*a_r=0，则原155行给

    N=d*C-sum n_r*rhs_r,
    2k*(F_i+F_j) >= N/d.

这个Lower即使N<d*T也有效，不应只因未达到每pair统一目标而丢弃。
原scalar证书另外给2k*(F_i+F_j-2c)>=2*(Mi+Mj-2d0)。

固定normal的小minor纸面界与实际det核验若给d in {1,2,3,4}，12/d是整数。
令每条允许边a->b的整权为

    W_ab=max(24*(Ma+Mb-2d0), (12/d)*(N-d*T))

（无有效dual时只取第一项）。由此原实际能量满足

    F_a+F_b-2c >= W_ab/(24k).

G paid边只需第一项；严格Empty的G/H边可删除；H保守未解边即使没有J成功
也要保留baseline。star取形式能量tau、Mstar=2d0，所有star边用W_star,a=
W_a,star=24Ma。不能把真实有向转移反射成无向边。

若将来找到整数Qstar=0且每条允许边满足

    Q_b-Q_a <= W_ab,

沿star,a0,...,a(L-1),star把实际pair inequalities相加，就有

    2*sum F_r+2*tau-2*(L+1)*c >= 0,
    sum F_r >= L*c-(tau-c).

这里直接对pair能量相消，不可将加强后的W擅自代回旧Phi=(q-M+2d0)/(2k)
的单窗推导。单对F_i+F_j<2c并不自动否定此累计结论。可按独立静态说明
保守接ActualDefectEstimate Z10 cB，而band及压力容量仍使用W9。

## 未来可核查的发现/验收接口

J目前仅准备同一固定basis族。保留有效但below-target的N/d不增加求解次数、
改变anchors或目标；它可为上述不同累计模型提供将来J逐项核过的边界输入。
若K原9边环在全部有效J加强后仍严格负，该环会立即否定此固定加强模型，
不应直接开全图potential求解。只有这个必要关不否决才考虑完整Q。
当前没有执行此加强模型的gate。

paid边是隐式稠密族，但其权为可分离的24*(Ma+Mb-2d0)，且Ma+Mb>=2d0。
对一个给定距离向量D，每个目标b的paid放松可用

    D_b <= 24*(Mb-2d0)+min_{a:Ma>=2d0-Mb}(D_a+24Ma)

通过按原M排序后的suffix minimum一次构造；其余15378条边稀疏处理，
star约束是-24Ma<=Q_a<=24Ma。由此有固定有限差分算法的可能，不需浮点LP。
source须遍历全部2374个有向标签；同Mi的id/rev仍各自保留D。eligible空集
的minimum取正无穷，不产生放松。同步算法应令Dnew_b=min(Dold_b,RHS)，
并明确所有RHS从同一Dold取值，不混用未声明的顺序更新。
这里没有运行该算法、构造任何Q或验证复杂度/实际时限。若将来执行，需
独立核全部paid、sparse及star约束，而不能只核K那9条环。

最终Lean不能信Python的Q存在声明：须从原state/FS重建每个用到的affine
Lower，核正权/全balance/cost、全部转移的几何或能量覆盖及整段累计桥。
原source余181589B仍要容纳数据、decoder、这些证明、counting/wrapper与
两个固定陈述；整体普通Lean/导出/nanoda仍须通过3200秒政策。没有任何
新globalfloor、无条件比例或可提交源码的完成声明。
