# 静态备选：以窗口势函数替代每个两窗的统一下界

本说明只作符号推导，不构造图、不遍历索引、不算FS/点/矩阵/核，不运行
cycle算法/优化/Lean。它不声称现有有限图存在所需势函数，亦非新比例。
I必要关仍先执行。此备选改变全局能量不等式，允许有限低能转移，不能被
某个合法两窗点的A_left+A_right<2c自动否定。

## 固定模型

使用新s1R实际F9、原17/20分离、相同H/B和原TS/BS。令SA=10^20，
kappa=Q*V*1024，d=kappa*(Nc-N9)，其中Nc=893766123055294719，
N9=893616123055294719；c=Nc/SA，c9=N9/SA，tau=2c-c9。

B的每个闭例外cell i原margin Mi给实际F9>=c9+Mi/(kappa*SA)。Mi非负，
例外Mi<2d。为每个cell建id/rev两个标签（共2374），不合并反射；标签
共用Mi。另设标签star，Mstar=2d。对任意真实九点窗口，若F9>=tau可选star；
否则由B完整覆盖选其有序反射及原cell。边界重叠可固定任一有效选择。
选择不需要计算F9；在证明中用经典分情形与有限存在量即可。

允许边包括：所有涉及star的转移；所有原Mi+Mj>=2d的有向cell标签对；
其余只保留G/H未能证明交域Empty的有向对。G paid不能当Empty移除。
G/H原严格排除的任意真实转移确实不能出现。四chart必须按物理窗口方向
嵌入，不能因反射对称把边图变成无向图。原index=((i*1187+j)*4+chart)。

## 足够的纯整数证书

寻找有限整数q_label，q_star=0，满足每条允许有向边a->b：

    q_b-q_a <= M_a+M_b-2d.                 (P)

真实窗口label a的F9>=c9+M_a/(kappa*SA)。定义

    Phi(a)=(q_a-M_a+2d)/(2*kappa*SA).

由(P)直接得

    Phi(b)-Phi(a) <= (M_a-d)/(kappa*SA) <= F9(window_a)-c.

沿相邻窗口相消即可提高整段的平均下界，即使某些两窗平均小于c。
这利用转移序列中不可无限重复的亏损，数学上不同于统一十点floor。
更强的是所有star边也被(P)要求，因此任意L>=1个真实窗口可用
star,a0,...,a(L-1),star闭合代数链；把虚拟star的下界tau加入后消去势：

    sum_{r=0}^{L-1} F9(window_r) >= L*c-(tau-c).

这是一个与窗口数无关的端点损失，不是声称虚拟star是物理窗口。
仅使用对所有star边强加的数值不等式，故不需要其几何可实现。

## 必要停止关（尚未授权执行）

G/H残留的15378条underpaid边都有Mi+Mj-2d<0。若这些有向边中存在
有向环，沿环相加(P)立刻矛盾；可输出原index序列、各Mi/边权及严格负总和
作为这个固定scalar graph-potential模型的精确反证，无需FS/实际核或优化。
查不到该类环只通过必要关；含paid边的混合环仍可能为负，且尚未构造q。
所有涉及star边也必须保留。不存在负环才有一般差分势；必须给具体整数q
及完整边核验，不能以浮点cycle-mean数值宣称成功。

这类反证不否定实际函数、多窗更精细状态或非线性余项。若执行需另固定
gate：只读H remaining、B Mi、G四chart index，保留每条方向；限定唯一完整
DFS/SCC必要关，不自适应加状态、阈值、核或LP。当前没有该执行授权。

## 到实际零点计数的义务

source 16566 remainder_bound_n通过block_energy_band将每个九点的hCert
相加，随后只用band_close_n、pressure_le_n及offdiag/defect。若(P)成功，
应另证累计窗口下界并替换这一次求和步骤：对m点、L=m-8，能量至少
(m-8)c-(tau-c)。容量上界仍用原WCert/TS；压力总和的端点边界仍由原B控制，
不能把势函数当成可增加的压力预算。m<9要另用非负defect，并选统一有限
边界常数。matching的close pair仍需c<=1/64。最后须在块分割/渐近步骤
实际证明新增常数损失消失；不能只说O(1)而忽略每块的数量和极限顺序。

因此该路线不直接调用原需要pointwise hCert的remainder_bound_n，必须补
累计版band lemma、remainder、matching及最后极限接口。它保留同H/B，
若这些桥和(P)都成立才有(H-B)/(1-c)及超过K的条件算术结论。

源码潜力是每label一个q而非每残余pair复制dual；2375个大整数、解码器、
全部隐式paid边检查、原state标签覆盖、累计证明和两个最终陈述仍须完整计费。
不能以潜在压缩代替<=2000000B与总3200秒的实际交付验证。数学可行性未知，
无新source预算通过或kernel执行记录。
