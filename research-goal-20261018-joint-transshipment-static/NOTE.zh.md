# 联合 affine 的精确 transshipment 接口与 forest 稀疏性

纯纸面addendum：没有导入networkx/LP、代入case、计算kernel、优化或Lean。
基于joint-affine-static和joint-affine-flow-proof的固定数学定义；旧包不改。

## 1. 整数缩放确实为2*SA*kappa

Q=32768、R=1024、D=1e9、V=1e10、SA=1e20，kappa=Q*V*R。
每个原window定义signed整数

  J_r=D*R*BS_r+sum_{e:r in e} a_e*(msl_e-2D*mw_e)，
  Traw=V*R*sum BS_r*L_r+Q*sum a_e*v_e+10*sum a_e*(cp_e-cn_e)，
  Craw=Traw-10*sum_r J_r*L_r。

前包的精确展开等式去掉flow项后给

  kappa*SA*A_window(g)=Craw+10Q*sum_r J_r*g_r。

把局部J按各id/rev映射到physical九gap，左右相加为Jjoint_r，
令X_i=20Q*p_i，则

  2*SA*kappa*(A_L+A_R)=C+sum_r Jjoint_r*(X_(r+1)-X_r)
                      =C+sum_{v=0}^9 b_v*X_v，
  C=2*(Craw_L+Craw_R)，
  b_0=-Jjoint_0，b_v=Jjoint_(v-1)-Jjoint_v (1<=v<=8)，b_9=Jjoint_8。

因此C、b均为整数，sum b=0。因10/20=1/2，需要外面的2；不能漏掉。
若使用Aflow则把J换成J-P+S，并相应把Cp/Cm纳入Craw；不得只改斜率。
raw A点值更强，原flow不必预先减掉；source接口可保留两者以核尺度。

目标(A_L+A_R)/2>=c、c=Nc/SA，对应整数

  C+sum b_v*X_v >=4*kappa*Nc。

这里Nc=893766123055294719是固定候选平均floor的scaled numerator。
这不是新的数值评价，而是同一有理目标的精确清分母。

## 2. 双对偶符号与可核验lemma

153条原edge约束均按u->v表示X_v-X_u<=w_e。给mu_e>=0，若

  out_mu(v)-in_mu(v)=b_v，

则sum mu_e*(X_v-X_u)=-sum b_v*X_v<=sum mu_e*w_e。因此

  C-sum mu_e*w_e <= C+sum b_v*X_v。

若左边>=4*kappa*Nc，即得实际E_L+E_R>=A_L+A_R>=2c。
必须核exact balance、mu非负、cost和constant；优化器最优性不是lemma前提。
不能把out-in反写为in-out，也不能跟随外部flow API的demand约定不作核对。
若balance有任何残差，就需另用真实变量box支付，不能按sum b=0自动删掉。

这条lemma只需有限sum交换和每条edge的真实上界。actual连接还需前包的
per-term line soundness、原state域、九gap物理嵌入及完整cover；纯dual代数
不替代它们。ordered四point若另加入约束，则不再是仅153edge的此接口。

## 3. “存在<=9条positive edge的forest”何时成立

当前问题若只含固定b的balance和mu>=0，无arc容量上界/其他side constraints，
则是十vertex的uncapacitated transshipment。153edge来自两完整cell，
包含各正跨度的上下界，整体连通并可双向走；sum b=0使flow可行。
一个真实DBM potential排除所有负cost有向cycle，故mincost无向下无界。
等价地，给X0=0后实际difference域非空且有界，linear minimum有限。
有限维LP/网络流对偶可给有限最优flow；本包没有编译这条存在/强对偶定理。

在已经存在最优flow的前提下，forest结论可直接证明：若positive support
含undirected cycle（有向相反的两平行arc也算长度2的multigraph cycle），
沿cycle取非零signed circulation z，incidence(z)=0。所有support流量正，
故足够小的正负epsilon扰动都可行。若cost(z)非零，一方向严格改进，与
最优矛盾；故cost(z)=0。选可使一条arc恰降到0的方向与epsilon，balance
和cost保持，positive support减少。有限次后support为undirected forest。
十vertex forest最多9条positive arc（有多个component则更少）。

这不是说任意最优solver输出天然稀疏，也不是仅删除有向cycle就一定成forest。
它是存在一份同cost forest certificate。若加入arc容量上界、每term额外
质量约束、额外线性side constraints，或者b仍是未固定的优化变量，则该
9edge断言不能不加证明地沿用。fixed rational theta选择后b固定，可先
清其分母再用同一transshipment结论；不据此声明整个theta联合LP的basis形状。

当前b为整数。forest中每个component的b和必须0，每条edge的flow由删除
该edge后子树的b和（带方向符号）唯一确定，所以forest最优flow也为整数。
这可避免证明任意float optimizer给出整数flow，但仍须实际构造并核验候选。

## 4. 对source交付的实际含义与未知项

若后续确有达到目标的forest，最小建议数据可以只存<=9个原edge编号。
用b沿forest leaf消元重建mu；不必信任decoder正确，只独立核非负/balance/
整数cost threshold。若解码不匹配即false。153edge本身来自两原state及sep，
不能再将全部144 geometry端点复制给每个certificate。真实source消费者需
把edge编号绑定正确的id/rev/offset和原stream state。

<=9edge是单个成功linear certificate的support上界，不代表全product只需
一个certificate，也不证明当前任何pair有足够margin。无该certificate就
不能声称联合affine已关闭。即使每对数据小，pair数、重建/BigInt计算、
kernel/export/Nano及2MB总源码预算仍未知；当前不启动proofbatch。

下一固定potential诊断若发现A_L+A_R<2c，则任意sound dual都不可能达到
上述整数threshold，直接停止这个固定二FS affine机会关。该算术尚未获
本包执行；这里不报告某pair成功或失败，不进行新的族或参数尝试。
