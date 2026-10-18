# F 仅准备：原pair1/5的155行精确LP，尚无模型或求解

本目录没有执行模型加载、FS代入或求解。root先完成sync32，再另作书面
决定。本包不是执行授权，默认主脚本只打印prepared状态，不import Sympy。

固定对象为E首次underpaid pair，exceptions1/5、id/id。只在新gate后
从两原FS/state重新生成68项beta/sigma，不能沿用D另一pair0/1的数值。
复用的D代码只调用其冻结纯函数，带原L0/points/mix/flow/printed margin
检查。旧E点仅作为已存在的代数一致性核对点，不能当F的feasible point：
它违反两条新增真实Ordered。

行集恰为原153DBM+两条四point：prefix X1+X7-X0-X8<=0，suffix
X2+X8-X1-X9<=0。保持原完整state/153edge编号，153/154为新增order。
X_i=20*32768*p_i仍实数，X0=0。sep链已经给Xi>=i*17*32768>0，
故Sympy的x>=0不缩域；不能以这一隐含域掩盖遗漏约束。

目标为C+b*X=2*SA*kappa*(A_L+A_R)，target=4*kappa*cNum。
C、b由Fraction表达式确认整数，并交叉核原自然数式：每term的constant
为2Q*a*mvT+20a*(mcpT-mcnT-(mslT-2DmwT)*L0)，gap coefficient
为DR*b_r+sum a*(mslT-2DmwT)。这里b_r指原pressure raw numerator，
不是最终position objective vector。9gap转10position必须sum b=0。

主算法固定Sympy1.14.0的_simplex(A,rhs,[b1..b9])，无float后备。
安装源simplex.py共35276B，SHA
a5e46fe38683337d14ff4c24f3166fdede8cfdca66fdaf610402e2cabef39dd6。
API为_simplex(A,B,C,D=None,dual=False)，文档dual符号与真正所需
证书不一致。因此不信任doc/status，直接验returned mu>=0、全10维
b+sum mu*a=0、C-sum mu*d=C+o，全部155条primal及Xi严格正。
Python字面0和Sympy Rational分开处理；任何Float返回均拒绝。
原始o/x/y先以字符串durable，再做exact检查，避免输出失败丢失唯一call。

只有一次primary call。若它报告InfeasibleLPError，未获额外gate时只能
保存未确认infeasible，不能声称Empty。未来gate可明确授权一个条件
auxiliary call（maxcalls=2）：仅在该异常后求lambda>=0、A^Tlambda=0、
d*lambda<=-1、objective0。用9坐标的两边等式18行加cost一行，155变量；
最后对完整10坐标balance和strict negative cost复核。清分母后输出非负
整数Farkas。不因条件未触发而换算法、pair或参数。

返回证书之一：Empty（完整行加权0<0）；Lower（mu非负、完整balance、
lower>=target）；Below（q>0的十个整数位置，逐155行通过且model<target）。
Lower/Empty只关这一个pair，不处理其他数百万pair；Below只否定固定
affine模型，不是actual能量反例。<=9/10支持是一般LP存在/体积性质，
不是forest或整数amount保证；实际输出支持更多仍可exact验证，不裁剪。

运行前需要新gate含primary_simplex_calls_authorized=1、
conditional_farkas_calls_authorized=0或1、max_simplex_calls、E生产/独审
manifest、静态5647…manifest、pair/目标c/SA和root确定的资源上限。
launcher最多一个child，外部deadline/输出cap，只终止自有PID；超限未决
且不重试。源码只读审查显示内部没有时间/iteration cap，故不能用
文件小或理性exact来承诺运行必过网站预算。当前没有任何benchmark。

verify_certificate.py只做相对保存模型的纯stdlib证书算术，不import
生产器/Sympy。source FS、actual line及model原始重建仍需另一代理独审。
本准备不运行该checker，也不生成网站proofbatch、Lean或新纪录结论。
