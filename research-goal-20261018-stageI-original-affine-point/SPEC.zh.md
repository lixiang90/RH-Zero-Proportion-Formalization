# I Phase1：唯一原 FS / 原点必要关（准备版）

root完成macro004后只授权实现准备；本目录没有执行FS提取、点值代入、
模型配置、parser、矩阵、LP、核或Lean。执行须另有不可变rootgate。
producer与launcher只用stdlib；frozen parser/math仅在真实gate之后导入。
准备阶段只ast.parse与字节hash，不import/eval任何producer函数。

## 唯一固定输入

profile为上游原s1R source，SHA f82a4914...a736cf，c9N保持原值。
目标Nc=893766123055294719，SA=10^20；不改c/tau/核或原FS。
只用G sample2417（prefix0/suffix604、id/rev）的原X，sampleSHA
a3349919ca3c07c71346a6a753396b8daa211c5e5492299cdaf300198fbf2689。
X_scale=20*32768。G/H独审已核其原153边及两Ordered均满足。

只读原B记录与A事件已定位如下（这些不是本目录的新FS提取）：

| cell | WD/root | original path | leaf pos / payload pos | end | payload bits |
|---|---|---|---|---|---|
| 0 | 0 | r00000000000000000110 | 1460 / 1462 | 1832 | 370 |
| 604 | 32 | r00000000000000100001000 | 3126 / 3128 | 3470 | 342 |

state SHA分别d2733ed2...259b、ab644cd5...c00。完整state、原packed与semantic
SHA均在producer FIXED_CELLS中逐字固定。原B/A/G identities全部相等。
原source137packed literals/48WD/70nested cuts由已冻结parser保持；不得
从一个tightened/reflected/joint state重解码anchors或估计right child长度。

## 最小函数与交叉核

`locate_original_payload(cell,model,math,traces)`复制并适配旧D:86–107。
从原root索引起，沿原A branch axis/mode/cut和真实left/right cursor到叶，
核原stateSHA、完整state、numeric/reflection guards、end；不接测试点。

`extract_original_affine(cell,...)`不接X/chart/offset，只用原L/U/L0、FS、
PT/lb。原p/r是固定tangent anchors，不能与测试物理点混淆。保留34term
全部质量（含constant部分），核active mokI/PT域、混合质量1024、原flow、
consumed bits、packed/semantic SHA、compact与printed AST原margin相同。
只提取这两个原叶，不遍历或评价其他叶的FS。parser解包原137文字量
不是重新发现FS，也不查询新核数据。

Q=32768,R=1024,D=10^9,V=10^10,kappa=QVR,K=kappa*SA。
delta_e=mslT-2D*mwT，所有差为signed。输出canonical_J是

    J_r=DR*BS_r+sum_{e:r in e} a_e*delta_e,
    Cstar=Q*sum a_e*mvT+10*sum a_e*(mcpT-mcnT-delta_e*L0_e).

必须与独立的Fraction形式
beta=mvT/(VR)+(mcpT-mcnT)/(QDR)-delta*L0/(QDR)、sigma=delta/(DR)
逐项/整体一致，故K*A=Cstar+10Q*sum J_r*g_r。不得把另一命名中的10J
与本canonical_J混用，也不得将原flow再次加入raw A。

`embed_and_evaluate`才接原X：左id r→r；右rev r→1+7-r。逐原span验证
membership，pressure和全部β+σs求和；同时核

    2K*A_window=2Cstar+sum_r J_r*(X_{mapped(r)+1}-X_{mapped(r)}).

逐项scaled numerator另核原Q*mv+10(cp-cn)+10delta(Qs-L0)，原flow在同点
的线性付款和certified floor也核回原margin。原L/U/L0/PT不随反射改变。
这些有限有理检查不替代将来的actual Lean薄lemma。

`original155`从原states/PR独立生成两窗144边+9sep+两真实Order，右窗
反射span(i,j)→(1+8-j,1+8-i)，Order也取负；逐行核原X的lhs<=rhs。
闭边界合法，不使用整数gap取整，不新增cuts。

joint Jphys先合并，再取C=2(CstarL+CstarR)、b为Jphys的十坐标divergence。
核sum b=0、C+bX=两窗twice_K_value之和=2K*(A_L+A_R)。最后只算

    Delta=C+bX-4*kappa*Nc,
    A_L+A_R-2c=Delta/(2K).

## 解释与停止

若Delta<0，这个原域内真实可行的固定点使同一两份faithful affine模型
不可能统一达到目标；停止这个固定family，不能换dual/basis/精度/anchor
重试。它不是actualF低于目标，也不是零点比例反例。actual核未评价。
Delta>=0只是不否决该点，不能自动启动15378全域basis族或宣布jointfloor。
无论符号如何，Phase2授权固定false，matrix/LP/Lean计数0。

旧F pair1/5/global4768已由H归为Empty，其成功Lower不能作为可行残余
能量增益的证据。node-Mi压缩已有覆盖也不能抬高本固定点raw A。

## 一次执行/输出合同

CLI模板（未运行）：

```text
C:/Python314/python.exe research-goal-20261018-stageI-original-affine-point/run_once.py --launch-authorized-I-point --gate <root不可变gate相对路径> --gate-sha256 <完整SHA256>
```

rootgate字段见required-gate-fields.json；其中prepared SHA在本准备包
源码最后冻结后填入。wrapper最多一个child，child/parent同为60s/8MB；
资源到限=inconclusive，异常和stage/traceback原样保存，不改参数重试。
input所有SHA起止核相同；launch/child/started/stdout/stderr/terminal保留。
独审由另一owner执行，不能import此producer；它不是producer数学输入，
不阻断本次准备。独审源码/运行由后续另一gate单独固定，数学结论仍需
独审通过，不能用本producer自检代替。

`result.json`顶层含inputs起止、windows[2]、domain_check.rows[155]、joint。
每window含canonical Cstar/J、原34terms/guards/FS与语义身份、反射映射、
Fraction点值、twice_K_value。joint含C/b/Jphys/原X/target/Delta及其Fraction
等式、obstructed布尔。failed/inconclusive不伪装成功，不抹去failure。

本准备只解决可审查的实现输入与数学身份；没有任何新有限计算结果。
原actual affine薄lemma、全域product覆盖、网站2MB/3200s、独立内核与
新κ均未完成。prepared manifest不是执行授权或网站提交材料。
