# 固定两FS模型的全域交付合同与小证书结构

本包为纸面设计；不执行G、统计扫描、LP、核查询或Lean。固定source/核、
tau、c、sep、B例外和原FS均不改。父任务的新size审计给underpaid
3,527,184、paid 2,108,692个orientation-pairs；本包引用冻结审计，不重算。
两者总范围仍是1187*1187*4=5,635,876。

## 1. 合法dual不要求同次primal合法

F运行的某个primal不满足155rows，只能否定那份primal见证。若独审从原
source/state/FS重建相同C/b/155rows，另有exact非负mu满足
b+sum mu*a=0且C-sum mu*d>=target，则这份dual独立证明Lower。
它不需要可行primal、互补松弛、solver的optimal status或残差阈值。
可如实同时报告primal_valid=false、dual_lower_valid=true，不能把原guard
失败改写为整次solver验证成功。此Lower仍只关闭它对应的pair/chart。

## 2. 未来完整全域数学checker的闭合规则

固定c9N=893616123055294719、tauN=893916123055294719、
Nc=893766123055294719、SA=10^20、kappa=335544320000000000、sep=17/20。
目标为E_L+E_R>=2*Nc/SA。完整覆盖依旧使用B的任意sep sublevel外包、
原c9全非负baseline、四独立朝向、根外分离压力和原stream导航。

对每个覆盖pair/chart，允许以下真实证书：

- 一侧>=tau且另一侧原>=c9；或者两侧原Mi+Mj>=kappa*(tauN-c9N)。
- 原153DBM的严格负cycle，包括28共同span的严格disjoint两edge cycle。
- 加两Ordered后155row的Empty：lambda>=0，sum lambda*a=0，sum lambda*d<0。
- 同155row的Lower：mu>=0，b+sum mu*a=0，C-sum mu*d>=4*kappa*Nc；
  C/b必须是原两FS的2*SA*kappa*(A_L+A_R)准确系数，不能沿用另一pair。

actual source接口、signed/Nat与原Mi whole-cell证明见既有flow-proof；
Ordered不是DBM edge。反射terminal仅与所选Ordered矛盾，不独自付款。
每个certificate只在两原FS合法的原states及该chart内使用，joint state
不得回喂原points/cursor解码。没有新FS或新kernel评价。

所有pair/chart都被上述规则覆盖，才推出separated平均floor；再接实际
WCert10、matching/counting和网站statement。单个F Lower或Empty不是全域
证明。Exact Below点只否定当前固定两FS affine模型，不是实际能量反例。

## 3. 建议的下一机会关只做完整cheap分类，不自动求批量LP

若root以后书面授权，固定一次完整scalar-paid+strict-projection/DBM-cycle
分类可以不在首个相容pair停止：遍历完整固定顺序，输出paid、projection、
other-negative-cycle、unresolved的准确数量。此阶段不新增LP或核值。
完成时四类互斥且计数和等于5,635,876；timeout/资源guard则仅是有效prefix，
标inconclusive，不能把尚未处理者算通过。已知单个F证书可另标记，但若
要计入closed类别，需开跑前显式绑定它的独审清单，不能事后改统计模型。

全局index固定为((i*1187+j)*4+chart)。可只存unresolved bitmap、计数和
完成prefix，不复制每个pair的geometry/FS/矩阵。全范围bitmap为704,485B；
若只在确定性underpaid顺序编号，bitmap为440,898B，映射由原Mi付款规则
重建。这些是审计artifact，不能因为小于20MB就声称可作为网站source；
两个bitmap本身仍各超过当前181,589B source余额。未完成时0bit不代表已排除。

该机会关若得到少量unresolved，才有依据评估剩余小证书路径；若仍巨大，
不能自动开数百万LP。没有此执行授权，本包也没有生成或更新任何bitmap。

## 4. 固定155normal的small-minor结构

每个chart有固定155个未缩放的integer normal：153个graph incidence
e_v-e_u，加至多两个Order normal。每个Order是两个incidence row之差，
例如prefix为(e1-e0)-(e8-e7)，suffix为(e2-e1)-(e9-e8)，rev时整体反号。
只有rhs和FS objective C/b随cell变。删X0 gauge后有9列。

任k*k square minor若含r<=2个Order rows，沿这些rows多线性展开为最多
2^r个signed incidence minors。incidence matrix全幺模，各项为0/±1，
故任square minor绝对值<=2^r<=4。此论证要求原±1 normal normalization。
solver即使为数值目的做正row scaling，也必须还原到此原normal；能量row、
额外sidecondition或改变normal normalization后，不直接继承这个界。

本矩阵整体rank9（原adjacent双向差分含一个spanning-chain basis）。
这不表示任意选的9rows独立，更不表示F返回的9positive supports已经fullrank。

## 5. Lower的9row-ID decoder条件

若选择9个reduced normals构成fullrank basis B，则其纯DBM rows是独立
incidence rows，作为undirected multigraph必为forest；含Order的整个basis
不称forest。delta=det(B)非零且abs(delta)<=4。实际解为

  B^T*mu=-b_reduced，

不能漏transpose。Cramer或forest消元+至多2*2 Order系统可从整数b重建mu；
每个mu分母整除delta，numerator大小无界。给rowIDs即可重建，不必逐pair
复制大mu。完整检查仍须：IDs<155、basis有效或明确失败处理、mu>=0、
full十坐标balance及exact cost。decoder算法错只允许checker false；最终
soundness不需信任decoder，也不需证明它找到最优basis。

有非空且finite optimum的9维LP可选support<=9的最优dual BFS；选定独立
support可补零扩成basis，但不能无依据把任意valid dual删减/换cost。
某已给support不fullrank时，应保留显式有理vector作另证/另核例外，或
给出确实保持certificate的basis转换；不擅断所有valid dual天然是basis。
Empty分支由下面小Farkas格式处理，不借finite-optimum假设。

## 6. Empty的<=10row-ID加2bit权重

cone K={lambda>=0: A^T lambda=0}位于非负正交域，故pointed。若存在
负cost Farkas向量，可分解为极射线，至少一条射线仍负cost。其positive
support S为positive circuit，k=|S|<=10、rank(A_S)=k-1。取k-1个独立
coordinate columns，cofactors给一维kernel向量；因是完整support的circuit，
这些cofactors全非零，符号一致。每个cofactor是原normal的square minor，
绝对值<=4。除gcd并取正号，primitive integer lambda非零项均在1..4。
零normal的退化单row情况也可用lambda=1；当前原行本身均非零。

因此存在一份<=10 rowIDs及每项2bit的Empty证书，2bit明确编码lambda-1，
不是把4直接塞进两位。最终只需exact核lambda正、full balance=0及cost<0，
不必在Lean证明给定support是极射线或重新推全部minor。该小权结论只用于
Empty的155几何normal；Lower含大b时mu并不因此<=4。

独立纸面交叉审阅上下文：joint_gluing_review确认上述三结构结论，并强调
fixed normalization、fullrank selected basis、cofactor全非零和最终balance/
cost核验；没有运行数据或验证当前F支持rank。此消息不是实际closure证书。

## 7. 整体source/time仍是硬门槛

size审计的3,527,184 underpaid意味着，即使每份Lower只存9个byte级row IDs，
逐pair复制也已有9*3,527,184 bytes，尚无chart/path/命令/consumer成本。
所以basis/小circuit解决的是单证书大整数重复，不单独解决全域交付。

可复核路径仍是原两stream的product消费者：重建两原states、独立joint
DBM；paid/geometry/Empty/Lower在合适product node闭合，复用aux theorem，
不再逐pair抄72端点或完整mu。量化node floor也可由其所有非空ordered
numeric后代的min Mi沿split覆盖归纳，若左右node minima之和已过threshold，
就能关闭整块product，不需要展开每个叶pair；reflection后代在ordered域为空。
这是数学规则，不是已有统计收益。本包未求任何node minima或重用率。

一个F certificate只有在其所有使用的几何rows由更大product node原样
蕴含，且两FS line在该更大域确实合法时才可向ancestor复用；不能因为
只有9rows就假定可以自动提升。child合法tangent不可直接用于parent。

最关键停止条件：覆盖计数有缺口；原source/FS/state/cursor或normal scale
不匹配；certificate只有float状态；强Mi/line actual桥未证；预计最终单文件
超过2,000,000B；或ordinary+export+Nano+generation在3200s内没有实际证据。
现baseline1,818,411B，只剩181,589B，原网页candidate wrapper也须在新
派生bundle正确替换，不能简单append更强theorem使旧精确candidate等式冲突。

即使cheap分类unresolved=0，也不能用Python收据代替Lean全覆盖；即使
每pair证书很小，也可能因数百万BigInt/FS重建或巨proof term超时间/内存。
当前无proofbatch/批量solver/新实现授权，所有完整floor与网站提交flags仍false。
