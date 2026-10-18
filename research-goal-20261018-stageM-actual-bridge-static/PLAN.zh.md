# M 的当前 s1R 实际 Lean 局部桥：下一单次 formal gate 计划

本包只读源码与已有 M 证据。没有新 Lean 源、编译、FS/核/点/矩阵/solver/RREF 或新数学数值计算；字节/行布局统计不是证书重算。现有 M 独审已通过：manifest `2887e7527180ca2b77d7779cd5c25ada853d040e82d0380a125f7f821c907be4`，receipt `13d73403029aa10b1f6e598919f1ce5c231a541516854601773f1f796c3f52a0`。其范围为固定 cell0/604、id/rev、279行、68个正权 term、77个原 LP变量、78个 full dual坐标，不能误称68个 anchor均为 active。

## 1. 下一条要证明的实际定理

对任意十个真实物理位置 P（不假设有理/整数，也不必P0=0），令 h_r=P_(r+1)-P_r。固定域为：

1. `(h0,...,h7)` 属于原 cell0；
2. `(h8,...,h1)` 属于原 cell604（原 suffix 的 canonical反序）；
3. 原两 Ordered 条件，按 id/rev 分别取正/负四点 normal；
4. 九个 h_r≥17/20，保留原 M 的155行。

在此域证明当前 `AMW.Cert.PC9QB6M.G h0 ... h7 + AMW.Cert.PC9QB6M.G h1 ... h8 >= 2*Nc/SA`，`Nc=893766123055294719`、`SA=10^20`。必须使用新名字 Nc，避免误用原 `PC9QB6M.cN=893616123055294719`。

九条 sep 不能静默删除；若要把外观缩成“原cell范围/Ordered”，还须另证明这些 literal下界蕴含sep（本轮未作此算术）。只证该实际局部不等式，不需要现在证明两cell在原树的可达性；原 B 的 cursor/state/FS 哈希身份及 I 非空点虽已独立重放，尚不是 Lean 全树导航证明。后者是后续全域 product-cover 的独立义务。

## 2. 必须依赖的当前实际源，禁止替换 profile

唯一实际源是快照 `research-goal-20261018-record-source-audit/snapshot/Solution.lean`，1,818,411B，SHA `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`，上游 commit `cfc7ce6113199b7d5f262812d81089778e84335c`。这是当前13含常数项系数 s1R，不能 import 旧 W10 Core/LeanCoverBase、`WindowGapEnergy` 或旧24mode `WindowKernel` 冒充同一实际 w。

当前真实命名空间/API：

| 用途 | 已有实际 API / 行号 |
|---|---|
| 同一函数别名与全局非负 | `AMW.Cert.wfun/w1/w2` 7613--7615；`wfun_nonneg`7618 |
| 全闭区间常量下界 | `AMW.Cert.Pyr.LBSound`8133；`AMW.Cert.PC9QB6MData.lbS`12279 |
| 原量化点/导数/切线 | `AMW.Cert.PyrD.TVal`9769--9773 |
| 有效interval到TVal | `AMW.Cert.PCell.ivIn`10540；`tval_of_ivIn`10543--10550 |
| 当前全部点表实际声音性 | `AMW.Cert.PC9QB6MData.ptS`12407，结论`∀x,PVI x(PT x)` |
| 原cell与term实际范围 | `AMW.Cert.PCell.InCell/gsum`9075--9084；`term_range`9365起 |
| 同一正权 ledger实际展开 | `AMW.Cert.PCell.Fg`9357；`PC9QB6M.Fg_G`10648--10650 |
| suffix实际反序 | `AMW.Cert.PC9QB6M_G_rev`14293--14294 |

表的依赖已在当前源中封闭：`lbS`由TOP/BK及block/top guards给出；`ptS`由TOPD/BKD、REG、PTT0..7 finite checks给出。不能仅把 Python I/M 的整数检查当成这些 Lean 解析命题已在本地重放。

## 3. 第一个新增小lemma：量化独立组件≤actual w

新增 lemma直接参数化**当前** `PyrD.TVal f L U p`，不参数化成一个没实例化的任意F oracle。前提为原`L0≤L`和`s∈[L/SC,U/SC]`；写所有减法为 cast 后的有符号实数减法：

`v=lo32(f p)/V`，`dlo=(lo32(hi32(f p))-2D)/D`，`dhi=(2D-hi32(hi32(f p)))/D`。

结论 `v+dlo*(s-L0/Q)-dhi*(p/Q-L0/Q) ≤ AMW.Cert.wfun s`。

证明只拆 TVal：真实 `dp=w1(p/Q)` 满足dlo≤dp≤dhi，且量化值的真实 tangent≤w。差额为

`(dp-dlo)*(s-L0/Q)+(dhi-dp)*(p/Q-L0/Q)≥0`。

用两个`mul_nonneg`和一次局部ring/linarith即可；无需新导数/曲率、Taylor、anchor、积分或采样。原`mtermTI`只封装固定1024质量的混合，不直接提供任意M dual的独立组件；不应重用它替代此thinlemma。

常量组件无需新解析证明：从`lbS L Uc s`与原`U≤Uc=max(L+1,U)`直接得`lb/V≤w(s)`，无论原lc是否为0。原0质量anchor仍不能启用。

## 4. 真实 PT word 与 Python compressed entry 的桥

这是必须显式完成的有限接线：Python `PTraw[p]`是PTT叶中的压缩项，bits96..115为relative lower offset、bits116..为relative upper offset，不能把该word直接传给实际`ivIn`。

实际源 `PCell.pwD`11203--11205把它展开为

`trip raw + ((p-((raw>>96)&(2^20-1)))<<96) + ((p+(raw>>116))<<120)`。

真正 `PT p`由`ptGetD PTT p`11241及12406取得；真正`ivA`用24bits96..119、`ivB`从120起读取。下一formal源应对每个需要的anchor缓存一次 `PT p = pwD p raw`（或直接证明`ivIn (PT p) L U p=true`）的普通kernel Nat等式，再从`ptS`及`tval_of_ivIn`得到当前 actual `TVal (tf PT) L U p`。low96的trip及v/mid/high字段也需同一有限等式绑定。无需重证整表或重算实际核值。

同理，选中constant行的`lb TOP BK L Uc`可缓存一次literal等式，避免78列balance归约中重复展开BK。只对非零dual行准备数值aux，未选行可由zero extension省去。所有这些是新 finite Lean义务，当前Python独审不会自动生成 Lean proof。

## 5. 整数稀疏 dual 消费者，不用279行巨型nlinarith

令`X_v=20Q*P_v`，`T_e=kappa*wfun(actualspan_e)`，`kappa=QVR`。直接使用已独审的 full78 balance，所以不需要在actual定理加P0=0；LP里的gauge仅用于discovery。

每个选中组件的真实row由第3、4节给出：constant `-T≤-QR*lb`；anchor `S*spanX-T≤-E`，其中`S=512*dloN`、`E=QRv-10R(dloN*L0+dhiN*(p-L0))`。geometry行由两原`InCell`、sep和两Ordered给出。row descriptor应从这些定义构造，不接受“任意literal矩阵与actual row相等”的未证假设。

新泛型有限和 lemma只要 `mu≥0`、每个选中row `A_i·z≤d_i`、`c+Σmu_i A_i=0`，即可由`sum_le_sum`、`sum_comm`和`sum_mul`推出 `-Σmu_i d_i≤c·z`。该lemma不信优化器最优性、不信decoder算法；不把Ordered假装成flowedge。旧纯Mathlib模块 `StructuralGoal20261016.AffineFlowCertificate` 可参考其 finite-sum证明风格，不能使用任何带旧实际kernel import 的模块。

实际exact certificate可用单个正整数commonDen D和非负整数n_i，普通kernel checker核：

- D>0及row IDs/类型/原guard身份；
- 全78列 `D*c_j+Σn_i*A_ij=0`；
- `D*target+Σn_i*d_i≤0`，target=4*kappa*Nc。

这避免所有Rat字段反复GCD，也避免让nlinarith一次消去279×78个项。候选D/n由现有exact dual机械导出即可，转换仍须另行授权且此轮未计算。可按≤8列一个独立aux check，再最后组合，沿既有per-aux内核内存经验，不开大批。

原dualmass消元已保证每个T列sum=native目标2a的关系，但actual消费应再次核原 full78整数balance，不信保存的scaled/native支持。raw新matrix含slope512*dloN，不适用旧det≤4。

实际raw objective恒等式是 `c·z=2*kappa*SA*(G(h0..h7)+G(h1..h8))`。先用当前`Fg_G`把ledger有限和连接actual G，suffix用当前`PC9QB6M_G_rev`；然后除正数2*kappa*SA。不得再次加入原I Cstar/J、flow、Mi，它们只用于旧混合身份检查，不是M目标的额外付款。

## 6. 可执行的最小源码/导入路径

**首选A：完整原单源的新副本后追加局部桥。** 原快照永不改。未来创建新候选文件，保持当前accepted正文/版权/许可原bytes，在末尾新namespace追加组件lemma、稀疏checker、固定局部数据及pair theorem。现有`lbS/ptS/Fg_G/G_rev`全部可直接用，无新增实际import；当前Mathlib/ChallengeDeps依赖仍需用网站固定版本。此文件仍只新增局部theorem，原finalκ statement不会因append自动提高。

**开发B：精确当前prefix的独立新模块。** 若本地没有当前s1R `.olean`，不能把它当已有import。可在下一gate新建合法模块名，逐字复制原源1..12407行（至ptS），保留全部版权/许可/原imports，并闭合当前`namespace AMW.Cert.PC9QB6MData`及noncomputable section；不包含后续COV/WD/13046leaf检查。反射定理14293--14294的同一body另复制并核。该prefix已经包含当前实际G及Fg_G、所有analytic/LB/PT数据，故局部桥不依赖树导航。原source-byte inventory给出prefix精确字节；本轮没有生成这个Lean模块。

本地未来可`import`这个**新当前prefix模块**，不能改成`LeanCoverBase`（import旧W10 ForcedCoverage2/FixedGeometry）或`WindowGapEnergy/WindowBoundedMomentFarkas`（沿旧24mode链）。目前未找到/未假设该当前prefix已编译；首次prefix finite table核验成本未知，不能承诺局部桥两分钟或网站总3200秒。

## 7. source与运行门槛

现有M certificate JSON仅3,695B，raw model106,051B、original-components41,927B是研究证据，不应直接复制全部进Lean。最终局部数据只需两cell144界、原68个term的组件选择/anchor引用（PT已有）、稀疏非零dual权或其可核解码提示；raw matrix/LP/primal/scaled floats均可去掉。构造支持含68base加9extra/geo未知，故非零候选行不超过77；不需279行全部复制为78列矩阵。

工程预算建议先限**新追加部分≤80KB**（包含所有literal、checker、proof text），不是已测保证。baseline headroom为181,589B；单个local bridge有实际尺寸空间。下一gate应先生成最终单文件、查实际bytecount，再仅核这一个局部consumer及其当前prefix依赖。通过后普通`#print axioms`用fullyqualified名字审计实际根（component、checker sound、pair lower），只允许标准axioms；随后是否export/Nanoda须根部单独排期。不得把本轮计划计为新proof数。

可选后续源码压缩仅是纸面方向：extra列=(S_extra-S_base)*span incidence，非零差可吸收进gamma，归一后只剩incidence/最多2Order，旧smallminor≤4可用于**归一**basis。原raw μ可能有大分母；只有最后原full78/非负/base质量/cost checker才是证据。当前没有在M数据上构造此decoder、取det、计算新权或预算，不能据此称source/time成功。

成功标准仍是**实际局部pair lower**，不是全域κ。后续剩余约束：原tree到literalcell的Lean导航、四chart及全部余项、单边非exception的tau+c9付款、root外/shortpair/计数、完整source和两内核总时间。独立M成功不免除这些门槛，也不自动授权扩大family或编译。
