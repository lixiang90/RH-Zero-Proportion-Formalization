# M：原 FS 组件包络的固定联合机会关（只准备）

当前只有源码/AST/字节身份准备；没有 import producer、原 parser/math 或 SciPy，没有提取 FS、评价点或核、构造矩阵/秩、运行 LP/Lean。未来须根部下一实际轮另行不可变 gate；本准备不是执行授权。独立 checker 不是 producer 输入。

## 1. 固定输入与新增信息

固定新纪录 s1R 原源、原 B cell0/604、chart=id/rev、原 FS/anchor/预认证区间、原 G2417 物理点和原155行联合几何；`cN=893766123055294719, SA=10^20`。不更改 sep=17/20、阈值、source/profile/BS/TS、cell/state/cursor、FS 质量、anchor 或有效区间。不扫描其他 pair/anchor，不作新核采样。I 正点只通过了必要关；J 的固定 basis 全范围结果及 L 的旧环负诊断都没有排除所有混合 A dual，更没有否定 actual F。

这里恢复原混合前的独立组件。对一项原 FS，令 `Q=32768,R=1024,D=10^9,V=10^10=10D,kappa=QVR`，原 `L0<=L<=U<=Uc=max(L+1,U)`，真实 span `s∈[L/Q,U/Q]`。常数 `b=lb(L,Uc)/V` 在原 `LBSound` 下始终是 actual w 的下界，即便原常量质量 lc=0。

仅对原 FS 正质量 anchor p，沿用原 PT 三元量化和 `mokI/ivIn/TVal` guards：

`v=lo32(trip), dloN=middle32(trip)-2D, dhiN=2D-high32(trip)`；`dlo=dloN/D, dhi=dhiN/D`，均为有符号减法。定义

`ell_p(s)=v/V+dlo*(s-L0/Q)-dhi*(p/Q-L0/Q)`。

原 `TVal` 给 `dlo<=d_p=w1(p/Q)<=dhi` 及 `v/V+d_p*(s-p/Q)<=w(s)`。因为 s,p/Q 均≥L0/Q，两 affine 之差为

`(d_p-dlo)*(s-L0/Q)+(dhi-d_p)*(p/Q-L0/Q)>=0`。

因此每条 active ell_p 都是 actual 下界；零质量 payload 不能衍生新 tangent。每项 `max(b,active ell_p,active ell_r)` ≥ 原非负质量和为R的凸混合 alpha。原 I 的 alpha=beta+sigma*s、Cstar/J 全身份将在未来 assembly 中重新精确核对；不把旧 flow 付款再次加入目标。这是新的 piecewise-linear 信息，不是对同一 A 换 dual。

实际解析来源为冻结 `Solution.lean` SHA `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`：LBSound 8133--8134；TVal/mterm_minV 9769--9829；tval_of_ivIn/mokI/mtermTI 10539--10614；同一实际 F9 ledger 10638--10649；实际反射定理14293。纸面组件代数尚未新编 Lean theorem；原网站 accepted 报告、A/I 独立整数重放不能代替新的 actual Lean 消费者。

## 2. 77变量整数模型

gauge X0=0，物理 `X=20Q*p`；77列按 `X1..X9,T0..T67` 排列，`T_e=kappa*w`。全77列 bounds 显式 free，不能依赖 SciPy 默认非负；组件常数和 sep 自己蕴含相关非负性。

前155行严格保留原 id/rev 图形：两窗36span各upper/lower共144行，rhs `20U,-20L`；九 sep 行 `X_r-X_(r+1)<=-17Q`；两独立朝向 Ordered 四点行rhs0。prefix offset0/id，suffix offset1/rev；原 span(i,j) 在 suffix 映为 `(1+8-j,1+8-i)`。Ordered rev 翻号，不能当成普通 DBM edge。原 state/FS/PT/L0 均在 canonical 域解码，然后才映射物理系数。

每项保留一个 constant row 及最多两 active anchor rows，最多204组件行；模型总行≤359，不执行数值以断言实际行数。

- 常数：`-T_e<=-Q*R*lb`。
- anchor：令 `E=QR*v-10R*(dloN*L0+dhiN*(p-L0))`、`S=(R/2)*dloN=512*dloN`，则 `kappa*ell=E+S*(X_j-X_i)`，行是 `S*(X_j-X_i)-T_e<=-E`。

目标没有常数项。物理 pressure 贡献是 `DR*BS` 的9gap divergence，68个 T 系数为 `2*a_e>0`。raw objective 在真实 T=kappa*w 时等于 `2*kappa*SA*(Fleft+Fright)`；目标为 `4*kappa*cN`。每项包络的原凸混合代回后，必须逐系数完全等于 I 的 `2ΣCstar+Σgamma_r(X_(r+1)-X_r)`，防止 doublecount pressure/原混合项或反射错误。

原 G2417 的同一个 X 取 `T=max原components` 后，精确核全部模型行以证明模型非空；这不是一次新点选择或 actual w 评价，不用第二次 feasibility optimization。位置域有界（X0固定、原双向 span bounds/连接保持），T 虽可向上无界，但正目标权重及有效常量行保证 minimum 有限。HiGHS status=infeasible/unbounded 单独不算证书，也不启动辅助调用。

## 3. 唯一 discovery 和数值尺度

预声明唯一 `scipy.optimize.linprog` 调用，method=`highs-ds`；presolve=true、time_limit=180s、maxiter=100000、primal/dual feasibility tolerance=1e-7、threads=1。没有 auxiliary optimization、换 basis/support、精度/参数重试、fallback solver、eigh 或扫描。线程环境只在唯一 child 内固定1。

native变量为物理位置 `y_position=X/(20Q)` 与 `y_T=T/kappa`；geometry row 除20Q、component row 除kappa；objective 除 `O=2*kappa*SA`，native目标2c。变量/row/objective尺度均为显式可逆有理数，保存为 scaling.json，不将大整数模型未经尺度转换直接丢给浮点。缩放 dual ν 对应 raw `mu_i=O*nu_i/rowScale_i`，但只使用 native μ正support提示；这些浮点值从不进入最终 exact 结论。

完整 raw77整数模型、scaling、solver 调用前 durable标记、native OptimizeResult 的全部字段/数组都先 fsync落盘，再做重建；nonfinite输出显式保存字符串，不能误作有理证据。安装的 NumPy/SciPy 版本和所读关键源码/Highs native二进制/DLL原文件哈希由 external-runtime.json 固定，准备时只读字节、不 import。该 runtime 是 discovery 工具，不是数学 trusted kernel。

## 4. 一次固定 exact 重建

每个 T 列只有该项 components 的 -1；dual质量平衡为 `Σmu_component=2a`。对各项按 native严格正 ν 选最大者作 base（并列取最小rowID）；每个其余正 component 是 extra，正 geometry 行独立保留。base质量是 `2a-Σextra mu`。

消去68个base后，position常量为 `b_position+Σ2a*a_base`，extra列为 `a_extra-a_base`，geometry列仍原normal。只对这个固定 positive support 做一次精确有理 RREF：未知数>9则保守未决，不删行/换 support；≤9时解原9个reduced balance，不一致则未决，欠定 free unknowns 预声明为0。所有 geo/extra/base质量必须非负，再显式核全部78列（含gauge X0及68T）的 raw balance。新 normal 含512*dloN，旧 determinant≤4 完全不适用；不限制有理分母或大整数权。

raw dual cost（无objective constant）为 `-Σmu_i*rhs_i`；≥target即合法局部 Lower。即使 native primal 重建失败，独立合法的 exact dual仍可用，不能重演 F 中无效 native point 抹掉合法 dual；但必须保存两边所有验证结果。

primal 只做一次 complementary-face 重建：正 geometry 行及正 extra/base tie 给9位置的精确线性等式，全部使用，不改支持。RREF free位置取 native物理坐标原始float的 exact dyadic，再转 rawX；不调分母或精度。T 取固定原 components 的 exact max，然后核全部原77列模型行。exact primal目标<target才是 Below；它只否定此固定 component-only polyhedral lower model，并非 actual F 低点、RH 或零点比例反例。

合法但低于target的 dual及合法但高于target的 primal也完整保留，不将它们误称 floor。两者缺乏决定性结论则 inconclusive，solver status/float residual不足以接受。若出现合法 Lower 与合法 Below并存，立即failure保留原始证据；不重跑。独立 checker须从原source/FS重新构造组件/域/尺度并核 exact证书，不能只信producer模型。

## 5. 执行和停止边界

未来拟唯一 child，soft270s/19MB、hard300s/20MB，计输入核验/assembly/import/solve/reconstruction和目录全部文件；超限、source或guard不符、重建失败均保留证据，不调整后重试。root gate尚未生成；本准备阶段绝无上述数学执行。

Below 后停止仅原组件模型，不扩anchors/核。Lower 后也只关闭这个真实非空固定pair，尚不代表全域提升、q的存在或最终计数；不能自动开全H/全pairs。全覆盖消费者、短对matching、source≤2MB与整个网站≤3200s流程都未知。原baseline单源已1,818,411B，只余181,589B；本研究JSON/模型大小不是最终Lean源预算证明。

唯一未来命令：

`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageM-component-envelope-preparation/run_once.py --launch-authorized-fixed-M --gate <根部新gate相对路径> --gate-sha256 <新gateSHA>`

AST/哈希准备 manifest 不授予执行，独审源码亦不作为等待准备的阻塞条件。宏观轮次/方向文件不作为不可变数学输入，本包不改计数。
