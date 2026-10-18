# F：原 source 模型独立重建与同次 raw dual-only Lower

本包得到有效的 fixed-pair Lower：保持原 FS、原 states、155 rows 和目标
不变，同次原始返回 dual 可独立证明 exceptions1/5、id/id 的联合 affine
下界达到目标。原始 primal 仍有38条违例，生产失败历史保留，不能宣称
LP 最优值或实际 primal 可行。该 Lower 只关闭这个有序共同域，不是全
例外覆盖、新全局 joint floor、无条件零点纪录或网站可提交证明。

root gate 为 `research-goal-20261016/gates/stageF-exact-lp-20261018.json`，
SHA `02015ab778511ce8ae424e488ce95ee28f4e34990e96aa5db8c0f4608c76a90d`。
gate 的 Lower 合同本身只要求非负 dual、完整平衡与付款；若声称 optimum
才额外要求可行 primal。root 后续明确授权仅审原 raw dual，不修改其
符号、点或求解器。生产失败包 manifest SHA 为
`ae64407781ef18022c7729523b645426bfa080fd44ad428d6b537ad4f8e0da24`。
它仍没有 result.json / certificate.json，本包没有写回或修改生产包。

## 唯一独立审查及源身份

`audit_fixed_raw.py` 仅标准库，不 import 生产 Python / Sympy，不运行
LP、optimizer、pair scan、actual kernel 或 Lean。执行前只有 syntax /
schema 审阅；唯一独审 PID24136，2.4652566秒，工具 chunkcd4531 真实
exit0，无失败或重试。receipt SHA 为
`11d8ca8ac6998e067e24ba146e1aafad720db7be764e3bdf9aae3d0374305b73`。

从我方冻结 A 的实际源 parser/原整数 FS checker，以及冻结 D 的独立
beta/sigma/signed coefficient 构造，重新读取固定新 source：
1,818,411B，SHA
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
两原 B cell 身份是1/5，不沿用旧 D 的0/1 coefficients。
68个原 term 全字段、原 FS/point guards、flow 与 main margin 与生产
affine-components 逐项相同。全闭包 source/script/input SHA 前后相同；
外部 simplex.py 只读核 hash，不加载或执行。

独立 objective 由两条路径重建：先从有理 beta/sigma 的原 scaled
constant/八gap coefficients 嵌入九gap，再从原整数 mvT/cp/cn/msl/mw
直接求和。两者精确相同。取 Q=32768、R=1024、D=10^9、V=10^10、
SA=10^20、kappa=QVR，最终

    C+b dot X = 2*SA*kappa*(A_L+A_R),
    target = 4*kappa*893766123055294719.

将九 gap coefficients 改写为十 position coefficients 后，sum b=0。
X0=0 只消去平移，变量仍是实数，九条 separation 推出剩余 Xi 非负。

全部155 rows 从原 B 的36正跨度/原 pair 顺序重建：两侧各72条闭 bound，
9条 sep=17/20，另加两条真实 Ordered 四点行。Ordered 没有当作 DBM
edge，也没有沿用 E 的违反 Ordered 点作为 F 的 feasible primal。
155 rows、C、b、九gap coefficients、目标和 gauge 全同生产模型。
独立 rows canonical SHA 为
`917d8b267e5ea6875f6fb4718fec0874db47dacb845b59897d9a576cdabbde49`。

## 原 primal 的38条真实违例

原 production 仅1次 primary 返回，没有 InfeasibleLPError，所以条件
auxiliary 未触发；child exit1 停于 primal 可行检查。本包独立得到同样
38条不满足 aX<=rhs 的 rows（zero-based IDs）：

    2,6,11,12,30,32,34,38,42,44,47,52,55,61,63,65,67,69,
    76,81,82,86,102,104,107,112,114,117,122,125,127,129,
    133,135,138,140,142,149.

receipt 对每项列出 kind、exact lhs/rhs 和 strict violation，与生产
failure-closure 完全一致。例如 row2 为1935360>798720，row149的
separation 为1922980>-557056。没有修复该点或忽略失败行。
原 objective 的数值与 bX 相同、原 primal/dual objective 数字也相等，
但不可行点的这种相等不能证明 optimum。

## 原 raw dual 单独给出的有效 Lower

原 raw result SHA 为
`eec4338b9dd6806e604c8df5f23c997e27ffa3069309c4a1a9350c307f0c71f6`。
本包原样解析全部155个 mu（没有选择替代 dual 或改任何符号），精确核：

    mu >= 0,
    b + sum_k mu_k*a_k = 0  （全部十坐标）,
    C-sum_k mu_k*rhs_k-target
      =1930287266556575787714099564000000 > 0.

清共同分母后恰为整数，denominator=1，非零支持9条原 rows：

    [9,29,36,74,84,110,130,153,154].

只省略原 dual 的精确零项，未做数值稀疏化。最后两条 Ordered 行权重
均正，故证书合法域明确包含这两侧有序条件，不外推到 E 的松 DBM。
完整整数 weights、十坐标 balance、lower、target 和 surplus 保存在
`recovered-lower-certificate.json`。其准确下界与目标分别为

    lower =1201522871265057331333498419564000000
    target=1199592583998500755545784320000000000.

证明只用行的非负加权：对任何满足155 rows的真实 X，有
bX=-sum mu*aX>=-sum mu*rhs，故 C+bX>=lower>=target。
它不需要原 primal 有效，不需要相信 Sympy 返回的最优性。

source-rebuilt-model.json 与 source-rebuilt-affine-components.json 保留
独立重建的数据。原 source 的 term-line soundness 及域桥仍是解析/后续
Lean 连接义务，本算术审查没有重新编译这些新 lemma。

## 不能扩大的结论

该有效 Lower 仅处理 fixed original pair1/5 的 id/id 有序共同域。其余
数百万 chart/pairs 未处理；不能由本局部证书推出 ten-point 全局 floor、
matching/counting 后的零点比例或 baseline 以外的新纪录。
新增消费者、source<2MB 与 ordinary/export/Nano 的完整预算仍未知。
未做优化器重试、新 FS/新点/核样本/阈值/Lean 或新的 scan；生产失败历史
与独立 dual-only recovery 分别保留。本包到封存为止。
