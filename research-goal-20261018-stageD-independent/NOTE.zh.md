# 固定 C point 的原二 FS affine：独立代入审查

本包一次独审通过。原固定 C potential 处，两个原 FS affine 模型之和
减目标 2c 为正；baseline clipping 不改变数值。此单点正值本身不证明
整个 cell pair 的联合 floor，更没有证明新的无条件零点比例。

书面 gate 为 `research-goal-20261016/gates/stageD-affine-point-20261018.json`，
SHA `4c1ba012a8fa5c42aeec686ac3836ac4e747061cd8cea5d97c30c44cd2bcd87e`。
只在生产 D 冻结后执行，输入生产 manifest SHA 为
`683cbf5372fc5246d28a88fadab3dadf59bd758ed9e99458619f503cb30427c0`。
固定 source 为 1,818,411B，SHA
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
原 C witness、完整 B/C 独审和静态 source-affine/flow 推导均作为冻结依赖
逐项核 SHA。所有输入在运行前后完全相同，旧封包及治理文件未修改。

## 独立实现与实际执行

`review_affine.py` 不 import 生产 Python。复用我方冻结 A 的源字节解析、
整数表/原 FS decoder 和 printed mcheck AST，以及我方冻结 C 的纯几何
153-edge 验证函数；新 affine 计算由本包另写两种等价构造完成。
只检查同一固定 id/id、exception 0/1、原 source root0/position1460 与
root0/position9146，不改 state、FS、point、tau、c 或精度。

执行前只有 syntax/schema 审阅，无数学预跑。唯一实际独审 PID 58408，
3.0482908 秒，工具 chunk bf80bb 返回真实 exit 0；无失败和重试。
receipt `independent-review.json` SHA 为
`30063fb0f81249f6eb54a698e43d6448bcb34fec8635bda553248c5f398c6861`。
该审查没有 actual kernel/F 值、新核点、新 tangent、LP、solver、pair scan
或 Lean；所用表值和点字均为原 source 固定字面量。

## 先静态核源，再独立核 68 项

已只读核对 source 的 mvT/mcpT/mcnT/mslT/mwT、eL/eU/eL0、mtermTI
和 mcheckGX_sound 的实际缩放，结论与静态 manifest 51220d528c3c…一致。
Q=32768、R=1024、D=10^9、V=10^10、SA=10^20，kappa=QVR。
原 L0 是原 adjacent lower 的跨度和，L/U 是原 eL/eU，lb 的上端为
uc=max(U,L+1)。active anchors 的旧 mokI 范围仍逐项成立。

对每一原项，保留源 v、cp、cn、msl、mw 的 Nat 定义，再以 signed
整数/Fraction 做以下减法，绝不将负 slope 或 cp-cn 截成零：

    sigma = (msl-2D*mw)/(D*R)
    beta = v/(V*R)+(cp-cn)/(Q*D*R)-sigma*L0/Q
    kappa*ell(s) = Q*v+10*(cp-cn)+10*(msl-2D*mw)*(Q*s-L0).

本包每项分别算 beta/sigma 和 signed scaled constant/slope，68 项均
精确相等；与生产 68 行全部字段逐项一致，包括原 FS、mix mass、原
lb、active guard、原 bounds、v/cp/cn/msl/mw、两 affine 值和外部质量。
额外构造八 gap 系数，再嵌入共同九 gap（prefix offset0、suffix offset1）
并核与直接 term sum 相等。pressure 全部保留，没有重复扣 baseline。

原两叶 payload/FS/flow semantic SHA 和 source main margin 均重新核对。
原 flow gamma/box penalty/certified numerator 与 main margin 的精确
恒等式也与生产全部相同，不把 flow slack 加入 raw A 的定义。
所有 153 条原闭几何约束、sep=17/20 和两侧 actual ordered 条件再次通过。
整个过程只在原 FS 合法区间评价，没有重解码 joint 收紧后的 points。

## 固定点的准确结果

固定 potential 不变：

    X=[0,557056,1355776,2131556,2724876,3392856,3986176,
       4635136,6374116,8254976],  X=655360*p.

独立值为

    A_L = 152082264558971027263976838343 / 16777216000000000000000000000000
    A_R = 37495735583468662581496221089 / 4194304000000000000000000000000
    A_L+A_R-2c =
        2167060893220488703515642699 / 16777216000000000000000000000000 > 0.

clipped sum max(c9,A_L)+max(c9,A_R) 减 2c 恰为同一有理数。两侧 A 均
高于其原 flow 支付给出的 affine certified floor，也均高于 c9。
这只通过所指定的单点必要机会关，不能由此断言整个共同域的 minimum。

另一个独立于单点值的静态事实是：这两个原 M0 本身都超过
`kappa*(cN_target-c9N)=50331648000000000000000000000000`。
两个 surplus 分别为
`24169728990071397846927248000000` 和
`6245599050221517825498512000000`。
结合原 main/flow 的纸面抽取，这解释了本 pair 已有的单窗 scalar
下界为何各自足够支付 c；它不是共享 gap 产生的新收益证据。
本包没有据此分类其余例外、寻找别的 pair 或声称完成新的形式化 lemma。

若本次 clipped margin 为负，只能否定固定二 FS 加基线模型对该共同域的
全域支付能力，仍不能否定实际能量；本次 margin 为正也不自动给全域
floor。两种解释在代码/receipt 中均保持，没有将必要关升级为成功结论。

新 joint floor、无条件新纪录、网站单源/consumer/runtime 都仍未完成，
预算记 unknown，upload-ready 为 false。独审到此停止；未启动其他阈值、
数学试验或 proof batch。
