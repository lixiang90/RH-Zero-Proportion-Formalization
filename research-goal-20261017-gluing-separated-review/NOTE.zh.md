# 固定分离域补充：原零间隔停止结论不能跨域使用

本说明补充而不修改已冻结的
`research-goal-20261017-gluing-joint-infimum/`。原结论适用于所有间隔
非负的域，或仅要求间隔严格正、但无固定正下界的域。它不适用于
固定 `g_r>=s=123/128`：规范提升中的 `g0=0` 不合法，也不能在该域
内令 `g0` 趋于零。因此固定分离域仍可能有联合不兼容收益。

## 同旧核的计数接口已经存在

`StructuralW10Followup20261016/MatchingThreshold.lean` 已有任意
`sep>=17/20` 的 `matching_defect_bound_summed`、
`actual_defect_estimate_effective`、`simple_dyadic`、`simple_cumulative`
和 `distinct_cumulative`。它们接任意 `WCert n`，需要 `W.Adm`、压力
总和、同旧核的 `SeparatedSummedCertificate W c C sep`，以及短对付款
`forall |t|<=sep, c<=wfun(t)`。零势函数把点态分离下界转成 `C=0`
的 summed 证书，接口在 `StructuralResearch20261016/Coboundary.lean`
的 `summed_of_separated_coboundary`，无需覆盖较小间隔。

`KernelPair123128.lean` 的 `kernel_square_ge` 已覆盖整个区间
`|t|<=123/128`，给出 **旧十二模实际核** `wfun(t)>=433/50000`。
故 floor 不超过 `0.00866` 时，已有短对付款足够。不能拿新二十四模
核的付款定理替代它；本说明使用的全部都是旧核接口。

正组合的逐边系数、拉回压力构成一个新 `WCert 10`，容量仍按实际
十点秩跨度逐行核验。已保存向量的精确容量与总压力已有旧包核查。
还需要把这个具体 ledger 和有限展开等式实现成 Lean；本轮没有实现
或编译该步骤。接口存在不等于新的 separated floor 已证明。

## 保存支撑 `{0,1}` 的 separated 收益上限

记 `m9(s)=inf_(h_r>=s) F9(h)`、`S=lambda0+lambda1`。
在 `g_r>=s` 时两个拉回也都在 `h_r>=s`，因此

`S*m9(s) <= inf_(g_r>=s) F_lambda(g)`。

另一方面，对任意 `h_r>=s`，取 `g0=s`、`g1,...,g8=h0,...,h7`。
两个拉回为 `h` 和 `h+s*e0`。旧能量增加首间隔时，只有首压力项与
顶点 0 相连的正配对项会改变。实际旧核满足 `0<=wfun<=1`，上界
来自 Core 的 `abs_kfun_le_one`（第 3509 行）及平方定义。因此

`F9(h+s*e0) - F9(h) <= b0*s + A0`，

其中 `A0=sum_(j>0) a9(0,j)=227594541/50000000=4.55189082`，
`b0=6789/25000000`。代入任意趋于 `m9(s)` 的极小化序列即得

`inf_(g_r>=s) F_lambda(g) <= S*m9(s)+lambda1*(b0*s+A0)`。

该额外项的精确值为

`26131252816157427809/213333335435312394516074912`

约 `1.2249024636883825e-7`。这是对**已保存 tiny-lambda1 支撑**、
相对于独立 separated 下确界的联合收益上限，不是该域的完全 no-go。

要让该保存向量达到原任务目标，必要条件仍是

`m9(s) > 0.00861010908517342`，

比已证全非负下界 `c9` 至少高约 `1.4723826034665691e-5`。现有
`cert_AM` 没有证明或否定这个 separated 改进。因此这一路的主要
收益必须来自更强的旧九点 separated 下界，不能归因于 tiny 第二项
本身。简单非负压力基线 `s*B9≈0.00420591`，以及第二拉回的
`s*(B9+b0)≈0.00446686` 都小于 `c9`，单靠它们与 `cert_AM` 取最大
不能产生所需增益。

本包另在 `PREFIX-SUFFIX.zh.md` 评估固定对称 `{0,9}` 的非线性
兼容性机会关。没有实施新优化、核评价、旧树解码、例外枚举、兼容性
检查或 Lean 编译。
