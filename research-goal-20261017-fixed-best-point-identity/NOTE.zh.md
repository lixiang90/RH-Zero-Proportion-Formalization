# 唯一既有 best 点的身份固定

本包只核对身份，不计算 P、w、F、Phi 或整数竞争能量，不另选点。

精确点的完整相对路径为
`research-goal-20261017-ternary-coboundary/support-audit.json`，
SHA256 为
`3d7fc73a21b5f8e8294be0eeb40881a08072412568dd684f7bed785fe1dc24db`。
JSON 顶层是 dict；字段
`zeroV_minimum_sample_exact_binary_float_gaps` 是长度 9 的 list[str]，
各字符串是已存在的精确 numerator/denominator。有理 tuple 原样见
`identity-replay.json:fixed_point.values`，未另作小数舍入或修补。

对应的发现源为
`research-20261016-followup/window_reweight_challenge.json:best_gaps`，
SHA256 为
`4d79a1c05aba683d9971755eb7bad6b109d042abad359c74e43cc1403b3f903b`。
其顶层同样是 dict，best_gaps 是 9 个 JSON 数字的 list。
逐项把该既存浮点数转换成其精确二进制有理数，与前一字段全部
相等。这只是身份核对，不是重新生成测试点。

原记录 ledger_sha256 等于当前冻结参数的
`61ad18366b0234d75c4204bc661446c94f1705c29c3e6041bed0147dd6476f11`；
全部 24 个系数逐项一致。原 profile 源 SHA 也与既存文件一致。
所有身份源在检查前后 hash 相同，不绑定 mutable 治理文件。

原 best_observed_minimum_upper=.008847438760183953 是浮点发现值，
不是实际函数的严格区间上界。support receipt 亦明确
actual_scalar_upper_bounds_proven=false。本包不提升该证明范围。
根代理若检查压力耦合全域预算，应固定使用上述已有有理 tuple，
不能因结果改变点、舍入、样本或核。本代理本轮到身份冻结为止。

只读复核：`python verify.py`；首次封存使用
`python verify.py --write-receipt`，拒绝覆盖已有 receipt。
