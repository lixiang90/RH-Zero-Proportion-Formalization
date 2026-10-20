# H33 算术 probe：仅源码准备

固定来源 c2f3b3d0d1e2d0a3fab63320092b0ac10aace2d501376431bb08e487ae673ad7。复制顶部原归属 notices 及 cAMn/cAM/dAM/PAMhi/floor_numeric；仅提高 floor_numeric 目标 H32→H33，原 proof body 不改。使用上游原有 Mathlib/NormNum imports 子集，显式打开 BigOperators 记号。没有 ChallengeDeps、旧 Candidate、Core 或 package 源码复用；实际库可用性/编译仍待 root 独占新门。

这是未执行的新 Lean 源码。没有 AST、import、Lean、compiler、kernel 或旧证书重放；源准备不是 PASS。不得自动执行或重试。floor_numeric 新目标应是 672123746878241714136624717231727/10^33 ≤ 原精确 RHS。失败保留真实日志并停止，不能自动换精度或修改系数。

对应静态算术与 20 个完整 H 分式 allowlist 见 research-goal-20261021-attempt030-static-triage-formal；最终完整候选及 K/wrapper 映射由 root 另行负责。
