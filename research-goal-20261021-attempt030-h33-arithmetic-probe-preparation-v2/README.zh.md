# H33 三项算术 probe：仅源码准备

原 v1 固定保存不改；本 v2 在 namespace AMW 的 end 前仅加入 h33_ratio_exact 和 h33_strict_improvement 两条 norm_num theorem。其余字节与原 v1 完全相同，包括固定上游 cAMn/cAM/dAM/PAMhi、floor_numeric 新 H33 目标和原 proof body、许可 notices。三项分别检查 H33≤原 RHS、固定 c/B 的比例恒等式、K33>attempt-030 R。

仅 Mathlib/Mathlib.Tactic.NormNum，未导入旧 Candidate/Core。不运行 AST、Lean、compiler、kernel 或任何旧叶证明；本包仅 source prepared，不是 PASS，不自动执行或重试。root 另门独占执行并观察真实 child/outer exit。
