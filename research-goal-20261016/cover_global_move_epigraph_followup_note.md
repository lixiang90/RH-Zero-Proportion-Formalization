# 全局竞争点的完整 300 样本补充

本批不修改上一批已冻结的 21 个文件。完整 300 样本的差核 hypograph 与能量 epigraph 联合计算，在跳过全部 15 个已知 signed-difference move 之后，另外得到 **9 个**严格全局竞争点排除证明。其中 6 个证明使用正的能量乘子，3 个不需要能量乘子。全部 9 个证明连同其先行的 102 个 OBBT 界、30 个 Newton 步骤通过独立重放。

9 个新父区域彼此不包含，也不包含或被先前的 15 个父区域包含；两组的路径集合均与此前联合能量—梯度的 7 个区域不相交。新 9 个区域对应旧树的 110 个分支；连同前 15 个区域，得到 **24 个互不包含的父区域、251 个旧分支**。这些计数由 standalone 重放重建相应祖先和旧分支后检验，而不是只统计已通过的 value 叶。

新自足归档 `cover-global-move-epigraph-evidence/proof.json.gz` 为 **48,466 字节**。独立重放不需要原始 44.7 MB OBBT 文件或旧 41k 节点快照；它从压力根、最小祖先投影、压缩 OBBT/Newton 单元和差核混合重建证明。能量下界混合也通过原 scalar/flow verifier 重新检查。旧 15 个证明的 72,868 字节归档保持字节不变。

更强的多 move 直接分离 pilot 同时使用多个全局必要条件 `U_delta≥0` 及能量 epigraph。在相同的首 100 个残余样本中，跳过已知 7 个 move 成功区域和原判据已闭合的 25 个区域后，没有得到新的 LP 分离。该负结果保留，不将零条见证的重放当作数学进步。下一实验将这些条件作为坐标 OBBT 的附加约束；交集非空时也可能收缩，而这属于后续尚未纳入本批的工作。

本批仍只有已核验的局部全局极小点排除证明。完整全域覆盖和实际差核数值表到最终 Lean checker 的连接尚未完成，因此 `complete_global_cover=false`、`actual_analytic_Lean_bridges_complete=false`、`new_zero_proportion_proven=false` 均保持不变。
