# 十点候选提交材料草稿

本文件尚不能随证明上传。候选的局部解析不等式必须先由完整有限证书在 Lean 中证明，再完成 Comparator、Lean kernel 和 nanoda 核验。

精确分数为 `3338842690820594373879991756052499665323 / 4956700000000000000000000000000000000000`。百分数为 `67.360193088558806744…%`；网站明确采用截断显示，因此十位小数栏应显示 **67.3601930885%**。用户沿用的 `67.3601930886%` 是四舍五入值；排序只使用精确分数。

对网站 attempt-024 的当前精确纪录，条件增量为 `0.00206231770927261779…` 个百分点。该比较已经由整数分数直接复核，但不代替局部解析证书。

建议方法说明：十点加权 Gram 缺陷证书，在原九点方法之外加入秩距九的配对贡献，重新优化对称配对权与压力；窗口及一般匹配和计数链沿用已有完整证明。完整归属与 Apache-2.0 通知需保留。

目标必须是无附加假设的 distinct-zero dyadic 和 cumulative 两种渐近结论；`FinalConditional.lean` 目前的显式 `SeparatedFloor` 参数必须先由局部有限证书消去。它只要求各间距大于等于实际匹配所需的 `17/20`；原始数值探索的 `4/5` 域更宽，但最终无需证明这一额外增强。随后再将相关定义、泛化引理、有限数据、窗口证明及最终三条定理装入单文件 `Solution.lean`。不要直接上传含本仓库路径导入的模块。

网站主来源：

- [当前纪录 attempt-024](https://www.riemannzeta.fun/submissions/attempt-024)
- [锁定 commit 的完整 Lean 源](https://github.com/josusanmartin/riemann/blob/9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb/submissions/attempt-024/proof/Solution.lean)
- [固定挑战定理](https://www.riemannzeta.fun/challenge)
- [单文件提交要求](https://www.riemannzeta.fun/submit)

记录源已精确恢复：Git blob SHA1 `fe197ef0eeb3109b74d38e6d635b72169a59cc47`，UTF-8 1835018 bytes，SHA256 `637d8197291a39ec2d9c7529642ac1df9731ceea706882a1c2e0b4391642d0ac`。`review_current_record.py` 比较了 18 个核心定义及核函数桥接别名，均与冻结的 W10 核完全逐字节相同。新增 PTT/曲率表仍需自己的 Lean 检查才能进入最终证明。
