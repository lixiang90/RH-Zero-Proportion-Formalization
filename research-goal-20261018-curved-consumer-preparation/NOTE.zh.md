# 通用 curved finite consumer：静态源准备

本包为同一 O/P 路线准备两个与 case 数据无关的 Lean 模块。只写源、读固定依赖与做字节/词法检查；没有编译、运行 Lean、生成新 case 数据、FS、曲率、矩阵或LP求值。原 StructuralS1RM20261018/Sparse78.lean 与 phaseA1b 失败源/日志保持原样。

## 稀疏对偶与余项付款

`StructuralS1RCurvedConsumer20261018.SparseDual.Row d` 含 `List (Fin d × ℤ)` 和整数 rhs，允许重复坐标与零项。`eval` 是逐 sparse entry 的实数加权和，`coefficient` 为同坐标整数汇总；`eval_eq_dot` 证明它们一致。weight 为 Nat，因此非负；den 为正 Nat。`balanceCheck` 仅有限整数正性与全 d 坐标平衡，使用普通 decide。

若对每行 `eval row z + remainder_i ≤ rhs_i`，且

`den*objective_j + Σ_i weight_i*coefficient_ij = 0`，

`den*target + Σ_i weight_i*rhs_i ≤ Σ_i weight_i*remainder_i`，

则 `target ≤ Σ_j objective_j*z_j`。符号由 `Σ_i weight_i*eval_i = −den*objectiveValue` 固定，后两不等式相加消去余项；正 den 消去。单个 remainder 不必非负。此处的整数 denominator 清除只影响最终有限证书，不允许把负 raw multiplier 强行转成 Nat。

根为 fully qualified `StructuralS1RCurvedConsumer20261018.SparseDual.remainder_sound` 与 `remainder_sound_of_check`。先独立核 finite integer balance，再以真实行桥提供 row+remainder；没有把 source CellA、REG覆盖或强切线假设隐藏在 consumer 内。

与旧 Sparse78 的 API 差异：singleton 用显式 `Finset.sum_eq_single` 及 off-diagonal 为0证明，避免条件相等方向不匹配；展开 `mul_sum` 只在独立 calc 步骤内，避免意外展开终端 RHS；正分母消去用严格正乘积反证，不复用旧不适配的 `mul_le_mul_left`。

## 保存驻点的有限二次网络

`QuadraticNetwork.energy a c q p = Σ_i c_i*(a_i·p−q_i)^2`。`residual ... j = Σ_i c_i*(a_i·pstar−q_i)*a_ij`。full d residual 为0给出平方恒等式

`Q(p)=Q(pstar)+Σ_i c_i*(a_i·(p−pstar))^2`。

权重 `c_i≥0` 推出 `Q(pstar)≤Q(p)`。源不要求图连通、正定、可逆、唯一解或保存求逆算法；只消费保存 pstar 的完整平衡。自环、重复边、零权和空维数不会改变恒等式。

`graph_lower_of_stationary` 取 `a_ij = [j=head_i]−[j=tail_i]`，另证 `linear incidence p=p(head)−p(tail)`，对应 O 保存的 residual：tail 减 `c*(span−q)`、head 加。根 `square_completion`、`lower_of_stationary`、`graph_lower_of_stationary` 均有 fully-qualified `#print axioms`；打印尚未执行，不能把这些声明当作已获 axioms 检查。

## O/P 固定数据接入义务

实际组件行由既有 source TVal、原FS guards 和量化 CellA/强切线薄桥给出。对一个 raw anchor 行，原 raw coefficient μ 与 κm/2 给实数二次权 `c=μκm/2`；清分母后的 consumer 使用 Nat weights 时，实际加权余项必须同步乘同一正 denominator。通过 hull(q,I) 的原REG连续链提供单一 m，不能只在 q 或部分子区间有曲率。几何/常数组件余项取0。固定 raw row 的全52平衡与目标尺度保持原 N2/O 语义。

网络 consumer 提供全域于同一固定 cellpair 的 `Q(pstar)` 付款；代入 sparse consumer 的支付不等式即可。它没有证明 source 原REG整数检查、actual components、真实 F9 objective 身份、全剩余分类、反射/计数桥、Cumulative/Dyadic、Comparator/nanoda或整个网站提交包。O 独审 `1720e826…` 仍仅固定 G1322606 付款，P尚未执行；源码体积/完整验证时间预算未知。

本包不生成任何新数值证书。未来先需唯一授权的小范围 compile 与 fully-qualified roots/axioms 真实检查；consumer编译成功也不能取代 actual 数据桥、完整case覆盖与3200秒/2MB交付关。
