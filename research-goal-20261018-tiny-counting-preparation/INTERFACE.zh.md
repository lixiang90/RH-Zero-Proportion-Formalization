# 当前 s1R 的精简求和计数桥：仅源码准备

本包没有运行 Lean、求解器、叶见证提取或核值计算。`Counting.lean`
导入尚待提供的 `StructuralS1RTiny20261018.Core`，因此当前不是完整可编译
项目，也不代表新的局部、全域或零点比例证明。

Core 必须使用固定当前源
`research-goal-20261018-record-source-audit/snapshot/Solution.lean`
（SHA `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`）
的实际核与定义。尤其需要以下现有接口原义不变：

- `Zeta23Ext.Bridge` 的 `wfun`、`windowGaps`、排序扩张及端点恒等式；
- `Zeta23Ext.BridgeW.WCert`、`Fw`、容量/压力、`window_pairs_le_band`；
- 当前 `OpethN.band_close_n`、`pressure_le_n` 以及实际谱/误差界；
- 当前 `Opeth.AMMatching.close_pair_block_bound`，分离 `17/20`，付款 `1/64`；
- 当前 `OpethN.Counting.ActualDefectEstimate` 与 `defect_to_dyadic`，以及
  实际零点的 `paperInputs_zeta`、累计计数和 simple-to-star 接口。

本包不导入旧 `GramDefect20261015.Core` 或任何曲率消费者。旧两个文件
仅为现成泛用有限求和、band、matching 证明体的有归属来源；移植后绑定
当前 Core，尚未通过编译或独立内核。

## 最小有限输入与精确边界付款

最终使用 `W=RiemannFail.W9`，其原 `W9_adm`、`W9_B`、`cert_AM` 来自
当前完整 Core。设新 floor `c`、`delta=c-c9>=0`，`delta<=c`，`c<=1/64`。
调用者必须真正证明以下实际函数命题，不能用 Python 结果充当 Lean 前提：

```
forall g : Fin 8 -> Real, (forall r, 0 <= g r) -> c-delta <= Fw W g
forall g : Fin 9 -> Real, (forall r, 17/20 <= g r) ->
  2*c <= Fw W (leftGaps g) + Fw W (rightGaps g)
```

第一项由原 `cert_AM` 与 `c-delta=c9` 化简；第二项仍待新的完整 raised
walk、根外压力定位、反射与唯一例外相邻冲突证明，不在本包中假装完成。

泛型 `sum_range_pair_lower` 以 N=0、N=1、N=n+2 强归纳：前两项分别用
`delta>=0` 和单窗旧下界，最后一项在旧 IH 后加第 n/n+1 窗的 pair 付款。
仅使用两次 `sum_range_succ`，得到 `sum E_i >= c*N-delta`。应用于任意
分离排序点列后成为 `SeparatedSummedCertificate W c delta (17/20)`。
没有新的 W10 权重矩阵或容量证明。

band 付款保留当前 W9 的压力 B 和带宽，matching 仅在分离余部付一次
delta。`delta<=c` 将其吸收到原 harmless 边界指数 9 -> 10，得到
`ActualDefectEstimate Z 10 c B`。这不是把实际局部窗口改成 WCert10。

## 最终接口

`actual_defect_estimate_of_pair`、`actual_dyadic_of_pair` 和
`actual_cumulative_of_pair` 全部保留上述实际输入。后两者返回

```
ratio c B =
 (6721290091768038344368273523390880473594 / 10^40 - B)/(1-c)
```

的任意 epsilon 损失 dyadic / cumulative `N0star` 下界。最终 submission
wrapper 还须以精确有理算术证明其 candidateKappa 等式、严格超过新鲜网站
纪录，并使用可信生成的 `ChallengeDeps.CandidateSpec`；不能在这里重定义
可信常数使比较通过。

当前完整源是 1,818,411B。manifest 给出的加法仅是这一源与准备中桥的
真实 UTF-8 字节库存，不是完整 flatten 文件；尚缺有限 pair 根、未来 Core
封装、最终候选 wrapper 和任何编译修复。最终必须实际复核单源 <2,000,000B、
普通 Lean/公理、导出/Nano/Comparator，以及网站总 3200 秒资源合同。
本包没有新增普通 PASS 模块，也没有修改任何已冻结源或治理计数。
