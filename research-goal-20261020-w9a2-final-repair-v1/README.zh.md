# Final.actual_summed 两端 StateAt 证明修复 v1

新源码在 StructuralW9A220261020/Final.lean，5,519 字节，SHA256 `ea99cc00802c2b3170a9b0c39b1f8b383e69f7c1ab76de851b9cd193c4353cf9`。旧 canonical Final 与本包 Final-v0.lean 保持 5,512 字节、SHA256 `9f9cb13f409ac82ddb1a00ca99d27c98921633b999b82da38cdbd00ea21f5c85`。

实际 ordinary-v4 中 Localization 28.157 秒、Counting 21.313 秒均退出 0，Counting 五个 roots 均只依赖标准三公理。Final 随后 18.5 秒退出 1，只有原第 69 和 71 行两个 error：simpa only 未展开参数尚未完全应用的 Counting.leftGaps/rightGaps，与 Graph 同名函数的 StateAt 类型匹配失败。该失败的 actual_summed/actual_dyadic/actual_cumulative 打印含 sorryAx，是错误占位符；失败收据正确拒绝了它们，不能当作接受证据。

本修复仅把两处旧 simpa 替为显式目标与原假设：

```lean
    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.leftGaps g) s
      exact hs
    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.rightGaps g) t
      exact ht
```

Graph 和 Counting 的 leftGaps、rightGaps 两个定义在只删除空白后原文完全相同：同一 Fin 9 到 Fin 8 的投影函数、同一 r.val 或 r.val+1、有相同命题的界限证明。故 change 仅显式选择定义性相等的目标；hs、ht 本身及其顺序均保留。两函数的完整原文和归一哈希在 repair.json 内。

替换正向和反向回投逐字精确，全源仅增加 7 字节和 2 行。actual_summed、strict_improvement、actual_dyadic、actual_cumulative 类型均原字节不变；其他所有定义、数值、压力、成本、边界、分母、阈值、公开 roots 和 #print axioms 均完全保留，原 canonical 未写入。

failed-ordinary-v4-evidence/ 完整复制 started、terminal 及 Localization/Counting/Final 各 command、child、log、receipt 共 14 文件。父 session 90216 的真实退出码 1 来自主线程工具观察，在 repair.json 中明确区别于子模块实际收据。原输入读取前后哈希一致。

本包没有执行 Lean、导出器、内核、数值搜索或新研究轮。新 Final 编译前须主线程冻结新 gate，且仍须重检实际 roots 不含 sorryAx；本包不声称任何完整提交验收已完成。
