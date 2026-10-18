# K 独立证书审计结果：固定 scalar 势函数模型被排除

root gate `research-goal-20261016/gates/stageK-independent-cycle-20261018.json` SHA256 `94f08440b03520ab92fe8f0c4f2686b383b1c5d6c72ae48fdf1f961067cbaca0` 授权唯一一次独审。生产终包 SHA `89fd14950a06a8e12c9feb7c09efd90bfdb6723f021fde14ddc39b2ca27c6916`，独审准备清单 `8d9120582f8348a22170a5ca6424d70061110136ccc27c5c6f49485f1b166ec0`。

真实执行 exec chunk `f78876`，child PID 21632，一 child，terminal exit0、limit_stop=null；wrapper 0.631713 秒，证书检查 0.133715 秒，终止时记录 43,113 B。没有 session/yield、重试或继续存活的审计进程。原 source/AST/prepared manifest 未改；本包新增本说明、执行元数据和最终清单。

审计没有导入生产实现，也没有 DFS、构图或搜索。它完整读取原 B 的 1187 个精确 margin 与原 H 的 15378 个升序 membership indices，仅对生产给定环的九条边重建 index/cell/chart/有向 vertex/原 Mi/严格负权，逐字段比较，核 simple cycle 的首尾和精确总和。

验证的环 indices：

```
2867814, 23816, 90540, 390637, 1543511,
484431, 157722, 1232184, 2912941
```

精确权和为

```
-500044450509522961774354964000000 < 0.
```

因此对这个固定允许边图，不可能存在所有边都满足 `q_b-q_a<=Mi+Mj-2d` 的 scalar q；沿此环相加即得到 `0<=负数`。该模型应停止，不再用同一约束搜索 q 或一般 LP。

严格范围：receipt 为 `given_simple_negative_cycle_only`、`checked_edge_count=9`、`all_15378_edges_reconstructed=false`。完整 H 成员表已读并用于九边 membership，但这不是 15378 边的数学重建或全图算法重放。环也不声称对应真实多窗同时可实现，不能据此否定实际累计能量、非线性余项、更细状态或新的零点比例。无新 FS、点、核、矩阵、优化、Lean；无新的全域 floor 或网站可提交结果。

`independent-review.json` 是独立精确证书 receipt，SHA256 `2b21a5a0a8c1a628a2aa14c8f7530de34d5ba9714adb30998013a1951e405d14`。其中保存全部已核九边、开始/结束输入身份、运行身份和范围字段；最终 `audit-files.json` 冻结本包所有原始输出及当前 read-only dependencies。
