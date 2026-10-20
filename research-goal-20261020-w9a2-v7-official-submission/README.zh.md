本目录保存root实际操作官网后的v7提交观察，来源是root的网页UI转录与实际CUA截图，不是下载的API日志。截图submission-running.png原样保留。

root报告一次提交点击正常返回，点击约在2026-10-20 13:02–13:04 UTC，页面于13:04之后显示“Verification running”及“Lean and both kernels are checking the frozen theorem contract”。这些时间是root观察范围，不是服务端job创建或开始时间。页面实际proofDigest为1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771，与prepared-v7对应的本地预测一致。

这只记录官网已提交且UI显示验证中，不证明Lean或两个内核已经完成，不构成accepted或纪录推广。页面配额组件仍显示1/3 used、2 remaining；root指出它是未刷新旧显示，不能据此推定当前服务端实际额度，也未观察到更新后的2/3 used。

root同时提供cb7558bc2944358366b5aac4d187f3b3ee5a637c的成功push及fixed-commit单源码HTTP200/字节相等收据；其范围只有该精确源码，不是全树新审计。此前prepared-v7中的false状态是提交前历史快照，保持原样；本目录单独记录后续UI观察。

本封包不操作UI、网络、Lean、exporter、kernel或方向计数，不修改任何旧材料、源码或截图。未记录signed handle、cookie或不可知的服务端job ID/创建时间。
