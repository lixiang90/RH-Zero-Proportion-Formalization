# 独立审计准备合同：固定 scalar 势函数的 cycle / DAG 证书

当前仅准备、AST 和文件身份；未读取 B/H 数值来执行审计，未构图、DFS、搜索 q、解 FS、评价点/核/矩阵、运行优化或 Lean。生产终包、结果及 root 新独审 gate 齐备后才可唯一执行。

`audit_certificate.py` 不导入任何生产 Python，也不调用图搜索。它从已独审 B 的原文件读取精确 Mi、从 H 原 binary 读取全部 15378 升序 indices；只进行下列证书验证：

- 若生产输出 cycle：逐给定 edge 重解 index（source=`2*i+chart//2`，target=`2*j+chart%2`）、核 H membership、原 Mi、严格负权、完整字典、simple cycle 的首尾与精确总和。只声称此固定 scalar outer-graph 模型矛盾；不重跑 canonical DFS，不声称环对应真实多窗。
- 若生产输出 DAG：核全部 2374 顶点完整拓扑序，并逐全部 15378 原 edges 核 rank 严格增加和负权。只通过 underpaid 子图必要关；不证明 paid/star 完整约束或存在 q。

即使生产 metadata 称全部 edges 负权，cycle 模式的独审只核给定环边；receipt 明确 `all_15378_edges_reconstructed=false`，不能冒充全图重放。两模式都完整加载原 H membership。

需 root 创建 gate，字段为：

```
independent_window_potential_certificate_audits_authorized: 1
expected_H_records: 15378
prepared_manifest_sha256: <本目录 prepared-files.json 的SHA>
resource_limits: {elapsed_seconds:60, closed_output_bytes:8000000}
new_graph_search_q_FS_point_kernel_matrix_LP_or_Lean_authorized: 0
automatic_retry_allowed: false
producer_manifest: {path:"research-goal-20261018-window-potential-cycle/files.json",sha256:...}
producer_result: {path:"research-goal-20261018-window-potential-cycle/result.json",sha256:...}
producer_terminal: {path:"research-goal-20261018-window-potential-cycle/terminal.json",sha256:...}
```

生产 manifest 内 files/package_files/read_only_dependencies/dependency_files 均须使用仓库根相对 path（如 `research-goal-.../result.json`）；result 和 terminal 必须在其中。审计完整验证清单各行、生产真实 exit/limits、开始/结束 input hashes，并固定标准库 runtime。新的 gate 独立于 I 值；I 通过与否均不改变图证书逻辑。

唯一执行命令应为固定 `C:\Python314\python.exe -B -X utf8 audit_certificate.py --launch-authorized-once --gate <root gate相对path> --gate-sha256 <SHA>`。launcher 写 exclusive launch/child/stdout/stderr，最多一 child，60秒/8MB超限终止；失败保留无自动重试。当前不会运行此入口。

最终审计仍须单独冻结结果和真实 terminal。即使这个局部模型被排除或必要关通过，都不代表新累计 floor、新无条件纪录、Lean 或网站提交通过；source/完整计数/资源义务仍独立存在。
