# 尚未执行的单次结构流读

`run_stream.py`没有被运行、import、AST解析或--help测试。它只接受固定旧v6 solution.ndjson（677296932B，原SHA1cc0f929919e0d4f58d947223c75a82450df57da11a9fe43fd93a90d8c8433d7），不扫描challenge，也不调用Lean或证明工具。后续实际执行仍须root独审并单独授权；本包没有enabled gate。

预备调用格式：`python -B run_stream.py --authorize-once --runner-sha256 <本冻结文件的SHA256> --output-directory <workspace内全新独占目录>`。不提供authorize-once则拒绝；runner self pin前后核对；输出目录不得存在；输入固定，不接受改为v8或其它路径。

单次顺序读取中同步计算输入SHA和字节，不为hash再读一次。总预算120秒，1MiB单行、32MiB名称表、256MiB自身进程RSS、2MiB result.json。独立watcher每50ms检查自己进程当前/峰RSS和总deadline，超限写失败收据并退出；Windows只查询GetCurrentProcess伪句柄，不查询或终止别的进程。这是观测后停止，不是硬OS分配限额，采样间隔内瞬态不能被此保证约束。API查询失败亦失败。root原工具实际exit仍必须另行观察；result的return_intent不能冒称真实外层0。

解析只保留有上限的resolved名称表、固定tag计数、两个top100序列段排名和三个公开根索引。表达式对象逐行丢弃；不存完整Expr图或每根visited集合。名称、层级和表达式索引需连续，引用需已存在；不识别的外层tag/表达式tag/层级tag、错误字段/根/字符串、过长行或最终hash不符均失败。声明记录保留type/value根，inductive组按一条serialization边界排名。输出的roots最多列每组前8个并显式标截断。

边界段从前一声明行之后到当前声明行末，包含首次输出的名字、层级、表达式和当前声明记录。共享节点可能早已输出，递归依赖声明会先截断边界；这不是当前声明独占proofsize，也不分解type/value的精确reachable大小。known_v6_namespace_match_not_proven_new标签不表示已求出与challenge的精确差集。

本准备阶段初版metadata helper只因checkout CRLF raw SHA不等canonical LF pin而退出1；没有fullstream。`prepare-initial-failed.py`和首次各5行前缀均保留；后续只以冻结canonical source核格式，记录精确CRLF→LF桥，不改任何旧receipt或source。两次准备都只看同一前5行，不额外扫描后续行。
