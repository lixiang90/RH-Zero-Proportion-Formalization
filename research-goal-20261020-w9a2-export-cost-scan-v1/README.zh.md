# 单次结构扫描未完成封存

本包保存一次历史 v6 export 序列化结构扫描的未完成终态。已有 `scan/result.json`、`outer-observation.json`、`stdout.txt`、`stderr.txt` 保持原始字节；新增 root 原工具观察转录、本说明及清单。清单中的 `scan/result.json` 使用相对路径，不散列或复制大输入。

root 实际原 exec session 为 53230，启动 chunk 为 852b38；原 write_stdin terminal chunk 008e11 返回 outer exit 1，打印外层 elapsed 20.563s、child exit 1、timeout false。`root-execution-observation.json` 的来源是 root 提供的这些实际工具结果转录，不是本子代理重新执行或下载的原始工具响应。

子结果为 `complete=false`、`success=false`，错误 `ValueError: Name-table budget exceeded`，elapsed 约 20.422s，observed peak RSS 56147968 字节。外层收据绑定该结果 SHA256，并记录 child exit 1 / timeout false。子结果内部 `actual_exit_observed_externally=null` 原样保留，外部实际退出另由外层和 root 观察记录。stdout 与 stderr 均为空文件。

本次没有完整 input hash、字节统计或排名；是否读完约 677MB 输入未得到完整扫描证据。20 秒退出和 RSS 样本仅描述这次触发 Name-table 预算停止的尝试，不能作为完整扫描性能、数学验证、新数学结果或官方验收结果。RSS 是观察样本，不是 OS allocator cap。只尝试一次，未增加 cap，未自动重扫。

这是结构解析收据封存，Lean / compiler / kernel / export 调用为 0；没有 fullchain 或官网接受。root 提供的 gate SHA256 前缀为 `2ff0b997`，本包不补造未提供的完整哈希。宏观 013 的 counter0 由 root 保持；本次不修改状态、计数、proof、大输入或任何旧文件，不运行网络、UI、Git 或重试。
