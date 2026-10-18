# sync43 native setup / preproduction 字节交付

此包仅核对冻结文件字节、清单及收据元数据，未运行编译器、研究 producer、求解器、数学求值或网络操作。sync42 文件和所有旧准备源保持原字节。

native setup v2 的指定 installation.json 收据 SHA256 为 `2b636d4a943acfdd44bc14225c3128992c2df634320a6623f735b362e220e797`，其中 `passed=true`、`proof_runs=0`、`official_website_acceptance=false`。这只记录可信工具安装成功，不证明候选编译、导出、双内核重放、冷路径时限或官网接受。内部 ELF/SDK/C/olean 的 pins 仅作为原收据中的元数据保存，并未复制或重新验证这些运行时文件。

收录 native v2 静态准备、上一版真实失败元数据、对应 setup gate、production v2 静态准备、独立静态审阅、production gate，以及该 gate 所钉住的 fresh-record 快照。production 准备和授权不等于生产执行通过。正在进行的 session 84529 收据和 v4 draft 均未读取或收录。

installation.json（5,886,525 B）和旧 v1-failure.json（5,837,651 B）按原始字节拆成不超过 3 MiB 的 pieces；archive.json 记录完整字节数、整体 SHA256、顺序及恢复目标，已逐字节合并回查。flat 清单只列分片，不上传超过 4 MiB 的单文件。恢复工具默认仅校验；在需要补齐逻辑 JSON 文件的 checkout 中运行 `C:/Python314/python.exe research-goal-20261019-native-tools-result/restore_metadata.py --restore`。它只写入不存在的目标，不覆盖任何不同字节的文件。

SDK 和其它 runtime/archive 依赖只保留身份及排除说明；没有随交付复制二进制。完整冷验证和官网接受均保持未通过/未确认状态。
