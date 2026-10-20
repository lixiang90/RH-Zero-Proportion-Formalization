# Production v2 导出后复核区间的静态盘点

本报告只读固定 runner、既存 manifest、已结束阶段收据及少量新产物的文件大小；没有查询进程、运行项目 helper、SDK API、编译器、证明或重读全量运行库数据。唯一实际 production 父句柄仍由 Root 的原 session 68962 观察。本报告不判断最终通过或超时。

现有收据给出的精确区间为：solution export 进程结束估计单调时刻 13072.484，Comparator 开始时刻 13780.734，差 708.250 秒。固定源码在两者之间完成 `run()` 的导出后 SHA、绑定、终端收据同步，随后执行 `immutable()`，再构造 Comparator 命令与环境。没有 NDJSON 解析或隐藏的另一编译阶段。故这 708.250 秒不能严格全算为 `immutable()`，更不能定位成单个文件阻塞。对照 ordinary 结束到 challenge export 开始的同类区间为 139.953 秒。

运行库 closure 本身有 171,231 个唯一路径，声明总量 15,815,618,680 字节。按固定代码路径和现存产物重建，导出后的 bound 集合为 171,535 个路径、17,147,323,293 字节，resolutions 为 171,235 条。这是控制流与 metadata 的重建，没有读取父进程内存。

`immutable()` 先逐文件重 SHA，再逐路径 `Path.resolve()`。其中原始 trusted cached data 和干净 overlay 各 43,549 文件、各 6,090,328,304 字节，两套路径都需要复核，合计约占运行库 closure 字节数的 77%。92,327 条 closure 文件不超过 4096 字节，文件打开与 metadata 成本不能仅用字节总量描述。

当前绑定的 Python 3.12 实现中，`Path.resolve(strict=False)` 调用 `ntpath.realpath` 后还调用 `stat`；正常存在的未加长路径前缀的 Windows 文件通常有两次 `_getfinalpathname`。171,235 条正常分支约对应 513,705 次 metadata API 调用，这是静态工作量，不是实际采样计数。13,982 条 closure 路径的原始 alias 与 resolved path 不同，主要包含官方 SDK 的目录别名。17 条 WSL UNC 文件只占 6,427,980 字节，但小数量不证明低延迟，收据也没有逐文件计时。

当前证据无法区分 SHA 吞吐、文件打开、路径解析、磁盘或缓存状态、杀毒扫描以及 UNC 的贡献。Comparator 已实际开始，说明该整段已经完成。冻结 runner 在两个 replay 都通过后还会于 `finish()` 再做完整 `immutable()`；其实际耗时仍由原句柄验证，不从本区间外推。

完整计数、准确边界与未证事项见 `inventory.json`；固定输入的小收据 SHA 见 `files.json`。
