这是未来收据收集 helper 的准备包，尚未运行 collector，更没有生成 local-verified 包或预认当前生产结果。

唯一作用是在 root 真实观察到原始 fullchain-v1 会话 68653、PID 48644 终端退出 0 后，核验并复制已完成的本地生产证据。要求原门 e6ae96…、原 runner 92cc8d…、原 monotonic t0=8988.234、exact650 源 1,830,001 字节、无 failure、四模块普通编译、两个 native export、原 CoreAudit 三条完成消息、serial Nano 的实际日志及 --wait、九阶段真实子进程退出、三收据 hash 链和最终打印耗时 <3200 秒。原父句柄终端记录必须是协议 w9a2-root-terminal-observation-v1，role=fullchain-v1，completion_receipt 指向实际 terminal.json；其 raw_tool_terminal 必须 pin 原工具实际 exit0、最终 terminal SHA 和完整耗时。内部成功收据不能代替外层真实退出。

未来执行入口（当前不执行）：

```
C:\Python312\python.exe research-goal-20261020-w9a2-local-verified-preparation/collect_local_verified.py --outer-observation <root实际记录路径> --outer-observation-sha256 <该记录SHA256> --preparation-manifest-sha256 <本准备包files.json的SHA256>
```

唯一输出目录固定为 `submission/w9a2-weighted-potential-20261020-local-verified`，必须不存在。helper 不导入或运行验收脚本，不调用 subprocess、网络、Lean、exporter 或 kernel；只读已完成收据、hash、复制文本和日志。所有输入检查先通过才创建输出。SDK/cache 不重复散列或复制，实际生产本地源、olean、export、日志与阶段元数据会重新核 hash；大 export/olean 留在原生产目录并记录位置/hash。原 13 个 prepared 文件逐字复制，原 verification-status 是当时历史状态；最新真实本地状态另写 local-verification-addendum。expected-wire 按已冻结 0809d3…包复制，模型在 UI 留空、预期服务端 manifest 为 null。原 prepared 包一字节不改。

所有未来成功包仍标 `submitted=false`、`official_website_acceptance=false`，无官网 job ID。网站实际提交/接受应另建后续 hash-linked addendum。此准备包和静态审查本身不能证明未来 root 进程会通过。
