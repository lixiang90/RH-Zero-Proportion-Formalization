# 冗余 native-v4 验证取消证据

官网已正式接受实际用户上传的原 v3：`lixiang90-single-exception-overlap-20261018`，状态为 `kernel-verified`，`formalVerification=true`。正式接受源的 SHA256 为 `024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81`。完整官方原始证据在 `research-goal-20261019-record-accepted-independent-1753`；本包只引用其冻结 manifest。

因此唯一运行持有人 root 决定终止冗余的本地 native-v4 冷验证，并报告实际 session 84529 terminal exit1。原始 mirror `failure.json` 记录 `KeyboardInterrupt: Received signal 15`，中断阶段为 `comparator-default-kernel`，当时子进程退出码为 −15。四模块 ordinary Lean 与两个原生 export 已完成；Comparator/default kernel 未完成，nanoda 未启动。

**这次运行是合法取消，既不是完整 PASS，也不是数学反例或证明被推翻。** 它不会自动重试；绑定 session 84529 exit0 的 post-PASS collector 从未执行，也不能用于这次 exit1。正式接受的结论来自 v3 的独立官网验证，不来自被取消的 v4。

`evidence/` 按字节保存 mirror 失败收据、root 停止 gate 和小生成收据。Windows 镜像没有 Linux 阶段日志，本次没有另取 Linux 日志，也没有复制 NDJSON、olean、ELF 或 cache。原 native-v4 `Solution.lean` 保持原位、未修改，其真实字节数和 SHA 记于 `status.json`。没有创建 v4 的成功提交材料，没有提交 v4。

本归档只读写字节与 JSON，未运行编译、生成器、exporter、内核、网络、Git 或数学计算。
