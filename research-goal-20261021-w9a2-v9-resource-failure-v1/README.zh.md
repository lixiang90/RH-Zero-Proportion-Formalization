# v9 单次资源编译实际失败封存

本包只复制原 `tmp/w9a2-20261021/v9-resource-v1` 的六个小文件到 `work/`，保持 started、child、terminal、memory、stdout、stderr 原字节。`root-outer-observation.json` 逐字保留 root 提供的原工具结果摘要，并明确它是 root 转录；封存者没有查询、轮询、恢复或自行观察原句柄。没有复制大源、可信库、编译输出或 runtime 闭包。

Root 报告原 session23402 的 write_stdin tool8f7a7d 实际 outer exit1，parent32660、child54436，child exit3221226505（0xC0000409）；原工具打印 terminal SHA256 `6e222b92535c3beb51c8103ea4e6bef0d1e88956882e9b5d5dfe34ce9ed9e579`，与被复制 terminal 实际字节 hash 相同。

时间口径分别保留：root 摘要的 final elapsed 为583.593s，对应 memory.jsonl 最后一次 final_after_wait 样本；terminal 的总 elapsed 为583.6710000000021s。不能把最后内存样本时间替代完整收据总时间。共21个样本，terminal 记录 peak RSS 6829252608B（root 显示6512.88MiB）、peak commit11914600448B（11362.65MiB）。commit 仅为诊断。

Terminal 的 compiler_resource_gate_passed=false、candidate_compile_and_C_generation_completed=false、resource_limit_exceeded=false、budget_expired_and_owned_child_terminated=false。这是子进程非零退出，不是 runner 7GiB RSS 主动停止，也不是3200秒 timeout；没有三个 fresh 编译/C-generation 产物完整成功的收据。本包不另行检查产物目录。

196B stderr 实际报告：`lean::memory_exception: excessive memory consumption detected at 'interpreter'`。这支持记录 Lean 的该异常，不能据此定位具体 declaration、认定数学命题错误，或确诊 OS/cgroup OOM。4096B stdout 含弃用 warning 和不完整的末条 JSON，不据其最后显示位置推断最后运行声明或主耗时位置。

现有 terminal 绑定固定 v9 source7552bbb829b86986798b58cf40caf998ea8c51ab19201998b533dae4b9518c99/1861120B、gate d2b275d90a1b814f5d6045abc57ccd2b1ae4b7178e573b4c997a06248fcb4ce9。这里仅保留收据中的绑定，不重新散列大源、SDK 或 runtime。独立 kernel replay/fullchain/official PASS 均未获得；正常 Lean 编译时的 kernel 检查不被关闭，但本次编译未完整通过。

已冻结 DRAFT-v9 的 startup/pending 记录保持历史快照，不改成当前 running 或 PASS；本次真实终态单独封存。没有新编译、export、内核重放、进程查询、网络、UI、Git、重试或阈值增加，也未修改 proof、DRAFT、状态或计数。
