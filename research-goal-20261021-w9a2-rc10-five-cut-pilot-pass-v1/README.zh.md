# 新六个 cursor 证明模块的 pilot 通过封存

本包仅保存一次新 rc10 five-cut pilot 的实际小收据、日志及三份新输出。范围是依赖已证明的加强版 Prefix/Core 缓存进行开发导入的六个新 cursor 证明模块，不是整个新单文件的编译/资源通过，也不是 Comparator、独立 kernel replay、nanoda 或官网验收。

Root 报告原 session23555 经 write_stdin tool4c02cb 实际 outer exit0，child50324 实际 exit0，并以 tool522e31 另读 terminal。`root-outer-observation.json` 逐字保留该摘要，明确原句柄退出来自 root 转录，封存者没有自行查询或恢复该句柄。现有 terminal 的 parent 为45320。

Terminal SHA256 为 `08f09bb1c8dfa10b3179878406811292788817f568531108b572beb718e3baa9`；总 elapsed48.18800000000192s 与最后 final-memory 样本48.04699999999866s 分别保留，不混用。3个内存样本记录 peak RSS4979691520B、peak commit10020028416B，commit 仅诊断。Terminal 的 pilot_pass=true，actual_child_exit_code=0，timed_out=false，RSS_stopped=false；stdout/stderr 均为空。

三份 fresh 输出按现有 terminal 和 root 指定值核同后原样复制：Pilot.olean77320B / `502f1af585dd03cb3fe538128cf5e5e28a25783cf01979f2909f2dc274260b12`；Pilot.ilean13806B / `d6dc68e8747db71adfdb5024ec7aa878139eb96f1eeee24187ae2f4dff85ec78`；Pilot.c1291B / `69f3c3fa149741d1ae7548ccba17c2276e2b1b482af116d3583838f9118e4f1f`。

原始 started/child/memory/stdout/stderr/terminal 六小文件及三产物均复制到 `work/`，保留原字节；文件清单给全部 bytes/SHA。源及 gate 身份只从既有 terminal 绑定，未重新读取或核大 proof、SDK、runtime、export 或 package 树。本次未重审公理/依赖或新增任何数学执行。普通 Lean 编译时正常的 kernel typechecking 不被关闭，但“通过”严格限于本 pilot。

这里使用 -j1/-M6500/7GiB RSS/3200s 的 Windows 开发测量，没有官方 --setup，也不等价 Linux cgroup 或最终全链资源。single_file_resource_pass、independent_kernel_pass、official_acceptance 保持 false。没有 compiler/进程/网络/UI/Git 新动作，没有新家族或重试，不更改原 work、frozen proof/DRAFT、旧失败、状态或计数。
