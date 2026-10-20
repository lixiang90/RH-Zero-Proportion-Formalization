# runtime v3 小差分独立静审

`PASS_STATIC_EXECUTION_REQUIRED`。核 v2 和 v3 的冻结清单，新包 be1227…、assembler cc7ca3…、helper 6b4ff6… 均相同；22 个读取输入前后 SHA256 和长度一致。实际 v2→v3 完整 source diff 等冻结 patch，旧 v2 未写入。

helper 只改两个哈希 C 符号所在库和实际加载路径核对，改为 libInit_shared.dll。现有纯 PE 文件扫描覆盖已官方逐字验证的九个 SDK DLL，两个精确符号均为该库直接导出、非 forwarder；九个扫描文件的 SHA/size/resolved metadata 逐项等实际 SDK archive-check 收据。没有由本审查加载 DLL、重扫 PE 或调用 API。

assembler 新增可选的 SDK archive 已完成组件复用。旧 v2 整体 setup 退出 1，但在其后失败之前，13951 个 archive member 比较已完成并保存实际收据 f052fa…。新路线仍先重核当前 archive 硬 SHA；要求 root 新 gate 接受组件；逐一重核每个成员当前 SHA、size 和 resolved path，且成员集合严格相同；保存旧实际收据与新的重检收据，原 tar 比较 fallback 保留。它没有把旧整体失败当整体成功，也不略过当前文件核对。

不存在新的已知确定差分 blocker。此前 source/ABI/Cache/legacy/旧工具来源逻辑不变，当前 gate 模板仍 authorized=false、compiler/export/kernel main 均禁止。实际 DLL 符号获取、哈希控制与全部来源闭包仍须新实际 setup 完成并由 root 确认真实 exit0；此静审不证明完整 runtime 或候选内核接受。
