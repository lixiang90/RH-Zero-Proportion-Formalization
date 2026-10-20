# Graph v2 与 draft-v2 独立静态复核

`PASS_STATIC`，79 个读取输入前后 SHA256 与长度一致。没有 Lean、导出器、默认内核、NanoDa 或数值/优化搜索执行。

主线程新 graph-repair-v2 的 10 项清单全部核实。相对冻结 graph-repair-v1，只在源码第 151 行把现有 simp 包成 `(try simp only [Fin.reduceFinMk])`，增加 6 字节；全部 222 处 CRLF 保持。同 reverse_span 类型原字节相等，正反回投精确；相对 canonical v0 累计仅增加 38 字节。全部其他定义、图数据、成本、StateAt 和公开 API 字节保持不变。

语法作用域符合该修复目的：每个 norm_num 后尚未关闭的 goal 上尝试原有 Fin 归一化，simp 无进展时由 try 恢复原 goal，随后原 ring 仍对每个幸存 goal 运行。它没有放宽结论或跳过 ring。

失败证据六文件逐字等于实际 candidate-ordinary-v2 job 文件；module 收据退出码 1、source SHA 等于 Graph v1、log SHA 等于实际 165 字节日志，唯一 error 为 `simp made no progress`。真实父 session 42867 退出码 1 以主线程 repair.json 记载为依据，普通 terminal 也为 passed=false。未把新 Graph 标记为通过。

同时核实 delivery draft-v2 的 18 项内清单和 21 项外清单。它的 flat 1,829,987 字节、SHA256 `43cfdfddf4282e29c5f7f251ce6b33462964919173104efe0533438097c5107b`，相对 draft-v1 只增加 Graph v1 的 32 字节，正反投影精确。从五个冻结模块非 import 字节、冻结 HEADER 和原 wrapper 独立重构等于该 flat。其余四模块、wrapper 和 trusted 文件与 draft-v1 逐字相等，三个公开定理类型原字节不变，并在仅删除空白后等官方 Challenge。

draft-v2 使用曾失败的 Graph v1。此处只确认源字节，不声称它编译通过。交付下一版须改用 Graph v2，新编译与完整内核验收均由主线程继续负责。
