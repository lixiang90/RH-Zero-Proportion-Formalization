# Tiny 开发版的一次普通编译准备

当前无 Lean 执行授权。本包只做源码切分、命名空间改名、原表别名、字节与
Python AST 检查。冻结 `Core.lean`（9fbdf3…）和 `Counting.lean`（ddb73b…）
原样保留；它们的 prepared manifests 没有修改。

## 为什么不能直接复用原 namespace 或编译原末尾

已通过的 `CurrentPrefix.olean`（8a67fa6c…）包含实际 s1R 解析与表、原
`PC9QB6M.St/Covered/CovK/walk` 的 c9 语义、以及 LB/PT 正确性。它不包含
137 大 packed payload 及其新 E 验证，也没有 W9 和最终计数 tail。

因此不能导入这个 olean 后在相同 namespace 重定义强化 Covered，亦不能
借旧 CovK 当强化 E。开发版把整段新 concrete 放入 `AMW.Cert.PC9Tiny`；
数据/ready/cursor/run 放入 `PC9TinyData`。只有 TOP/BK/lbS/TOPD/BKD/lbD/
REG/hR/PT/ptS 十项别名复用原已经证明且逐字相同的实际核表。137 个 packed
字符串保持原字节；全部新 E 的 numeric、cut、cursor 和 run 仍需重新编译。

本机可信 `CandidateSpec` 原文件已只读快照；candidate 既不是原 s1R record
literal，也不是新 tiny literal。修改 trusted 常数以迁就旧 wrapper 不合法。
开发 Core 只保留至 `end OpethN.Counting`，旧 ActualDefect/AMFinal/public
candidate wrapper 独立归档。完整第三方 notices 和 license comment 保留。

## 模块与真实结论

1. `Dev/Core.lean` 导入已 PASS CurrentPrefix，重证强化 E、还原 c9 baseline，
   保留 W9 和当前 H 的实际计数闭包。编译成功本身不代表 tiny pair 完成。
2. `Dev/Localization.lean` 证明真实分离域的根外付款、完整强化 E/反射唯一例外，
   再用共享 gap 冲突证明实际 `pair_floor`；不依赖 Counting。
3. `Dev/Counting.lean` 是 frozen Counting 仅改 import 的版本，pair/old floor
   输入保持显式，导出当前核的 dyadic/cumulative 接口。
4. `Dev/Final.lean` 用已独审固定有理数 `tinyKappa`，实例化全部有限参数、
   当前 W9 old base 和 Localization pair，目标是无额外前提的真实 dyadic /
   cumulative 定理。它不重定义 trusted `candidateKappa/currentRecordKappa`。

Final 的六根审计覆盖强化 `Data.run`、base cert、actual pair、literal strict
comparison 及两个最终结论。Core/Localization 无自身 print，receipt 只先记
ordinary compile，公理审计延后到 Final；Counting 另有五根完整名称 print。
任一失败立即停止，不把部分 PASS 外推为全域比例完成。

## 唯一未来 runner

`compile_dev.py --gate ROOT_GATE --gate-sha256 ROOT_SHA`

目标按 Core -> Localization -> Counting -> Final 串行；新目录
`tmp/current-s1r-tiny-20261018/dev-v0/lib`。先 pgrep 确认没有其他 Lean，再把
已通过的 CurrentPrefix olean 复制到第一 lib 的精确 modulepath 并双端核 SHA。
这是已观察过的同 namespace root 解析限制，不能只加第二条 LEAN_PATH。
不重编 1248 秒前缀、不编曲率/Sparse/Nano、不运行 solver/FS/kernel Python。

参数与既有协议一致：`-j1 -M13500 --tstack=262144`，prlimit 栈 256MiB，
`relaxedAutoImplicit=false`，`Elab.async=false`。没有自动超时/日志截断。
1200 秒/模块及 20MB 日志是人工报告点；超过时报告真实同 handle 资源，由 root
决定，不自行 kill/restart。保留全部 command/child/source snapshot/log/GNUtime/
receipt/start/terminal/failure。每个 module source 和 runtime 都绑定 hash。

## 仍未满足的最终交付门

manifest 的 uncropped 字节加法包含完整旧 prefix（也包含其已无必要的旧 concrete）、
全部新模块与 license；不是已经构造通过的最终 flattened submission。未来可经明确
依赖裁剪移除旧 concrete，但本包没有依赖裁剪或大小伪承诺。

普通编译四模块全过且允许公理范围正确后，仍须冻结准确 scope、准备真正 tiny 的
可信 CandidateSpec、实际单文件 flatten/size、完整 source 的普通编译、export、Nano、
Comparator/网站 3200 秒资源合同。开发缓存节省本地重复工作，不可从网站最终独立
验收预算中扣去源内 prefix 编译成本。GitHub 同步和提交材料亦未由此完成。
