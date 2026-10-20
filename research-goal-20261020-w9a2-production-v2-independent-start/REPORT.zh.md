# Production v2 绑定计划与启动的独立只读核对

本复核仅用标准库读取 JSON、源文件及 SHA；没有导入或运行项目 helper、Lean、exporter 或 kernel。结论仅为绑定计划与启动检查通过，不是 production v2 PASS。原实际 handle 68962 由 Root 持有并等待。

- 新 gate SHA `3ebcc3b75ee2a75775281a2a0e9321f7610baddcab5965fcf002fd51e2d763fd`；原 frozen runner 仍为 `92cc8dcf…`。单一 `/root` owner、3200 秒预算、0 自动重试/修复、禁止 cached user olean 均明确。
- 启动收据 PID 49320、t0=11264.218 与新 gate hash 相符。已经观察到 generation.json 的 fresh source generation，实际生成的 Candidate 与 frozen draft-v6 同 SHA `a517df6a…`，1,830,052 bytes。
- 该源与旧 failed flat source 的唯一差异，是 Counting 三个 Bridge.wfun 前缀，共 51 bytes；其余平铺字节相同。
- disabled preflight 的 assembly PID 34720、原 session 49850、真实外层 exit0、raw tool result、disabled proposal 和归档 manifest 全部对应；proposal 自身 proof_runs=0、未生成/复制证明源。新 gate 另作显式授权，没有把 disabled proposal 当成生产通过。
- 262 个 bound manifest 输入全部重新核 SHA/大小及适用的 resolved path；draft manifest、source plan、普通 v6 两模块实际完成收据及十二个标准公理根一致。普通阶段仅是开发预检，不复用其 user olean 到 production。
- 旧 runtime closure 精确复用 v5 的已完成可信依赖数据，SHA `4d295c05…`；对应实际 setup PID 40712、原 session 35077、exit0 与 source/data checks 相符。其 user proofs setup 编译/复用为 false，official runtime equivalence 仍为 false，原 Windows/Python/Mathlib local-cache/WSL 信任边界保留。
- 十个 package overlay 路径与 closure 相同且没有已知 user olean；interpreted overlay 恰五个工具 olean，含 nested Parse。没有重复全量 runtime 数据遍历；唯一生产 runner 正在承担完整文件 pins 与后续不可变性检查。

新 gate 的 fresh leaderboard receipt/body 以及严格改进的精确有理数也已对应。生产普通编译、精确比较、default Lean replay、serial Nano、总耗时与三个完成收据仍以原 Root handle 的实际结果为准。
