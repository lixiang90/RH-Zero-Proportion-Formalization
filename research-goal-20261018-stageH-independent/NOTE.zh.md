# H 独立整数证书审计完成

本包审计固定 H 生产结果，不运行发现算法。producer manifest
`327562525e30d7b706777e71af003e51ca93a218ac7cfd9bfa0994abe56f8f8c`，
root 执行 gate SHA
`2533ebb71be8f21d3ce9306a54e12250229b962974f6f86e2a02b450eb977eb9`。
原准备源码 `45396edbb2ca0162451ebbb19ce00ed853818b7f59a4362af9b899a85d922ac9`
没有修改。此前仅 AST 准备，本次只执行一次数学审计。

真实 CLI terminal exit 0，工具 chunk 8e2b20，wall 3.6781362 秒，
审计 receipt 计时 2.535049700003583 秒。审计完整固定 G 未解序列的
19,838 records：4,460 Empty、15,378 unresolved。

每一个 Empty 都由本脚本直接读取原 source PR/B state，独立重建四朝向
原 153 DBM 行和两 Ordered 四点行，核正整数 sparse 权、完整十坐标
normal 和为零及原 RHS 加权和严格小于零。没有信任 producer 的
Floyd/shortestpath/assignment、最优性或候选 tag。

独立核 G status/bitmap 全部 5,635,876 原 index 并提取同一 19,838 序列；
H 每条原 index 按序且唯一、HRC1/ULEB 完整解码、prefix/count/hash、
certificate 和 remaining 两条流的精确 EOF 通过。已独审的有序可行样本
2417 保守留在 unresolved，没有寻找新点。

没有 import H/C/G producer Python；BF、Floyd、运输、LP、优化器、新
kernel、FS、点拟合和 Lean 调用均为零。具体 source/model/证据 hash 在
independent-review.json 和清单中。

15,378 个剩余项只表示没有本次几何排除证书，不表示已证明非空、实际
低能或最优值。本包不证明完整 joint floor 或新的无条件零点比例；
后续实际函数/计数、Lean、独立 kernel、单文件 2 MB 和全流程运行预算
均未因此完成。没有自动重试或新增试验。
