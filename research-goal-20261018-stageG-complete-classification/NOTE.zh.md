# G 唯一完整分类：生产完成，内置独审失败保留

书面 gate：`research-goal-20261016/gates/stageG-complete-classification-20261018.json`，
SHA `1ff39dcea19f6db3fa4b49c8036dfc8b7a22728e00994ef8147173011395acb7`。
准备版所有 source 和输入哈希保留；没有改变阈值、FS、原 state 或朝向。

唯一 child PID 15652、parent 58832，exec session 61986，真实 terminal
exit 0，wrapper 30.819247100007487 秒，无资源停止/失败。完整范围
5,635,876 cases、688 个耐久 frames 全部生产完成，closed output 4,574,379
bytes（该数为 terminal 当时口径，不含此后独审失败说明和封存文件）。

生产四类计数：paid 2,108,692；strict_projection 3,507,051；
other_strict_cycle 295；unresolved 19,838。合计完整范围，且 paid 数与既有
纯整数规模审计一致。F 的新序号 4768 为 unresolved，只作注记，没有
将其另外有效的 Lower 证书计入此次闭合数。

`prefix.json` SHA
`afaf3c0a3d33585164fabc4722cf04ecd34a0d48a6513b5a1a7e5d174a8322cf`。
status/bitmap 为 1,408,969 / 704,485 bytes，projection/cycles gzip streams
为 1,328,952 / 15,240 bytes；log 1,009,334 bytes。
精确四状态及 binary 规则见 SPEC。unresolved 仅表示本固定判据没有提供
排除证书，绝不表示非空或实际低能。首个 potential 仅一个诊断样本。

## 内置独立 replay 的单次失败

依授权执行 `replay_complete.py --write-receipt` 一次，真实 exit 1，
1.8446292 秒。源码 line 93 的 path join 拼写为 `ROOT[s['path']]`，
触发 `WindowsPath` 不可 subscript 的 TypeError；尚未进入 frame/case
证据循环，未生成 independent-complete-replay.json。
完整 trace 和命令保留在 replay-failure.txt，元数据在 replay-attempt.json。
失败源码和所有生产输出原样封存，没有自动修复或重跑。此包不能宣称
独立数学回放 PASS；独立代理的自有 checker 将另包给出结论。

## 作用域

这是固定完整数学机会分类的生产结果，不是完整 joint floor，更不是
无条件零点比例新纪录。19,838 unresolved 仍是全域缺口；没有启动任何
LP、kernel、新 FS/transport、阈值或 Lean 批次。4.6 MB 研究数据不是网站
Lean 源码，181,589-byte 源余量、完整消费者和网站全流程运行预算仍未知。
完整正式证明、独立 kernel、云端提交和网站提交材料均没有因此完成。
