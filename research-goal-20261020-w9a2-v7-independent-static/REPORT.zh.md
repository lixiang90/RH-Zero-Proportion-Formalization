# draft-v7 独立原始字节审查

结论：`PASS_STATIC_BYTE_PROJECTION`。2026-10-20 仅读取已冻结文件，以独立标准库脚本在内存构造正向与反向投影；没有执行派生脚本、Lean、exporter、kernel、solver 或数学搜索。

旧源为 prepared-v6 的 1,830,052 B，SHA256 `a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26`。新源为 draft-v7 的 1,829,242 B，SHA256 `dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6`。

独立检查精确确认 23 处授权差异：在 `mcheckP`、`mleafP`、`leafStep`、`node`、`walkC`、`walk`、`walkCut`、`walkCutR` 的八个 `def` 前各插入 14 B 的 `noncomputable `；删除全部十五条独立 `#print axioms` 完整行，共 922 B。净减少 810 B。原始偏移、行号和大小逐项列于 `byte-review.json`。新旧源之间不存在其他字节差异；反向投影精确恢复旧源。两者均保留 221 组 CRLF、零裸 CR 和末尾 LF。rc0 至 rc47、所有数值数据、三个公开根的声明及证明、其余定义和证明，以及此次停放的十九个旧消费者均由全局字节投影保持。

同时逐行核对 draft-v7 `files.json` 的全部七个文件大小及 SHA；九个输入文件的前后哈希一致。仅把该包的脚本当作冻结数据读取，没有导入或执行它们。独立 `check_bytes.py` 实际退出码 0，工具输出 chunk `fffd0b`。

语义范围沿用已冻结的两个静态报告：`research-goal-20261020-w9a2-unused-dependency-static/files.json`（`cb17ce3e4b495f484dd36b152b30785cada29275f85cfc0e7ecc7a30b5628efc`）记录十五条命令只作信息输出、官网比较器自行检查导出公理及旧消费者停放；`research-goal-20261020-w9a2-static-build-cost-formal/files.json`（`c42347e3222396f65c27d47195696c645013433b67ed583ae008dda24dae6d4b`）记录八个显式 noncomputable 标记的代码生成边界。此处不扩展为新一轮语义或编译核验。

本结果不声称 v7 已编译、导出、通过任一 kernel、满足 3200 秒门或获官网接受。先前 a517 官网超时和原始过程状态保持原义；v7 需要官网对这个精确新源给出实际结果。若有新的本地日志收集合同，不能继续要求已删除的源内 `#print` 输出，也不能用空日志替代实际导出公理审计。未修改任何候选源、冻结旧包或主轮计数。
