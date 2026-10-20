# draft-v8 独立字节审查

`PASS_STATIC_BYTE_PROJECTION`：新源精确等于冻结 v7 在 `PTT_0`、`PTT_1`、`PTT_2`、`PTT_3`、`PTT_4`、`PTT_5`、`PTT_6`、`PTT_7`、`PTT`、`PT` 十个唯一 `def` 锚点前各加入 `noncomputable `。共十处、增加 140 B、删除零字节；没有任何其他改动。独立脚本在内存生成的正向投影等于实际新源，反向投影逐字节恢复 v7。

新源 `research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean` 为 1,829,382 B，SHA256 `5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b`。旧 v7 为 1,829,242 B、`dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6`。全部其他源字节保持，涵盖数据、证明、三个公开根和先前停放的消费者；另显式确认原八个 noncomputable 标记、零条 print-axioms 命令、rc0 至 rc47 完整源行、221 个 CRLF、零裸 CR、LF 总数及末尾 LF 均保持。

draft-v8 冻结 manifest `7f449697314ee04088f1874a6cfdd609c02bb322995feb1197406133ded2a776` 的六个文件均按实际大小及 SHA 核对，八个输入前后哈希不变。`check_bytes.py` 仅用 Python 标准库读取冻结字节，没有导入或执行包内派生脚本；实际退出 0（工具 chunk `e605ff`）。

本小审只确认十处 raw projection 和准确标签，不重复消费者、源 profiling 或 SDK codegen 审查。相应语义边界属于 `research-goal-20261020-w9a2-v7-resource-static-formal/files.json`（`d0d2cbc52609572056faa4dd06cbff7053ba633e5c36482b9df293bb4fdfd913`）。没有运行 Lean、compiler、exporter、kernel、solver、资源 gate 或官网提交，没有改候选源或主轮 counter，也不声称新源编译成功、内存或速度改善、数学重放通过或正式接受。
