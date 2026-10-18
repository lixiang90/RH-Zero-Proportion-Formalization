# 去重 Production 四模块单源准备

本包只冻结文本拼接工具；upload-source generator 零执行。四个输入为 Production.Core、Production.Localization、Production.Counting、Production.Final，共1,854,229 UTF-8 bytes。精确字节/SHA以 input-pins/prepared 为准。

Core 来自 canonical strengthened TinyGoal Core，精确以同7字节命名族 PC9QB6M→PC9Tiny；只删旧最终定理代码，旧尾两块版权 block 原字节保留，原 full third-party licenses 全保留，137个 packed walk payload 与所有数学数据/见证不变。三桥只有 import 路径变化，正文与原已通过版本完全相同，原官方 wrapper 字节不变。

算法仍只移出完整单模块 import 行。四个内部 import 由此前拼入的正文替代；24个可信外部 import 原字节/原顺序移到头。所有源体的非import字节逐段保持，并记录offset/hash；不重定义 currentRecordKappa/candidateKappa，不压缩/改写数据。

旧 production-v0 真实在 nanoda 阶段耗尽统一3200秒而失败；ordinary与Comparator/defaultkernel已通过，但不是完整成功。旧 source/prepared/failure/draft 均不覆盖。新文本源和本工具均未通过普通编译、导出或重放。纯静态同源审查不是完成验证。

未来唯一 generator 调用必须由新 production-v1 launcher 在单一 monotonic t0 之后执行，包含在统一3200秒预算内；不在此准备阶段运行。输出目录本包 draft/ 必须不存在，独占创建一次，无自动修源/重试；上传元数据恒 upload_ready=false，直到全套后续验证和材料收集通过。

新可信 CandidateSpec 由新冷目录中从固定官方模板、真实当前可信ledger exactExpression、候选p/q生成。候选与预期纪录见 candidate-parameters.json；若最新纪录变化，停止并重新评估。不得修改旧installed Spec。

仍须完成实际生成/保留字节审计、四模块冷ordinary、公理标准三项、全部三个官方完整陈述及依赖/primitive比较、默认kernel/nanoda、统一generation-through-receipt≤3200秒和官方验收。8GiB仅文件大小限制，不声称RAM上限。不运行网络或网站提交，official acceptance=false。
