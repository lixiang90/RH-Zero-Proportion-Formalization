# Tiny 单源交付准备合同

本包只准备纯文本拼接工具；prepared 不表示已经运行 generator，也不表示上传就绪。
不修改普通编译正在读取的任何输入，不启动 Lean、export、Comparator、nanoda 或网络提交。
本机旧 CandidateSpec 不符合 tiny 目标，不允许修改它来通过编译。

## 输入和保持规则

固定顺序：CurrentPrefix、Dev.Core、Phase1.Localization、Phase2.Counting、Phase4.Final。
模块路径更新，Lean namespace 仍为 Dev.Localization/Dev.Final；wrapper 完全不变。
五个原始 UTF-8 文件合计 1,977,052 bytes。实际 SHA 和大小由 input-pins 及 prepared 绑定。
每个源仅移出完整的单模块 `import` 行：内部依赖由前面拼入的正文替代；其余所有
第三方/可信 import 原字节、原顺序移到总文件头。所有非 import 字节（包括全部版权、
许可全文、来源说明、数据、证明、section/end 和 option）逐段完全保留，输出记录 byte
offset 和 retained-non-import SHA。未删除评论中的任何 import 文字。
不剪裁旧通用 checker、不重写 payload、不添加旧 candidate 包装，不优化本轮代码。
若输入 SHA 改变，工具硬停；编译修复必须另外版本化再准备，不静默拼入新源。

## 官方公开接口与可信规格

三个名称和完整陈述取自官方冻结模板
`research-20261016-w10-cert/website-snapshot/challenge/templates/Challenge.Candidate.lean`。
provenance 给出官方仓库 josusanmartin/riemann 的固定 commit
9e6ca6615b9dbfec4a1d722995cff0ffe3abf9bb，两个模板的原始 URL/哈希可核。
较新捕获 cb97717d3ea82c45f19f2ce04c410440b6492aa6 的 contract/CONTRIBUTING/
prepare-candidate.ts 仍指向完全相同的三个名称、陈述和可信生成流程。
本次 web 打开较新固定 commit 的三个 template URL 返回 cache miss；没有获得新的模板
字节，不称本次已实时确认它们。正式 production 前须核最新部署合同与模板。

wrapper 只添加两个私有等式，把可信 candidateKappa/currentRecordKappa 与新 Final 的
tinyKappa/baselineKappa 连接；三个公开定理直接调用 Final.strict_improvement、
actual_dyadic、actual_cumulative。没有重定义任一可信常数，没有旧候选包装。
本包 `.lean.txt` 是拟拼入正文的源片段，尚未 elaboration。

提交参数 p/q 见 candidate-parameters.json。正确规格的流程是：官方服务器从提交表单
取得这两个十进制整数字符串，从当时 kernel-verified ledger 最后一条记录取
currentRecord.exactExpression，再由原 CandidateSpec.lean.tmpl 替换
CURRENT_EXPRESSION/NUMERATOR/DENOMINATOR。参见冻结 prepare-candidate.ts:22–30,
90–105。本包只记录请求参数/预期纪录，绝不写 ChallengeDeps 路径，也不把自制预览当
trusted。若正式纪录变化，旧 record_identity 可能失败，应停止并重新评估目标。

## 未来文本生成命令（本 prepared 未运行）

```
C:/Python314/python.exe -B -X utf8 research-goal-20261018-tiny-flatten-preparation-v3/generate_draft.py --generate-draft-once --prepared-sha256 <prepared-files.json的SHA256>
```

仅允许独占新建本目录 draft/；若目录或任一输出已存在则拒绝覆盖。输出
Solution.lean、candidate-metadata.json、generation.json；upload_ready 恒为 false。
元数据没有伪造 author、submission id 或官方 attestation。
工具本身不调用子进程/网络/编译/求解器，不改原输入；前后逐依赖哈希复核。
中途失败保留原已写输出，不自行修源或重试。

## 尚未闭合的验证门

1. 四模块本次 ordinary 编译及其故障记录由 sole compiler 所有；本包不预言结果。
2. 实际文本生成、独立保留字节/许可证/内部 import/三个 statement/源体积审查。
3. 官方新鲜 record、contract、工具链与依赖身份；由官方模板生成正确 tiny Spec。
4. 最终单源在新可信规格下完整 ordinary elaboration，所有有限检查及三个 theorem
   无额外前提，公理仅 propext、Quot.sound、Classical.choice。
5. 单源 export、Comparator 精确 statement、公理闭包与独立 nanoda 全部实际通过。
6. 网站全流程 Comparator 3200s / job 3240s 与部署限制内的真实资源证明。
   捕获的 8GiB 来自 `ulimit -f` 文件大小限制，不能解释成 RAM 上限；实际内存限制
   另待部署合同确认。模块 cache 成功或源文本小不等于此门通过。未来 soleowner
   统一 launcher 的总 t0 必须在调用本 generator 之前，纯文本生成时间同样计入
   3200s，不先单独生成再重新起表。
7. 最终源小于等于 2,000,000 UTF-8 bytes，网络提交 JSON 不超过其独立上限；完整
   GitHub 同步、来源/许可证、提交元数据与用户最终交付。没有任何上传授权由本包产生。

源码预算只按实际 UTF-8 bytes，不以 gzip/JSON 或 olean 尺寸替代。metadata-only
preparation 给静态精确预测；实际生成后的真实字节及验证仍需核。任何未来失败都要
留原版本/原退出证据，不把 prepared、模块数量或条件结果称为无条件新纪录。

## 版本与停止线

旧 v0 prepared918b377…/generator ebbaaba… 保留且未执行。v1仅绑定正式授权的
同命题API修复源与Final import-only变化，非重新选择数学目标。普通模块编译仍由
soleowner负责；本包既不执行它，也不预判通过。即使新普通模块通过，本 prepared
仍不自动授权生成。须由root审查后决定统一生产launcher的唯一执行。

本 v2 仅绑定 Phase2.Counting 的 let/Nat cast 归一化和 Phase4.Final 的函数别名/根计数名修复。算法、wrapper、阈值、数学命题均保持；输入版本是已冻结准备，不代表 ordinary 通过。generator 仍须在统一生产 t0 之后执行一次。

本 v3仅将最后输入更新为普通内核和六个传递根公理审计已通过的 Phase4.Final；绑定该次 receipt/terminal，不复用其用户 olean 做最终单源检查。本文仍是准备，generator 零执行。
