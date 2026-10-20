# 本次官网接受的最小证据链

只读既有资料整理；没有网络请求、提交、编译、数学试验或计数修改。接口行为依据已冻结的官方源码 commit `1135c0386310a0a038004d3b0fe64d0237e47dce`，不是新取得的服务端部署版本证明。本次是否提交、重放或接受均不由本报告推断。

固定候选是 `lixiang90-w9a2-weighted-potential-20261020`、Li Xiang/@lixiang90，源码 1,830,052 B，SHA256 `a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26`。精确 K 为 `3337881639516708570682858853672166187793/4955348542279967171490000000000000000000`。当前预期组合 proofDigest 为 `e76462f687d4e95d7f9f2ebb558bd5d2d5452814f01e54fd657856dbb12157d1`，仍只是预测；不能写成官网已观察值。

提交后只需完整连接下面四项，新增一个小 official addendum，保留冻结包中的历史 pending 标志。

1. **同一实际上传。** 保存实际 admission/status 响应的 submissionId、实际 proofDigest、时间与 job 身份，核对解码后的实际 wire solution 仍为 a517/1830052B。文件上传后不编辑 textarea、不 trim 或换行转换。实际 digest 先与预测 e764 比较；若不一致，保留真实响应并定位 manifest/source 的字节差，不把预测值写成真实值。签名 job handle 是登录账户的状态句柄，公开交付引用公开 commit 证据。
2. **官网两内核核验。** 保存官网 `verified` 结果、其 attestation 和完整可得 verifier log。attestation 必须属于同一 submission/作者/精确 p/q，`result=kernel-verified`、`kernels=[lean,nanoda]`，三 theoremNames 恰为 `candidate_strict_improvement`、`candidate_critical_line_bound`、`candidate_critical_line_bound_cumulative`，允许公理恰为标准三项；保存 previousRecordId、upstreamCommit、challengeDigest、verifierTemplateDigest、verifiedAt。日志应实际有普通 Solution 构建及两内核最终接受文本。保存 completedAt/observedAt 的原含义，不把单步耗时或时间上限冒充公开总 elapsed。
3. **正式晋级。** `promotion.status=promoted` 或 `already-promoted` 及其 immutable evidenceUrl 才是发布状态；`verified` 本身可能仍 awaiting-configuration 或 superseded。另从官方公开 ledger 取得同 ID、精确 K、Li Xiang/@lixiang90、`status=kernel-verified`、`formalVerification=true` 和 sourceUrl/proofUrl 的记录。若后来有更高纪录，保留本次实际 promotion/ledger 历史，不能仅因它不再是 current 而否定既有接受；superseded 且未晋级则不能声称新纪录发布。
4. **公开字节闭环。** 按实际 evidence commit 下载同目录下四个文件：`submission.json`、`proof/Solution.lean`、`verification/attestation.json`、`verification/verifier.log`。源码原字节必须等于 a517/1830052B；原始 manifest 与 source 重算组合 digest，必须等于第1项的实际 job proofDigest。核对 manifest 的精确 p/q、三 theorem 名、作者、license 和已审字段；这把成功 job、两内核 attestation、已发布 record 绑定到同一份源，而不只是同分或同 ID。

组合摘要算法是 `SHA256(UTF8("submission.json") || 0x00 || manifest_raw || UTF8("proof/Solution.lean") || 0x00 || solution_raw)`。它不等于单独源码 SHA，也不等于 attestation 的 challengeDigest 或 verifierTemplateDigest。

可见状态与入口：

| 入口 | 作用与边界 |
| --- | --- |
| `https://www.riemannzeta.fun/submit` | 原账户的 queued/running/verified/rejected 页面；显示实际 digest、结果、日志与 Open immutable evidence。`running` 文案不表示任何 kernel 已通过。 |
| `/api/submissions/status?job=<signed-handle>` | 需登录及正确签名句柄；捕获源码中的 GET 会启动/推进已入队任务或完成 promotion，并非公开被动查询。本报告没有调用。完整结果可能带 attestation；已完成队列响应可能只保留 verdict、digest、log 和 promotion，须再取公开 attestation。 |
| `/api/submissions/active` | 登录账户的现存任务恢复入口；不是公开接受证据，也不是新提交入口。本报告没有调用。 |
| `https://www.riemannzeta.fun/api/leaderboard` | 公开 GET，读取 current 与 records；保存 HTTP/body/时间/cache headers。其构建数据与缓存可落后官方 GitHub 晋级，不能仅因短暂旧 R 重复上传。 |
| `https://www.riemannzeta.fun/submissions/<actual-id>` | 公开 record 页面；可见 Kernel verified、精确表达式、作者及 evidence 链接，同样可能等待部署刷新。 |
| `https://raw.githubusercontent.com/josusanmartin/riemann/<EVIDENCE_COMMIT>/submissions/<actual-id>/<file>` | 四个公开原始证据文件的固定 commit 读取入口；commit 从实际 evidenceUrl/sourceUrl/proofUrl 获取，不用本项目 checkpoint52ce…代替。 |
| `https://raw.githubusercontent.com/josusanmartin/riemann/<PROMOTION_OR_LATER_OBSERVED_COMMIT>/data/records.json` | 含新 record 的官方固定 ledger。evidenceCommit 与 promotionCommit 不同；前者先写四证据，后者再追加 record，不能误从前者读取旧 ledger。若响应未暴露 promotionCommit，可记录其后实际观察到且确含该 entry 的官方 main SHA。 |

上一轮可直接复用的证据方法与确切路径：

- `research-goal-20261019-record-accepted-independent-1753/ACCEPTANCE.zh.md`、`comparison.json`：HTTP200/Age0/MISS、公开 kernel-verified record 与 source/manifest 原字节同一性；`digest-verification.json` 将实际任务 digest `23e3dd…` 与公开原始 bundle 精确相连。其 `accepted-files.json` 为 c528b3b8…。
- `research-goal-20261019-official-policy-acceptance-audit/audit.json` 及 `snapshot/submissions/lixiang90-single-exception-overlap-20261018/verification/attestation.json`：正式 attestation 与日志中的 `Nanoda kernel accepts the solution`、`Lean default kernel accepts the solution`、`Your solution is okay!`。完整旧日志身份和固定链接见该包 `provenance.json`。
- 该旧 policy 包的 `snapshot/scripts/run-comparator-e2b.sh` 和 `snapshot/e2b/run-verification-job.sh` 在旧接受 commit6bc7…分别约束主验证3200秒、外层3240秒，并指定 full mode；这是上轮固定版本的政策证据，不是本次精确总耗时。新接受后如需要重证政策版本，按新官方固定 commit 另存这两个小文件，不能把 attestation 的 trusted-upstream commit 当成网站仓库流水线 commit。
- 本次固定输入在 `submission/w9a2-weighted-potential-20261020-prepared-v6/`；预期 server manifest 与 digest 说明在 `submission/w9a2-weighted-potential-20261020-expected-wire-v6/`。`research-goal-20261020-w9a2-replay-submission-addendum-preparation/README.zh.md` 已规定用新 addendum 记录实际结果，不改历史 false 标志。

宏观008的范围仍保持：原本地 cold3200 失败永久保留；本地分阶段数学通过不替代官网接受。只有官网固定完整流程实际接受并完成上述身份闭环，才能用官方接受补足本路线的最终整轮门。
