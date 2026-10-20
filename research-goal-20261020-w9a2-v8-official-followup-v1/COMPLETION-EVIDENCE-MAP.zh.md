# 正式终态后的证据定位（静态预案，非本次验收结果）

依据已保存官方primary与旧accepted schema静态提取；本文件不证明当前v8已通过。`owner-active-observations.jsonl`在等待期间只追加实际白名单字段，尚未封为终态收据。当前目标仍完整、active，review12/counter0；交付等待不增研究轮。

1. owner结果应绑定v8 ID及proofDigest fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4。`status=verified`与`promotion.status=promoted/already-promoted`分开核对；`awaiting-configuration`、`superseded`和UI标题不是公开新纪录。durable completed响应可能不再包含attestation及两个commit，须从公开evidence补全。
2. 正式attestation核schemaVersion1、submissionId、Li Xiang/lixiang90、model null、Codex、精确p/q、30位scoreDecimal、previousRecordId、upstreamCommit、三个固定theoremNames、result kernel-verified、verifiedAt、challengeDigest、verifierTemplateDigest、kernels有序tuple `[lean,nanoda]`、permittedAxioms `[propext,Quot.sound,Classical.choice]`。不自造leanPassed/nanodaPassed字段；本次challenge/template digest不能用proofDigest或旧accepted常量代替。
3. 官方repo josusanmartin/riemann：promotion的evidenceCommitSha E与promotionCommitSha P不同。E下须取`submissions/<v8ID>/submission.json`、`proof/Solution.lean`、`verification/attestation.json`、`verification/verifier.log`；P下取`data/records.json`。若durable仅给evidenceUrl，从该固定40hex URL和ledger的sourceUrl/proofUrl定位E。
4. E的源码必须1829382B/SHA5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b；submission JSON1343B/SHAd88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a；原始字节按submission.json NUL + JSON + proof/Solution.lean NUL + proof重算fb457。不可trim或规范化221CRLF。全部身份、分数、契约、定理、公理字段须匹配本次提交。
5. P ledger row同v8ID、status kernel-verified、formalVerification true、exactRational本p/q、Li Xiang/lixiang90/null/Codex、sourceUrl/proofUrl同一E。页面/API可能缓存，固定P ledger与固定E四文件是主证据。independentReview null为正常schema，双内核证据在attestation.kernels。不得拿推广后的自己K要求再次严格超过自己。
6. 公共verifier.log可能截断；owner durable日志有omittedBytes时须保留标记。attestation无elapsed字段；如果本次未披露总秒数则保持unknown，不能以click到页面时间伪造3200秒实测。原local v1/v2失败、Nano中断和cold3200失败保留，官网成功另建实际证据，不翻旧flags。

源码scope参考：form.tsx202–217/498、status route88–104/243–282、attestation.ts16–70、challenge.ts190–214、verify-submission.ts321–360、github-promotion.ts239–246/436–484/559–590/630–635。终态时再以实际固定commit和数据为准。
