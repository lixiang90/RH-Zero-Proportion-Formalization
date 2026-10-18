# 正式接受版本的官方政策与运行证据

本包只读取得官方 `josusanmartin/riemann` 仓库提交 `6bc7f07fb939e066ac2923493d9a01cca553fe87` 的两个 E2B 脚本、`CONTRIBUTING.md`，以及正式接受记录 `lixiang90-single-exception-overlap-20261018` 的公开 `verification/attestation.json` 和 `verification/verifier.log`。原始字节均从 GitHub base64 内容还原，并重新计算 Git blob SHA1；SHA256、字节数和固定提交链接见 `provenance.json`。没有执行取得的脚本。

官方 attestation 明确记录精确 κ、`kernel-verified`、`kernels=[lean,nanoda]` 和标准3个允许公理。完整日志包含 ordinary `Solution.Candidate` 构建成功，以及 nanoda 和 Lean 默认内核均接受的终结文本；不是仅依据网页 running 状态推断。

同一固定提交的 `run-comparator-e2b.sh` 对 Comparator 主验证设 `timeout --signal=TERM --kill-after=15s 3200s`；外层 `run-verification-job.sh` 以 `--mode=full` 调用完整验证，设3240秒外层超时，并显式指定原生 Comparator、lean4export 和 nanoda。内外两个时间范围应分别描述。官方文档规定精确陈述比较、公理检查、Lean 与独立 nanoda 均须接受。

策略上限不是精确实际耗时。公开日志提供个别 Lake 构建用时，attestation 提供接受时间；本包没有把它们相加冒充完整流水线秒数。日志中 trusted Challenge.Candidate 的 sorry 警告属于用于比较的模板占位定理；实际 Solution 的公开定理通过两内核且受标准允许公理约束。

attestation 的 `upstreamCommit` 另有值；对它在本仓库的附加查询返回 no-such-commit 404，不能把它直接称为本仓库流水线版本。这里的5个原始文件已经分别固定到实际 accepted-source commit；附加接口返回原样保存在 transport 中，不隐去查询范围。

本包未运行编译、生成器、export、内核、数学计算或网站提交。原 v3 接受证据、v4 取消证据和原始源文件均保持原字节。
