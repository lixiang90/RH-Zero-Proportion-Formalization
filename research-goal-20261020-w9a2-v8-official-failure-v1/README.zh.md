# v8 官网终态失败封存

本包保存本轮第三次官网提交（v8）的实际失败观察。四份原始文件由 root 保存，本次仅新增本说明及 `files.json`，不改原始文件字节。

- 提交 ID：`lixiang90-w9a2-weighted-potential-v8-20261020`。
- 实际页面 bundle / proofDigest：`fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4`。
- root 记录的固定源：1829382 字节，SHA256 `5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b`。本包不复制或重新验证大源文件。

`technical-log.dom.txt` 是认证后恢复提交页面中可见技术日志的保存文本；`full-visible-result.txt` 包含页面诊断与该日志；`terminal-result.png` 是 root 实际取得的终态截图；`observation.json` 是 root 的观察转录。它们不是私有 verifier-status API 的原始下载响应，也不构成完整进程输出未截断的保证。

实际日志显示 ChallengeDeps、ChallengeDeps.CandidateSpec、Challenge.Candidate 分别成功 build（138s、3.0s、5.9s），随后出现 Challenge export marker。Challenge 中三条 `sorry` warning 属于可信挑战模板，不能据此归咎于用户 proof。依赖的 `Replayed` warning / info 行不能当作本次实际重编译耗时证据。

Solution 阶段记录为 `Building Solution.Candidate (939s)`，随后 `Lean exited with code 137`、build failed、`bash exited with 1`。939s 是该 build 阶段显示值，不是本次完整流水线的精确总耗时。日志没有 Solution 成功完成、Solution export 或任何完整双内核完成证据。

页面分类为 `lean-elaboration-failed`，其 `Solution.lean:2057:30` 对应日志中第一条 `push_neg` deprecation warning。Solution 共有七条此类 warning；该位置不能定位一个已证实的 type error。退出码 137 的成因在本包中未知：没有 RSS、cgroup OOM event 或等价证据，不能确诊 OOM，也不能将该结果解释为数学命题被内核拒绝。

`observation.json` 记录 owner active 状态于 2026-10-20T15:40:11.565Z 为 `none`，来源是 root 对已打印安全 DOM JSON 的转录，不是本包保存的 raw API 响应。终态页面观察时间记录为 2026-10-20T15:49:35.568Z；不据此补造 server job 创建时间或 ID。页面记录当日剩余上传次数为 0 / 3（不是已用 0 次），重置时间为 2026-10-21 00:00 UTC。

本次官网验收失败，official accepted、public promotion、双内核完整完成和完整研究目标均未达成。旧源、旧提交及本地失败证据保持原状。本次封存没有编译、export、kernel、网络、UI、Git 或新提交动作，也没有修改方向状态或研究计数。
