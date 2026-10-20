# v8 失败封存与状态窄审

审查对象为已推送 commit `3635d319550a1f3994eabc93328ac36c09302305` 的小文件封存及状态表达。只核 failure 清单五成员、followup 清单三成员、方向/状态/continuation 当前入口和 Git commit 路径；不重新核大源或 runtime，不运行网络、UI、编译、export 或 kernel，不修改 proof、状态或研究计数。

两清单的 bytes / SHA256 核对结果及输入 pins 见 `audit.json`。Git 路径清单只说明本地该 commit 内容，不独立证明 GitHub 当前远端状态。followup 中的 COMPLETION-EVIDENCE-MAP 是较早静态预案，虽不是本 commit 新变更路径，仍作为三成员清单输入核对；它不是本次验收完成证据。

failure 原始观察与日志支持：同一 v8 ID / fb457 bundle，Solution.Candidate build 显示 939s，Lean137、bash1；无 Solution 成功完成、Solution export、双内核完成或接受。2057:30 是首条 push_neg warning，不是已定位的 type error；没有 RSS / OOM event 不能确诊 OOM。四原始文件保持原字节。

followup journal 前三行是同一 ID / bundle 的 running / queue0 记录；末行是 15:40:11.565Z 的 none。其来源范围由 README 和失败 observation 明确为 root 对已显示安全结果的转录，未保存私有 API 原始响应或 token，不能把 journal 称作 raw API 下载。当前 quota 为剩余 0 / 3，2026-10-21 00:00 UTC 重置。

commit 状态的 current_official_submission 和 latest_submission 已正确指向 v8 failed，official_acceptance / official_kernels_complete / goal_complete 均 false；main_rounds_since_review=1、last_review_number=12。DIRECTION 与 continuation 首段明确本次失败覆盖较早 running，保持完整研究目标 active，而非认定完成。

发现待 root 修正：`website_submission_authorization` 内旧首投同级字段仍以 `actual_website_state`、`latest_owner_API_state`、`details_poll_state`、`actual_proofDigest` 等名称保存 timeout / running / e764 历史信息，没有独立的 historical-first-attempt 范围。虽然同一对象的 latest_submission 已是 v8 failed，直接读取旧 “latest” 字段仍可能误判当前。root 已认可，应另做状态澄清，将旧值明确归入 historical_first_submission；本审不更动已推送状态或失败收据。该发现不否定四份原始失败证据或两清单完整性。

本审结论限于这些小文件、commit 路径和状态范围，不重审数学、单文件源码、SDK、runtime、公开 promotion 或远端同步，也不授权新执行或提交。
