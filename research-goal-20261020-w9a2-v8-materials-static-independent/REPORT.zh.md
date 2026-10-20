# v8 DRAFT 提交材料独立静审

结果为“字节与 wire 绑定匹配，另有明确的 DRAFT 文字准确性问题”，不构成可提交、资源 PASS 或数学验收。没有执行材料生成脚本、编译、exporter、kernel、数学检查、网络、UI、API、进程查询或提交，也没有修改旧 DRAFT、源、root 状态或 counter。

## 实际核对结果

逐项读取并验证三个 `files.json` 对应的全部 19 个文件：prepared-v8 为 13 项，expected-wire-v8 为 2 项，preparation outer 包为 4 项。三个实际清单 SHA256 分别为 `5bfb2d54a88cf28dd2b0b5b413bf3e5df5f3967d04d85d4037f93eddf051ca1e`、`7be638eb265f940efaecd305d4a0a8db9d4fedc4cd4c640d974939979eadad25`、`review.json` 内记录的 preparation 清单 SHA。准备观察所记录的前两个 digest 与实际一致；其 exit0 是已有纯 metadata 准备观察，不是本审重新运行该脚本或证明任务。

`prepared-v8/proof/Solution.lean` 实际为 1,829,382 B、SHA256 `5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b`，逐字节等于冻结 draft-v8。保留 221 个 CRLF、零裸 CR、一个末尾 LF，距 2,000,000 B 源限制余 170,618 B。

`submission.draft.json` 与 `expected-server-submission.json` 完全同字节，均为 1343 B、SHA256 `d88b70050b2a1e1a69d2e1044bcc6a3d1a75c56ab8342f8559f77fe9b270362a`。字段互相一致：Li Xiang / lixiang90，model 为 null（UI 空），harness 为 Codex，605 个字符且 605 个 UTF16 code unit 的 summary，同一 method、三个固定 theorem 名、Apache-2.0，以及精确 p/q：

```
3337881639516708570682858853672166187793
/4955348542279967171490000000000000000000
```

该服务器 manifest 相对 v7 仅改变 submission ID 为 `lixiang90-w9a2-weighted-potential-v8-20261020`；作者与其余字段不变。LICENSE 与 ATTRIBUTION 文件实际同 v7 字节；嵌入 source notices 随完整冻结源复制保留。这里核对保留和身份，不作新的法律判断或数学重验。

按已保存 primary `direct-submission.ts:21–30,56–80` 的顺序，独立重算：

```
SHA256("submission.json\0" || exact manifest UTF8
       || "proof/Solution.lean\0" || exact source bytes)
= fb457eecc550ce09bee528294dfff90137631c08e95fa26ffba1e99ec4e11bd4
```

保存的 client 将空 model 映为 null，传递原 `solution` 字符串；schema 的直接提交通道允许 1000 字符 summary。没有把客户端仅用于比较 flow-test 的换行归一化应用于上传源。另对旧 v7 的实际冻结 wire/source 重算，得到 `1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771`，与既有 root 实际 UI proofDigest 观察一致。这里没有下载或重抓任何 v7/v8 网络请求；新 v8 的上述 digest 仍只是预测，尚无实际官网 observed digest。

## 准确性问题及全部相关位置

1. **继承的源版本句不准确。** `prepared-v8/ATTRIBUTION.zh.md:1` 称 `proof/Solution.lean` 是“draft-v5 原始字节的完整副本”。实际源是冻结 draft-v8 的 5424… 字节，已经历 v5/v6/v7 继承修正及 v8 的十处 noncomputable 插入。该句不能用于当前源 provenance。文件同 v7 字节及许可文字保留属实，不会使旧版本句自动正确。旧包保留；新的权威 ready 包应准确说明当前 raw-v8 身份和继承关系。

2. **启动转录的 parent/child 角色误标。** `v8-submission-materials-preparation/root-resource-start-report.json:5` 将 12924 放在 `parent_pid`。实际 v1 终态证据是 parent 54132、Lean child 12924；`prepare_materials_v8.py` 也沿用该误标作静态 assert。prepared README、MATHEMATICS 与 preparation README 中泛称 session72573/PID12924 可以作为 child 的历史简称，但新权威材料不可继续把它标为 parent。此问题不改变源或 bundle digest，也不改写原转录。

3. **pending 是旧准备时刻快照，不是当前资源状态。** 必须一并保留并在新权威材料明确接上后来终态的位置包括：prepared-v8 的 `files.json` scope、`verification-status.json`（pending、outer null）、`README.zh.md:3`、`MATHEMATICS.zh.md:43`、`evidence-references.json`（terminal null）；以及 preparation 的 `files.json` scope、`execution-observation.json`、`root-resource-start-report.json` 和 `README.zh.md:5`。这些在 14:04 左右准备时的 pending/null 不应原地修改，也不能作为当前仍在运行或有 PASS 的证据。

   新的当前事实必须另引 `v8-resource-failure-v1/root-outer-observation.json` 与原 v1 terminal：session72573 实际 outer1，约 663.234 秒，runner 自己的 commit 阈值主动中止，资源 gate 未通过。这不是 OS OOM、数学拒绝或官网 verdict。root 在本任务发起时报告 resource v2 尚未开始；本审未查询当前过程，既不推断 v2 已启动，也不产生 v2 PASS。

prepared 的所有验证/提交/接受 flags 仍为 false 或 unknown，历史 v6/v7 成功、超时或中断没有被移作 v8 证明。没有发现另一个“已验证”“已接受”或“可上传”的新增假声明；上列三个类别已覆盖本次逐文件读取发现的 provenance/status 问题。数学说明保留为历史描述，未在本任务中重验。

## 结论的使用范围

可以依此确认这份 DRAFT 的 exact source、表单字段、清单字节及预计 bundle digest，并据问题列表准备未来新的权威材料；不能据此提交或称 resource PASS。旧 DRAFT 永远保留其 pending 快照及原哈希。本独审只产生新审计包，未产生新的 submission package，也没有执行或授权任何下门。
