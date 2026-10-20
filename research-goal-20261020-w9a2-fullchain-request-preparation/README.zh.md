此包只准备最终多stage request字段，不运行assembler，不授权gate，不调用compiler/export/kernel/下载，不复制或生成source body。

request-proposal.json已绑定最终draft-v5完整源（1,830,001B / SHA650ad176… / manifest497f905f…），以及六次实际普通批次的原授权gate、封存receipt/log/command/child/started/terminal与root退出attestation。预期选中Prefix(v0)、Core(v1)、Graph(v3)、Loc/Count(v4)、Final(v5)。v0–v4整体仍真实exit1，v5真正exit0；选中六模块必须由assembler再次核对各自PASS、最终source SHA、每个开发olean前序来源及十二个标准公理根。旧失败Final含sorryAx占位会被新v1明确作为rejected诊断保存，不参与证明或选择。

真实closure/runtime-only setup session44009尚未由本包观察完成。request因此故意保留closure hash、setup_outer_observation、freshRecord receipt/body的ROOT_MUST占位，不能通过assembler。已填的setup_runner指实际封存runtime-closure-v2/assemble.py（SHA276107a5…）；root仍需核对应唯一actualsetup0，而不能复用旧失败v1。schema角色仍用trusted-runtime-closure-v1，目录版本为v2。

root观察runtime setup原父handle真实exit0后，保存原始外层工具返回对象，按root-terminal-observation-template schema新写setup observation：实际session、setup receipt内assembler_pid、实际runner SHA、completion_receipt指同次read-only-setup-receipt、raw_tool_terminal指原始外层返回对象（真实exit_code0/output），再计算SHA。之后执行一次新HTTP freshRecord读取。将本request复制为NEW actual request，仅填上述真实pins及必要的新output/work目录，计算NEW request SHA；旧proposal保持冻结。

正确入口是新修复版v1，**不要执行原目录的assembler**：

```powershell
C:\Python312\python.exe -B -X utf8 research-goal-20261020-w9a2-fullchain-gate-preparation-v1/assemble_gate.py --request ROOT_NEW_ACTUAL_REQUEST.json --request-sha256 ROOT_EXACT_NEW_REQUEST_SHA --preparation-manifest-sha256 e16ef51b40b0ed7618857095330724061801ae4cc364ce3a0622c7c0bec90da3
```

assembler v1本身SHA588c1812…，其完整source SHA见evidence-scope.json。它最多输出disabled gate proposal，root复核后须另写NEW authorized gate并启动未改完整runner，原源码生成/4普通编译/2native exporter/完整锁定CoreAudit/defaultLean/serialNano/三fsync收据/真实外exit0均在同一3200秒合同内，不复用任何candidate olean。所有开发证据与实际setup/record pins进入bound manifest并由原runner immutable()复核。

当前request输出不代表production、双内核、3200秒或官网已通过。作者按用户明确授权填写Li Xiang；全部完整验证通过后由root实际提交并核官网结果。主轮计数未改。
