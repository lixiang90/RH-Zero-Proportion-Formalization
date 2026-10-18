# N2：同一 pooled 模型的一次基础设施恢复准备

当前仅准备源码、AST 与字节/既存元数据身份；没有解压旧数学证据、恢复数学、提取 FS、组矩阵、点/核/LP/Lean 运行。另需 root 的不可变执行 gate。

## 不变数学与调用边界

完整导入冻结 N 的 `component_model.py`、`reconstruct_support.py`、`check_raw_certificate.py`，以及 N 原 source/parser/定位器工具。不复制或修改模型、same-S native dominance、固定 support、精度、参数、锚点、阈值或目标。仍为原 H 升序15378个 index、原四 chart，42组/51自由变量/完整52坐标。M2417、J5331088仍为明确既有 Lower deduction。

原失败包 `files.json` SHA181473343e98152ab01e622b6346cd37516bb9724477ac26ade56e15dc9b7377 已冻结。原唯一执行675次 LP，published675条（其中1 deduction，故674次调用对应发布前缀），第676条有 durable evidence 但 replace 失败。恢复不能只抄 failure 的内存计数。

未来执行先验证旧包/全部输入 hash，再精确解析旧 gzip member、canonical JSON、member offset/长度/压缩与解压 hash、完整 EOF，核 published byte boundary 恰落在其声称的 member 末尾。旧675个 call-intent 与675个 native 记录必须按 call number/index/row mapping 一一对应。旧 case676候选必须恰为原 H 前676个，任何缺项、重复或不一致直接停止。

每旧 case 都在不求 LP 的条件下，由冻结原 cell 组件重新确定同一 pooled 原模型，核 canonical model SHA，调用冻结 raw checker 重查原 Lower/primal；存在 primal 时另重核全部原行及每窗原 M0 floor。原676th只有全部通过才写新的 recovery commit。不是将旧 tmp 自动改名当已接受前缀。旧 FS 缓存保留全部字段并核冻结 J 的 Cstar/J/term hash/state/witness；不重复已提取 cell。未缓存 cell 才由同一冻结 point-free extractor 提取一次。

任何已经进入旧 call-intent 的 index 都在禁止再 LP 的集合中；新 case 求解前显式 assert 不在此集合。旧675次加新最多14701次，总上限15376。各新 case仍至多一次原 method/options，高度相同 rawnative 完整保存，再调用同一冻结 support 重建与 raw checker。无辅助、重试、修补、参数/precision/support 扫描或新 solver。

若旧 recovery 发现首个 exact Below，亦可如实停止；Below 仍只反驳 pooled 原组件模型，不是实际 F 反例。全range有 unresolved 仍不构成 floor，未访问 suffix 不填 closed/unresolved。

## 唯一设施修改：append-only fsync progress

新目录不写 mutable prefix，也没有 `os.replace`。`progress-commits.jsonl` 逐 complete case 写单行 canonical JSON：包含 body 与 SHA256(body)，body 含 ordinal/Gindex/previous_commit_sha256/累计类别、旧新调用数、witness member引用、所有新 stream 的 durable bytes/hash、H index前缀hash。写 witness/native gzip member并 fsync 后，才 append此行并 fsync。只有完整 LF、链hash/序号/index/stream边界全部正确的连续 commit 前缀是可接受进度；partial最后行不作证据。没有自动恢复/续跑入口。

恢复 case 的新 proof record 引用已冻结旧 member，保留其 bytes/hash，不复制/删除原包。新 case 的完整 native 结果单独 gzip 保存，先于 exact reconstruction durable；新 full original FS cell组件亦每 cell一份 durable cache。新的 call-intent 在 LP前 fsync。旧/新源文件与安装 runtime start/endhash均保存；异常、resource stop与原始尾部保留，不偷偷修复。

此处旧失败包只有约6.6MB，恢复解码只读这一个短前缀，不是加载旧全域历史checkpoint。未来独立数学审查仍必须自己核 source组件/全 raw rows/52平衡/原成本；本 producer恢复不是外部独审。

## 运行与停止

`run_once.py` 只启动一个新 child，hard/work 时间和closed-output由 root gate指定，线程环境同原 N。旧 N源与旧证据没有改写。监控只看 stdout/进程，不用持有 live mutableprefix文件；N2没有此类替换路径。

命令模板：`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageN2-pooled-component-resumption/run_once.py --launch-authorized-same-model-N2 --gate <ROOT_GATE_PATH> --gate-sha256 <ROOT_GATE_SHA256>`。

原 N 675项已发布数据约70秒只是该真实前缀，未进行新 benchmark，也不作为完整剩余runtime/payload可行性的证明。网站2MB/3200秒、完整Lean与无条件纪录均仍未闭合。这里只授权准备；本模板不授执行权。
