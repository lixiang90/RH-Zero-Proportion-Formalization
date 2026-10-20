# authoritative-v8 生成器纯静态独审

`PASS_STATIC`，范围为固定 runner 的正常原始工具结果协议，并保留下面明确的 root 外层唯一终态记录检查要求。没有发现会阻断该正常协议成功收据、或把 compiler-only 成功偷换为独立双核/官网成功的确定代码矛盾。本结论不是运行结果，也不是当前资源 PASS 或生成/提交授权。

审查对象是 `research-goal-20261020-w9a2-submission-authoritative-v8` 冻结包：manifest SHA `afa2c6fa4a4834d6bd05fd58de13a6403ff49c91a4d727bc773ea991363ab9b2`，生成器 SHA `b22bf7b388f777693743094188734c4b98c60293036035affa1384a3da420038`。四个成员实际大小和 SHA 均匹配。逐行静读完整 345 行代码、两份新模板、README；只读对照冻结 v3 runner 的 terminal 字段和既有 root-outer 模板。没有执行 Python、AST、生成器或 runner，没有读取 `tmp/w9a2-20261020/v8-resource-v2` 的任何活 work、terminal 或输出，没有查询进程、API、网络或 UI。

## 门控与状态链

- 模板 `allow_material_generation=false`、`proposal_only=true`，generator 及未来成功归档/outer/terminal 的 pin 留空。代码 116–124 先拒绝禁用提案和缺失 generator pin，并固定 root owner 与独占新 ready 目录。空模板不能产生 ready 输出。
- 125–135 固定旧 DRAFT、wire、draft-v8、独立材料审查和原 start 归档；未来 outer 与 terminal 必须同属 gate 所 pin 的成功归档。137–158 固定原 session93095、parent35104、runner/gate，要求 root 的实际原工具 raw exit0 和 actual parent exit0，并绑定打印 SHA 与原/归档 terminal 的同一字节。controller 的 return-intent 没有代替这些外层证据。
- 173–210 要求 root 的同 clock 实际完成时间与 terminal elapsed 均在 3200 秒内，固定 t0=29449.203、child5564、RSS-only schema v2、低于 7 GiB 的 peak working set、`-M6500`、commit 仅诊断、final memory query 成功、没有 failure/预算或资源中止、没有 retry/repair 或 cached user Candidate。原 source 与 fresh source copy 都绑定 5424…/1,829,382 B。
- 211–229 将实际 argv 与冻结 start/child 逐字比较；三个唯一、非空的 `.olean`、`.ilean`、`.c` 必须有实际完整大小/SHA、固定 fresh path，并与唯一 `-o/-i/-c` 参数吻合。代码没有执行 Lean 或重建产物。
- 230–251 保留 v1 session72573 的真实 outer1、parent54132/child12924，并固定 proof raw bytes、server d88b… 与 bundle fb457…；生成前复核直接输入。旧 pending DRAFT 没有原地改写或被升为 PASS。
- 生成分支只在上述验证之后创建独占目录；新 ATTRIBUTION 首句明确 draft-v8 及 v5→v6→v7→v8 继承关系，保持剩余归属/许可与原始 proof/server 字节；新 current parent/child 角色与 v1 分开。封包前再次复核直接输入，并检查输出 proof/server 与已验字节相等。
- 状态的正面结论只限 single-file ordinary Lean compiler、C generation 与本地 RSS 门。独立 Comparator/公理检查/default-kernel/Nano、数学双核、完整 production3200、官网 verdict/接受全部仍 false/unknown；`upload_ready=false`、`submitted=false`。README 同样明确 Windows 资源门不等价官网 Linux8GB cgroup，且没有官方 `--setup`。

## 唯一记录检查的准确限制

代码 159–167 的计数只收集 `terminal_sha256` 等于指定 terminal pin 的 JSON 记录，实际强制的是“恰一个匹配记录”。它不会自动拒绝原 output 中另一个不同 SHA 的终态记录。固定 d47d… runner 的正常 finish 只打印一个 final 记录；在 root 提供未经改写的真实原工具 raw 这个可信边界内，没有已知正常路径矛盾。

root 已明确决定不新增生成器版本，而在未来实际归档时另作严格检查：**原93095 raw 中所有含 `terminal_sha256` 的 JSON 记录合计必须恰为一个，而非仅匹配目标 SHA 的记录恰一个**。此检查必须针对真实完整原始工具 output，并与 raw exit0、选定 terminal SHA/path、child0/resourcePASS 一起保存。若缺失、重复、混入其他 SHA 或原始工具终态未知，不能依据本静审生成可接受的权威材料。本审没有读取未来原 output，也没有提前宣称此项已经完成。

## 审查结果的使用边界

本次只生成独立静审报告；没有运行材料生成器，没有创建 ready/submission 包，没有修改任何冻结源、模板、metadata 或 counter。未来仍须 root 先取得并归档真实成功终态、完成上述全记录唯一检查，再另立 enabled gate；生成后也必须保留实际 metadata 进程终态及完整 package manifest。若生成失败或留下未封存的部分目录，目录名本身不能成为成功或提交依据。官网与两个独立内核的接受仍属于后续独立证据。
