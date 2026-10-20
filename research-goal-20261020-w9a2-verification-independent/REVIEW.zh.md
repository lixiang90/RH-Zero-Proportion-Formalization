# W9A2 完整验收入口 v1 独立只读审查

本次审查针对 delivery 冻结的 v0 与 v1 完整验证入口。没有 import 或执行验证
runner，没有运行 compiler、exporter、Comparator、默认 Lean replay 或 nanoda；
没有修改候选源码、完整 Core、已有证明收据或主轮计数。主代理随后启动的独立
ordinary 批次不在本审查执行范围内，本报告不观察或宣称该批次通过。

静态结论是 v1 在本次审查范围内通过；不是普通 Lean、全链3200秒、生产双核、
网站、GitHub同步或提交材料验收通过。完整runtime DLL/ELF/可信缓存实际闭包
仍需主代理取得真实证据后另行审核并建立执行gate。

## 唯一发现与版本化修复

v0 Windows nanoda argv 使用 setsid 而没有 --wait。util-linux 的实现会在调用者
已是进程组leader时fork；不带 --wait 时父进程可立即返回成功，不能据此确认
真正nanoda的退出码。此问题违反真实子进程exit码的验证合同。

依据为 [util-linux setsid 原始实现](https://raw.githubusercontent.com/util-linux/util-linux/master/sys-utils/setsid.c)
第92–107行。本依据说明工具语义，不构成对当前WSL实际安装版本的身份审核。

delivery 保留 v0 全部文件，并在新独占 v1 目录中只给该 argv 加上 --wait。
独立检查证明：对 v0 runner 仅执行这一处精确字节替换，结果恰好等于完整 v1
runner。独立重建的 unified diff 也逐字等于 delivery 的原差分文件。

v0 runner SHA256：`42932741b4759dff17df3df3ddf2d4e6a5a1d32461dc5859aaf558c1f5b22022`。
v1 runner SHA256：`92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8`。
差分 SHA256：`157affbf34b59b42119766b12d5e08c2a867fd6d54876c4f2fcbce8c43882cef`。
v0 prepared manifest 的5个文件和 v1 manifest 的7个文件均重新逐 bytes/SHA核对，
所有输入前后身份与准确清单见 `review.json`。

## 验证链的静态范围

统一 monotonic t0 在 gate/pins 核对之前建立，deadline=t0+3200。所有阶段共用
remaining；hash分块、源生成、子进程等待、日志fsync、最终三收据fsync与其SHA
均在该deadline内检查。清理仅在失败后发生，不授予PASS；最终检查若超时也会
留下 failure.json 并以真实非零退出结束。Python控制器自身未来退出仍必须由
外部执行handle观察，程序没有用自己写的 completion_return_code 替代真实exit。

入口从冻结五模块与wrapper在预算内重建完整单文件，保留全部非import字节，
核对完整SHA、bytes与2000000字节上限。可信 CandidateSpec 从绑定模板、已核
整数比例和新鲜HTTP receipt生成，不执行leaderboard中的任意表达式。新鲜检查
明确是运行开始时的0–900秒receipt；最终提交前若纪录变化，主代理仍须再核。

四个ordinary模块 ChallengeDeps、CandidateSpec、Challenge.Candidate 与
Solution.Candidate 都从新空lib编译。没有复用开发用Prefix/Core或用户候选olean。
native exporter随后分别导出同一组public roots、允许公理与完整原primitive。

CoreAudit 原源 SHA256
`7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2`
被硬锁。其 compareAt/依赖与primitive核对、transitive axiom检查及默认Lean
空环境完整replay与原固定Comparator合同相符；replay仅按原合同移除Quot的
三个特殊声明。全部三个明确成功消息与真实exit0都是必需条件。8个固定
Comparator/Export源文件的canonical LF hash也独立重新核对。

nanoda消费相同solution.ndjson的二进制stdin，固定 num_threads=0，三项允许
公理、hard error与unsafe_permit_all_axioms=false。固定nanoda源码中0确实选
serial全声明检查；Checked N declarations with no errors消息在全检查之后输出。
入口还要求N>0、打印公理属于允许集合以及真实退出0。v1的 --wait 修复保证
WSL setsid发生fork时也等待并传播真正子进程的退出状态。

三份成功收据采用排他创建、flush、fsync；deadline收据引用verification的SHA，
terminal引用前两份SHA，最终控制台再给terminal SHA。主代理必须同时核外部
handle真实exit0、磁盘terminal SHA和failure.json不存在。成功收据明确保留
official_website_acceptance=false，不冒充官方attestation。

## runtime授权边界

两个模板继续保持 execution=false 与 complete closure=false。runner要求主代理
确认可信setup真实exit0及完整source-bound runtime闭包，随后逐项绑定文件、
链接解析、工具源pin、实际Python/Lean身份、DLL/ELF与可信package/tool cache。
候选编译路径不加入旧项目lib；解释执行工具overlay只在CoreAudit阶段加入。
这些是执行前必须以当前实际证据填充的授权关，不是本静态报告替其填true。

本次未发现第二处确定的实现缺口；这不证明尚未提供的runtime闭包完整，也不
证明任一实际编译或kernel成功。未来若改源或运行环境，应另建冻结版本与gate，
不得覆盖当前v0/v1、原完整源码和本审查证据。
