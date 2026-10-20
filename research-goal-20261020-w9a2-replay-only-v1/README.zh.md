这是macro008授权准备的独立数学重放包；runner没有执行，gate-proposal.json为禁用状态，没有写enabled gate。保留原fullchain-v2会话68962/PID49320的TimeoutExpired、真实outer exit1、cold3200失败及全部原文件。

只复用原a517/1830052源码与两个实际exit0的精确exports（challenge a292e2…/349332110字节，solution 1cc0f9…/677296932字节）。新任务不编译Candidate、不调用exporter，也不导入Candidate或Mathlib/Zeta的olean。原15打印根、四模块实际普通编译及export完成收据连同完整失败archive ae3eb7…在新任务内绑定。

runner从原92cc8d…的准确Python源码建立非main模块，不读取或写入pyc，仅复用Attempt的run/cleanup/IO/environment/deadline方法；不调用原execute、ordinary、proof_replays、finish或fullPASS逻辑。新收据是mathematical-replay-only。可信CoreAudit仍以原7e88…源码的Lean --run执行，实际调用单列为trusted_CoreAudit_lean_run_calls，不能把它说成没有Lean进程。

新任务的3200秒从main开头，覆盖门控、来源和当前字节pin、完整CoreAudit三条消息及真实exit0、随后serial Nano、后验hash和三份fsync收据；root必须再观察新原父句柄实际exit0并核最终terminal SHA，且failure.json不存在。CoreAudit失败即停止，Nano不启动。Nano配置逐项固定为原配置，num_threads=0，允许propext/Quot.sound/Classical.choice，hard error，setsid --wait，须完整Checked N声明无错、N>0和真实exit0。禁止自动修补/重试。

运行时复用已完成source-bound旧closure 4d295c…与setup实际PASS的来源链。只读取旧closure一次，选择其14,194条可信运行时记录：保守完整13,951个官方SDK文件，加直接controller/DLL/PE/ELF及五tool olean/源码和Nano来源。当前字节在前后均散列；SDK根alias只resolve一次，没有逐文件Path.resolve，更不遍历/散列17万Mathlib/Zeta/pkg overlay。SDK、五tool（含Export/Parse）与直接执行文件的成员资格在本准备的静态metadata检查中已核；本准备未对当前SDK或export数据重新散列。LEAN_PATH只有旧tool-overlay，SDK来自固定LEAN_SYSROOT。

冻结后由root另外新建gate文件，只将gate-proposal.json的allow_replay_execution改为true、proposal_only改为false，其他字段逐字数据保持。启用门不能覆盖本包。CLI（当前不运行）：

```
C:\Python312\python.exe -B research-goal-20261020-w9a2-replay-only-v1/run_replay.py --gate <root新启用门路径> --gate-sha256 <该文件SHA256> --preparation-manifest-sha256 <本包files.json的SHA256>
```

唯一新工作目录tmp/w9a2-20261020/replay-only-v1必须不存在。生成mathematical-replay.json、deadline-receipt.json、terminal.json及两个stage的实际日志/PID/收据；原输入与失败job只读。完成后也始终cold_full_3200s_passed=false、official_website_acceptance=false、submitted=false。旧collector-v2不能用于本重放；后续单独写数学重放addendum。官网对同一a517源的官方固定3200秒实际接受仍是最终目标门，本包不声称Goal完成。
