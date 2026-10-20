这是future collector准备包；collector没有执行，数学重放是否成功尚未预认。唯一适用的实际运行身份为replay-only-v1原session83153/PID15012/t0=15521.156，gate587b70…、runnerf9048b…、准备清单d5552f…。必须等root通过原工具句柄观察真实exit0，提供protocol w9a2-root-terminal-observation-v1（role=replay-only-v1），runner指f904、completion_receipt指实际terminal.json，raw_tool_terminal包含原工具exit0及最终打印的terminal SHA和完整耗时。

未来由root执行，当前不执行：

```
C:\Python312\python.exe research-goal-20261020-w9a2-math-verified-v1-preparation/collect_math_verified.py --outer-observation <root实际新记录路径> --outer-observation-sha256 <该记录SHA256> --preparation-manifest-sha256 <本目录files.json的SHA256>
```

collector拒绝未完成/失败状态、wrong PID/session/gate/source、缺少三收据hash链或最终打印terminal SHA、不同clock或全部fsync后达到3200秒、CoreAudit/Nano不完整、额外阶段、非严格串行Nano配置/允许公理、原cold失败被升级。它核对两阶段真实子进程exit0/日志/元数据和对应bound SHA，CoreAudit完整三消息、Nano exactargv/setsid --wait/完整Checked N、0候选compile/0export/1可信Lean --run/1Nano。只重hash新收据/日志/控制文件、同一a517源和原a292/1cc0导出对象；不重hash14k SDK/runtime文件。

原cold-v2会话68962/PID49320的actual outer1/TimeoutExpired、源普通Lean PASS和两个export PASS由原ae3eb7…归档绑定，完整原目录不动；新包仅复制少量原失败引用证据。prepared-v6原13文件逐字复制，source a517/1830052及许可证、署名Li Xiang、605字符summary和UI模型空保持不变；expected-wire-v6原包复制，server model=null、预测组合digest e76462…仍非官网观察。

唯一新输出目录为submission/w9a2-weighted-potential-20261020-math-verified-v1，必须不存在。新数学addendum是之后的本地数学状态；原prepared的verification-status仍为原历史快照。cold_full_3200s_passed永远false，submitted/official_website_acceptance/official_fixed_complete_3200s_accepted全部false；官网固定完整限时接受和最新精确R复核仍待root完成。

此collector只有文件读取、SHA、JSON验证与独占/fsync复制，没有subprocess、网络、proof、compiler、exporter或kernel调用。不运行旧cold collector，不改源码、旧失败包、runtime或任何已绑定冻结文件。
