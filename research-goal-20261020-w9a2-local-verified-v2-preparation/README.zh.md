这是 v2 的未来收据 collector 准备包，collector 本身没有运行，不代表当前生产会通过。

从已封存且独审的 v1 collector（01b3aa…、原清单11d3d3…）仅做15条固定路径、源码、材料、wire、session/PID/t0/gate字面值替换，+12字节，正反投影精确。可读源码差分见exact-source-diff.patch。所有原检查逻辑保持原字节：三真收据hash链、原父句柄真实exit0及terminal SHA、同monotonic时钟全链<3200秒、九阶段子PID/日志/退出、四个普通模块、两native exports、原CoreAudit三消息、serial Nano的--wait/配置/实际日志和允许公理，无failure，exact新源码和13份prepared文件逐字复制。

固定新生产身份：原session68962、PID49320、t0=11264.218、work fullchain-v2、gate3ebcc3…、runner仍92cc8d…、source a517df…/1830052字节。新的protocol外层观察role必须fullchain-v2，completion_receipt必须实际terminal.json，raw_tool_terminal必须原工具实际exit0与final printed terminal SHA。原失败v1的68653/48644/650/e6ae身份不能通过本collector。

未来仅由root观察原68962真实退出0后执行：

```
C:\Python312\python.exe research-goal-20261020-w9a2-local-verified-v2-preparation/collect_local_verified.py --outer-observation <root新实际记录路径> --outer-observation-sha256 <该记录SHA256> --preparation-manifest-sha256 <本目录files.json的SHA256>
```

新prepared-v6（55c28b…）和expected-wire-v6（f81666…）分别绑定新源与预测组合摘要e76462…。原13文件会逐字保留历史状态，新的实际本地生产结果另写local-verification-addendum；UI模型仍空，预期server model=null。唯一未来输出为submission/w9a2-weighted-potential-20261020-local-verified-v2，必须不存在，当前未创建。

不执行proof、compiler、exporter、kernel、网络或runtime assembler。不重复制或全量hash SDK/cache；只核已完成原收据并重hash本次生产拥有的源、olean、export和日志。未来成功包仍submitted=false、official_website_acceptance=false，无官网job；官网结果须另加hash-linked addendum。所有旧包、已绑定的runtime/gate/runner/source保持不变。
