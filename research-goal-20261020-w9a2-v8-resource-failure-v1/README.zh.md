本目录封存唯一v8 Windows编译资源运行的真实失败。原session72573实际outer退出1（root工具chunk912386）；实际parent PID为54132、compiler child PID为12924。root-outer-observation.json与record_failure.py为root原文件，保留原字节；封包者未执行record_failure.py，未修改其方向记录动作。job/下仅逐字复制本次started、child、terminal、memory、stdout、stderr六个小文件，不复制源码、库或编译输出。

terminal.json SHA256为b9e50233b9a50ecd9dd14945e2cce321d70d70ef05fec62fd6bcb4a1a001a162。实际elapsed663.234秒、child wait退出1，runner因预声明的7 GiB峰process-commit阈值停止其ownchild。PeakWorkingSetSize峰375066624B，PeakPagefileUsage峰7728263168B，共24条资源记录，stdout/stderr均0字节。当前三个预期Candidate.olean/.ilean/.c输出均未存在；本次没有完成编译/C生成。

这不是3200秒timeout、已确认OS OOM、Lean数学拒绝或官网判决。驻留RSS与峰process commit是不同计量；本档只保存数值和本次阈值停止事实，不推断具体线程栈/映射/声明原因。没有自动重试、提高阈值、提交v8或内核/export动作。不得将此失败称作资源门通过、独立双核或wholepipeline PASS。

direct-input-status.json仅对冻结v8 source、工作区fresh source copy、实际runner及gate作直接当前hash，并与初始pin比较，同时记录封包前后这些直接文件不变。失败runner没有执行成功路径末端的全直接pin复核；本次归档补记的是失败后的实际小范围现状，不是完整runtime/SDK/package fresh audit。

旧prepared-v8/expected-wire-v8中的false/pending保留为原时间点的DRAFT历史快照，不再代表任务仍active。该快照转录的原启动消息曾把12924标为parent；本档按真实started/terminal及root外层观察明确：54132是parent，12924是compiler child。旧v7官网失败与所有源码、收据、包均保全。新的资源诊断轮由root管理，封包者不动review10/counter1。

本次仅文件读取、六个小文件raw复制、直接hash及说明/manifest写入，没有新进程查询、runner/AST/证明/编译/版本探测/网络/UI/Git执行。
