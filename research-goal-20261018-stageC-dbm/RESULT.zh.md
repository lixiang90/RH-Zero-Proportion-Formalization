# 固定 Stage C 已结束：第二个 case 松 DBM 可行，两 ordered 条件也成立

SPEC.zh.md 是运行前的准备规格，原文保留。实际执行由 root 的另一个
书面 gate 授权：research-goal-20261016/gates/stageC-dbm-20261018.json，
SHA 8020cdd1c37cf1d5b786f803be0f8a2105b99ab9dab31168eb17af8d856994e7。
B 生产 manifest 3f9408f2…89ad，B 独审 manifest e6458883…7288 均先逐项
核对文件与依赖。implementation.json 在执行前记录脚本/命令和零次 scan；
launch.json 在 Popen 前记录实际命令 SHA。没有参数恢复或重试。

唯一 child PID 58936、parent PID 36072，child 0.3646889 秒，launcher
0.8321118 秒，exit 0。没有触发 300 秒或闭输出 20MB 限额。先核查四
朝向的首组 id/id，按 prefix id、suffix id 升序，结果：

* ordinal 0，prefix exception 0、suffix exception 0：共享跨度的两条
  原 edge 98、41 构成严格负 cycle。这一项被排除。
* ordinal 1，prefix exception 0、suffix exception 1：完整 153 条
  DBM edge 允许精确可行 potential。按约定立即停止，没有计算后续 case。

因此实际只检查 2/5,635,876 个 case。不能写成“全部四朝向已排除”或
“例外对已完整不相容”。这里停止的理由不是资源或浮点求解状态，而是
一份可逐项重放的整数 feasible potential。

X=20*32768*p，下列 10 个 X 整数是一个实数域可行见证：

    [0,557056,1355776,2131556,2724876,3392856,3986176,
     4635136,6374116,8254976]

first-feasible.json 保存原两份 B cell、来源、153 条 edge 的端点/上界、
实际差及非负 slack。prefix 原来源 root0/position1460，suffix 原来源
root0/position9146。全 72+72+9 条闭约束都通过；没有取整 sep、改 cell、
新加 cut 或取核值。整数 potential 只是整数 RHS 下方便验证的一点，不
把被覆盖的原实数数学域限制为整数位置。

两窗口各自的原 ordered 关系也单列精确核验：prefix 的 h0-h7 在 X
单位为 -1,181,924，suffix 为 -1,082,140，均 <=0。因此本例的结果标签
是 ordered_conditions_hold，而不是仅因丢弃 orientation 才可行。
即使 ordered 不成立也应立即停止；本实现没有丢弃任何首个可行点后继续。

这仍然**不是实际低能点**：只说明这些原见证失败 cell 的闭几何外包
能够相邻。没有计算 F9、没有证明任一窗口低于 tau，也不反驳候选全局
下界。它只否定“用当前不变外包的相邻不可兼容直接结束”的机会关。
不自动授权更强 ordered 处理、细分、改见证或其他新试验。

cycle-prefix.bin.gz 的解压字节为 `RZDBM1\n`、tag2、edge98、edge41、
tag0xf0，共 11 字节。它包含一个严格 cycle 和一个结束可行标记，不是
全量数百万负 cycle 的证书。scan.json 绑定全部输入前后 SHA 和结果，
first-feasible.json 是完整可行见证；terminal.json 记录唯一进程正常退出。

replay_cycles.py 是独立 stdlib 检查算法：不 import scan_once，不调用
BF/solver；从原 source PR 与 B cell 重新生成原 edge，逐条核上述
cycle/potential、两 ordered、全部输入/输出 hash。唯一运行 0.235458秒
exit0，通过 1 个负 cycle 与 153 个 potential 约束。它由本代理提供，
不代称另一代理的独立审查完成；后者由 root 另行组织并在新目录封存。

没有优化器、核查询、新 threshold、FS、cut 或 Lean；没有改旧 B 包。
完整消费者/编码/新 kernel/export/Nano 的源码及总运行预算仍未知。
本包不打开 proof batch 或网站上传 gate，无新 joint floor/无条件比例。

scan.json SHA：fa80495ddeb322984dad3f5a528b2813d05d459d6d0fdff68ae333842db2361b。
first-feasible.json SHA：bbb1c08a3d913a10b45cb40ec4b9ab3a0cfa5432419585d9922f0638ca222812。
