# 去重 Production v1：冷验证静态准备

本包尚未执行 generator、Lean、export、Comparator、nanoda 或网络。旧 production-v0 真实 exit1：ordinary、精确陈述/依赖/primitive、公理及默认kernel通过，nanoda在剩余352.089秒内未完成，统一3200秒超时。旧证据、源、草案和prepared不覆盖；旧collector不得执行。

新输入为四个等价 Production 模块。canonical strengthened Core 的 concrete/COV/137 payload/见证/实际计数段与旧 Dev 对应段经精确命名族替换相同；移除了重复旧PC9 checker和十个alias，旧尾两段版权block及完整license原字节保留。三桥只有import变化。新flatten-v4预测上传源1,856,430字节，约省122,850字节；generator零执行。这只承诺少输入冗余，不承诺kernel或nanoda必然提速。

独占目录为 `/var/tmp/rh-zero-20261015/tiny-production-v1` 与仓库 `tmp/current-s1r-tiny-20261018/production-v1`，任一存在则拒绝。generator输出只在新flatten-v4/draft/创建一次；Windows helper固定新PID文件路径。所有旧输入保持不变，新root gate必须绑定本prepared、Production源码prepared、flatten-v4和一次真实新鲜的精确记录receipt；R变化则停。新Spec只在新冷目录从可信模板/ledger/pq生成，不改旧installed Spec。

单个Linux主进程的 monotonic t0仍在pins/生成之前。唯一deadline=t0+3200秒，所有子进程只得剩余时间。源生成、四模块冷ordinary、九个可信tool冷编译、两个完整export、Comparator+defaultkernel、完整nanoda及前后哈希/fsync receipts全计入；0自动重试/修源、0用户olean复用。先前模块通过仅是数学链条依据，不代表这份新单源ordinary已通过。

完整根和primitive、公理白名单、默认kernel重放与nanoda完成条件均不变。RLIMIT_FSIZE=8GiB是文件限制，不是RAM限制；每阶段记录time-v RSS。Linux进程组及Windows精确PID清理与v0相同。必须exit0+三份最终receipt+无failure+总耗时≤3200，才有完整local PASS。中间成功不能替代末门。

**线程和官网边界：** 本v1暂保持此前local配置 num_threads=4，未凭硬件猜测上调。锁定官方 Comparator/Main.lean 的runNanoda未写num_threads，锁定nanoda的serde默认0会串行；因此local4线程不是相同官网配置，不能把local统一时间当官方时间验收。源码静态证明更多线程仍检查全部声明且join/panic失败，但吞吐、RSS及部署条件需实证，不能靠调线程假称官网通过。本包显式记录 official_runtime_equivalence_claimed=false；官网受限环境/最新协议/attestation仍待实际验收。

执行形状（本准备未运行，须root审查后单独gate）：

```
wsl --distribution Ubuntu --exec /usr/bin/python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261019-tiny-production-preparation-v1/run_production.py --gate /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261016/gates/ROOT_NEW_GATE.json --gate-sha256 ROOT_NEW_GATE_SHA
```

所有 submitted/official_website_acceptance 恒false。本包不改变目标、不缩减证明范围，也不授权重新运行旧失败attempt。
