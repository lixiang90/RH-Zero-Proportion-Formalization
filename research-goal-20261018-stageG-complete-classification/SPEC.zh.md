# G：固定全范围机会分类，准备版

本目录只准备一次有界分类，不启动新求解器、核值、FS、点拟合、阈值
或 Lean 批次。执行须由 root 另行给出不可变书面 gate；当前未执行。
输入是已冻结 B 的 1187 个原完整例外 state、各自 exact 原余量 Mi、
原 PR 顺序与四个独立反射朝向。原 state 不作 joint 收紧或重新选 FS。

## 固定数学合同

全局序号 `q=((i*1187+j)*4+chart)`，循环次序严格为 i、j、chart。
chart 0..3 为 id/id、id/rev、rev/id、rev/rev；与旧 E 的朝向优先序号
不同。总数 5,635,876，已知 F 个例只在新序号 4768 作注记，不额外闭合。

`Q=32768`，`SA=10^20`，`kappa=Q*10^10*1024`。
`c9N=893616123055294719`，`tauN=893916123055294719`，
`cN=893766123055294719`。付款阈值只由
`kappa*(tauN-c9N)=2*kappa*(cN-c9N)` 构造，不手抄长整数。
所有坐标是实数 `X=20*Q*p`；相邻间隔要求 17/20，不能 ceil 成整数 gap。

依次采用下列互斥类别：

0. paid：`Mi+Mj >= kappa*(tauN-c9N)`，等号支付。
1. strict_projection：付款不足，按全局共享顶点 1..8 的 28 个正跨度
   字典序，某一 lower 严格大于另一 upper。接触不排除。
2. other_strict_cycle：付款不足且无上述冲突；原 153 边存在给定的严格
   负环。可先用原单 state 加 sep 的负环，仍映射回同一原边编号。
3. unresolved：未提供排除证书。它不声称几何非空，不声称实际低能，
   不要求保存每例可行 potential。搜索算法未能给出合格环也只能记此类。

153 边编号固定：每窗按原 36 span 顺序先 upper 后 lower，左窗 0..71，
右窗 72..143；sep 边 144+r 为 `(r+1,r,-17*Q)`。右窗顶点平移 1，
反射的物理跨度为 `(8-j,8-i)`；没有 Ordered cut。两 Ordered 条件仅在
首个可验证 BF potential 的诊断样本中另列，不改变 G 分类。

producer 只导入冻结 C 的纯 geometry/BF 函数，不调用其旧 inputs/scan。
每个声称排除的环都重新检查连续首尾、原边编号、长度 1..10 与总权严格
小于零。独立 replay 不导入 producer 或 BF，不求解任何模型。

## 二进制证据和完整性

四条流按 8192 cases 为 frame，非每 record 建 gzip member：

* `classification.2bit.bin`：每 q 两位，低位先；每四个 chart 一字节。
* `unresolved.bitmap.bin`：每 q 一位，低位先，且恰当且仅当 status=3。
* `projection.frames.gz`：每 frame 一个 gzip member；按 status=1 顺序每例
  一字节 `2*sharedSpanID+direction`。direction=0 表示左 lower>右 upper；
  direction=1 表示右 lower>左 upper。spanID 是上述 28 跨度的字典序。
* `cycles.frames.gz`：每 frame 一个 gzip member；按 status=2 顺序每例
  一长度字节，再给定长度的原 153 edge IDs（uint8）。

每条流先 flush/fsync，再 append/fsync `commits.jsonl` 的 hash 链，最后
atomic replace `prefix.json` 发布耐久前缀。每 frame 固钉起止序号、四类
计数、各段 byte offset、raw SHA、已压缩流前缀 SHA 和上一 commit SHA。
log 的 canonical JSON 是 ASCII、排序 keys、紧凑 separators，加一个换行。
首个 unresolved 可选诊断样本不代表其他 unresolved。

完整范围是 687 个满 frame 加 7972-case 尾 frame。完整 status 为
1,408,969 bytes，bitmap 为 704,485 bytes；尾段分别 1993/997 bytes，
bitmap 末字节高四位必须零。完整 replay 同时检查全部流和 log 的 EOF。
异常/资源停止时只承认已发布前缀；不能把未访问 suffix 填 unresolved
再称完成。未提交的缓冲和尾部 bytes 不算证据，不能自动恢复或重跑。

独立 replay 从新源 PR 和 B 原 state 重建每个使用的边，逐全部
paid/projection/cycle 检查。它重算计数和 bitmap，而不相信 log 计数；
核 summary 与 published-prefix SHA/count/outcome 一致。完整分类通过
仍可能有 unresolved，绝不等价于全域 floor 通过。

## 资源、执行和停止

root gate 字段规格见 `required-gate-fields.json`。准备阶段只作 Python
`ast.parse`；不能调用三个脚本的数学入口或 inputs。唯一授权后 CLI：

```text
C:/Python314/python.exe research-goal-20261018-stageG-complete-classification/run_once.py --launch-authorized-complete-G --gate <root不可变gate相对路径> --gate-sha256 <完整SHA256>
```

wrapper 只 launch 一个 child：硬 300 秒/20,000,000 bytes，child 工作软
270 秒/19,000,000 bytes，留出关闭证据、SHA、terminal 的时间。软停止
关闭缓冲但不接纳它；硬停止只能报告 inconclusive/prefix，不能重试。
所有启动/命令/PID/失败/terminal 持久化，输出不能静默覆盖已有尝试。

独立审查 CLI（只有执行结束后才用）：

```text
C:/Python314/python.exe research-goal-20261018-stageG-complete-classification/replay_complete.py --write-receipt
```

不足完整范围时还必须显式 `--prefix-only`。暂无任何运行结果。

仅 status+bitmap 已约 2.11 MB，不能视为网站 Lean 源码。负环证据最坏
未压缩 `11*3527184=38,799,024` bytes，gzip 和 20 MB 闭合均未保证；
资源 guard 到限即停止。没有新消费者、完整 Lean、导出、Nano、3200 秒
网站运行或 2 MB 源码验收结论。此包仅判断固定数学机会，非提交材料。
