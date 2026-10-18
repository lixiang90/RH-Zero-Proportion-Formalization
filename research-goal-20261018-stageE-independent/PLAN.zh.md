# Stage E 独立结果审查策略（仅准备，未执行）

本文件只规划独立审查。尚无 root 的 E 书面执行 gate，也无生产 E 冻结
结果；本包没有执行 pair、固定点诊断、核、优化、solver 或 Lean。
旧 D/C/B 封包及治理计数不改。后续须同时取得 root E 书面决策和生产
manifest pin，才能按对应结果分支开展一次结果审查。

## 1. 为什么 E 是不同的数学机会关

保留每个 B 例外原叶的完整 source main margin M_i，而不把它们全部
压成 c9。由 source main/flow 的 signed 抽取，原 cell 上已有强下界

    E_i >= c9 + M_i/(kappa*SA),
    kappa = 32768*10^10*1024, SA=10^20.

因此两原 cell 的 margin 之和若满足

    M_i+M_j >= T = kappa*(tauN-c9N),

即已支付目标 E_L+E_R>=2c，其中 2cN=c9N+tauN。这里 equality 归 paid，
只有严格不足者需 DBM 矛盾。D 的首相容 pair 各自旧 scalar floor 已够
支付 c，说明不应再对它求 LP；这不代表其他 pair 也能支付。

此策略仍为原固定 B1187、tau、c、sep=17/20、四个独立 orientation 和
153 条原 source-indexed edges，既不改 FS 也不改阈值。它不重复 C 的
geometry-only 规则：C 要排除全部盒，而 E 只需排除尚未付款的盒。

全域逻辑仍须保留：若任一实际窗口>=tau，另一窗口的全域 c9 使平均
>=c；若两者均<tau，Stage B 的任意 separated sublevel cover 将它们
送入原例外或反射，此时 paid 对给目标和，unpaid 对须严格几何排除。
不能只覆盖 minimizers，不能丢原 root 外分支、595 ordered 反射处理或
两窗口各自的朝向。强 floor 解析抽取是待正式 Lean 连接的依赖，不会
因为 Python 余量比较正确就自动成为已完成新 theorem。

## 2. 生产流与独立重建合同

生产准备方案为 `research-goal-20261018-stageE-floor-dbm`：magic
`RZE1\n`，按 orientation-major id/id、id/rev、rev/id、rev/rev，再按
prefix ID、suffix ID 升序。总数 4*1187^2=5,635,876，保留有序对和自身对。

每 fixed ordinal 对应恰一个 record：

* `0x40`：paid，独审须重新取原 B M_i/M_j 并核 sum>=程序由 source
  scales 和 tauN-c9N 算出的 T，不能信任生产 paid boolean。
* 原 C `method*16+cycle_length` 加 edge IDs：必须先核 sum<T，再独立
  重建该 chart 的原 edges，检查 cycle 连续闭合且 signed 权和严格负。
* `0xf0`：首个 underpaid feasible；必须是最后 record，与单独保存的
  fixed ordinal、IDs、orientation、point 完全一致。

tag/cycle length/edge ID 不在合同内即失败；零 cycle 不关闭，接触端点
不排除。所有 margin 读取十进制整数字符串，不经 float、不舍入。
原 Mi 是 source original main 的量值，不能用 tau margin 或 point
affine 值替换；两个 source cell 的 reference state 和 FS 不互换。

独审不 import 任何生产 Python。几何直接从已冻结并已独审的 B 完整
36 正跨度生成，rev 使用窗口 `(8-j,8-i)`、suffix 加 1。边为
`Xj-Xi<=20u`、`Xi-Xj<=-20l` 和九条 `Xr-X(r+1)<=-17*32768`，
X=20*32768*p 是实数变量，不把 sep 或 gap 整数化。
生产若复用 C 纯函数，仍需绑定原 C SHA；不因此将其实现当独立审查。

## 3. 若首个 underpaid DBM 可行

只在 root E gate 与生产冻结后审查保存的固定 witness，不另跑 pair
scan、不调用 BF/Floyd/LP、不给另一个 potential。完整核：

1. 原 B 行、source hash、原 margin/FS semantic 身份、四 chart 与固定
   ordinal 相符；从原 Mi/Mj 独立计算 T 和 underpayment，严格 sum<T。
2. 十个 exact potentials 用原两个 states 重建全部153边，逐条检查，
   比较原 source edge IDs/差/slack，不能只检查 shortest-path 选边。
3. 两侧 actual ordered 四点式单列精确判断；任一违反也停止当前松盒
   gate，标明该 point 的 ordered 违反，不自动舍弃并继续。
4. 若提供此前 prefix records，在结果审查批准的预算内逐 record 核
   paid/cycle 证书，证明“首个”而非抽样；预算不够就明确仅核 witness，
   不冒充完整 prefix。不得改变 source、点或阈值求更理想结果。

underpaid feasible 只表明“固定 scalar-floor + 这些闭几何”的当前证书
规则无法关闭该 pair。即使两 ordered 也真，仍不说明真实 F9 低于 tau
或真实能量和低于 2c，不能写成 actual floor/比例反例。

## 4. 若生产报告 all closed

不能用一个 cycle、若干 paid 对、source hash 或数量摘要代替完整独审。
先向 root 提交一次全量独立 certificate replay 的经济方案与预算，取得
相应授权后执行；当前不自动启动。建议方案不调用搜索算法：

* 逐 record 流式解压，严格连续 ordinal 直到且仅直到 5,635,876。
* 对 paid 只重算 exact Mi+Mj>=T；scalar 条件与 orientation 无关，可
  使用按原 i/j 的只读缓存，但每 chart record 仍计入覆盖。
* 对 unpaid 只重放给定的负 cycle：lazy source-edge decoder 读取各
  edge 的原跨度及朝向，只构造 cycle 的至多10条边并核闭合/strict sum。
  不为每 case 建整153边表，不重新找 cycle，故无须再做 full BF scan。
* 独立按 record 分类汇总 paid/strict-cycle/orientation/root-pair 数，核
  它们之和及 stream SHA/EOF 与生产一致。全 closed 时不得出现 feasible
  tag 或未处理后缀；资源停止只能 inconclusive，禁止重试换参数。

这样可能节省 CPU/内存，但未运行 benchmark，不能预称在预算内完成。
若全 replay 未完成，则 independent-allclosed 仍为 pending，不能称新
floor 已证，也不能以局部可行点审查代替该完成条件。

## 5. 完成边界

解析强 floor lemma、whole-domain product/coverage、actual ten-point
WCert、counting/matching、网站 wrapper、完整 source<2MB 和 ordinary /
export / Nano 总时间都仍是独立完成条件。原 579013B 几何复制超过
181589B 余量；E 若采用原 stream 导航，也须真实证明/计量消费者而非
由小 JSON 或 cycle stream 的尺寸推断网站可交付。

本准备包未评价任何 E case，未进行新的数学算术、pair、核、优化或
Lean；只记录 E 结果分支与全量独审要求，等待 root 决策和生产冻结。
