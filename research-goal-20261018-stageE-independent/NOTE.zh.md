# E 首个 underpaid 松盒见证与全部报告前缀：独立审查

独审通过。case ordinal1192（id/id，prefix exception1、suffix exception5）
原 Mi+Mj 确实不足目标付款，保存的十个 potential 确实满足全部153条
原闭 DBM 约束，但两侧 actual Ordered 都不成立。因此它只说明固定的
`exact scalar-floor + relaxed DBM` 规则未关闭；既不能断言 ordered
交集非空，也不能断言其为空，更不是实际能量下界或比例的反例。

之前 `PLAN.zh.md` / `plan-files.json` 保持原冻结内容。本次在另有 root
书面 gate 和生产结果冻结后，按该计划只核给定结果与全部报告 prefix，
没有另跑模型 scan。gate 为
`research-goal-20261016/gates/stageE-margin-dbm-20261018.json`，SHA
`4c83f5f157c9dba302c712951f681394df4d15e703770eda64b420a124e0c3bf`。
生产 E manifest SHA 为
`73b1cc1367b32cd769712370defef03288d625b4ab04c02df56ffe4b92b3b21a`。

## 独立性与唯一实际执行

`review_first_underpaid.py` 不 import 生产 Python，不运行 BF/Floyd、LP、
pair scan、核函数、优化或 Lean。全报告流仅重放给定 paid/cycle 证书；
没有寻找一个新 cycle 或 point。原两 FS/flow 仅用我方已冻结 A/C
实现，在各自原 state 中复核源余量和语义，不在新 potential 处评价 F。

执行前只有 source/schema/syntax 审阅。唯一独审 PID55568，主体
3.4637856秒，工具 chunk337035 返回真实 exit0；无失败/重试。
receipt `independent-review.json` SHA 为
`9663a9f7f126920fae995e0fafb4418f3a5fb653cef3b2f722459d7bdc9d4ee5`。
source/B/C/D、静态强 floor 及 E 全部闭包输入 bytes/SHA 前后相同。

准备期发现的 gate 字段差异仅在生产唯一运行前改为 `c9_numerator`；
原数学参数不变，无失败模型 run。本独审逐项绑定实际运行脚本的冻结 SHA，
不使用旧准备版本。原 plan 未被改写成执行授权。

## exact Mi 付款与全部报告前缀

从原 source scales 算 kappa=32768*10^10*1024，再用原 tauN-c9N 算

    T=kappa*(tauN-c9N)=100663296000000000000000000000000.

并独立核 `2cN=c9N+tauN`。所有 Mi 直接读取已完整独审 B 的原 main
margin，重新核其原/raised 关系，并对所选两叶从 source 原 FS 再算。
没有换成 floor(Mi/kappa)、tau margin、point affine 值或浮点数。
付款允许 Mi+Mj=T，只有严格不足者才允许 geometric cycle。

本包从 `RZE1\n` 解压完整2050B，一直到精确 EOF，逐 ordinal核完
生产全部1193个 records：

* 766 个 tag0x40：原 Mi+Mj>=T，全部 exact付款相等。
* 426 个 strict two-edge cycles：均先核 Mi+Mj<T，然后从原 B pair
  order/state/朝向 lazy 重建原 edge，核两边首尾闭合、来自两窗口共享
  顶点1..8的同一跨度，且整数权和严格负。没有借零 cycle 排除边界。
* 最后一个 tag0xf0：恰为 ordinal1192，之后没有字节或未标记录。

解压 stream SHA 为
`8b727133d933d14f0cd363ac849e7d047fc3534cd2653c6d1f03e238c8c75b47`。
这些 records 全位于第一 id/id chart；其余 chart 及未处理后缀不计作通过。
5,635,876个完整 cases 中仅1193个已处理，余5,634,683个没有独审结论。
这足以核“首个 underpaid relaxed feasible 即停止”的实际运行，不能
冒充 allclosed。若有 allclosed，本 reviewer 代码在入口拒绝，须另获
完整 lazyedge 流式审查授权；本次没有走该分支。

## 固定 feasible witness

原 source main 余量为

    Mi=56577247050221517825498512000000
    Mj=4621809023144565169846040000000
    Mi+Mj=61199056073366082995344552000000 < T
    T-Mi-Mj=39464239926633917004655448000000.

原 scalar floors 的和减2c为
`-4933029990829239625581931/4194304000000000000000000000000`。
这只是原固定下界模型的不足，不是实际能量和的负余量。

固定 potential 保留为

    X=[0,2663120,3234020,4032740,4830940,5493380,6086700,
       7127020,7697920,8254976], X=655360*p.

直接从全部36正跨度生成两侧72+72和九条 sep 原边，另与我方冻结 C
独立 edge 表示逐项相等。153条实际差<=原上界全部成立，min slack=0，
所以闭边接触不能删。原 edge 表 SHA 为
`5f324f3810bb7e49ff72f2aa29453469e982d8051ef622fd1a489e87b4f24cb1`。
X仍是实数域见证，整数坐标不把原问题改成整数域；sep=17/20未取整。

prefix actual Ordered 的第0/7 gap为2663120/570900，差+2092220；
suffix对应570900/557056，差+13844。两者均违反 h0<=h7。本包保留
这个结果并停止，没有丢弃该点后继续，也没有暗中求 stronger ordered
feasibility、另一个 point 或更强 dual。

所选原两叶 FS semantic SHA分别为
`a8ab41871aedca5b6c74bc11541340f6c62ef941a65635cd968cf29c90bf74c6` 和
`a90049b3ffed282e97a1bc968376893cb123f6d9ea81cf3882f2eb73e1282111`；
原 state、stream position/end、packed payload 和原/raised余量全同B。

## 结论范围

全域强 floor 的 source analytic 连接、原 streams 的 product consumer、
完整四 chart 覆盖、WCert/counting/matching、网站单源bytes与ordinary /
export/Nano时间仍未完成；本审查不把固定模型未关闭当成实际数学否定。
同样不能由某个违反 Ordered 的 point 推出加入 Ordered 后一定闭合。

没有新 joint floor、无条件纪录或网站可提交性；source/runtime预算仍
unknown。新阈值、FS、点、ordered增强、优化、Lean或新的模型运行都
不由本审查自动授权。本包到结果封存为止。
