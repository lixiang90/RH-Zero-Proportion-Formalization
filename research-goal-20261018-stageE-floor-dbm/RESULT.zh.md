# E 唯一模型检查已结束：首个不足付款的松 DBM 点违反两 ordered

SPEC.zh.md 是运行前规格，原文保留。实际执行另获 root gate：
research-goal-20261016/gates/stageE-margin-dbm-20261018.json，SHA
4c83f5f157c9dba302c712951f681394df4d15e703770eda64b420a124e0c3bf。
绑定 B 独审、D 独审、原 floor 证明与 E 全域静态逻辑的 frozen 包。
输入 schema 的 c9_numerator 在执行前适配，未发生失败模型或重试。

只有一个 child，PID55704/parent50968，child0.4889593秒，parent
0.826552秒，exit0。300秒/闭输出20MB均未触发；没有新点/FS/核值、
LP 或 Lean。数学脚本/所有输入前后 hash 完全一致。

## 阈值及计数

程序构造 kappa=32768*10^10*1024；DeltaN=tauNum-c9Num；
T=kappa*DeltaN，并另核 T=2*kappa*(cNum-c9Num)。使用 Mi 全部精确
整数，没有改用 Mi//kappa 或截去余数。T 为

    100663296000000000000000000000000.

按固定四朝向-major、prefix id、suffix id顺序，实际只处理1193个
case，分为766个原 scalar floor付款、426个共享跨度严格两edge负
cycle、1个不足付款的松 DBM 可行点。未声称其余5,634,683个case已处理。
没有抽样、跳过首可行或换参数。E不同于C：先用已有定量原余量付款，
仅不足付款的pair进入同一原几何条件。

首个不足付款且 DBM 可行者是 ordinal1192，id/id、prefix exception1、
suffix exception5。其原 margin：

    Mi = 56577247050221517825498512000000
    Mj = 4621809023144565169846040000000
    Mi+Mj = 61199056073366082995344552000000 < T
    T-Mi-Mj = 39464239926633917004655448000000.

由原常数 floor 相加得 f_i+f_j-2c 的精确值为

    -4933029990829239625581931 / 4194304000000000000000000000000.

这只是已有常数floor付款不足，不是实际 F 的值。

## 精确可行点与 ordered 范围

同原36+36正跨度闭 bounds 及9sep，共153edge，存在整数 potential
（原变量仍取实数，scale=20*32768）：

    [0,2663120,3234020,4032740,4830940,5493380,6086700,
     7127020,7697920,8254976].

first-underpaid-feasible.json 保存原两完整 B cell、朝向、全部153edge
与非负slack、Mi/Mj/T、十个有理位置及两ordered。prefix h0-h7 的
scaled差是2092220>0，suffix差13844>0，故两ordered条件均不成立。
结果标记 underpaid_relaxed_DBM_feasible_ordered_violated，并立即停止。
未把这个点丢弃后继续，也未把四point ordered关系冒充一条DBM edge。

因此当前“原常数floor+丢弃ordered的闭DBM外包”机会关未关闭。
不说明真正有序窗口能同时低能，更不反驳候选下界；没有计算实际核或
该点的FS affine值。能否加入完整ordered约束属后续新决定，不自动授权。

## 可复核性及停止范围

RZE1流解压2050B，含按固定ordinal的766付款tag、426负cycle记录及
最后一个0xf0。每个cycle都由原source-indexed edge组成、严格负和；
接触/等号未误排除。scalar equality允许付款。原C纯几何engine按
SHA强绑导入，不调用它的旧扫描入口、不改旧源、不写bytecode。

replay_witnesses.py不import E/C生产器、不BF：从原PR与B数据重新
构造edge和原整数付款条件，逐1193record验证、检查EOF/计数/hash，
并逐153edge核末点。一次运行0.2802914秒exit0。它是本代理提供的
独立算法，另一代理的独立审查仍另存，未预先代称完成。

模型仅运行一次，后续没有新scan、点或优化。源文件总量及
consumer/kernel/export/Nano预算未知；没有证明所有例外对的新joint
floor、无条件零点比例或网站可交付源码。

model.json SHA：27476a63f4f705f292cecef20cd6af8dabeb389682319c22058a89ce37100ed1。
first-underpaid-feasible.json SHA：e227a288007a8dbb984d0b69b5d367d34595b653ccd2da83e2226806751c746c。
