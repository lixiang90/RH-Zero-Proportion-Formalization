# Stage C 准备实现：固定四朝向 DBM 机会关，尚未执行

本目录准备唯一算法，没有 start/launch/scan receipt。必须先取得 B 独立
封存包和 root 的新书面决定；Stage B 的授权不能用于启动本关。

输入固定为 B 的 1,187 个完整闭 cell、原 PR 顺序、tau 和 sep=17/20。
四组合按 id/id、id/rev、rev/id、rev/rev 排序，每组 prefix id 升序，再
suffix id 升序，共 4*1187^2=5,635,876 个 case。不筛选有利子样本。

X_i=20*32768*p_i 仍取实数。原第 k 个正跨度 (i,j) 的闭上下界为 l,u。
id 保持端点；rev 映成 (8-j,8-i)，l/u 不变。每 cell 的 edge 2k 是
X_j-X_i<=20u，2k+1 是 X_i-X_j<=-20l。prefix edge id 0..71；suffix
id 72..143，端点整体加 1。edge 144+r 是 X_r-X_(r+1)<=-17*32768，
r=0..8。共 153 条 edge；不对 sep*32768=27852.8 取整，不加 ordered cut。

先逐 lexicographic 的 28 个共享正跨度 (i,j),1<=i<j<=8，比较两 cell
的闭投影。只有一方 lower 严格超过另一方 upper 才给两条原 edge 的
负 cycle；端点相接保留。随后可缓存单 cell 自身 72 bounds+8 sep 的
必要负 cycle；该 cycle 映入全 153 edge 后再次检查。其余运行 all-zero
super-source 的 10-vertex 整数 Bellman-Ford。每个负 cycle 都检查首尾
连接及严格负整数和，不信任浮点/求解器返回标志。

如 DBM 可行，BF 的整数 potential 是其整数 RHS 下的一个真实可行见证，
不是把原实数域改成整数域。归一到 X0=0，逐条核全 153 edge；保存
原两份完整 cell、朝向、十个 X 与有理位置、每条差/余量。按每个朝向
另外检查原 h0<=h7 的四 point 关系：prefix 与 suffix 各一次；输出
ordered_conditions_hold 或 relaxed_box_feasible_ordered_violated。
两种情况都立即停止；绝不能丢弃不满足 ordered 的首点后继续搜索。
这样的松外包点不是实际低能点，也不是函数下界反例。

全部不相容时必须完整覆盖 5,635,876 case，保存 canonical 顺序的负
cycle stream/count/SHA；不能把一个超时前缀当完整证明。proof stream
为 gzip 的字节流：magic `RZDBM1\n`，随后每 case 一个 tag：高四位
method (0共享、1单prefix、2单suffix、3完整BF)，低四位 cycle length，
再跟每 edge id 的 uint8。所有 edge id <=152。首个可行 case 的 tag
为 0xf0，无后续 payload，并且必须是最后 record。case ordinal 隐含于
固定遍历顺序，因此每个严格 cycle 都可脱离 BF 独立重放。

replay_cycles.py 不 import 生产器，不调用 BF/优化器：从原 source 的
PR literal 与冻结 B geometry 独立生成 edge，逐 record 只检查 cycle
或最终 potential；核源码/输入 hash、数量与完整性。尚未运行该 checker。

run_once.py 只 Popen 一个 child，外部监控 300 秒/闭输出 20,000,000B，
只终止自有 child。child 也周期检查限额。达到限额只是 inconclusive，
不自动重试、换参数或增强 ordered 条件。guard 失败则封存 failure。
没有核查询、threshold/FS 变更、new cut、Lean 或 pair proof batch。

书面 gate 字段合同：pair_scan_passes_authorized=1、固定 B producer
manifest SHA、B independent manifest path/SHA、tau_numerator、denominator、
separation、exception_count=1187、固定 orientations 和 resource_limits。
启动时必须显式提供 --gate 和 --gate-sha256。当前没有 gate 参数填值，
也未启动扫描。生产代码的默认调用只打印 prepared 规格，不读 cell。

本关只判断松外包几何的数学机会。baseline+完整新 formal consumer、
geometry/DBM proof encoding、kernel/export/Nano 的源码及运行总预算均
未知；既有静态 product consumer 不能填补这些未知项。即使全部几何
不相容，也不自动成为全网站可交付证明或新无条件比例。
