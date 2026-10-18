# E 固定模型准备：原余量付款 + 原四朝向 DBM（未执行）

与几何-only 的 C 不同，这是一个新的必要模型：同一 B 1187 closed
cells、同原 FS/余量、同 tau/c/sep，不取新点或核值。仍按 id/id、
id/rev、rev/id、rev/rev，prefix id、suffix id 依次遍历 5,635,876 case。

所有阈值由表达式构造：Q=32768,V=10^10,R=1024，kappa=QVR；
DeltaN=tauNum-c9Num，paymentThreshold=kappa*DeltaN。代码另核
2*cNum=c9Num+tauNum，故 threshold=2*kappa*(cNum-c9Num)。不在代码
中手抄长阈值。每个 Mi 从原 B 记录解析，核 Mi>=0、Mi-threshold
严格等于其保存的 tau_margin<0。

原 source 与冻结 affine-flow 证明给每 cell 的已有常数 floor
f_i=c9+Mi/(kappa*SA)。反射只运输同一常数。若 Mi+Mj>=threshold，
则 f_i+f_j>=2c，这个 case 直接付款，不需要几何或更强 FS 查询。
记录 scalar-paid，不能把“首 pair 已付”推广为全部 pair。

仅付款不足的 pair 进入原 C 几何算法：28共享正跨度闭投影的严格
负cycle、可缓存的单cell必要sep负cycle、或完整10vertex/153edges
DBM。直接 import 的仅是原 C 冻结 source 的纯几何函数，SHA强绑，
不调用旧 C 的输入/扫描入口，不改变旧包或写 bytecode。每个 cycle
依原source edge id重新检验严格负和。没有新 cut/ordered增强。

首个付款不足且 DBM 可行的点立即停止，两 ordered 四point是否成立
另列。保存原 Mi/Mj、精确阈值与不足量、两完整原cell、朝向、10个
potential、全部153边与余量。这个点只反驳“原常数floor+几何必要
条件已经关闭”的模型，不能当实际低能点或能量候选的反例。

若没有首可行，必须实际覆盖全部 5,635,876，计清 scalar、几何各
种证据及顺序 hash。binary witness stream：magic `RZE1\n`，隐含
固定 case ordinal；0x40代表原floor付款；cycle tag依 C 方法和长度
再存edge uint8；0xf0代表最后一个 underpaid feasible case。独立
replay_witnesses.py 不import任何生产器/不BF：原source PR、原 B
Mi 和 geometry独立重建，逐record验证原付款或cycle/potential。

root必须另发新gate，绑定 B 独审、D 独审、原floor static、E全域
逻辑static。拟字段：pair_model_passes_authorized=1，stageB_producer
manifest SHA、stageB_independent_manifest_path/sha256、
source_floor_static_manifest_path/sha256、stageD_independent_manifest_path/sha256、
stageE_static_manifest_path/sha256、原c9/tau/c分子和denominator、sep、
exception_count、orientations、resource_limits。默认调用只打印准备
状态，不加载cell或产生start/scan。当前没有执行收据。

唯一运行限300秒/闭输出20MB；达限=inconclusive，失败也封存，不
重试或变参数。禁止新kernel、FS、点、LP、Lean或证明批次。完整
网站consumer/源码/运行预算未知，即使数值模型全部关闭也不能
自动视为网站提交或无条件新比例已证明。
