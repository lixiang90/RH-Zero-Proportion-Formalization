# O 固定二次余项的独立重放准备

本包只准备代码。没有 import 审计器/provider，没有数学执行；prepared manifest 的生成只读字节、解析 Python AST、校验文件 hash。必须由 root 另发 gate，才能用唯一 CLI 启动一次子进程。

固定 G1322606、cell278/665、rev/id；绑定 O finalmanifest `9eeb3927…` 与 packet `a952a8bd…`，原 snapshot `f82a4914…`。复用自己的 frozen A parser 与 v1 源 FS/305-row 重建函数，不 import O、N、N2、M、I、J 的生产代码。两原 FS、82 个正原质量锚点 guards、完整 raw52 balance/cost 重新核；原 N2 的 ed007 独审作为身份/语义 hash/成本对照，不再重放全部2375条 metadata。

CellA 使用独立 SZ(p,n) 自然数双计数运算，按原源 Nat subtraction、零分母 division、signed floor/ceil 与 IV 分支运算；没有调用 O provider。只求预声明 hull(q,I) 覆盖到的23个原 REG 单元。I 只取42个物理跨度的原 bounds 交集与17/20分离，不细分、不作 Floyd 或新曲率查询。49个正 raw-dual anchor 的原来源、行号、权重、q、hull、完整原 REG 连续链、m 与 μκm/2 逐项比较。

逐单元比对源 CellA.ok、E2L/E3L、k/side、FA0/1/2、K0/1/2、W2L 与 m。variance/clamp 独立分组求和。网络只读生产保存的十维 p*，逐行累加完整10坐标 stationarity 与 Q(p*)，不重新求解线性系统。残差为零和非负权给出恒等式 Q(p)=Q(p*)+Σc(B(p−p*))²。独审不依赖生产 gauge 选择或最优性声明。

最终核 raw dual cost + max(variance,network) − target 严格正。成功只表示固定条件 pair 的完整整数/有理数付款有效；量化 CellA 下界、强切线余项的 Lean 桥仍待证。没有整域 floor、无条件新κ、源码体积或验证时间预算通过声明。

执行接口：`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageO-independent/run_once.py --launch-authorized-once --gate <root gate relative path> --gate-sha256 <hash>`，cwd 为本仓库。建议 hard300s/20MB，1child、no retry。依据固定两源FS、305行、23个有限 CellA、49个权重和保存 p*；没有搜索、RREF 或解矩阵。该资源建议未经本包试跑/benchmark；如失败或达限保存 failure/terminal，不重启。

冻结端点应包含 prepared manifest、O files/packet/result/terminal、原 N2 final 与 own Below 独审、ownA/v1/packing 源和运行时 exe/DLL。started 记录全部输入 hash，结束及子进程 terminal 后再次校验；输出为 cell-replay.json、independent-review.json 以及完整 raw logs/terminal。
