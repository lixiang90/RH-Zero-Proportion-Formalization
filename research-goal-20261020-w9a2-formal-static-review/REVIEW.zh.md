# W9A2 实际证明候选的独立静态审查

本包在 macro007 后实际第1主轮内准备。子代理没有更改主轮计数、数学参数、
核表、叶数据或任何候选 Lean 源码；没有运行 Lean、原 walk、核函数、LP、
Karp 或几何搜索。下面的 PASS 仅是源码与冻结元数据的检查，不是实际无条件
定理或双核验证通过。

## 数据与 selector

独立审查读取官方原源、当前 Core、冻结 geometry 与原 sorted metadata。
官方原源 SHA256 为 `241068ee5abab772ea1aba7533ec33b9140df7dc1728aeb4c61bfb648fe195c7`。
Core SHA256 为 `c5180e8cb9d219bec5cf29e4d65e0cfc304f4d40a12ad6d52332603e115fccd6`。
`audit.json` 记录全部输入的前后身份。核/分析数学前缀除删除旧 CandidateSpec
import 外逐字一致；整个 Data namespace、135 个 packed literal 声明和48个
rc 定理逐字一致。stEq/St_eq 只是原样前移。mcheckP 和 mleafP 的函数体在
移除新增 goal 参数后逐字恢复原版；原 fleaf、walk 和 walkC 定义完全一致。

qState 的24个73字段状态与冻结 first24 精确相等，qCost 是各原 margin 的
`335544320000000000` 整除，且24个状态互异。全部11794条数值叶元数据中，
11794个状态也全部互异；24个 selector 状态各命中一次，剩余11770条均用
good increment `1000000000000`。

每条元数据都核对
`margin >= 335544320000000000 * selected_increment`。无失败，最小余量
`48973028972000000`；good 分支最小余量
`18662069705779938066800000000`。这排除了元数据层面的重复状态见证冲突或
漏选低 margin。该扫描没有重新证明 sorted metadata 与实际 walk 的对应，
更没有代替新48个 rc 的定量 `decide +kernel`。

审查脚本v0因把原 walkC 错写成不存在的 walkCP anchor 而在元数据扫描前退出；
源与 `audit-v0-failure.json` 保留。v1只修复该审查脚本的名称，随后检查通过。
没有因此改变候选源码或启动编译。

## root 外、反射与 Graph 的合同

静态数学审查未发现新的数值或局部 floor 假设：

- QuantGoal 对好态和24个指定 cell 都保留原 Pg 的反向分支。原 cert 经
  quant_forget 仍只输出原 cN，故旧计数链不会被无声提高。
- root_QuantGoal 对全部 separated gap 用同核 wfun 非负性保留全 pressure。
  SMAX 尾部只引用原 cN 的有限检查，并补其余七个 gap 的 sep pressure；
  true-WZ guard 也只用原 coverChk 声明，补全部八项 pressure。小于等于
  1/2 的分支与 sep=17/20 矛盾。剩余配置沿原 badOf/idx/incell_root 进入
  完整 Data.run；不存在只覆盖数值叶或极小点的收缩。
- ordered_quant 的 `g 0 <= g 7` 与 Pg 的 `g 7 < g 0` 恰好矛盾。
  located_state 对任意真实 Fin8 gap 独立选择 id/reverse，两种方向都经当前
  Fg_G 和 PC9QB6M_G_rev 变回当前 actual W9；v=48 接纳全部 root 外好态。
- Graph.StateAt 的偶数顶点指向 qCell(v/2) 的 id 方向，奇数指向 reverse。
  located_id/located_rev 采用同样编号，cost 直接读 qCost 或 qGoodIncrement。
  qCost 是 Nat，Graph.cost 是 Int，最终比较中的 real cast 单位一致。
- Graph 的排除只用同一真实十点路径共享的七个 gap。每个所选区间必须严格
  分离；闭端点接触不会被排除。good 的几何条件为 True，两端 incident 边
  均保留。静态接口与已冻结2267条严格见证检查相符。

因此本次完整数学义务应由当前 source 的实际 Lean elaboration 与有限整数
检查消除，不能再增加与用户目标无关的模型前提。

## 编译门槛与剩余范围

当前5份 Lean 源 raw 合计1827766字节，不含最终单文件处理、可信 spec 或
public wrapper；不据此宣布网站体积已验收。定量 selector 会在原数值叶中
额外做完整 St 比较，其生产时间影响未测。

建议唯一冻结 ordinary gate 的依赖顺序为 Core、Graph、Localization、Counting、
Final。首先必须确认新 qTargetFrom_sound 递归、mleafP 目标泛化、全部48个
实际定量 rc、具体 PR/root 化简、反射、Fin/Int cast 和全有限势求和都通过。
最终根应逐个打印传递公理，且仅允许 propext、Quot.sound、Classical.choice。
任何编译失败须保留该源、命令、日志与 receipt；只提出精确 proof-only 修复，
未经主代理新 gate 不自动修复重跑。任何有限检查不成立都必须停止并交回，
不得修改 margin、cell、阈值、潜势或数据来追求通过。

当前 compiler_runs=0；最终实际 ζ dyadic/cumulative、独立 Comparator/Lean/nanoda、
冷检时限、单文件大小、届时最新网站纪录严格比较、GitHub字节同步和提交材料
均不在本静态 PASS 的证明范围内。旧已接受记录的收据不覆盖这个新候选。
