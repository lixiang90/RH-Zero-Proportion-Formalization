# 固定 Stage B 的独立完整分类审查

本包只完成 root 书面 gate
`research-goal-20261016/gates/stageB-20261018.json` 指定的单阈值分类独审。
gate SHA 为 `1548e22dcd1446a7110cb3c2452a574d0edc323c3bb81b35591a1d0e93324273`。
没有读取另一阈值，没有 pair query、核点、优化、新见证或 Lean 执行。
没有修改原 A、B 生产包或治理文件。

输入为固定上游 source
`research-goal-20261018-record-source-audit/snapshot/Solution.lean`，
1,818,411B，SHA
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
B 生产冻结 manifest SHA 为
`3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad`。
本次对生产整包及其只读依赖逐项检查 bytes/SHA，运行前后全部相同。

## 独立性与唯一执行

`replay_classification.py` 不 import 任何生产 Python 模块。
从我方已冻结的独立 A 实现加载源解析、真实整数 walk、termTI、flow、
printed AST 和 cut 合同；其唯一打包 helper 也是我方先前独立实现。
我方 A manifest SHA 为
`2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c`。
该复用避免重新实现已审好的基础树语义，B 阈值分类和输出比较由本包实现，
不是复跑 B 生产脚本。生产模块只作为固定字节和结果数据检查。

执行前只检查 syntax/schema 并封定脚本；没有数学试运行。
`run_once.py` 保存 argv、cwd、脚本 SHA 及 child PID，最多启动一个 child，
从外部执行 180 秒和 32,000,000B 输出上限，无自动重试。
唯一 child PID 59364，exec session 57713，真实 terminal exit 0。
独审主体 46.188135s，parent 46.8967233s，未触发上限、无 failure receipt。
`independent-review.json` SHA 为
`bd2b92c42716cabc3558df96fcb5eb666a950798d79b13c8db3585b75f369fbd`。

## 固定扣款、完整树与见证身份

源 cN 原值始终为 `893616123055294719`；新 tau numerator 为
`893916123055294719`，共同分母 `10^20`，差值恰为
`300000000000000`。独审从 printed Nat.ble AST 递归检查：cN 在左侧
恰一次，右侧没有；该路径只经过 Nat.add 和乘正整数，系数恰为
`335544320000000000`。因此同一 state、FS 和 flow 的准确余量为

    M_tau = M_original - 335544320000000000 * 300000000000000.

没有对 ready cut 的旧阈值结论直接加新阈值：全部原树重新展开，原阈值
仍逐点执行原 active mokI、term decode、flow 和 printed AST 余量检查。
48 roots、27,234 nodes、13,593 branches、13,046 numeric、595 reflection、
零 Farkas 与独立 A 完全一致。48 parent / 70 nested 的完整合同仍相同。
189,987 active mokI、443,564 term decode checks 仍同 A。

27,234 个 canonical all-node events 的解压 JSONL SHA 与我方重新计算的
整树 trace 严格相同：

    c486090f64a67eccae8de6914688626738e212ebe7ade515d6825efa28abc10e

对 13,046 行逐行比较 root、stream position/end、完整二叉路径、两种余量、
state hash 和原见证定位。原 FS/flow 从我方解码器重新取得，逐项比较
packed payload 和 decoded semantic SHA，不仅比较计数。分类得到
11,859 closed / 1,187 exception，与生产全部相同。余量等于零归入 closed，
未在边界丢失叶。numeric 解压 canonical SHA 为
`ca06915728a86b7f538ffc6f9e392e74d9246d00feda181a0bdbb79105a637a3`。

## 完整闭几何、反射与根外分支

全部 1,187 例外逐行独立复原 8 adjacent + 28 PR 的全部上下界、源 pair
顺序、M=0、坐标比例 1/32768、连续 ID、原 root/provenance，以及每个
nested cut 的 state/fuel/start/end/state SHA。完整 source subtree 终点也在
每个 enclosing cut 内，因此生产的 start-only provenance 条件未掩盖
越过 cut 终点的叶。exception 解压 canonical SHA 为
`ef930bb15e093c3ab5ea75a8e8d95d760ecde606c573366c0c4606b2fe743aa0`。

这里的变量是实数 gaps，分离恰为 `17/20`；从未将
`32768*17/20=27852.8` 上取整。所有 cell 都保留闭上下界。
反射逐项检查系数 `a(i,j)=a(8-j,8-i)`、BS 回文及全 36 对坐标置换的
两次反射恒等。595 原反射叶全部检查 `U7<L0`，只与有序半域
`h0<=h7` 矛盾，不支付能量下界。`h0=h7` 可取 identity 朝向。
为供未来 conservative geometry 使用，例外明确删除有序条件，所得
cell 只会放大；没有把该四点不等式当成单个 difference edge。

root 外未重新求 WZ。对我方独立 A 已核的 160 行原整数 WZ guards，
逐行核源 coefficient、原 cN、WZ 两端和整数余量，然后加全部 `s*B`
得到 `c9+s*B>=tau`。八个尾部逐项核
`b_r*SMAX_r/32768+s*(B-b_r)>=tau`，没有重复第 r 项付款。
八个 gap<=1/2 分支在 s=17/20 分离域为空，连端点也不例外。
全部 COV 真假段连续、闭端点正确，源 48 roots 恰覆盖 false interval
的笛卡尔积；本包仍由独立 A 的实际源结构验证这一事实。
生产 root-outside 文件的 160+8+8 共 176 行全部与独立 Fraction 算术相等。

因此本次有限审查所支持的全域逻辑是：对任意 `h_r>=17/20` 且
`F9(h)<tau` 的实数向量，在有序半域必进入某个原 exception 闭 cell；
整体 sublevel 被这些 cell 及其反射的并覆盖。这里仍依赖 source 已有
LB/PT/WZ 的解析 soundness 与 reversal 定理，Python 没有重新证明
这些 Lean 证明项。它不是只覆盖 minimizer 的说法，也不把例外当作
存在实际低能点的证据。

## 尚未通过的完成条件

没有进行两个窗口的兼容性判断；没有新 separated/joint floor、无条件
比例新纪录或网站可提交结论。后续两个窗口必须各自允许 identity /
reversal，四种朝向另行授权和证明。

本次重新计量朴素 73 整数十进制 payload：579,013B，与生产完全相同；
该文本甚至未验证为 Lean 编码。baseline 距 2,000,000B 只余 181,589B，
因此这一朴素表示已超余量，gzip 或 JSON 的大小不能算网站源码预算。
旧三桥 38,361B 只作迁移参考。新 formal consumer、几何/DBM 证明、
新桥和 wrapper、完整 flattened source 和 ordinary/export/Nano 运行量
仍全部未知，完整源码/运行 gate 为 false。没有因本次分类成功而启动
证明批次，也未把研究数据包说成 upload-ready。

本包到此停止；无 pair scan、优化器、核点查询、Lean 或治理计数变更。
