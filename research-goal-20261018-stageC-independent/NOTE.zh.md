# Stage C 首个可行例外对的独立结果审查

独立结果审查已通过：固定 case ordinal 1，id/id、prefix exception 0 /
suffix exception 1 的闭几何确实有可行点，而且两侧原 ordered 四点条件
都成立。这停止“当前固定例外盒全部不兼容”的几何闭合机会关；没有
计算该点实际 F9，不能称其为低能点或目标 joint floor 的反例。

本包只在 producer freeze 后执行一次结果核验，不另跑 DBM scan，不调用
BF/Floyd、优化、核点或 Lean。没有改原 B/C、源码或治理文件。
书面 gate 为 `research-goal-20261016/gates/stageC-dbm-20261018.json`，
SHA `8020cdd1c37cf1d5b786f803be0f8a2105b99ab9dab31168eb17af8d856994e7`。
生产 C manifest SHA 为
`31e29433295f301c663fc2077d071bae4dfb89b1514eaa694e878fd9f5c8aae0`。
B 生产 manifest 为 `3f9408f2…89ad`，B 我方完整独审 manifest 为
`e6458883…7288`，本次逐项绑定其完整只读依赖。

## 实际执行与独立算法

`review_feasible.py` 运行前仅检查 Python syntax；在 C frozen pin 已收到后
显式给出该 SHA，唯一结果审查 PID 49368，主体 2.3549181 秒，工具返回
真实 exit 0（chunk 9d5242）。没有失败或重试。
receipt `independent-review.json` SHA 为
`37cf42f572f607a0a3b7740a1f41b0298ff617fb906308663c1e4d9999b1c1ef`。
全部输入 bytes/SHA 在运行前后相同。

没有 import 生产 `scan_once.py` 或 `replay_cycles.py`。直接从冻结 B
1,187 行中取原两个完整 cell，独立映射全部 36 个正跨度；source 原 pair
顺序由我方冻结 A parser 再从原 source 确认。每侧 id/rev 独立，rev
使用九点窗口的 `(8-j,8-i)`，suffix 另整体加 1；四 chart 均重建映射并
保存各自 SHA，只验证所报告的固定 case，不搜索其他 case。

令 `X=20*32768*p`，原实数域不变。36*2*2+9 共 153 条边逐条从 B
原 L/U/A/B 生成：`Xj-Xi<=20u`、`Xi-Xj<=-20l`，九条分离边为
`Xr-X(r+1)<=-17*32768`。不四舍五入，不丢 28 个 nonadjacent bounds，
不把 joint 收紧后的 state 送入原 FS/flow decoder。

## 两个报告 case 的全部证据

固定顺序下 case 0 为 id/id、exception 0 / 0。11B 解压 stream 的首个
证书是 edge [98,41]，本包直接从原两个 B state 复原为：

    X8-X1 <= 5015700
    X1-X8 <= -5232660

两边相加权和 -216960，严格负，闭边界也不例外。原 edge 相接闭合，
其物理正跨度在共享顶点 1..8 内。最后是且仅是 case 1 的可行 tag0xf0。
完整 11B SHA 为
`8f4e09de6e110efe2b66e92738e28971473c0706da376f372e1e3e456795e26e`。
这只是验证给定的短证书，没有重新求负 cycle。

case 1 来自原 prefix root0/position1460 与 suffix root0/position9146。
固定整数 potential 为：

    [0,557056,1355776,2131556,2724876,3392856,3986176,
     4635136,6374116,8254976]

本包独立检查全部 153 条 source-indexed edges 的差与 slack，每一项
与生产原记录严格相同，最小 slack 为 0，故接触边界必须保留。
整数 potential 只是实数域中容易精确验证的点，不限制原变量为整数。
actual id/id 153-edge 表 SHA 为
`ae1e6f0f59276bcb03f2ab10eda767dfc9ac84d929f7464f98349e8c942536ca`。

prefix ordered 原第 0/7 gap 分别为 557056 / 1738980，差 -1181924；
suffix 对应为 798720 / 1880860，差 -1082140。两者均 <=0，所以本例
并非仅因丢弃 Ordered 才可行。ordered 条件独立核四点式，未伪装成
单个 difference edge。检查的是同一 potential，没有另求更强点。

生产只处理 2/5,635,876 cases，按首个可行即停止合同正确结束；本包完整
核完这两个报告 case，不把后续未处理者写成已排除或全覆盖。

## 原 FS/flow 身份与数学结论的限度

除几何外，本次只对这两个原 numeric leaf 从固定新 source 重新解码
原 FS/flow，并以我方独立 A 的 printed AST / termTI 实现检查原余量。
不是在这个 potential 处求核值，也不是产生新 witness。
source 仍为 1,818,411B、SHA
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
两叶原 state、payload bit/end、packed SHA 和 semantic SHA 全部同 B。

| exception | 原 source root/position | 原余量 | tau 余量 |
| --- | --- | --- | --- |
| 0 | 0 / 1460 | 74501376990071397846927248000000 | -26161919009928602153072752000000 |
| 1 | 0 / 9146 | 56577247050221517825498512000000 | -44086048949778482174501488000000 |

tau 余量只扣同一固定 debit
`335544320000000000*300000000000000` 一次。两 semantic SHA 分别为
`161848d29fac7b4839fb95164edb00cdda9088b9c587316013ef02f00581bb38` 和
`a8ab41871aedca5b6c74bc11541340f6c62ef941a65635cd968cf29c90bf74c6`。
这说明原 interval witnesses 在这些 cell 上不足以支付 tau，不说明
实际 F9 在可行点低于 tau。

完整 source / 新 consumer / DBM 形式证明 / wrapper / ordinary-export-Nano
总运行预算仍未知；该结果不打开 proof batch 或网站上传 gate。没有新
joint floor、无条件零点比例纪录或可提交新结论。固定几何方案到此停止，
没有自动增强 ordered、细分 cell、改阈值或切换优化家族。
