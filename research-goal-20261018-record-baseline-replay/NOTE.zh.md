# 新纪录原 floor 的完整有限身份重放：Stage A

固定输入是新纪录原始 `Solution.lean`，SHA256
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
不修改输入；原常数 `cN=893616123055294719`、`SA=10^20` 全程保持。
本包没有提高 threshold、分类新例外、扫描窗口对、求解、生成新
核锚或运行 Lean。本结果是原证书的 Python 精确有限身份重放，
不是新的 floor、比例、网站验收或内核证明。

## 已真实执行的阶段

Packing/parser 最终 v3 为 PID34296，exit0，用时2.485秒。137个
zfNat64 literal 全部符合 ASCII 字母表、declared bit length、唯一
leading digit 和 inverse encoding。展开只在内存中产生普通 Nat。
对应 canonical decimal SHA 与另一个代理独立 positional decoder
逐一按声明名和原行号相同。全部数值表只读新源码：8个BS、34个
TS、28个PR、32个BND、496个BK、48个BKD、2095个PT、48个WL/WD、
48个root、70个ready state/cursor和118个cut lists。

原 floor 完整数学 pass 只有一次：PID33820、exec session62798，
exit0，27.862秒，峰 working set87,904,256字节。所有48个原root
均从原bad区间组合重建，全部分支完整游走至源码给出的end cursor。
没有按网站 leaf 数截断。推导出的计数为：

| 类型 | 数量 |
| --- | ---: |
| 原节点 | 27234 |
| 分支 | 13593 |
| 全部终端 | 13641 |
| 数值终端 | 13046 |
| reflection终端 | 595 |
| Farkas终端 | 0 |

网站所说13046与**数值**终端数一致，不等于全部终端数；原统计
值没有被作为 expected assertion。每个数值叶都用紧凑整数公式
和打印的 mcheckP Nat.ble AST 各算一次，13046次全部相同且非负。
最小原整数余量为65,385,001,396,000,000，位于root11/pos27229。
没有据此计算或试验任何更高 floor。

34项见证共443564次解码；每个正质量支持都检查原PT存在、完整
pwD有效区间、`vu>=1` 和 `vl<=L<=point<=U<=vu`，总计189987个
active mokI checks。混合只检查正质量分量，不把质量1024与whole
term混淆。共15179个reachable ydec entries均有合法PR tag；Nat
饱和减法与有符号DBM实现一致所需的split前提检查27186次。

完整 plain walk 的每个节点保存了实际状态和end cursor；在这些
已重放节点上，按源码原fuel、原cut列表顺序及精确state相等守卫
重新解释48个parent和70个nested ready cursor合同，27304次state
相等检查、70次cut命中全部通过。原cut不被当作无需证明的黑箱。
根的walkCutR归一化与raw nested walkCut的state/M合同分别保留。

最后原root WZ补充仅执行一次：PID58296，exit0，2.700秒。160个
**原COV true段**的CellN.WZ整数值和`cN*SW<=a_adj*WZ`全部通过；
最小guard余量为24,036,010,866,362,157,838,000,000。没有加新区间
或新核锚。CE、CJ、FA中12个profile数及所有π/GAM/normalization
常数都从新source读入；没有借用旧核的系数。Leanowner的独立
101声明闭包比对确认98个声明相同，唯CE/CJ/FA的profile magnitude
有变化。本补充绑定该comparison.json的固定hash。

根外的其余有限合同也完整核查：COV首尾连续/端点、14个bad段、
八个压力尾部、八个小gap付款、root的总跨度预算，以及全部bad
组合恰好由48个原roots覆盖。COV有174段，合计root记录190项
（174段加16个尾部/小gap项）。

## 保留的失败和一个纯metadata错误

最初parser v1在解析无外括号的顶层Lean应用时失败；v2完成主体
后在可选定义清单中用了Python简称bcut/gpt，源码名实际是
bcutL/gptF，故又失败。两个脚本、固定命令、PID和完整失败receipt
均保留。准备v2时一次stdout的GBK Unicode错误先于文件创建，
随后missing-file launch没有执行parser；该准备故障亦单独记录。
这些都没有开始数学叶检查。v3修复后再执行上述唯一完整数学pass。
没有静默重启长检查或删除失败历史。

v3 summary里的`WD_identity_count=2`是metadata错误：之前48项
WD dict identity assertion已通过，但后续cursor解析局部变量`wd`
覆盖为两字符字符串，使summary取错len。root独审已指出；原已跑
脚本/receipt/hash保持不动。consolidated summary另从原source
核对48个WDn=rdw WLn，并明确纠正该字段。这不改变数学walker，
也没有为修metadata重跑整walk。正式独审仍应独立核对这48项。

`baseline-replay.json`形成时有意将true-COV WZ标为剩余缺口；
随后`root-wz-replay.json`的单独有限补充闭合了它。原中间receipt
不回写。最终状态由`stage-a-summary.json`组合这两个固定证据，
不能只看早期中间flag推断仍在运行或已完成更高目标。

## 数学范围和后续界线

本重放核查有限整数见证、几何遍历、active interval前提和原根外
整数付款。LB/PT点表的实际解析soundness、CellA/WZ解析soundness
及其Lean证明项仍是固定原源码中的既有依赖；本包没有在Python
重新证明这些分析定理，也没有重新运行Lean、Comparator或nanoda。
用同一source的mcheckP AST作独立算式比较也不是独立内核验收。

事件归档`baseline-events.jsonl.gz`含27234条canonical JSONL事件。
独立流式解压只复核了其字节hash和事件计数；不是第二次数学重放。
source及运行中各脚本的头尾hash全一致。最终清单保留所有闭合
receipt、失败版本、命令和模板出处，不依赖mutable治理文件。

Stage A的有限原floor工作现已结束。新的独立数学审查尚待root安排。
在独审通过并明确授权前，不开始Stage B的raised threshold分类、
例外pair扫描、见证搜索、参数变化或Lean批次。网站源码总大小和
完整内核预算也没有因这次Python原floor重放而通过。
