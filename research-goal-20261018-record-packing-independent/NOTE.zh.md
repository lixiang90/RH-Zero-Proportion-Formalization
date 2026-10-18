# Stage A：新纪录源 packing 与声明索引的独立核对

本包仅处理固定 raw source 的普通 Nat 数字身份与声明元数据。
不解释证书 walk，不评价实际核，不检查有限数学 guard，不执行 Lean。
它不是 13046 叶完整回放、提高阈值分类或新能量 floor。

固定来源为
`research-goal-20261018-record-source-audit/snapshot/Solution.lean`，
SHA256 `f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`，
原始 1,818,411B。该源码第 117–122 行的 `zfNat64` 成功分支只
构造 `Lean.Syntax.mkNumLit (toString value)`；它的静态源码摘要
记录在回放 JSON 中。这里不运行源 macro，也不以它证明任何 guard。

`decode_packing.py` 没有导入 producer decoder。独立实现把 alphabet
映射为 ASCII 索引，再求各位 `digit * 2^(6*position)` 的整数和；
这与源中“逐字节 shift/fold”不同。逆向用反复 `divmod(value,64)`
生成唯一文本。全部 137 个 packed call 均必须属于已识别的普通
Nat literal 声明，并逐项验证：

- ASCII 与固定 `A-Z a-z 0-9 + _` alphabet；
- MSB 顺序、六位进制、所声明 bitlength 不超过 65536；
- 文本长度、首位有效位数、整数 bitlength 与唯一零 `A`；
- encode/decode 逆及 canonical 十进制整数往返。

所有直接 Nat 常量声明中的 packed、hexadecimal、decimal 数字
均提取普通整数的 bitlength 与两种 SHA256：无前导零的十进制 ASCII，
以及最短无符号大端字节（零使用单个零字节）。这些摘要适合随后
与 producer inventory 逐项比对；本包不输出庞大的完整十进制 payload。
同名常量通过 source line 和 byte offset 区分，不猜测 Lean namespace。

JSON 还给出所有 TOP/BK/WL 直接数字声明的索引与普通 Nat 摘要，
并单独标出相关 computed Nat 声明仅作元数据、没有求值。其他函数
型 BK/WL 分派不被当作整数数字 literal，也未执行。

源码所有 48 个 `rcN` 根、48 个 `readyN_parent_cursor`、70 个
`readyN_K_cursor`、70 个对应 `readyN_K_state` 和 48 个 WD 根流
都记录 declaration name、行号、byte offset、原始行 SHA 与签名。
精确名称集合及 cursor/state 对应关系均检查。它们的数值等式仍是
**源中定理声明**，没有在本次 Python 回放中执行或证明。

源注释先用保留 offset 和字符串的 nested-comment masker 排除，
避免把注释示例算进 literal 或声明集合。数字值取自这份新的固定源，
没有取自旧 Core 的 nonnative 定义或旧 profile 数据。

一次标准库读取和 exact packing 回放后冻结。本轮未与 producer
packing list 比较；可在 producer 名单冻结后另作只读比对。任何此类
packing 一致性都不能替代原 floor 全根、nested cuts、全部真实叶、
几何/见证身份以及原有限 guard 的数学回放。原始 13046 叶总数在
本包中只保留为任务合同，未独立核数。
