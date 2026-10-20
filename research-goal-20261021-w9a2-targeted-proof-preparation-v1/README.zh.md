# v11 定点证明 producer 准备；未执行

唯一依据宏观014（SHA `2c2c95cd40ef75493d74e0cc4e4d9bb03032e8911c7adfb4b041f672469329f4`）。本目录只冻结脚本、本文和预执行清单。此阶段不执行脚本、元数据生成或 Lean；只有 root 后续明确授权才能执行一次。

输入固定 v10 `86e3f46c…41e14d` / 1,914,823 B、原事件压缩包、既有 v10 packet 和几何归属源码（仅读 hash，不 import）。未来输出 fresh `research-goal-20261021-w9a2-delivery/draft-v11`。

固定改动只有四项实际失败义务：

1. Graph 两个全称定理各产生49个固定u、量化全部v的 ordinary-decide opaque行引理。原类型不动，`fin_cases u` 后恰49个显式对应行引理的 bullet；不用first/trial。
2. r37目标root1的290残余，跳过原两cut内部（含本身），对proper descendants只扣除完整包含的原cut，最小化 `max(insideResidual,total-insideResidual)`，同分取最小pos。新子proof只用旧CutsOk，父和rc37用`newhint :: oldcuts`。
3. r43目标pos169的249原raw残余，同一minimax/pos规则，空旧cut。新raw子proof得Covered，原e0明确改成带新cut的169游标等式，c0消费新CutsOk；不声称新等式等于旧raw等式，c0 Covered类型和外层root43保持。

只有一个hint/target。两侧必须都严格减小，否则停止，不改规则。原73字段/M0、fuel=128-globaldepth、pos/end、归档state hash必须核同。几何仅复制既有纯interval closure公式；不解码WL，不执行叶能量/余量/tangent/checker/solver或原数值模型。需检查两个目标根共1992原状态，而不是新一轮数值核查。

所有源编辑按UTF-8原始bytes处理。新行用LF，保留原Graph头/类型的CRLF及原proof末CRLF；反向六个替换span必须逐字恢复整个v10，135 packed与221CRLF、末一LF和所有未编辑原字节保留。原公开三命题、K、数据、图和其他根不改。

未来单次准备预算30秒，metadata≤2,000,000 B、新单文件≤2,000,000 B、全部新输出≤4,000,000 B；fresh目录、xb写入、输入前后SHA、无覆盖/重试/自动修补。任何身份、几何、原源形状、尺寸或预算失败均保存failure并停止。现有预执行清单的`execution_authorized:false`表示此准备阶段没有执行授权，未来root授权不需要改写该冻结清单或原脚本。

本脚本只准备新proof源码；它不调用Lean/内核/export/旧generator或collector/网络/UI/Git，也不接触资源work。即使未来metadata exit0，也不是证明、资源、双核或官网接受。
