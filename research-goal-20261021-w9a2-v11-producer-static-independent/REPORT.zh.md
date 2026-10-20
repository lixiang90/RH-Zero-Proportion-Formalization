# v11 定点 producer 执行前独立静审

PASS_STATIC，未见确定的Python文本或Lean组合阻断。完整静读24978B冻结脚本f78375a32387ba5b6d5372c40f424d740483c374a051a62e2c35355fd21b8fb7、README及pre-execution清单e1eb91b3…；两成员现行bytes/SHA及宏观014的8780B/2c2c95cd…核同。未运行/导入/AST解析producer，未生成metadata/source、解WL、重算数值或运行Lean；不改原producer。

残余逻辑符合macro014。r37仅目标pos1、旧两cut620..79718和110366..137099，总637−256−91=290；跳过旧cut内部及自身。其余proper descendant以cursor区间界定，逐旧cut要求不相交或完整包含，部分交叠拒绝，只扣完整包含的numeric。r43仅169..70606子树，总249、空旧cut。候选唯一按(score=max(inside,total−inside),pos)取min；即使先保留0/total候选，存在严格分割时其score必更小，最后仍要求0<inside<total且score<total。无fallback、阈值族、energy或新分支搜索。

几何仅遍历37/43两根：原BAD/PR/indices建root，原closure公式分支，完整73字段M0、JSON+末LF hash逐事件核；源中原hint literal及fuel同时与旧packet核对。全归档24504条只作固定framing，实际新geometry范围由旧packet绑定为两根1992状态。未把metadata当实际Lean stEq。新hint的fuel=128−globaldepth，根43子游走因此使用其107入口的正确剩余层数。

r37新子cursor使用原v10_r37_cuts，Coverage依赖原cuts_ok；新列表newhint::oldcuts，经cutsOk_cons组合，父cursor及rc37改用新列表/新CutsOk。它不依赖新父或rc37，无循环；CutsOk本身不要求列表不相交。r43新raw子cursor先在空cuts上得到Covered，再把原v10_r43_e0的目标明确改为cut-aware169游走，c0应用新CutsOk但同一Covered(toCl v10_r43_s0)类型不变。当前源中e0仅定义及c0的rw两处引用；外层43的原cuts/父/root不改。旧空cuts失败目标不被遗留或冒充已证。

Graph两个原header/type逐字保留。每个固定u行用(i:State)，i严格覆盖0..48（State=Fin49），仍∀v并采用原ordinary decide；只替换独立词u，不替换其他标识。原定理intro u/fin_cases u后49个显式对应bullet，引用opaque行定理。98行、98bullet均有唯一性断言，good、所有v、strict Conflict、orientation、qCell和原Edge未被削弱。固定Fin numeral/proof irrelevance使行命题与cases目标在静态类型层面相容；可编译性仍未经Lean确认。

六个编辑span：r37 helper+parent、rc37 proof、r43 helper+e0内部类型、c0 proof、两Graph proof。每个原锚唯一、span不重叠，完整反向替换必须逐字恢复v10；还核221CRLF、135packed标记、末LF及原Covered/Graph类型。实际生成后仍需独立raw投影，不把未来断言当已完成源审；公开三根/K由未编辑范围保留。

固定ROOT下只写fresh draft-v11及本producer目录，xb/fsync不覆盖。OUT初始必须恰为3个冻结文件，禁止将root授权文档放进OUT。前后PINS含脚本/README/pre清单及所有数学输入；source≤2MB、metadata≤2MB、total≤4MB有预估与最终实际文件计数，失败写receipt并抛出，无自动修复/重试；不存在旧generator/model/compiler/export/网络调用。

时间门是合作式monotonic检查，最后一次check在print之前，elapsed_seconds_before_receipt也不是完整终态计时。Root已明确补足采纳条件：原实际outer0及实际工具总wall≤30秒（含收尾/print），再核最终文件/pins/caps；只凭自报elapsed或completed=true不采纳。该外层条件足以关闭本次准备的最终时长收集范围，不构成OS硬实时/内存保证。

本审查只允许root考虑执行一次已冻结metadata/source准备，不授权Lean或官网。未知selected pos/state/new源体积/终态仍未知；生成失败须保全停止，生成成功也仅准备关，后续资源/双核/官网仍未PASS。静审封存即停止。
