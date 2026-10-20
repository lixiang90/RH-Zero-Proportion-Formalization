# 保全旧包的运行时范围纠正

本addendum对应原准备清单SHA
`1be4100663d739976fc3d36e654309480b045547a3660cf620a73b0e7d7956fb`。
旧包、旧README、候选INCOMPLETE manifest及v1 runner均不覆盖；下列新证据纠正旧描述。
所有compiler/export/kernel/proof执行仍为0，本addendum也不批准任何runtime。

1. **libLake是link输入，不能据rsp断言必须动态加载。** 旧README称native
   exporter的PE import需要libLake_shared.dll，这句话证据范围过大。rsp中的-lLake
   只证明它被交给链接器。当前PE ordinary import没有libLake_shared；可保守pin
   SDK该文件，但不得称其为实际已加载的必要DLL。mandatory-PE-subgraph.json依据
   原review-v1实际导入图只沿ordinary edges重放，并保存此检查。
2. **84项是泛OS optional delay，不是全部必需加载项。** 原全图递归同时展开
   了大量OS delay imports，造成376图像。只从5个实际exe的ordinary import范围
   出发另得有限子图、无未解析ordinary import。实际已加载模块协议与API-set
   schema推断需要各自保留范围；不要求加载/证明所有Windows可选组件，不能以
   这些delay项替代对真实运行路径的检查。
3. **旧interpreted overlay缺Export.Parse。** 冻结v1模板的两个tool lib目录均
   没有Export/Parse.olean。实际2041280B artifact位于
   `tmp/Comparator/.lake/packages/lean4export/.lake/build/lib/lean/Export/Parse.olean`。
   原CoreAudit和Comparator.Compare均import它。应在新的gate/closure里加入该
   nested同源lib并绑定它与其余实际5个解释执行artifact的source/SDK来源。
   冻结runner无须改动；9源小trusted setup仅为备选，不需重编Mathlib或Nano。
4. **Python动态stdlib扩展不能漏。** 旧controller-loaded-paths只查询python312、
   VCRUNTIME140和ucrt，未覆盖实际_hashlib.pyd与_decimal.pyd。冻结runner同样的
   stdlib imports会加载它们；_hashlib还需要实际crypto DLL。完整新闭包必须另
   绑定这些真实动态模块及其actual/ordinary DLL来源。此只读采集与v1 assembler
   已交independent_math的research-goal-20261020-w9a2-runtime-closure-v1负责，
   本包不运行重复批次，不把旧3模块快照称完整Python闭包。
5. **复用旧binary有较强具体证据。** 优先看
   verification/three-website-declarations-modular-nanoda.json中同exporter SHA
   bc718c9f…的真实export_process_ran=true、export_exit_code=0及固定source/SDK，
   而不是只用analytic receipt的reused/prior exit0。Nano同b1980476…的source-pinned
   历史真实run也保留。日期/盘符变化不自动要求重build；9源Windows setup是备用
   源绑定方案，root应先评估这条较小证据链。
