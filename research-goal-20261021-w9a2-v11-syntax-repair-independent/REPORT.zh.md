# v11 单处语法修复的窄范围独审

PASS_STATIC_ONE_SPAN_REPAIR。旧静审未识别非ASCII rb字面量的Python语法错误；旧f78375…脚本、预执行清单、静审和原584896失败保持冻结，原静审不被升级成执行成功。root明确修复决定允许新版本，尚未授权本审查执行producer。

新24993B/SHA21146ef340be7de8dd1a3bd4debe1fbcc098610bf0a381e2ddca0d15b2b2b8ec逐字独立核对：只有offset13279的33B变成48B，将含⟨⟩的rb字面量改为Unicode raw string再.encode("utf-8")；反替换精确还原24978B/f78375原件。ASCII正则部分及UTF-8括号模式不变，结果为bytes，能与已有bytes前缀连接；不改minimax、geometry、source模板、pins或预算。

repair OUT当前恰为同名脚本、README、pre-execution-files.json三份普通冻结文件；清单1935B/SHAbe9c97fa…成员bytes/SHA核同。保持fresh draft-v11、一次新授权、30秒/源2MB/metadata2MB/total4MB、xb、前后pins、失败停止和六span逆投影。原预清单和本清单的execution_authorized=false是准备时状态；root后续gate必须在OUT外，不能改这三文件。

只读已有AST-only收据绑定新21146源码/24993B，记ast_parse_succeeded=true。Root报告原工具59f4ec实际outer0/0.4630138秒；本审查未重复AST、import或执行模块，也不把解析成功称geometry/source/Lean通过。按旧静审其余完全相同的逻辑范围及本修复，未见新的确定阻断；仍须root明确授权唯一新准备执行，采纳要真实outer0+实际总wall≤30秒及最终caps/pins。任何新失败封存停止，不自动修补。

本报告位于producer OUT外。0 producer、geometry/数值、Lean/compiler/kernel、source生成或原脚本再解析；旧报告不改。封存即停止。
