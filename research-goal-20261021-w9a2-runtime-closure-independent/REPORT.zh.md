# 全文件 proof-only 定义抑制代码生成的独立静审

结论：有条件支持“保留本文件真实runtime闭包，对其余普通def/abbrev/instance显式noncomputable”的源级提案；不支持把所有命令机械加前缀，也不能把它描述为关闭所有native entry。没有实施或验证新源码，不能声称可编译、内存下降、137根因已定位或官网可通过。

固定输入仍是v8，1829382B/SHA5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b。本次只读该源、既有有限报告及同pin v4.33.0-rc2/d8b189 SDK与现有Mathlib的少量相关源码；没有源改写、Lean/compiler、数学/数值重放、大export/closure、网络、Git/state或counter操作。下文是源码和实现边界，非运行时内存profile。

声明类别/特殊属性的完整词法盘点引用formal_owner冻结的`research-goal-20261021-w9a2-runtime-closure-formal/source-inventory.json`，1678524B/SHAda9b9258508f7d6f83facfc70b127231f480cecefe4e9a3b651760bce5aa88d0，已核当前直接SHA与汇总字段。它排除了nested comments/strings，包含3521个显式声明；候选为2257普通def、5abbrev、5instance，共2267，已排除21个既有非计算定义与两个decoder。此inventory明确不是完整runtime call graph；本独审补的是SDK语义和自动生成边界，不再执行其分析脚本。

## 为什么18处没有切断全部工作

v7八个checker/walk、v8十个PTT定义的modifier只使这些入口跳过compile。v8原有显式noncomputable def总21条，另三条为FMaj、FMajC、quadForm；既有源盘点仍有2259个plain def。WL链就有136个numeral（135 packed）、88个中间selector、48个WL根selector、48个WD，共320个普通定义。仅改少数巨体或最终函数不会普遍跳过其余定义的IR处理。

`noncomputable section`本来并未统一skip codegen：Basic.lean134–140的shouldGenCodeFor要求“非theorem且无显式noncomputable”，section影响compileDecl的logErrors。18处新增标记保留literal、类型检查、透明定义body、72处decide+kernel及全部48个根；标记更多ordinary定义也仍保留这些工作，以及InfoTree、快照、内核表达式和序列化。不能由源码大小或标记数量推算峰值内存。

## 按声明种类区分

| 源命令 | 同pin SDK行为及边界 |
| --- | --- |
| def | Basic.lean186–191创建同一name/type/value/hints/safety的kernel defnDecl；217–223加noncomputable环境标记并跳过compile。不是改成axiom/opaque，也不关闭kernel reduction。 |
| abbrev | Basic.lean202–209仍创建defnDecl且hints为.abbrev；modifier可以抑制compile，但不能把abbrev改写成普通def或改变透明性。源有5个类型/接口别名，不能因不是`def`关键字就漏计。 |
| instance | Basic.lean211–212按实例type是否Prop选择thm或def。本文件5个Decidable实例是Type值字典，属def路径。Meta/Instances283–305、327–329注册Expr和instanceReducible；SynthInstance325–427以表达式应用/统一构造结果，并非注册即evalConst实例。显式noncomputable可保留类型类注册、字典body和Meta/kernel归约，不能把它换成Prop证明或移除实例。 |
| theorem/lemma | 本来不生成该声明的可执行代码；MutualDef96–99反而拒绝noncomputable theorem及noncomputable partial。不可无差别前缀化这些命令。 |
| structure/inductive/constructor/field | MutualInductive216–225拒绝noncomputable inductive和constructor；Structure321–322拒绝noncomputable字段。这些不属于普通def替换集合。 |
| macro及其生成函数 | 是实际elaborator runtime，必须保留可执行路径；不能因输出最后进入证明就视作proof-only。 |

Parser/Command100–121规定modifier顺序：doc/attributes、visibility、protected、meta或noncomputable、unsafe、partial或nonrec。实施时若把前缀放在private/protected之前，或重复既有noncomputable，会产生语法问题。该静审不提供批量改写器。MutualDef1095–1100把主定义的computeKind传给提升的let-rec，这说明部分辅助定义继承标记；不能据此推广为所有generated声明都消失。

PreDefinition/Main307–310的非递归分支对noncomputable走addNonRec，否则走addAndCompileNonRec，两者都传cleanupValue=true；不是借非计算标记绕过定义清理或kernel addDecl。保留source type/body与上述kernel声明路径提供数学语义保持的依据；不保证未来新源的所有elaborated私有辅助项或export字节完全相同。新源仍必须正常typecheck并通过原检查，不得借此删除48检查、换native oracle或放宽公理。

## 本文件真实runtime边界

源码120–125的zfNat64宏执行ZeroForgePackedNat.decode64，并调用private digit64；成功后toString→Syntax.mkNumLit，135个packed用法都依赖它。宏命令还生成parser/macro实现，不能把“三项闭包”误写成三个显式用户def。必须保留宏生成入口和两个decoder的完整执行依赖；其中Nat/String/Except等导入库实现保持原样。

SDK KeyedDeclsAttribute166在注册时evalConstCheck宏实现，Elab/Util158–165随后实际调用e.value(stx)。Environment2536–2539/2619–2626区分这种runtime求值与kernel声明访问。若digit64/decode64或真正运行的meta helper被错标非计算，ToLCNF440–452会拒绝可执行caller对其依赖，或宏注册/展开因没有可执行实现失败。section可能只不报告某些compile错误，不能让runtime调用凭空成功；失败也不会合法地产生一个放宽检查的新证明。

源级检查和formal_owner的完整词法盘点一致：当前没有本地elab/elab_rules、自定义tactic、run_cmd/run_tac/#eval、initializer、deriving、native_decide/+native、evalExpr/evalConst、extern/implemented_by/csimp；独立attribute命令只有原irreducible，13个simp属性全部位于theorem/lemma。普通simp定理匹配、norm_num对表达式构造证明、Decidable实例推导不能一概等同于执行被化简函数的native实现。

这一点仍有明确的机制边界：Mathlib NormNum/Core65–69会evalConstCheck一个注册的NormNumExt，SDK Simproc125–132会evalConst注册的Simproc/DSimproc。那些插件确实需要native/解释器实现；当前文件没有定义并注册这些本地插件，导入库插件也不是本次源级modifier的对象。若新增此类属性或任何动态eval，本次普通定义分类立即不再充分，必须补全runtime caller闭包。静态无特殊token不是对任意未来imported metaprogram动态行为的无限保证。

源13533的export Meshuggah(sincN phiC hat)只增加名字别名：BuiltinCommand298–310折叠addAlias，ResolveName56–75存alias extension；它不新建kernel def或再次compile，不是遗漏的三个本地可执行wrapper。

## 自动生成项并不等同于剩余源码def

结构投影很容易被误判：Meta/Structure109–123为非Prop字段生成透明abbrev defnDecl，但源码明确“special compiler support; no need to compile”；Prop字段通常生成thm。这不是一个需要机械加modifier的普通source def。

相反，类型和其他辅助生成有独立路径：MutualInductive1569–1573/1592–1595直接compileDecls类型并建立recOn/casesOn/ctorIdx/ctorElim/noConfusion/below/brecOn等；CtorIdx98、113明确compile辅助定义/alias。Structure还有flat ctor、默认字段、parent projection/instance等生成路径，既不会被对显式普通def加前缀自动覆盖，也不宜假定每一项都另有native编译。本文件没有deriving命令，14个structure与1个inductive仍需原elaboration、kernel规则及相应生成处理。

因此可审查的目标是减少“显式theorem-only普通定义的代码生成”，不是0 Lean进程、0 native runtime或0自动生成工作。真正runtime宏继续执行；导入的elaborator/tactic/runtime继续执行；结构/归纳处理继续执行。

## 静态采纳条件与停止点

可供root书面选择的条件性提案是：只对明确的普通def/abbrev/Type-valued instance集合添加合法modifier；保留宏生成实现、digit64/decode64及其runtime依赖，既有theorem/lemma、结构/归纳/字段、所有证明body、数据、公理检查与公开命题不动。全plain-def抑制有比18项更广的作用，但只证明减少了指定入口的可执行编译请求，不证明减少了主要内存来源。

本审查没有实施该集合、没有新source projection、没有compiler/smoke或原官网日志以外的资源测量；无法宣称2267项候选整体已可编译，也不能给出速度、RSS或通过概率。下一实现或compiler必须由root另行选择授权，本任务封存即停止，不开启InfoTree、新数值或优化家族。
