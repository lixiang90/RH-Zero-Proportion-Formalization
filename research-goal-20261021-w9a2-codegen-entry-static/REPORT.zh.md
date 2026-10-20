# 固定 Lean 定义编译入口的有限主源审查

结论：对本次查到的**安全、普通定义 elaboration 路径**，显式 `noncomputable` 确实删除主声明的 `compileDecl` 调用，不删除其 kernel 定义。这个事实支持把没有 runtime consumer 的定义从 declaration compiler 工作集合中移除；它不证明“整个 proof-only module 无 native 工作”，也不给出减少多少秒、多少内存或官网能通过的保证。没有派生或修改候选源，没有运行 Lean、AST、编译器、export、kernel、版本探测、网络或进程 API。

SDK 根为 `C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/src/lean`。下述路径均相对该根。历史已冻结 fullchain-v2 gate 记录 SDK version `4.33.0-rc2`、commit `d8b18978322de05a8f3dba51ef03cf5461676c17`；本审只复用该来源范围，固定少数实际引用源码的当前 bytes/SHA，不重审 SDK archive、runtime 闭包或大 export。输入清单见 `input-pins.json`。

## 直接入口与保留的内核声明

`Lean/Elab/DeclModifiers.lean:120–138,207–219` 把显式修饰符记为 `computeKind=.noncomputable`。`Lean/Elab/PreDefinition/Main.lean:299–310` 对非递归 singleton preDef 明确分流：显式 noncomputable 调用 `addNonRec`，否则 `addAndCompileNonRec`。

`Lean/Elab/PreDefinition/Basic.lean:179–240` 给出可逐项核对的差异：两条路径都整理类型/值、建立 declaration、执行 `addDecl`；差别是传入的 compile Bool。另有 `shouldGenCodeFor`（134–135）排除 theorem 与显式 noncomputable。

| 源声明 | 该路径加入的 kernel declaration | 显式 noncomputable 对主编译调用的作用 |
|---|---|---|
| 普通安全 `def` | `defnDecl`，包含 type、value、regular reducibility hints、安全性 | 不调用主 `compileDecl` |
| `abbrev` | `defnDecl`，包含 type、value，hints 仍是 abbrev | 不调用主 `compileDecl`，不把 abbrev 变 opaque |
| 非 Prop 类型的 `instance` | `defnDecl`；实例/可约性处理仍存在 | 不调用主 `compileDecl` |
| Prop 类型的 `instance` | `thmDecl` | 本来就不能按其 Prop 值推算大量 runtime codegen；底层还过滤命题 |
| `theorem` | `thmDecl` | 已排除主 codegen；再加 noncomputable 被拒绝 |

声明构造见 Basic:186–214，noncomputable 标签与编译条件见 217–229。theorem 的冗余修饰符拒绝见 `Lean/Elab/MutualDef.lean:89–99`。`Lean/Compiler/NoncomputableAttr.lean:16–26` 是独立环境标签扩展；该标签不把定义改成 axiom。`Lean/AddDecl.lean:22–33,229–239` 说明正常 addDecl 的 kernel 检查与后续 addAndCompile 是不同入口；本结论不启用任何 skipKernelTC。

严格范围：当 elaborated preDef 的 type/value 相同时，上述代码保留这些表达式作为内核声明，并跳过对应主编译调用；不能仅凭改一个 token 推断整个环境字节相同。noncomputable 标签提前进入环境（MutualDef:1212–1217），attributes、tactics、deriving 可以观察环境，辅助声明及元数据仍需分别核对。它也不跳过 proof elaboration、termination checking 或 kernel type checking。

## noncomputable section 不是全模块禁止编译

`Basic.lean:137–140` 对 section 标志调整的是 `logErrors`。`Lean/CoreM.lean:730–765` 仍调用 compiler；如果失败，恢复编译状态、给相关声明加 noncomputable 标签，并按 logErrors 决定是否报错。因此不能用一个 `noncomputable section` 替代所有必要的显式声明修饰符，也不能把 section 内计算性定义计作已经删除编译工作。

`CoreM:767–768` 从 Declaration 提取编译名字；`Lean/Compiler/Old.lean:27–35` 对 defn/opaque/mutual definitions 提供名字，theorem 等返回空。`Lean/Compiler/LCNF/Main.lean:31–49,156–212` 还有命题、type former、macro-inline、matcher 等过滤，再经过 LCNF/IR。源码注释提到 type-class instance，但实现第44行仍是 TODO；不能仅凭“instance”身份断言它不编译。这也是 def 数量不等于实际 compiler 工作数量的直接证据。

这里的 compileDecl 指 Lean declaration compiler（LCNF/IR 等）入口，不等于已经调用系统 C compiler 或链接 exe。`Lean/Shell.lean:552–568` 在 frontend 成功后另按 `-c` 调用 emitC 并写 UTF8；删主声明 IR 工作不等于取消整个模块的 C emission。

## 辅助声明的边界

1. **where / let rec。** `MutualDef.lean:1065–1101,1135–1136` 将 lifted let-rec preDefs 带入统一处理，继承来自主 headers 的 computeKind；主 headers 有显式 noncomputable 时这些 lifted preDefs 也取 noncomputable。where 与 let-rec auxiliary 名字都纳入 pre-definition 阶段（1162–1165），where 展开入口见 398–416。这支持该既有 lowering 路径的继承，不能外推至任意 macro 自行创建的声明。尤其 1069–1076 明确把 theorem 内**非 proof** let-rec 转成 def；若外层 theorem 的 modifiers 是 regular，外层 theorem 无主 codegen 并不能保证这些局部数据辅助定义无 codegen。
2. **structural / well-founded recursion。** `PreDefinition/Structural/Main.lean:95–107,183–203` 保留 kernel helper、转换后的递归定义与证明处理；`PreDefinition/WF/Main.lean:70–89` 仍执行 mkFix、decreasing tactic、unfold/eqn 处理。两条路径调用 `Basic.addAndCompilePartialRec`，而 Basic:280–295 只有 `preDefs.all shouldGenCodeFor` 时才建立并编译 `_unsafe_rec` runtime 对应物。因此显式 noncomputable 能阻断这里的 runtime recursion 编译入口，但 termination 证明工作和 kernel auxiliaries 并未消失。本审不声称已穷尽 partial_fixpoint 等其他特殊递归实现。
3. **unsafe / partial。** `PreDefinition/Main.lean:312–320` 的 unsafe 分支直接走 `addAndCompileUnsafe`；Basic:255–275 对该分支直接调用 compiler。本报告的安全普通定义结论不可扩张成对任意 unsafe command 的禁编译定理。显式 `noncomputable partial` 在 MutualDef:98–99 被拒绝。
4. **match。** `Lean/Meta/Match/Match.lean:1087–1124` 自行建立 matcher kernel declaration，按 `bootstrap.genMatcherCode` 决定是否调用 compileDecl；这不是读取父 preDef 的 noncomputable Bool。LCNF/Main:41–43 又会过滤 matcher/matcher-like/casesOn-like。因此只能确认 matcher 声明构造与条件编译入口独立存在，不能把每个 match 算成一定生成 native code，或把它的全部开销算作显式 noncomputable 可删除。
5. **deriving。** `MutualDef.lean:1445–1465` 在定义后另调 processDefDeriving，未把父 header 的 isNoncomputable 实参传进去。`Lean/Elab/Deriving/Basic.lean:178,235–263` 区分 Prop 实例、明确 noncomputable/section 分支和 addAndCompile 分支；属性与 instance wrapping 仍可生成辅助声明。更直接的反例入口是 `Deriving/Inhabited.lean:115–138`：handler 给 auxFunName addDecl 后直接 compileDecls，section 只改变 logErrors。因此“所有顶层 def 都标记了”并不保证 deriving 的全部辅助函数不进入 compiler；还可能出现需要明确 noncomputable deriving 的依赖错误。
6. **attributes / 自定义 elaborator。** Basic:216、224–229 在跳过主编译时仍执行相应 attributes 与 realizations。AddDecl:233–239 的 addAndCompile 是可独立调用的入口。不能把父声明的词法修饰符当作覆盖整个 elaborator 的全局 native-code 禁令。

## 整个 proof-only module 的可得结论

若范围仅是已识别的安全普通声明，并已确认它们和可继承的递归/let-rec 族没有真正的运行消费者，显式 noncomputable 可以删除上述主 declaration compiler 调用及受 guard 控制的 `_unsafe_rec` 编译工作，同时保留对应 kernel 表达式。对本来就在 Prop/type-former/matcher 等过滤分支的声明，新增修饰符可能几乎不删除后端工作。

decoder macro、macro/elaborator 的实现函数、它们实际调用的 helper / instance / registration 及运行依赖必须保留可执行闭包；仅保留表面宏名字不够。把其依赖标为 noncomputable 可能破坏后续 elaboration，而不是安全地获得同样证明。本审没有枚举或证明当前候选的完整 runtime 闭包，也没有批准一次全模块替换。

不能保证：模块零 native code、零 IR、零辅助声明、kernel 环境逐字节完全相同、源码变小、某个源字节数/defcount 对应固定时间或内存收益、下降后的峰值低于 8GB、总时长低于 3200s，或修复已观察的 Lean137。imports/mmap、parser 与 syntax、info trees、proof terms、kernel checking、olean/ilean serialization、实际宏执行及余下 emitC 仍可能消耗资源；本审没有 profiling 或阶段归因。若以后采用该方向，必须先让固定修改范围与 runtime 闭包边界可审，再由 root 另设门；本审不实施提案、不追加执行或新数值家族，counter1/review13 不变。
