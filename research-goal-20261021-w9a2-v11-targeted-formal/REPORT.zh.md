# v11 作者侧定点 API/类型静审

结论：未发现所审新增证明的确定 arity、类型、声明顺序或循环依赖阻断。仅审实际新 helper、两条改写游标/覆盖链、98个 Graph 行命题和原全称定理的49个显式分支；不是独立完整字节投影审查，也不是 Lean/资源/独立内核通过。

输入新源为1,945,173 B / `a267dd84df81d59e308b220f3b8374fc4c0cc32bea6eaa35db04d846e2b07893`。root报告 producer `0e4376` metadata exit0、1.6049158秒；本审没有重跑 producer、AST、decoder、几何、数值模型、Lean或进程查询。

## 两条 walk 证明链

同源11266–11268的 `walkCut_ok lbS lbD ptS hR bits hc fuel` 返回 WalkOK；10771/10769依次展开为 `∀ pos, ∀ s, U … s ≠ 0 → Covered (toCl s)`。因此新增调用中的显式参数顺序 `… WD37 oldCutsOk 105 185 newState nonzero` 和 `… WD43 cutsOk_nil 101 23071 newState nonzero` 对应接口；`rw [newCursor]; decide` 的目标只是正数end≠0。没有以元数据hash替代游标等式。

* r37：`v11_r37_e` 检查原fuel105、pos185、end142950，使用旧 `v10_r37_cuts`；`v11_r37_c` 只依赖该等式与旧CutsOk。新列表 `(185,newState,142950)::oldcuts` 的CutsOk由11246的 `cutsOk_cons newCovered oldCutsOk`构造。旧 `v10_r37_parent` 的目标和 `rc37` 的列表/列表证明均同步改用新列表，仍是同一根Covered结论。旧Covered在新helper之前，新Covered在新列表之前，父和rc37在其后，没有新根反向支撑自身hint的循环。
* r43：`v11_r43_e` 先以空cuts检查fuel101、pos23071、end53837，取得新Covered和单hint列表。`v10_r43_e0` 现在明确检查 **带v11_r43_cuts** 的fuel107/pos169/end70606；`v10_r43_c0`同步消费 `v11_r43_cuts_ok`。此处没有声称原空cuts等式仍被证明；c0的Covered类型保持，原外层root43 hint/parent/rc43仍使用同一c0命题。

两个新state使用明确St构造器；St/列表元组和cutsOk访问的 `(Nat × (St × Nat))` 配套。`CutsOk`本身只有逐成员Covered前提，没有不相交前提；r37新祖先与旧hint重叠不导致证明循环。新的游标等式、实际全St匹配与余下归约仍需要真正kernel检查。136/154及110/139仅是源合同所记残余拓扑数，本审没有重算，也不视作内存上界。

## Graph 行证明与有限枚举

对实际源逐行作文字类型对照：两组各49个固定`u=(i:State)`、仍量化全部v的行命题，恰为对应原全称命题代入u；0…48完整，无遗漏good状态。每行都是普通 `theorem … := by decide`，没有abbrev或内联展开原大proof。原两个定理各保完整头/类型，proof为`intro u; fin_cases u`，后接49个按0…48对应行常量的显式bullet，没有trial/first。

实际State在16892为 `Fin 49`。同SDK Init/Data/Fin/Basic.lean:54–55及245–246将数值i解释为 `Fin.ofNat 49 i`，值为i%49；此处全部i<49，和枚举的对应Fin值相符，证明字段由proof irrelevance处理。Mathlib Data/Fintype/Basic.lean:36–44的Fin枚举来自 `List.finRange`；同SDK List/FinRange.lean:28、33–39按0及递增succ列出。Tactic/FinCases.lean:54–76从Fintype.elems完整性取得成员，再按头/尾顺序生成各case。故源中的固定0…48 bullet次序和该有限枚举接口相配。此为源码静态推理，未执行tactic或typechecker。

行引理是opaque theorem常量；原全称proof只组合行常量，不在证明文本里重复2401对闭合decide。是否减少实际峰值、总时长，及所有行proof能否过kernel，仍未知。Edge、cost、potential、strict Conflict和原类型的实质内容没有在这项审查中被放宽。

输入pins和本报告随清单冻结。完整v10→v11反投影/所有未编辑数据/公开三命题由唯一另派独立审查负责；本作者侧类型审不冒充第二份完整独审。原失败版本与收据保持失败，当前完整数学、双核、资源和官网目标仍未完成。
