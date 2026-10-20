# Core v1：唯一 Bool 化简报错的最小 proof-only 修复

本包只准备新版本，不运行 compiler、export、kernel、求解或数值重放。原 canonical
Core、开发切分v0、Prefix、失败命令/日志/收据与所有冻结数学数据保持原字节。
没有修改主轮计数。本包的 source-generation 成功不表示新Core已经编译通过。

主代理实际ordinary gate
`3960ea16d3ef7b2bf7d91453e95ec77aa143aee295ca655df0a45c01661d0533`
先通过 Prefix（436.328秒），随后Core在644.610秒后exit1。保全的唯一报错位于
开发Core第143行：qTargetFrom_sound 的false分支中，`simp only`把布尔测试
化为 `false = true`，但没有把这个命题继续化为False，故条件表达式未消去。
这不是任何finite checker返回false的证据；也不能反过来把无其它日志报错当成
完整数值有限检查或实际定理的PASS。

修复只在相同theorem、相同分支、相同proof行加入一个已有标准化简规则：

```lean
simpa only [qTargetFrom, hs, Bool.false_eq_true, ↓reduceIte] using h
```

当前固定SDK的 `Init/Data/Bool.lean` 第206行直接给出
`Bool.false_eq_true : (false = true) = False`；本包保留该源的准确hash与相关原文。
因此这是补充条件化简，不是新增数学命题、定义、前提或公理。没有修改lemma
statement、qTarget/qState/qCost、任何阈值、潜势、图边、payload、guard、cursor，
也没有删减root外、反射或闭边界分支。

## 版本与可逆投影

新完整source位于 `canonical-full/StructuralW9A220261020/Core.lean`：1770091字节，
SHA256 `c2af225175f9a5ab14d2ba2612714a21e0613f66107a1d75b9d47bf1c77ba02a`。
新开发source位于 `development-split/StructuralW9A220261020/Core.lean`：1185248字节，
SHA256 `26e23c7fc4fbae33bdfff446901eaeb0f22f0f08fe13fa4e326541565a25279f`。

两份source都比各自v0只多20字节，差异恰好是上述proof行的一处规则插入。正向
替换得到v1、反向替换逐字恢复v0；新开发suffix去掉原固定import/option prologue，
与原Prefix去掉开发用末尾end后合并，逐字等于新完整source。整个原Data namespace
仍逐字相等，包括48个rc、全部打包数字、根与游标。

原canonical Core SHA仍为
`c5180e8cb9d219bec5cf29e4d65e0cfc304f4d40a12ad6d52332603e115fccd6`；
原开发Core仍为
`b2f536448f48a50d3994cbccf7b3bd94ea54f388664d98e120c112130794ff1e`；
原Prefix仍为
`bfd774658f3f855596a5453f86f4d98fbc884ca651b3e595d68f70b9553f5b3c`。
本包没有复制或改变Prefix；后续ordinary gate若复用其既有olean，须由主代理
另pin原通过收据/当前artifact，并使用新排他job和准确新source root。没有自动重跑。

`repair.json`保存输入前后bytes/SHA、既有Prefix收据、失败证据与全部投影断言。
`failed-v0-evidence/`逐字保全原失败日志、命令、收据及终端状态。
两个 `.diff` 是独立完整source与开发source的准确版本差分。未来flatten应引用
本包的新完整source并另建draft-v1，不覆盖既有draft-v0。

## runtime闭包审查的简要交回

现有历史source-bound证据支持复用同SHA的Nano与Windows exporter：Nano
`b1980476…`独立于Lean SDK；exporter `bc718c9f…`的历史真实export exit0、固定
源码与当前构建trace指向同Windows Lean4.33rc2/d8b189 SDK。不应仅因日期或路径
变化强制重build；当前SDK/DLL与文件身份仍须完整绑定。

旧interpreted工具路径有一个确定缺口：Export/Parse.olean实际位于
`tmp/Comparator/.lake/packages/lean4export/.lake/build/lib/lean`，不在模板原列的
两个tool libs中。当前4个Comparator legacy oleans与该Parse olean的5项SHA均
精确等于旧 `verification/comparator-core-public-driver-check.json`；可采用准确
来源/SDK/file pins复用，或把9源小trusted native setup保留作完整overlay/提速备选。

Mathlib/Zeta23缓存仍需固定源内容、匹配ltar/trace与当前实际data hash来源的桥接，
不能把仅HEAD或ordinary PASS当成来源。这不要求从零重编整Mathlib。

PE证据的84个未解析项全部为可选OS delay import；5个exe的ordinary静态闭包为
42图像、无missing，尚不能代替实际动态加载审查。与冻结runner相同stdlib imports
的当前Python312 metadata进程实际加载 `_decimal.pyd` 与 `_hashlib.pyd`，原packet
没有pyd，需要补它们及实际DLL依赖。rsp中 `-lLake_shared` 只是链接输入，当前PE
图没有Lake import，不能仅据rsp声称Lake必须动态加载。主代理继续该闭包工作，
本包不填complete或执行授权，也不把任何metadata观察当证明工具运行成功。
