# 开发用 Prefix/Core 切分审查补记

本补记只涉及开发模块边界，不更改被冻结完整 Core 或数学。
`prepare_split.py` 没有调用 compiler；输出在本包的 `development-split/`。

完整 Core 的第10613行 `-- SWAP BEGIN certificate:` 是切点。切点处 namespace
都已经闭合，但第6661行开启的匿名 section 仍活着。因此“所有 section 已闭合”
并不准确。清理嵌套 Lean 注释和字符串后，静态追踪所有顶层 namespace/section/
end，结果显示活跃匿名 scope 仅继承 `Elab.async=false` 与 `linter.all=false`。
这两个 option 不经 import 继承，开发 suffix 已显式恢复。

切点的活跃 scope 没有任何 `open`、`open scoped`、variable、local、notation
或 attribute 命令；没有假定 prefix 文件内的 open 能被 import 导出。
Matrix、Finset、RHLinalg、Filter、Topology、ComplexOrder、BigOperators 等
后续实际使用的 open 命令仍在未改动 suffix 内。Prefix 的声明、全局语法及
`zfNat64` 宏通过 import 保持原公有名称。

Prefix 里的5个 private 声明分别为 digit64、hasDerivAt_left'、
hasDerivAt_right'、err_scale、one_le_pi。suffix 的实际代码中，这5个名字
均出现0次；没有跨模块 private 名称引用。Prefix 自身导出声明的内部依赖
由 Prefix 的普通 Lean 编译承担，不用把 private 声明改成 public。

开发 Prefix 追加一行显式 end 关闭遗留匿名 section；开发 Core 只追加
`import StructuralW9A220261020.Prefix` 与上述两项 option，然后逐字保留 suffix。
删除所加 end/prologue 后合并两份文件，字节精确恢复完整 Core：
SHA256 `c5180e8cb9d219bec5cf29e4d65e0cfc304f4d40a12ad6d52332603e115fccd6`。
完整 Core 的当前 hash 也前后不变。

静态结论：该切分没有发现阻止保持公有数学接口的跨边界依赖，可以作为下一
冻结 ordinary gate 的开发输入。实际 import、宏加载与 elaboration 仍须普通
Lean 确认。最终网站源码应回到完整单源；开发 Prefix 的缓存或分模块编译不能
作为最终单文件冷检、Comparator 或 nanoda 的收据。

`split-audit.json` 记录所有准确路径、bytes、hash、添加命令和逆合并检查。
本补记不修改早先 `files.json`；新增材料由 `split-files.json` 单独封存。
