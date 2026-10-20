# 现代/旧式 Zeta Lake trace 独立静审

本目录不改运行时 v4/v5、数学源或数据。`check.py` 是单独实现的纯 Python 只读算术检查，没有 import 运行时 helper，没有加载 SDK DLL，没有 SDK API、compiler、export 或 kernel 执行。

实际检查 exit 0。检查了全部 140 份当前已有 Zeta23 `.trace`，以及它们的 8821 个非 SDK 包依赖。唯一使用现代 `module` 头的 Zeta 模块是 `Zeta23.FromPNTPlus.EulerMaclaurin`。独立 parser 保留导入顺序、重复和 public/meta/all 标志，使用当前 `.hash` 字面值递归计算四种 transitive trace 及三种 artifact trace；全部 Zeta import 叶、isModule 叶和完整 inputs 树 depHash 相符。所有读取的源文件、sidecar 和 trace 均在结束时重新核 SHA256/bytes，未变。

Euler 的依赖叶为 `Mathlib.NumberTheory.AbelSummation transitive imports (public)` = `96f70e16101598b7`、`:importArts` = `baf83acae4c1bb2c`，完整 depHash 为 `5a11c1a174c9ac72`。

规则由当前官方 SDK 的 `Lake/Build/Module.lean` 逐式读取：普通/meta/all artifact 分别从 1723 顺序混合 `[olean]`、现代时 `[olean,ir.sig,ir]`、现代时 `[olean,olean.server,olean.private,ir.sig,ir]`；旧式三种均只有 olean。legacy trans 每个导入使用 child legacy/all-art；all trans 按 all/meta/public 导入标志选子类；meta trans 每个导入用 child meta/meta-art；public trans 仅计 isExported，且只按 isMeta 选 meta 或 public。public trans 分支确实不看 importAll。输入 import trace 在旧式时用 legacy/all-art，现代时按 all/meta/public 分支。每项导入依次 mix child trans、child artifact。

`ParseImportsFast` 的显式 legacy import 默认 exported=true，现代普通 import 默认 false；public 设置 true，meta/all 独立，每项后重置。隐式普通 Init 和 meta Init 的 Import 构造器 exported 均 false；SDK 模块没有 Lake package Module，不参与这组包 trace 混合。本检查只确认该行为，不把 SDK source/data 来源视为已验证。

对 v5 源码的只读检查确认 `header_info` 保留上述标志，原 `header` names 接口保持；`TraceHashGraph` 逐式实现这些公式。`visit` 的节点插入为依赖优先，实际 `outputs` 先由 `verify_outputs` 对数据字节求 SDK Lake hash、核 trace 和 sidecar，再存 `output_hashes` 给后续 graph 使用；不依赖本独审的未验证 literal 代替实际字节检查。现代 `zeta_trace` 保持固定包配置的完整 9 inputs，使用 true/false 各自 Bool hash。

本结果的边界：它检验现有 source-header 与 literal sidecar 的图算术和 trace 内部一致性；不检查数据字节的实际 Lake hash，不重新证明 Git source、官方 SDK archive 或 Mathlib ltar 来源，亦不构成生产单文件独核成功。该来源检查仍须 root 的实际 runtime assembler 完成。
