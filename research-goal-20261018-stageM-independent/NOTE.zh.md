# M 组件包络独审准备：没有数学执行

此目录不导入 M/I/J 生产代码，仅在未来独审 gate 后导入已冻结原 A 独审
`replay_independent.py`（c3f46e2c...62af9）及其独立 packing decoder。
准备阶段只进行 source、AST 和文件哈希，不提取 FS、构造模型/矩阵、
评价点或执行 LP/核/Lean。M 终包已存在但不构成独审执行授权。

审计会从 source/B 原 state、root/path/cursor 重建两份原 FS（0/604，
id/rev），核全部68项活跃 anchor、原 mokI/量化区间、1024质量、
L/U/L0、原 semantic/packed SHA、原 margin 的打印 AST。只沿两原 path，
原 A/B 全树及 nested contracts 作为已冻结完整独审前提。

随后自己构造155几何行、每项常数 lb 行及原正质量的独立 anchor 行，
不按 joint 收紧域改 L0/FS。独立计算 signed dlo/dhi 与 E/S，核正跨度、
反射、原混合恒等、pressure、77列目标、原 raw/scaling 模型，不相信
producer 的 component 数值或矩阵。constant 总保留，即使原 constant
质量为0；零质量 anchor 不衍生新 tangent。

原 quantized component 到 actual w 的作用域仍是原 source 的 LBSound、
TVal/mokI/ivIn 及 actual reversal。新 component 薄 Lean consumer 尚未
完成；独立整数回放不替代它，也不提供全域 covering/counting。

对已保存 exact dual 只核原全部行的 μ>=0、完整78坐标 balance=0、
cost=−Σμrhs。对已保存 exact primal 只核全部77原坐标、所有行及目标，
不运行 RREF、换 support 或调整任何有理数。合法 dual 单独足以接受
局部 Lower，不要求 native/primal成功；合法 Below 只否定固定 lower
模型，不是 actual F 低点。两者若矛盾硬失败。两者合法且目标相等时
独立报告精确 equality，不信任 solver status/浮点 residual。

所有 discovery 外部 runtime 文件只读核哈希，不 import NumPy/SciPy。
本次审计不启动任何 solver、点选择、核值、FS支持或 Lean。

后续 gate 字段：independent_component_audits_authorized=1、
audit_script_path/sha256、producer_manifest_path/sha256。

```text
C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageM-independent/audit_certificate.py --audit-authorized-fixed-M --gate <root独审gate> --gate-sha256 <SHA>
```

当前数学执行数0。失败后原样保留，不自动修复重跑；任何局部 Lower 都
不等于新无条件零点比例、全域正式证明或网站源码/运行预算通过。
