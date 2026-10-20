# draft-v1 独立静态复核

结果为 `PASS_STATIC`。本目录的 audit.py 独立读取并重构单文件，没有 import 或执行交付生成器、验收 runner、Lean 源、编译器、导出器或内核。

核对 v0 的 15 项清单、v1 的 18 项清单、v1 外层 21 项清单及修复包 14 项清单。共 56 个实际输入的读取前后 SHA256 与长度一致。冻结 v0 canonical Core、旧扁平单源、其余四模块、完整 wrapper 与 trusted 文件保持原字节。

v1 单源 1,829,955 字节，SHA256 为 `8928832f3503d39ad6786ae26a394299779d3a53b7c590e7ca7df793ae7614f3`，距 2,000,000 字节上限余 170,045 字节。相对 v0 只有单源第 10763 行增加 `Bool.false_eq_true, ` 共 20 字节，正向替换与反向投影逐字相等。v1 的 Core 与独立修复包 full Core 完全相等。

从冻结五模块剔除 import 行，再按冻结 HEADER、外部 imports、模块边界注释及原 wrapper 独立重构，结果与实际 Solution.lean 全字节相等；import 移动清单及各段偏移完全一致。

三个公开定理 candidate_strict_improvement、candidate_critical_line_bound、candidate_critical_line_bound_cumulative 的类型文本分别与冻结 wrapper 逐字相同、与冻结官方 Challenge 在仅删除空白后相同。每个 theorem 在扁平源中仅有一处匹配。

本复核不证明普通编译、Comparator、默认内核或 NanoDa 已通过，不证明统一 3200 秒验收、实时纪录或官方接受。没有增加研究轮次或新的数学/数值族。
