# 固定 O 单例：两种明确 Lean 数据文字的字节库存

范围严格限于已冻结 O 的 G-index `1322606`，原 cells `278/665`、朝向 `rev/id`。本包只读取该 O packet、其原 N2 单个压缩 member 和源文件的已知身份，进行文字序列化及字节计量；没有重新运行曲率、FS、矩阵、求解器、新点值或 Lean。没有读取或统计其余 N2 prefix 的支持模板。

## 格式一：完整有理文字

`LiteralOnePair.lean` 是固定 UTF-8 数据文字，精确 **15,950 bytes**。各段包括：

| 内容 | 字节 |
|---|---:|
| 注释、import、namespace、固定 pair/chart/target 与 `qr` | 393 |
| 全部 305 个 raw dual 有理权重 | 4,213 |
| 23 个原 CellA 的 REG selector、端点及精确 m | 2,100 |
| 49 个正锚行的原 row ID、物理跨度、原 q 和 CellA 映射 | 1,514 |
| gauge 0 以外的 9 个精确 p* 坐标 | 7,705 |
| namespace 结尾与段间换行 | 25 |

全部 49 个锚行的 μ 均在 305 元 `rawDual` 中，按原 row ID 引用，**没有缺失 μ**。固定 p* 的九个分子及分母均显式保存；第 0 个坐标为 packet 已保存的 gauge 0。此格式不需要 normalized support/base 来验证给定 raw μ 的非负、full52 balance 和 cost；这些信息不是显式 dual 证书的数学前提。

有理数全部保留已保存的精确分子/分母，不作舍入或编码选择。最大整数为 p* 字段的 424 decimal digits / 1406 bits；最大分母为 423 digits / 1403 bits。raw μ 最大整数为 29 digits / 96 bits，最大分母为 7 digits / 23 bits；m 的最大分子或分母为 30 digits / 99 bits。

文字包含数据，不包含下面列出的 generic proof/实际解析供料；没有编译，也没有证实其可直接作为提交文件。

## 格式二：仅保存确定性重建所需的 selector 合同

`SelectorOnePair.lean` 精确 **1,465 bytes**，保存 42 个 group base row ID、9 个 normalized unknown row ID、49 个 positive anchor row ID、23 个原 REG `(chain, ordinal)`，以及固定 pair/chart/target。9 是原记录的 rank 元数据，不是本包新计算的秩。

此格式**不保存任何 raw μ 数值，包括 49 个锚行 μ**，也不保存 23 个 m 数值或 p* 的九个数值及分母。其小体积有条件地依赖以下尚未实现为 Lean 的确定性重建合同：

1. 从同一原 source、两原 cell/state/FS 与原 row 顺序恢复 pooled 42 groups 和全部 raw rows。
2. 使用已存 base/unknown IDs，按原 `abs(delta S)` 归一化恢复固定支持的有理候选；原 rank 与非退化性必须检查，不能由 selector 数量假设。随后恢复 raw μ，并检查全部非负/full52 balance/cost。归一化系统的小行列式结论不表示原 raw μ 的分母至多 4。
3. 仅对 selector 指定的原 REG 单元执行同源 CellA 整数算术，复核 guards 和定量 m；重建全部原 hull、row→cell 关联和取最小值。不能通过重新选择单元、细分或新 anchor 修复失败。
4. 用已核 μ、m 和原 q 形成同一非负二次网络，固定每个连通分量的 gauge，求有理 p* 候选；检查 full10 stationarity 和 payment。p* 的大分母由此产生，**没有因 selector 文件省略分母就消失**。

任何重建步骤失败均应拒绝本候选；不能默默换支持、改变精度、增加曲率单元或重新求 LP。当前文件没有该重建器，没有其 Lean source/runtime 基准，也没有任何可运行单源交付的结论。

## 两种格式仍需的证明接口

共同未计入的接口如下：

- 原 source、ledger、两个原 cell 的可达性/FS/guards/provenance，以及 `rev/id` 物理映射；完整 155 条几何约束、pooled component 行、目标和 source actual w 的连接。
- 给定 raw μ 的非负、full52 balance/cost 的整数/有理 checker soundness。
- 23 个原 REG CellA 的有限算术与定量实际 `w2 >= 2*W2L/DZ^2` 薄桥；原 source 的非负结论不能单独替代该定量值。
- 原量化锚切线的强 Taylor 余项，保留原 L0、导数上下界付款和原 q；曲率覆盖须包含 `hull(q, I)`。49 行对应的 μ 已包含 source 质量，不可再乘外部 a 或旧 FS mass。
- 非负网络、full10 stationarity 和统一二次付款下界的 generic lemma，及 exact payment 对 `target - dualcost` 的比较。给定 p* 只需检查恒等式，不必信任求解算法。
- 仅 selector 格式额外需要上述 source decoder、固定 normalized-support 重建、原 CellA/min 和 Laplace 候选构造；全部输出仍须由普通 kernel 所接收的 checker/lemma 复核。

两个数据文字均未计入上述 generic source、import 基线、原 source 或 whole-job 运行成本。JSON/gzip 大小不是上传 Lean source 字节。**15,950 / 1,465 bytes 是本 pair 的指定数据格式测量，不是最终单源大小，也不是 source/runtime gate 已通过。**

当前只有这一条 pooled Below 的曲率付款实例。若后续主流程只在 pooled Below 时尝试曲率，Lower 分支无需每次求 Laplace；但 Below 比例与支持复用率未知，本包没有对剩余 13,003 个 case 作任何外推。此库存不增加任何全域零点比例证明。

## 复现和冻结

`serialize_inventory.py` 的固定格式执行过一次并保存两份 `.lean` 和 `inventory.json`。`freeze.py` 仅作 AST、字节、section totals、现有 hashes 和指定单 member 的身份核验，不重新执行 serializer 或数学计算。`files.json` 固定本包及只读输入身份；旧 O/N2/source 文件保持原样。
