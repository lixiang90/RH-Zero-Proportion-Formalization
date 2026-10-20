本次有限独审通过字节和元数据检查；没有发现这 25 处替换中的额外修改。未运行 Lean、项目解析器、打包解码、证书 walk、叶数学、独立内核或网络。源文件尚不能因此称为编译通过或官网接受。

唯一一次完整独立源码投影核对由本目录 audit_source.py 实际运行，工具 chunk e61775，exit_code=0，wall_time_seconds=1.0012433。该脚本只用 Python 标准库读取字节、JSON 和精确有理数，不导入或执行 producer、Lean 源或证书计算。13 个直接输入前后 bytes/SHA 均相同。

原件为 attempt-030 的固定下载源：1,798,336 B，SHA c2f3b3d0d1e2d0a3fab63320092b0ac10aace2d501376431bb08e487ae673ad7。新件 draft-v12 为 1,799,144 B，SHA a3b0ee880a647539e4bdb65a31e693de5b8e2e5ad085ec46ebbd031319a848cb，低于 2,000,000 B，余量 200,856 B。draft 两成员 manifest 7d1825014a602b4eaaaa4350061fe1edb10f0b99d06115645d8df0dcdc6006c6 已逐项核真。

独审从原件分别搜索三组确切 ASCII 字面量，独立获得 4 个 H 的 10^32 写法、16 个十进制分母写法、5 个最终比值；排序后的 25 个原始 UTF-8 offsets 与 projection.json 完全相同。以原件的未修改切片重新正向拼接恰等新件，再从实际新件按累计位移逆向恢复恰等原件。替换净增加 46 B；另有 762 B 的 Li Xiang/Codex 变更说明，总增加 808 B。原来和现在均无 CRLF。没有运行 producer 复现这份源码。

109 段原注释按顺序逐字保持，新说明是唯一新增注释；25 个修改区间均在这些原注释之外。因此原 Samuel Lavery、R. Arun Chandru、Zero Forge、Yuhang Shi 等来源说明、历史数值、许可文本以及源末尾完整 Apache 许可均按原字节保留。新说明明确归属 attempt-030/commit 94954faf2713ae9628d6fbca0ae24fe64370507c，并未声称本次已获验收。

数学修改范围如下，行号均是原件行号；具体逐项 offsets、行号、外层显式声明在 audit-result.json。

- 1951、1956、1979：AMW.floor_numeric、HWexpr_ge、HW_ge 的终端 H 下界改为 672123746878241714136624717231727/10^33。
- 16514–16642：defect_to_dyadic、actual_dyadic、actual_cumulative 中的同一 H 下界逐字传播。
- 16668–16682：Opeth.AMFinal 的 dyadic/cumulative 比值及两条 norm_num 比值恒等式更新。
- 16706：am_export_candidate_exact 的目标比值更新。

全部输入包 import、pi/sqrt(2)/2/cos/sin 原有界、窗口系数、c、B、表、编码和检查器字节未变。尤其从 namespace AMW.Cert.PC9WF 到 end AMW.Cert.PC9WFData 的 1,002,484 B 连续块在新件中逐字存在且没有任何替换，SHA 7aa634cc1d1753c74f9f3df603ab0b23ad73f9924725eacb23db41f21227235d。这里的结论是旧证书和证明文本保持，不是重新证明旧证书。

三个公开声明 candidate_strict_improvement、candidate_critical_line_bound、candidate_critical_line_bound_cumulative 的完整类型头保持原字节；它们继续使用可信导入的 currentRecordKappa、candidateKappa 和实际 Ncount/N0star。全部非上述字面量的证明文本保持原字节，包括公开 wrapper 的证明体。提交准备必须让可信 CandidateSpec 请求的新分数等于本文新 K，并以提交时真实 currentRecord 为准；本源码没有改写可信 spec。

独立 Fraction 元数据核对给出 H33-H32=7/10^33，同一 c/B 下 (H33-B)/(1-c) 恰为

10937570556368350644414459367124615168 / 16237684365380724838807895177884765625。

它比 attempt-030 的确切分数大

114688 / 16237684365380724838807895177884765625 > 0。

这不是新的叶数学或 H 下界证明。本次没有独立重算 floor_numeric 的有理 RHS；该新不等式和整条形式链仍由实际 Lean/双内核门承担。

已捕获的网站 primary 源支持这么小的精确改进进入比较逻辑。这里复用的是 source-normalization-review/source 的旧固定快照，不是对当前部署的新网络核实：

- challenge.ts:22–26、54–59 允许至多 200 位正整数字符串；222–228 的 compareRationals 用 BigInt 交叉相乘，没有 Number、epsilon 或最小改进阈值。
- direct-submission.ts:39–56 分别检查 UTF-8 2 MB、分数不超过一和相对 currentRecord.exactRational 严格变大；canonical server submission 保存输入的精确 score。
- github-promotion.ts:259–282 用 30 位小数生成展示，但 exactRational 保留 submission.score；313–330 在晋级时再次按精确比值检查当前纪录和 previousRecordId，故竞争中的新纪录仍可使提交失效。
- attestation.ts:51–62 分别检查 attestation 精确分数相等和展示字符串相等。没有要求旧新展示字符串不同。
- records.ts:18–22 取数组最后一个 kernel-verified，否则最后一个 published；此规则不把排序后最大值当作 current。

独立长除法得到两者共同的 30 位展示 0.673591770245738332299780842385，共同的 28 位百分比 67.3591770245738332299780842385；二者 binary64 也相等。按上述固定捕获实现，显示不变不妨碍精确严格比较。但这不保证当前部署未变、请求未被其他规则拒绝、形式验证通过或晋级成功。

同时完成 FloorProbe v2 的有限静审：7634 B/SHA 2750bae9e75c3b0c030057a90b92fb7cea0d84399112fbba701561d30dc5dbc8，三成员 manifest 已逐项核真。统一 CRLF/LF 后，cAMn、cAM、dAM、PAMhi 四定义等原件；floor_numeric 整条声明除 H32→H33 目标字面量外等原件；另两条 norm_num 目标分别是同 c/B 的新比值和新 K 严格大于 attempt-030。没有执行此 probe，没有把静审当作其实际 Lean 结果。

本次没有确定的字节范围阻断。下一证明门仍须真实检查新的 floor_numeric，以及新请求 spec 下的整文件/公开定理/独立内核和官网晋级；这些结果不在本静审中推定。主轮计数、Git、原件、草稿、producer 和旧证据均未修改。
