# 平铺 Counting 的独立只读复核

实际失败输入是 fullchain-v1 新生成的 `Solution/Candidate.lean`，1,830,001 bytes，SHA `650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13`。原 ordinary log SHA `e02e5ca0b3fa36045f28831eb7553cdd61e829345af9100d330771880f4f2224`，原父会话 68653 实际 exit1，不是 timeout。本复核没有运行 Lean、内核或新优化。

三处裸 `wfun`（平铺行 16765、16785、16812）应明确为 `Zeta23Ext.Bridge.wfun`。`Fw`、`Fw_windowGaps`、`window_pairs_le_band` 都在 BridgeW 内打开 Bridge 后定义，`OpethN.band_close_n` 的输出也是该 Bridge kernel。Cert 版本同样表示归一化余弦核的平方，并与 Bridge 版本定义相等：Core 已有 `RiemannFail.cert_wfun_eq : AMW.Cert.wfun x = wfun x := rfl`。定义相等不会消除裸标识符的名称歧义。

污染入口是 Graph 段行 16104 的 `open AMW.Cert ...`：该段的 `noncomputable section` 没有在平铺模块边界结束，继续覆盖后续 Counting。Localization 的 `end` 只关闭自己的 section。依据固定 SDK 的 namespace 多分量 scope/section/end 规则，对整份源文本追踪得到零 scope 匹配错误；在 Counting 内，源中已声明的有效 open namespace 常量短名冲突只找到上述三处 `wfun`。此清单不等同于完整 Lean 名称解析，也不覆盖所有导入库中的重载。

行 16842 的 linarith 是同源下游。真实 log 中，`he` 的 band sum 已含错误恢复产生的 `sorry` 项，`hb` 仍使用 Bridge.wfun，因此没有同一个能量和式可消去。令修复后的共同和式为 Q、压力为 P、平方和为 D、defect 为 F、A=4kδm、BR=W.B·R，四个已有不等式的差式相加为：

```text
(Q+P-cm+ck+C) + (D+A-Q) + (BR-P) + (F-D)
= F+A+BR-cm+ck+C ≥ 0.
```

它正是所需 remainder bound；纯整系数字典核对通过，没有发现独立算术缺口。

独立核对 formal_owner 的 Counting-repair-v1：新源 21,606 bytes，SHA `502aa125cfe2566cdbddc3ede296f17dc58ad63a4a750cb6502b24a237b9050a`，恰好添加三个 `Zeta23Ext.Bridge.` 前缀、增加 51 bytes；删除这三个前缀后逐字节恢复原 Counting。没有修改 linarith、付款、状态图、阈值或公理要求。本轮无需扩大到改 Graph 或 flattener。

这份报告确认最小修复的含义与已观察失败的同源关系；它不声称新平铺源已经通过。仍须新的完整 flat ordinary、准确公理审计、独立内核与生产预算门。
