# 保存官网纪录快照的独立离线核对

结论：固定K已低于此快照按捕获规则选出的当前纪录attempt-030。原67f143 outer1是严格比较门失败，不能翻为read-gate PASS；HTTP200/body完整与比较失败可同时成立。本审查自身仅离线metadata/大整数算术，原始四文件未改。

raw API 98637B/SHA cf42027c…d0c6中的base64解码，逐字等保存records.decoded.json的70978B/SHA8f5cf6e7…5582；以Git blob格式`blob 70978\0`+bytes独立算SHA1，恰为API及receipt的69894c773516bc52f579e867e87fdaf0c4bcce76。四输入当前hash及保存selection源码pin列input-pins.json。根实际HTTP200及Date Tue,20 Oct2026 18:48:59 GMT来自root收据；本审查没有重新请求或独立证明HTTPS来源/当前时刻的新鲜性。

保存的records.ts（997B，captured commit1135c038…）选择critical-line原数组最后一条kernel-verified，若无则最后published，不按日期/decimal排序。41条均critical-line，38条kernel-verified，37条有正exactRational。最后一条是零起index40的attempt-030；它同时是37份可用精确分数的唯一最大值。index3 anthropic-2026-montgomery-taylor缺exact，保持未知；不能借scoreDecimal推断它的精确比例或声称完整比较全部38条。缺失历史分数不影响已知attempt030高于K这一反例。

完整原row（原JSON对象字节加末LF）已抽取到attempt-030.raw.json，不是字段摘要。行内author Samuel Lavery/GitHub samlavery，date2026-10-20，status kernel-verified、formalVerification=true；model Claude、harness Claude Code。source/proof URL固定commit94954faf2713ae9628d6fbca0ae24fe64370507c/submissions/attempt-030。method及summary叙述W9A2、variance/range-end anchors、16-unit tangent grid、11857 leaves等；这里只转录ledger metadata，没有读该proof、attestation或验证该技术描述，更未重放任何内核。

精确值为

```
R = 2187514111273670128882891873424900096
    / 3247536873076144967761579035576953125
K = 3337881639516708570682858853672166187793
    / 4955348542279967171490000000000000000000
R - K = 2970169526532495010853639899142418514073460025200614154938056939
        / 41197253401595693398125017906128453929107597815394730000000000000000000
      > 0
```

用Fraction精确约分/比较，不使用decimal排名；展示值R≈0.673591770245738332299780842385，K≈0.673591698149438669336049831808，差约7.2096299662963731×10⁻⁸（0.0000072096299662963731个百分点）。37个可用exact中只有attempt030严格高于K。

主路线的数学含义仅限此已知分数门：固定K的proof-only资源优化即使成功，也不能使K严格高于该R；不得只修改提交metadata分子分母或将旧proof改称更强定理。原无条件实际函数/完整证明/双核/源码/官网目标仍在，但“固定K→晋级当前纪录”已被此快照否决，应由root书面回顾目标及下一proof-producing gate。没有授权或启动任何新数值/优化/核/参数族；不能自动把新record摘要中的改进与本势函数组合成新比例。未来任何提交仍须再鲜核当前R及完整验收。

实际本独立审计工具ac2e8a exit0、0.5038501秒，只有保存JSON/base64/Git hash/Fraction/Decimal显示及原row提取。0网络、候选或对手Lean源/proof读取或重放、compiler/solver/optimizer、state/Git修改；只写此新小证据目录。此audit成功不是官网proof、attestation或record接受的新验证。封存即停止。
