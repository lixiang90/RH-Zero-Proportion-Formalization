# 唯一例外 Core 的确定性源转换准备

本目录的 generator 只转换固定 source 文本与已独审的唯一例外元数据；不导入叶parser，不遍历树，不计算FS、核、数值margin、矩阵或LP，不执行Lean。执行generator本身仍须root明确允许。原 source SHA f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf 与全部旧包保持不动。

输出目标为 `StructuralS1RTiny20261018/Core.lean`。继承当前完整source的实际核、W9、LB/PTT/WL/WD、数据与许可归属、所有泛用band/matching/OpethN.Counting定义。当前Counting准备文件直接进口该Core；不导入旧核，也不产生Core→Counting反向依赖。

固定改动：

1. 原concrete cN保持原值，添加tinyDeltaN=389500523、tinyTauN=cN+2*tinyDeltaN。
2. 用唯一例外JSON的完整73-field规范化St构造tinyExceptionState，原stEq/St_eq搬到它附近。定义TinyGoal为`Pg tinyTauN ∨ (InCell tinyExceptionCell ∧ Pg cN)`，Covered只绑定这一强化谓词。
3. mcheckP与mleafP显式接goalN，唯一cN main项改该参数，原其余整数表达式与guard不变。leafStep完整stEq选择tinyTarget，只解一遍原payload并作一次原main检查。
4. generic mleafP_target_ok给Pg goalN；薄mleafP_ok将其提升到TinyGoal。split使用通用谓词TinyGoal，reflection分支只加入外层Or，CutsOk/70ready/cursors的调用原文保留、一遍统一验证。
5. cert_of通过tiny_forget将各root TinyGoal遗忘到Pg cN，继续使用原root_cover，故原cert_AM命题由同一遍树保留。非sep区不冒称tau。

生成时保存完整Core.diff/source大小/hash，逐字核所有zfNat64数据、关键literal/流声明及原ready cursor行不变。没有使用sorry、admit、新axiom或native_decide；不以已有Pythonfloor代替Lean证明。新proof源码即使语法完整，也尚未经任何Lean检查，必须报告所有未检验项，不作PASS声明。

本Core暂不提供sep根外raised lift、实际单窗dichotomy、相邻双窗pair-floor及最终Counting实例；这些命题直接缺席，不用预设floor参数、axiom或stub填洞。旧结尾record定理仍只描述原基准，不能当tiny结果；最终flatten时应替换旧candidate wrapper并实际测量字节。

开发时可按root建议使用已编译CurrentPrefix缓存，但本准备选择单份源原位替换路径以避免双份concrete walk和payload。编译如何切块只由sole compiler后续决定；本任务不启动编译。网站2MB/3200s、普通Lean、公理、export/Nano、最终新鲜纪录严格比较均未通过本准备。

拟执行：

```
C:/Python314/python.exe -B -X utf8 research-goal-20261018-tiny-core-preparation/generate_core.py --generate-once
```

执行仅生成一次新Core和静态diff报告；禁止覆盖已存在Core或重写冻结输入。若转换anchor或固定元数据不匹配即失败保存，不静默换源或数学参数。
