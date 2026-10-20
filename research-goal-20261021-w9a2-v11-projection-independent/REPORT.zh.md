# v11 完整源码及定点元数据独审

PASS_STATIC。新源1945173B/SHAa267dd84df81d59e308b220f3b8374fc4c0cc32bea6eaa35db04d846e2b07893，较v10增加30350B，距2MB余54827B。六个替换span全部独立重建模板，完整forward reconstruction逐字等新源，完整逆投影逐字等1914823B/86e3旧v10。范围外所有raw保留，包括数学fraction/K、135个packed bitlength+payload、221CRLF、单末LF、许可/归属、其他数据/proof及三个公开根。

实际元数据身份及完整prepared小manifest成员bytes/SHA核同（producer侧7项、draft侧2项）；完整pin列input-pins.json。Root报告唯一修复producer原0e4376实际outer0、工具总wall1.6049158秒，execution记准备elapsed0.656秒；该真实终态来自root观察，不由本报告重新执行或凭自称字段推导。原f783语法失败及旧报告保持原范围，未改成PASS。

本独审允许的archive拓扑检查仅读固定1999185a…gzip：24504条framing，保留37/43共1992事件。逐branch核left=pos+8、left.end=right、right.end=parent.end，按叶kind累计numeric；不重新构造geometry，不解WL，不算energy/tangent/margin。独立枚举proper descendants、跳过r37旧cut内部及自身、拒部分交叠、只扣完整包含的旧cut；604个r37候选和498个r43候选的全部score/contained列表与packet逐项一致。按min(score,pos)重选结果如下：

|目标|选pos|end|depth/fuel|块内剩余|外部剩余|
|---|---:|---:|---|---:|---:|
|r37 root1，总290|185|142950|23/105|136|154|
|r43 pos169，总249|23071|53837|27/101|110|139|

两侧均严格减小，tie取最早pos。新hint与原target四份数组恰73Nat/M0，字段序逐项等实际St；独立紧凑ASCII JSON+LF SHA与原archive对应事件及packet同时相等。r43原v10_r43_s0 literal同时等target数组。此为hint原字节/归档hash身份核验，不是实际Lean St-equality或几何证明PASS。

两个walk helper模板逐字重建并核同实际源。r37新cursor以原v10_r37_cuts/CutsOk运行，其Covered不依赖新父；newhint::oldcuts经cutsOk_cons，原父及rc37共同使用新cuts/新CutsOk。r43新子cursor为空cuts；原v10_r43_e0明确成为v11_r43_cuts的cut-aware107/169等式，c0以相同CutsOk得原Covered(toCl v10_r43_s0)。其旧raw空cuts等式没有被冒称保留；外层43的原cuts/父/root raw不动。无旧rc37/rc43/run结论捷径或Covered循环。

两个Graph block独立依据原完整proposition重建：各固定u=0..48、仍∀v的49个ordinary-decide row，加原header/type及49个显式fin_cases分支。98row/98bullet及全部实际字符串逐字核同。原edge_potential/exclusion_checked全类型、原rc37/rc43及c0 Covered类型保持；Edge/good、qCell、所有orientation、strict Conflict、图势表及数值不动。最终实际函数dyadic/cumulative与K在未编辑尾部，保持原无条件命题范围。

审计实现的一次小修正已保存在selection-check.json：首版PowerShell stack tuple把+1当数组附项，导致fuel核对停止；改用命名pos/depth字段后仅重读同一固定拓扑并完成。没有修改或重跑producer、proof或数值模型。

0 producer/Python import/AST、Lean/compiler/kernel/export、数值或源改写、process/Git/network动作。新状态匹配、两组cursor、Graph98行及整个新单文件仍须实际Lean/资源关；本静审不承诺内存下降、独立双核或官网PASS。封存后停止。
