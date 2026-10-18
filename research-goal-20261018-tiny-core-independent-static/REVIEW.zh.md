# tiny Core 转换脚本独立静审

所审 generate_core.py SHA75d9ea6aa8f3276fb9641ffa40cc5229e4cc55cce0006cc2e4456a10c8314ca0，依macro006。只读脚本、原snapshot相关定义和既有tiny独审metadata；没有执行生成器、叶解码、算术重放、核、LP、P或Lean。本包不替root开gate。

数据：source f82a4914…、unique-exception3904ff3b…都硬钉；root11/pos27229/end27674/id462及73state长度有断言。flat按L+A与U+B交错，再M=0，符合原St与PR顺序。stEq原定义包含所有73字段，St_eq原定理只依St/Nat，提前到toCl之后没有新的数学前提。它不是只比较8gap或一小段state。

阈值：原cN保持；tinyTau=cN+2δ。mcheckP唯一阈值项参数化goalN，其他guards、FS、flow与term变换不改。mleafP对应加入goalN，generic mleafP_target_ok只给Pg(goalN)；wrapper经完整stEq选择旧cN或tinyTau，再转入固定TinyGoal。原zeroForge_forceR_cov实际对任意Prop泛化，原farkas_cov对任意P'泛化，故两者没有暗中沿用旧Covered语义。

强化与忘却：TinyGoal=Pg(τ)或(InCell(E462)且Pg(c9))。全等例外分支用St_eq从原hg给E membership；其他分支Pgτ。reflection原g7<g0分支改成left/right，恰落Pgτ的朝向分支，不把它当能量。spH/cov_splitB使用统一TinyGoal，CovK/CutsOk/walk自然强化；70cut必须仍由新Covered重证。cert_of只把强化hrun逐点tiny_forget后送原root_cover，故恢复原全非负c9，未把sep压力外guard偷换到全非负域。

遍数/身份：原generic数值cursor语句、packed zfNat64、点表/REG/BS/TS/PR等在protected列表中要求文本相同；转换只有指定唯一anchor与局部block，源绝不覆盖。保留原cuts而改变其Covered目标并不意味着原c9 proof可直接沿用；所有48parent+70nested数值cursor在同一新walk下要重新通过。文本不变不是计算通过。该设计只给一个目标值的numeric检查，不另保留一遍旧全树检查。

未见脚本增加假设、sorry/admit/native_decide或axiom。静审无具体数学或身份反例；Python替换anchor/regex实际唯一性、最终diff和保护行校验仅在未来授权纯文本生成后才能确认。Lean API/类型与新cursor计算尚未执行。生成Core仍保留baseline最终record导出；最终单源必须替换固钉old候选wrapper，不能只追加新R导出。

待完成：分离域的根外付款→完整raised-or-E定位、四朝向反射/共享gap、c9与邻对floor实例、当前W9 summed counting、H−B比例、严格改善与dyadic/cumulative根；普通Lean/axioms/Comparator/nanoda、2MB/3200秒/GitHub/提交材料都仍是独立交付义务。
