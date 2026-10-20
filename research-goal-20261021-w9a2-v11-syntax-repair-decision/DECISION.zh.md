# v11 准备器解析失败后的单处语法修复

原冻结准备器24978B/SHAf78375a32387ba5b6d5372c40f424d740483c374a051a62e2c35355fd21b8fb7的一次执行已停止。Root原工具584896实际outer1、wall0.4730801秒：Python在234行拒绝包含⟨⟩的rb字节串，报`SyntaxError: bytes can only contain ASCII literal characters`。这是源码准备器的语法错误；静审漏检，不是Lean、几何或数学失败。解析在模块执行之前失败，未运行旧模块验证或准备算法，不能声称已有v11。

原准备目录、脚本、预执行清单和静审保持冻结；失败另包封存。Root明确选择一项常规实现修复，不原样重试失败关：新目录research-goal-20261021-w9a2-targeted-proof-preparation-repair-v1使用同一文件名prepare_targeted_v11.py，只将该非ASCII rb字面量改为Unicode r字面量再`.encode("utf-8")`。反向还原必须逐字等于f78375原件。ROOT/DEST算法、唯一minimax规则、全部数据/数值/证明方案、30秒/2MB/2MB/4MB、fresh/xb及失败停止条件均不变。不得借机扩展家族或改预算。

新代码先静审，并仅对这个新脚本做一次ast.parse语法检查；不import或执行其模块，不检查旧Lean证明。随后Root须另行明确授权新脚本的一次源码/几何准备，要求原outer0和实际总wall≤30秒。当前文件只授权修复代码准备与解析静审，不授权Lean、export、额外内核或官网提交。任何新的解析/生成失败继续封存、停止，不自动补丁或重试。

本修复属于宏观014后第1轮内的实现错误处理，counter1/review14保持；不作新研究轮或宏观回顾重置。完整无条件实际函数证明、双核、2MB、官网3200秒及promotion/Git目标仍active。
