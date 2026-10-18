# Localization 源码准备接口（未编译）

本包没有运行Lean、leaf、FS、核、矩阵、求解器或P。canonical源码独立import已冻结Core；开发版只做import与namespace字符串映射，不循环import Counting。

## 文件与namespace

- `StructuralS1RTiny20261018/Localization.lean`：import `StructuralS1RTiny20261018.Core`，namespace `StructuralS1RTiny20261018.Localization`。
- `StructuralS1RTiny20261018/Dev/Localization.lean`：import `StructuralS1RTiny20261018.Dev.Core`，namespace `StructuralS1RTiny20261018.Dev.Localization`；所有PC9QB6M/Data/反转helper引用纯rename为PC9Tiny/Data。`RiemannFail.W9/Fw_W9/cert_AM`保持名字。
- Dev.Core由solecompiler代理独占，不由本脚本生成或修改；其正式冻结pin须在未来编译gate里另绑定。canonical Core、Counting与全部旧包保持冻结。

## 常量与实际结论

`sep=17/20`，`base=c9N/SA`，`delta=tinyDeltaN/SA`，`c=base+delta`，`tau=tinyTauN/SA`；其中tinyDeltaN=389500523，tinyTauN=c9N+2*tinyDeltaN来自Core，未重新选择阈值。

公开接口：

```
base_floor (g : Fin 8 → ℝ) (hg : ∀ r, 0 ≤ g r) :
  base ≤ Fw RiemannFail.W9 g

pair_floor (g : Fin 9 → ℝ) (hg : ∀ r, (17:ℝ)/20 ≤ g r) :
  2*c ≤ Fw RiemannFail.W9 (leftGaps g) +
        Fw RiemannFail.W9 (rightGaps g)
```

`leftGaps g r=g⟨r.val,...⟩`，`rightGaps g r=g⟨r.val+1,...⟩`，与Counting的定义相同；后续实例可用`simpa [各自leftGaps,各自rightGaps]`对接。pair_floor没有预设floor、采样、minimizer、模型Below或曲率前提。

## 证明链

1. `Fg_ge_full_pressure`和`Fg_ge_term_add_pressure`从原Fg定义及每个实际wfun平方非负导出。`pressure_rest_of_sep`显式保留tail所用gap之外的七项压力，不重复第r项。
2. `original_hS`、`original_hcov`使用原Data.cert中完全相同c9表达式/原proof源码。没有tau版coverChk或新WZ查询。当前Core匿名proof没有可直接命名的接口，准备稿重复相同proof；后续可版本化提取共享，当前不改冻结Core，也不从原全域floor反推这些guards。
3. `flagged_pressure_budget`与`tail_pressure_budget`只是源码中对固定八行的norm_num证明，当前没有执行。原flagged COV给term≥c9，另加全部sep压力；原tail给单gap压力≥c9，另加其余七gap压力；small≤1/2由sep直接矛盾。
4. `root_TinyGoal`其余badOf/choose idx/incell_root步骤逐原root_cover构造，完全使用原COV、SMAX、PR、48roots和新Core的Data.run强E；没有重划root或cut。
5. `ordered_exception`从低于tau和ordered剔除Pg tau及反射支路。`exception_or_reverse`用实际W9/G的反转恒等式给两朝向。
6. prefix第二gap≤34980/Q，suffix第一gap≥64168/Q，四朝向共同矛盾。由两窗各自旧base和平均反例推出各自<tau，导出actual pair_floor。

## 状态与后续门槛

所有proof体都已写出，没有sorry/admit/axiom/native_decide，也没有stub或先验floor代替缺口。但没有任何Lean parser/elaboration/kernel执行，API/有限norm_num/cursor/rootE依赖及全部proof仍待solecompiler实际验证。本包不宣称普通PASS、全域比例或最终source/runtime已过。

旧source、Core原baseline包装与当前可信CandidateSpec之间的已知规格差异不通过替换可信常数处理。开发版仅改import/namespace，最终应由新正确tiny spec及wrapper接Counting；本站2MB、3200秒、导出/Nano和严格新纪录比较另gate。
