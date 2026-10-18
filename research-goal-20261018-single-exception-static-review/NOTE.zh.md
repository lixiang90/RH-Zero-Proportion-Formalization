# 唯一例外 + 相邻两窗不相容：独立静态逻辑审查

本包只读同一新纪录 source 与已封存 Stage B 的合同/源码，审查 root 提出的新逻辑。没有重分类13046叶、解压叶表、重新算margin、FS、核、矩阵、求解器、曲率或Lean；P保持冻结、未执行。下面给出的唯一最小叶、次小余量和cell坐标来自root本次只读发现，**本包不把它们称为已经独立重放的新阈值分类**。

## 1. 需要证明的完整单窗命题

记原floor为 c9，原main缩放κ=335544320000000000。root提出 δN=389500523，δ=δN/10^20，c=c9+δ，τ=c9+2δ。使用相同核、权重、sep=17/20、原树/FS/flow/guards。

root报告全部原13046个numeric leaf中的唯一最小项是root11、pos27229、原B exception462，原M0=65385001396000000；次小root37、pos84312，M0=261389376341096919346000000，其除κ的整数floor为779001046。若完整原叶证据对ΔN=779001046的扣款再次获证，则除462之外每叶满足M0−κΔN≥0。等号也支付τ；不能将等号误分为例外。

目标单窗命题必须针对任意实数gap h_r≥17/20：

> F9(h)<τ ⇒ h∈C462 或 reverse(h)∈C462。

保留ordered半域时先得`h0≤h7`下的唯一C462，再由本核实际反转恒等式推广；h0=h7可选id。此处C462可以松为原完整closed cell，甚至只用下面四个adjacent bounds；放松只扩大例外集。它不是minimizer/KKT/Newton区域，不能改用以前仅保留极小点的覆盖。

Stage B 已完整处理48 roots、70 nested cuts、13046 numeric、595 reflection和根外区域，并由独立实现复核。该B使用更大的ΔN=300000000000000；其**根外**付款可按阈值单调性复用到新τ，不需新WZ。其旧numeric分类不能直接当新分类已通过，仍需所有原M0的固定新扣款证据及唯一状态身份。

## 2. 四朝向无需pair搜索

root给出C462的相邻闭bounds（单位Q=32768）：

    L=[64168,33989,64287,34192,64031,65043,33724,64461]
    U=[65648,34980,65278,35097,65033,66904,34464,67523].

十点的九个物理gap记h0..h8。prefix八gap是h0..h7，suffix是h1..h8，故prefix的第二gap与suffix的第一gap都是物理h1。

- prefix为id朝向时，h1≤U1/Q=34980/Q；为rev时，h1≤U6/Q=34464/Q。因此两种都给h1≤34980/Q。
- suffix为id时，h1≥L0/Q=64168/Q；为rev时，h1≥L7/Q=64461/Q。因此两种都给h1≥64168/Q。

由于34980<64168，id/id、id/rev、rev/id、rev/rev四种组合均矛盾。使用原闭端点，没有接触/严格性缝隙；不必再加Ordered或PR相关性，也不必做DBM、LP、FS或核评价。

原cert_AM的命题给每个非负八gap的F9≥c9。若`(Fprefix+Fsuffix)/2<c`，用另一窗≥c9分别推出两窗均<2c−c9=τ；由完整单窗命题两窗都必须落入C462的某朝向，与上面共享gap矛盾。因此条件性地得分离十点平均floor≥c9+δ。最终单份新source如何只检查一遍树而同时保留原cert_AM命题，见下节。

必须用严格平均反例`<c`推导严格单窗`<τ`，最终结论为`≥c`。这不是对任何单窗floor提高到τ，也不声称C462中有实际低能点。

## 3. 原Lean walk的最小推广路径

本次只审查路径，没有写或运行新Lean。原source SHA固定f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。

- `mtermTI`（10603起）与generic `mcheckGX_sound`（10170起）已经允许自由cN，是同原FS/flow给raised numerical bound的正确底层接口。原printed `mcheckP`（10988附近）及其专用proof绑定原cN；需参数化同一main表达式或等价薄consumer，不能只改最终结论。
- `Covered`（10659附近）是`CovBy 8 PR (Pg cN 8 BS TS)`。`CovK`/`WalkOK`（10667/10669）、`mleafP_ok`（11067）、`leafStep_ok`（11087）、`walkC_ok`/`walk_ok`（11116/11123）皆经过该固定语义。
- 优先采用root提出的强化目标`E(g) := Pg τ ... g ∨ (InCell C462 g ∧ Pg c9 ... g)`，将最终单份新source的concrete Covered改为`CovBy 8 PR E`。这比仅附加`InCell C462`强，能从同一遍树恢复原c9，不必再保留一次旧整树证明。
- 令`targetN(s) := if stEq s C462 then c9N else tauN`。`mcheckP/mleafP`只推广显式target参数，**每叶只解一次原payload并进行一次该target的原整数检查**。generic soundness给`Pg targetN`；stEq为false则得到Pg τ，为true则由完整St_eq/原InCell得到`InCell C462 ∧ Pg c9`。完整state匹配是语义关键，不能仅凭root内一个数字position接受任意state。返回cursor仍是同解码器的真实end，不能凭exception接入任意end。这里不要求对每叶先跑c9再跑τ两个checker。
- 反射分支保持原`u7<l0 ⇒ g7<g0`，只排除ordered半域，不支付τ。其源码证明就在11087后的分支。Farkas/空cell若通用，则只能按原严格矛盾证明排除；本源实际A/B为0个Farkas。
- 原split/tm的几何覆盖可推广到任意目标谓词；新proof需把这些结构步骤的语义泛化，保持原integer cursor/split/normalization不变。只复用旧`Covered(c9)`结论不够。
- `CutsOk`（11150）、`cutAt_ok`、`walkCut_ok`、`covered_of_walkCutR`（至11185）依赖同Covered；70个ready cut以及`ready_cover_cursor`（12432起）统一对强化E重证一次、沿原相同函数/cursors。只有包含C462的原子树可把exception一路上传；不能把旧ready cut原floor当raised成功跳过。旧state/start/end/fuel可作为完全相同的有限计算输入，尚须新kernel确认新的consumer。
- 原`root_cover`（9477起）硬编码目标Pg(cN)，但本方案可**保留其c9版本**：由τ≥c9，把每个root的E结论单调遗忘为Pg c9，再送入原root_cover；由此在最终新source中恢复全非负的原`RiemannFail.cert_AM`（14584）命题，而不另跑原c9整树。
- 另外只需一个sep版root外lemma：按已封存B付款证明“根外Pg τ或进入原48root”，结合root E得到分离dichotomy。不能把sep*B付款用于任意非负域，所以不应要求新root_cover在非sep域也证明E或τ；这正是原c9根外路线和新sep根外路线应区别之处。

最小可实施路径是：在新的交付source拷贝中原地推广一套concrete Covered、target参数和soundness，原大payload仅保留一份，70cuts仅证E一遍，分出“遗忘E得到全域c9”与“sep root外得到dichotomy”两条薄结论。冻结原source不改；不建议append第二套完整walk/ready证明后保留旧全树再算一次。此路径不需要N/P的多例外curvature模型。不过目标参数化时仍须核所有printed main常数/guards身份及branch end，新的kernel/runtime工作、consumer/70cut proof/cursor源码和最终合并大小均未量化；不能以只有1个例外就宣布2MB或3200秒gate已过。

## 4. 硬停止条件与最终边界

后续单次新阈值证据若发现第二exception、原462state/路径或任一cursor/guard不一致、根外付款不能单调复用、反转恒等式/四朝向嵌入不符，应停止该固定候选，不自动换δ或重划树。本包没有执行这些后续检查。

即使分离十点平均floor成立，仍须本核W10 prefix/suffix平均ledger的容量/pressure/H/B身份、实际close-pair付款满足新c、matching/band计数与最终严格超过最新纪录的精确算术；原c9短pair结论不能无条件当成c9+δ。原核在|t|≤17/20的1/64结论可作潜在供料，但具体新实例/计数桥仍需证明。

本包给出有效的条件性数学路径和源码接口审查；不宣称新增floor已在Lean核验、无条件比例提高或提交材料完成。P和此前所有证据保持原样。
