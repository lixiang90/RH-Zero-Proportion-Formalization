# 单一例外的相邻双窗：独立整数/几何核对

此包响应 root 在用户放宽验收幅度后给定的固定参数：δN=389500523，τN=c9N+779001046，分母10^20。没有优化、改变核/FS/精度、重新解叶、矩阵、LP或Lean。所读源固定f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf；依赖已经独审的完整StageB archives与源AST单一cN debit身份。

## 整数与几何结果

完整13046 numeric rows的唯一最小原margin为65385001396000000，root11/position27229/exception462。次小为261389376341096919346000000，root37/position84312，其除κ=335544320000000000的整数商为779001046。固定新debit为261389376259358720000000000；其余13045叶全部非负，最小剩余margin81738199346000000。仅e462不能支付新τ。

e462原闭cell被完整保存，来源/witness/state hash与numeric archive一致。prefix窗口原gap为g0..g7，suffix为g1..g8；反向后分别倒序。相同物理gap g1在prefix id/rev中是h1/h6，因此≤max(U1,U6)=34980/32768；在suffix id/rev中是h0/h7，因此≥min(L0,L7)=64168/32768。严格34980<64168排除全部四chart，含所有闭边界，甚至不必重新加入两窗各自的Ordered侧条件。

## 完整全域逻辑（仍待Lean实现）

原global c9对所有非负gap成立。对sep17/20域，若一个九窗F9<τ，新τ低于StageB旧raisedτ，故原已审160 COV/8tail外guard由单调性仍支付；595 reflection仍只用于Ordered半域排除。完整原树numeric除e462外均已支付τ，所以整个严格sublevel包含于E462及其反向。相邻两窗不能同时低于τ，因此至少一窗≥τ，另一窗≥c9，平均≥(τ+c9)/2=c9+δ。这里没有把reflection当能量证明，也没有把原ready cut的c9证明当新τ证明。

必须形式化原完整树的「τ-covered或落于e462」分类与所有cut/root端点合同，然后接反向、相邻四chart矛盾、prefix/suffix容量≤2、同sep17/20的原1/64短对付款，以及实际计数和dyadic/cumulative链。新c<1/64。整数archives是旧已审证据，不等于生成了新Lean证明项；完整单源2MB/3200秒、axioms、Comparator/nanoda及提交材料仍未通过。

## 精确严格改进

源比例公式必须扣已有压力B9：R=(window_H−B9)/(1−c9)，新候选使用相同分子除1−c。独立结果为

`3337839448633819172184136761695440236797 / 4955319193827760237900000000000000000000`。

它严格大于11:54UTC fresh API确认的当前R，显式交叉整数为65004510546645210152657416049195016947383767241550000000000000000000>0。精确有理差保存在receipt。增益来自相邻例外不能同时实现的结构；δ数值很小，不能称已完成无条件新纪录。

## 执行历史

首版audit_once.py在最终比例接线处错误使用H/(1−c9)，exit1/chunk67b4ce；全部archive/margin/四chart断言在该行前完成，但无成功receipt，失败源和terminal保留。root明确授权版本化修复，audit_once_v1.py只扣回原压力B9并加显式cross整数/修复元数据；因首版无durable中间缓存，重读同archives一次。v1真实exit0/chunk52ac6a，1.7402201秒。此额外metadata read不是新核/优化实验；两版δ、目标、源、geometry均相同，无其他case执行。

最终receipt SHA4ef9de005b872c920cba7ce45f392821b5179f52152cc6d0e78e1ff526f567ba；unique-exception SHA3904ff3b5b0e4867fdb9354c6b8232ede49cde102036f513a10467ac96f0327a。根方向/macro006由root管理，本包没有修改治理。
