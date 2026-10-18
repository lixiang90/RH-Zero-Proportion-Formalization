# 固定九边升级环独审准备

仅 source/AST 准备，不执行数学。显式继承已冻结 K 环及完整 J 独审，
自己解码原 JLB2 全15378条序号/canonical signed ULEB/EOF，只取原固定
九indices。独立核有向标签映射、对应chart分母d、24倍旧Mi权与
(12/d)*(N-d*T) 的 max，再核原环闭合及精确sum，与L结果比较。
不import producer，不重解FS/矩阵/图/核/点，不换环、basis或其他dual。

负值只排除本固定 J 增强 outer-potential 模型；不排除 mixed affine 的
其他有效 dual/basis，不否定实际 F，也不是物理多窗反例。

未来唯一 root gate 需要 independent_fixed_cycle_audits_authorized=1、
audit_script_path/sha256。CLI：

```text
C:/Python314/python.exe -B -X utf8 research-goal-20261018-upgraded-cycle-independent/audit_cycle.py --audit-authorized-fixed-cycle --gate <root独审gate> --gate-sha256 <SHA>
```
