# J 独立完整审计器：仅准备

当前只写源码、AST 和文件/runtime 身份；不 import 审计器或数学模型，不执行 FS、rank/det/矩阵、图、点、核、LP 或 Lean。生产终包及 root 单独 audit gate 到达后才可唯一运行。

审计器不会导入 J producer、I producer 或新的 original_affine_core。唯一数学代码复用为自有已冻结 A `replay_independent.py`（其自身只载自有 packing decoder）。原 A trace 作为已独审、固定 SHA 的只读 cursor 历史，按每个原 B path 逐支核 raw WL tag、axis/mode、独立 cut、原状态/child/cursor；不重新搜索几何或遍历整树。

完整范围固定 H 原升序 15378 indices。四 chart 的155行由原 source spans 独立映射；Ordered 按 canonical first gap−last gap直接构造，反射不反向窗口顺序。selected basis 删 X0 后转置为 A=B^T。独立 Bareiss 核 determinant、Fraction 前消元核 rank；非奇异共享 S 必须为整数且 AS=|det|I，actual |det| in1..4。所有 source normal 保持原归一化。

若输入所用 chart 全部奇异：只核四 chart rank/奇异、所有 records tag3、原 H 全序及两流 EOF，不需要 FS 能量；producer cache 只钉 bytes，不声称其 affine 语义经核。

否则每个 needed cell 用自有 A parser point-free 重建原状态、原34项FS/guard、PT有效域、payload/semantic hashes、compact与printedAST margin、原 flow及 consumed bits；独立生成 Cstar/J8 和 term-component SHA，与 producer cache 逐字段比较后才使用。原 L/U/L0/anchor 不按joint域改变，没有物理点输入。

每条非奇异 record 独立反射嵌入得到 C/b，解码共享 S 重建 n=-S*b[1:]，逐全10坐标核 d*b+sum n*normal=0。负 n 是 tag0；n>=0 时精确 N=d*C−sum n*rhs，无论是否达到 target 都核 signed N/d：N>=dT为 tag1，否则tag2，不能丢弃或 clipping。JLB2 magic、原index逐序、canonical signedULEB、全部15378记录、classifications EOF及第二条remaining流全部逐字验证。

需要 root gate 字段：

```
full_J_classification_audits_authorized:1
expected_H_remaining:15378
prepared_manifest_sha256:<本目录prepared-files SHA>
resource_limits:{elapsed_seconds:300,closed_output_bytes:20000000}
new_search_optimizer_points_kernel_or_Lean_authorized:0
automatic_retry_allowed:false
producer_manifest:{path:"research-goal-20261018-stageJ-fixed-basis-preparation/files.json",sha256:...}
producer_result:{path:"research-goal-20261018-stageJ-fixed-basis-preparation/result.json",sha256:...}
producer_terminal:{path:"research-goal-20261018-stageJ-fixed-basis-preparation/terminal.json",sha256:...}
```

生产 manifest 用 root-relative path，并包含 basis、cache、cache-index、prefix、两条binary、result、terminal。此最小 validator 要求完整生产15378结果，不自动将partial升为complete。若生产partial需root另定审计范围，禁止自行重跑。

唯一未来执行命令：固定 Python3.14.5 `C:/Python314/python.exe -B -X utf8 .../audit_once.py --launch-authorized-once --gate <gate> --gate-sha256 <SHA>`。一 child，300秒/20MB，exclusive raw outputs，超限终止，无自动重试。完整整数审计也不构成新 global floor、规定公理/Lean/nanoda、源码预算或网站提交通过。
