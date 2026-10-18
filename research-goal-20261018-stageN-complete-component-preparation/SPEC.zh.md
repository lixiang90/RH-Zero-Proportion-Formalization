# N：全剩余原组件、物理跨度共享的固定发现关

本包目前只准备代码。必须另获不可变 root gate；本次准备无 FS 提取、矩阵、秩、点值、核值、LP 或 Lean 执行。旧 M/I/J/H 与原 source 全部只读。

输入是 H 已冻结的 15,378 个升序 Gindex。原定义 `index=((i*1187+j)*4+chart)`，chart 顺序 id/id、id/rev、rev/id、rev/rev。显式复用已经独立核验的 J Lower index 5331088 和 M Lower index 2417；其余最多 15,376 个 case，每个至多一次固定 HiGHS，零辅助、零重试。J 的 Lower 由既存 H/J remaining 列表之差及 JLB2 tag 身份交叉；M 的 separate-68T Lower 对更强 pooled 模型仍有效。deduction 不需要新模型或求解。

## 模型与有效域

坐标 `X=20Q*p`，Q=32768，κ=Q·1024·10^10。保留155个原几何行：两窗各36跨度的上/下界共144行，9条真实 `17/20` 分离，2条依 chart 符号映射的 Ordered 四点约束。原 state/cursor/FS/PT/区间 guards 不收紧、不换锚。

每原项的 constant 行以及所有原正质量 anchor 行均保留：`S span(X)-T<=-E`。constant 的 S=0、E=QR·lb。anchor 使用原量化点三元组，`dlo=mid32-2D,dhi=2D-high32`，`S=(R/2)dlo`、`E=QR*v-10R(dlo*L0+dhi*(p-L0))`，L0 是原 sumL。提取检查原 FS、两个语义 hash、原 printed-AST/compact M0、原流以及 beta/sigma 身份；每个需要的原 cell 只缓存一次，并与 J 独审已核的 Cstar/J/全部 term hash 比较。J 缓存不含明细，不能直接代替提取。

本 N 每相同物理跨度共享一个 T，汇入任一窗的全部原组件，目标权为该组 `2Σa`；原68项来源及其原混合恒等仍保留。当前固定 source 的纸面计数为42组，运行才由 source 实际映射核验42组、51自由变量、52完整平衡坐标；不在准备阶段执行映射。所有变量 free。目标为原压力与 `Σ2a(group)T(group)`，需达到 `4κ*Nc`，Nc=893766123055294719。

这比 M 分离的68T松弛更强，无新 actual kernel 接口。对实际点，令 T=κw 即满足全部组件约束。任何有效模型 primal 的每窗值也必须至少为 `2κ*c9N+2Mi`；实现对每窗作此精确诊断，避免遗漏原几何/混合/流。Below 只说明本 pooled 原组件 polyhedral 模型不足，不是 actual F 反例。已含原 M0/global c9 下界，不能再将它们作为未用的 clip 救援。

## native 与有理证书

固定 method highs-ds、presolve true、time_limit180、maxiter100000、primal/dual tolerance1e-7、threads1。完整设置由 gate 钉住。native 使用 p=X/(20Q)、U=T/κ；几何法向不变，rhs=原bound/(20Q)；anchor slope=dlo/D，rhs=-E/κ；constant rhs=-lb/V；pressure=BS/SA、U 权=组a/SA。只在 nonzero 坐标做有理除法，再填 NumPy dense51列，避免每 case 创建全部 Fraction 零。

native-only 支配预处理：每组整数 S 相同的组件保留最大 E，相等取最小原 rowID。此操作在所有 X 上保持 max 完全相同。原 raw 行、组件和 provenance 不删除；省去的 dual 权扩回0，最终 primal 检查全部原行。

native 结果完整递归序列化并 durable gzip 保存后，才作有理重建。每组 base 固定为正 native dual 最大项，相等最小 rowID；没有正项则 dual 不合格，不换 support。extras 与正几何行固定；ΔS非零时以 γ=|ΔS|μ、signΔS incidence 为列，9位置方程只做一次确定性 exact RREF，自由未知量固定0。超过9未知、负 hint、同S异E或不一致时保守 unresolved，不求另一 basis。相同S/E extras 可同 base 合并。

恢复每 extra μ=γ/|ΔS|、每组 base μ=2Σa-Σextras，必须每行权非负并核全部52平衡、原 rhs 成本。normalized 小行列式只属于归一化矩阵，不声称 raw μ 分母<=4。初版 RREF 不宣称已实现 forest 快速求解或最稀疏支撑。

primal 仅用一次固定 native face RREF，free 位置取 native binary64 的原样 dyadic 缩放；T 取全部组件的 exact max。base μ=0 不推出 base/extra tie；face 方程只是候选生成，最终逐全部原 raw 行与 objective 检查后才承认 primal。另一个不 import native/reconstruction 的 `check_raw_certificate.py` 重新检查全部行、完整坐标、原成本与 target；不能只信 solver status、归一化小系统或提前消去的方程。

Lower 是有效 raw dual 的成本>=target；Below 是有效 raw primal 的目标<target；二者同时出现硬失败。valid 不够高/低的 primal/dual、native status、失败原因全部保留。Lower 不要求 native optimum 或有效 primal。第一个 exact Below 保存后停止。没有证书只归 unresolved，绝不声称非空。完整遍历但有 unresolved 也不是完整 floor。

## 持久化、停止和范围

`original-components.jsonl.gz` 每原 cell 一份完整提取；`native-results.jsonl.gz` 每真实调用一份无损 native 结果与原 rowID mapping；`case-records.jsonl.gz` 每 H index 一份 deduction 或完整有理重建/验证结果。均每条独立 gzip member，无每条大矩阵副本。model 用完整 canonical SHA 绑定，从缓存原组件和 chart 可确定重建。`call-intents.jsonl` 在每真实 LP 前 fsync，避免异常掩盖调用数。

每 complete case 先 durable witness/native，再 atomic prefix 发布 committed_records、计数、输入序列前缀 hash、每个 gzip durable 字节数/hash。结果只承认 published prefix，异常或 hard kill 遗留 suffix 不算完成，不填假 unresolved。输入/外部 runtime start/end hash。此包不做通用恢复或自动续跑；任何失败不重试。

root gate 另指定总 hard/work 时间及 closed-output 上限，launcher 只创建一个 child，只终止自身 child。HiGHS time_limit 是内部检查，不是 hard wallclock；wrapper 的总时限独立生效。实际完整运行时间/峰内存/压缩输出未知。M 原7.83秒含约6秒导入/输入身份成本，不能乘以15,376作为逐 case 推算，也不能反推 N 全域能及时完成；本次不作新 benchmark。源文件2MB/网站3200秒和独立 kernel 仍未知且未过关。

命令模板（只在 root 新 gate 后）：

`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageN-complete-component-preparation/run_once.py --launch-authorized-complete-N --gate <ROOT_GATE_RELATIVE_PATH> --gate-sha256 <ROOT_GATE_SHA256>`

完整数字分类也只是待独立重放与实际 Lean consumer 的有限候选，不宣称无条件新纪录、提交就绪或上传验收。
