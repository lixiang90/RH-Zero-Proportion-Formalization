# 固定 C 点上的两份原 FS 仿射诊断（仅准备，未执行）

等 source mtermTI signed-affine 提取与原 flow 支持 A_FS>=c9 的静态
note 全部冻结，并等 root 的单次算术书面授权；本包本身不授权运行。

固定输入是 Stage C 首可行点及原 prefix exception0、suffix exception1。
不另选点，不计算实际核值，不求解 LP，不收紧原 state 或 L0。原 source、
原 A trace、两 FS/flow 语义与原紧闭 geometry 全部验 hash；沿冻结路径
重放 split，仅用于重建原 cell，不产生新 cut 或遍历新树。

Q=32768，R=1024，D=10^9，V=10^10，SA=10^20；
kappa=Q*V*R=SLOPE=335544320000000000，K=SA*kappa。
每原 term 保持原 mtermTI 的 L0=sum(original adjacent L)、L/U 与 uc。
从原 decoder 取 R 混合权；mvT/mslT/mwT/mcpT/mcnT 已含该 R 混合，
不再乘 R，也不含外部 TS 的 a_e；求总能量时只乘 a_e/SA 一次。

    sigma=(mslT-2D*mwT)/(D*R)
    beta=mvT/(V*R)+(mcpT-mcnT)/(Q*D*R)-sigma*L0/Q

每 term 用 signed Fraction，beta+sigma*s<=actual w(s) 的解析理由由
原 mtermTI 和静态提取 note 提供；不是把 Nat.sub 错当 signed 差。
脚本保留全部原 active mokI guard、所有自然数分量与 scale。

34 个 term 加原 BS pressure 形成 A_FS。两窗口嵌入同一九 gap，prefix
offset0、suffix offset1。用 beta/sigma 和独立 scaled numerator 两种
写法逐 term/whole sum 验精确相等，再在原固定 rational C 点求 A_L、
A_R 与 A_L+A_R-2c，c=893766123055294719/10^20。

原 flow 的 P/S/Cp/Cm 只用于重建原 cell 下界：令 gamma=DR*b+sum
a*(mslT-2D*mwT)，penalty=sum(width*max(P-S-gamma,0))。以原 signed
affine 在 adjacent lower corner 的 scaled numerator 为 base，
certified_num=base+10*(flowCm-flowCp-penalty)。检查
certified_num-kappa*cN=原 compact margin=原 printed AST margin。
这证明信息只用于说明原模型的已有 c9 floor，不把 flow 数值再加到
固定点 A_FS 中。beta 定义及实际点值本身不含 dual flow 加成。

若该同一可行点 sum<2c，只能判定这两份固定 affine 模型不足以证明
共同 cell 目标；不是实际 F 反例。若 sum>=2c，也不推出全 cell floor。
输出不论正负都封存；不自动改点、FS、阈值或跟进优化。

拟新 gate 字段：arithmetic_passes_authorized=1、stageC_producer_manifest_sha256、
stageC_independent_manifest_path/sha256、fixed_point_sha256、target_c_numerator、
denominator、source_affine_static_manifest_path/sha256、source_flow_static_manifest_path/sha256。
执行必须显式提供 --execute-authorized-once --gate --gate-sha256。
当前只有脚本/规格，无 start、evaluation 或 failure receipt。

新消费者及完整网站 source/runtime gate 仍未知。本包不编译 Lean，
不改变任何 frozen source 或治理计数，不宣称新下界/无条件比例。
