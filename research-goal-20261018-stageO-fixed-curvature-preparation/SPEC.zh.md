# O：固定1322606原锚/原REG曲率机会审计——仅准备

本包未执行数学。另需root不可变gate；AST/文件身份与原REG字面库存读取不是曲率评价。旧包、root治理和当前target均不改。

## 固定输入和缺口

只读 N2 首Below G1322606/cells278,665/rev-id，保持原完整52坐标有效raw dual及全部305行/原68项/82正质量锚的独审前提。每个原row的μ不变，不拟合、不重新求解、不择另一support。只取μ>0的原anchor行，constant/geometry行不附曲率。目标缺口固定为target−rawdualcost，绝非target−primalvalue。

O读取已有组件缓存/原FS字段和原PT字面值，不新解码/选择FS或取新核点；原Below独审8a793215…和ed007f28…作为已冻结前提。source f82a4914…的profile/正尺度全部从同source字面提取，不迁移旧24核表。现有source/parser只做字面提取。

## 预声明的跨度与原单元覆盖

每physical span的I固定为该组全部原项[L/Q,U/Q]的交集，再交下界length·17/20。不Floyd、LP、额外DBM闭包或自适应收窄。原Below primal说明这些区间非空；若实际检查不符则失败，不能换规则。

每个正μ anchor固定q=p/Q；必需H=hull({q},I)，不是仅I。用source REG12386–12387的16条既有chain：起点rgA，随后已存链endpoints，终点rgB。每个ccell(a,b)只取原相邻端点，不创建新间隔、不在H处细分，也不在现有大单元内另造小单元。按chain编号升序取第一个完整包含H的chain；该chain中所有与H闭相交的原单元固定纳入（端点相接包含）。无chain完整覆盖时该anchor付款0，不改锚或另选oracle。

涉及的原单元去重后只评价一次source CellA有限整数式。`cellA_quantitative.py`逐式转写sourceIV/SZ、farJ(n=0,1,2)、S0/G1/G2、K0/K1/K2及W2L，保留Nat.sub与有符号floor/ceil。验证同一source c.ok/E2L>0/E3L>0与W2L>=0。它们本为hR的原chainOk/convOk单元；若失败属于source转写/输入不一致，立即失败，不能换单元/精度。

每原单元定量下界候选m_cell=2*W2L.v/DZ²，来自既有CellA.w2_nonneg证明中的quantitative inequality。尚需薄化成实际Lean theorem，当前source只输出nonneg。每行m取其固定覆盖中所有原单元m_cell之min；无新π、sin/cos、Fourier采样或Taylor精度。m=0可使用旧ell基线；不是给未知曲率段武断宣称凸性。

## 固定的两种有理付款（未来gate须明确授权）

权c_r=μ_r κ m_r/2（物理s单位，κ=QRV），原 E/S/L0/derivative误差支付不变，不再乘external a或原mass。则actual raw O≥D0+Q，其中Q=Σc_r(B_r t−q_r)²。

1. 每physical span exact weighted variance，再把qbar clamp到固定闭I，求和给uniform下界。
2. 同一c/q的正权图按连通分量最小编号vertex gauge0，构造一次exact有理reduced Laplace方程并确定性消元。必须全部10坐标stationarity残差精确0。Q(t*)是全空间uniform下界，t*无需满足几何域；它不是新kernel锚，绝不在那里求w值。图不连通保留多个gauge，不能用regularization。无PSD/eigen/LP/数值优化/不同gauge重试。

固定取上述两个已证下界的max，不扫参数/曲率预算。若矩阵意外奇异、残差不为0则失败，不修点或付款。若total payment<target−dualcost，只报告这一预声明付款不足，不否定实际命题或更强付款。

## 执行、输出与范围

当前只有源码/合同/AST与byte pin；未恢复FS、算曲率、建矩阵、求解或Lean。未来root gate另定hard/work资源及最大原REG查询数（上限是source字面库存）。`run_once.py`一child、零重试；每失败保留stage/lastcell/querycount/trace。未有执行gate不得调用audit_once的执行入口。

固定CLI模板：`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageO-fixed-curvature-preparation/run_once.py --launch-authorized-fixed-curvature-O --gate <ROOT_GATE_PATH> --gate-sha256 <ROOT_GATE_SHA256>`。

完整输出包含所有正μanchor行、q/guards/覆盖/原cell整数中间值、min m、两种付款的exactFraction和stationarity/variance证据，以及成本/缺口/最终余量。成本与目标是同raw尺度。无论数值是否支付成功，外部独审与actual强Taylor/CellA量化Lean桥仍需完成。只涉及这个固定pair，不能外推全部13003剩余项或无条件比例。网站2MB/3200秒和完整proof成本未知。
