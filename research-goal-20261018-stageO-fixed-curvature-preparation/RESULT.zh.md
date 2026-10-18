# O 唯一执行：固定 pair 的相关二次付款严格足够

root gate `stageO-fixed-original-curvature-20261018.json` SHA f17cd64c0889038d7dad678a93960a276f585dda294d9cdd28d0edd03b69fa10。prepared e6cfb7330076dccd9a11ca246c41d1ac293ac5bbf8ede2d20b91c46d60f6888f 和五脚本均未改。实际 parent25112、child47068、工具session38623；唯一child terminal0，wrapper14.367696500004968秒，child12.392998099996476秒，未触资源上限，无失败/重试。输入与两个Python运行时端点hash前后相同。

只处理固定 G1322606、cell278/665、rev/id 的原有效raw dual。49个正μ原anchor全部按预声明hull(q,I)规则得到覆盖；只评价23个source原REG单元，无新单元/细分/锚/FS或核采样。所有CellA的ok/E2/E3/W2L检查通过，m=2W2L/DZ²，未改profile或精度。

两种预声明付款均保存：逐span variance/clamp 与一次exact Laplace。network更强且使 old raw dual cost+payment−target 严格正，结果 `conditional_fixed_pair_floor_closes=true`。所有有理数、中间K0/K1/K2区间、每行m/c、variance、p*和完整10坐标stationarity残差都在 `curvature-packet.json`（SHA a952a8bd239bddaa0c8d1f24b45a5096cb3a3b6ff19f067baaba46686eb11cbf）。

本结果显示保留跨度相关性的二次网络能补上本pair线性组件松弛的缺口。它不是全域结果，不是新的零点比例证明。还需外部独立纯整数/有理数重放，以及当前source实际量化CellA下界和强Taylor余项的Lean桥。没有执行任何新LP、kernel anchor、细分、FS选择、精度/支撑重试或Lean。

本包封存后停止该次实验，不自动扩pair或修改模型。source文件体积/完整运行时间与提交预算仍未知。
