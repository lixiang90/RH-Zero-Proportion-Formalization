# N2 唯一恢复执行：首个 exact Below，正常停止

原失败 N 包 `181473343e98152ab01e622b6346cd37516bb9724477ac26ade56e15dc9b7377` 保持原样。N2 prepared `e83e14f92e4471189c4f558807dec830baed560fe682fc3a9ef70ddb3d89e297` 与三个准备源均未改。root gate `stageN2-same-model-resumption-20261018.json` SHA `286427f9f3c78f39fefbf7080d6ae13c1ec70494d548b1b0418c255dc5607f3d` 只授权这一次基础设施恢复。

实际 parent6844、child25804、工具 session19667，terminal exit0，wrapper202.66999960000976秒，child结果201.38896460001706秒；未触1800秒/160MB hard上限。全部输入和外部 runtime start/end SHA相同。完整 stdout/stderr、raw native、调用意图、gzip member offsets 与 append-only commit日志保留。无重试，未改数学模型或参数。

恢复阶段逐 complete gzip member/EOF 与原模型/raw证书检查后，接受旧676候选，其中原published675之外的第676条单列恢复。旧675次 LP 与 intents/native 一一对应，重复旧LP=0。

本次新1699次，合计2374次 LP。完整 committed prefix2375条：2373 Lower、1既有M deduction、1 Below。原 H 后缀13003未处理，不归 closed/unresolved。J既有Lower5331088在该后缀中，未被N2遍历；不要将它混入本prefix计数。

首 Below：Gindex1322606、cell278/665、rev/id，完整51坐标primal通过305条原raw不等式，68原项共82个原正质量anchor guard全部保存为passed。两窗原M0强floor均有正surplus。exact raw objective−target 为

`-764508264970606216043785120151702128431083387761572608614400000 / 11967742143606171662460708372177`。

这些标量与原包字段只读导出到 `first-Below-readout.json`，没有新FS/矩阵/核/点搜索/LP。它不是实际 F 反例：只说明当前固定原组件、跨窗相同physical span共享T的polyhedral模型存在低于目标的可行点。不能排除更精确的实际余项、其他有效不等式或别的证书结构。

全域目标未证，外部N2独立数学审查pending，未运行Lean，也未通过网站2MB/3200秒预算。`freeze_result.py` 仅核字节、commit链、序号和既存scalar metadata，不重新执行模型数学。后续任何curvature、核、FS、矩阵或求解均需root新gate。
