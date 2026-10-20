本v2是root在有效v1结果（立即child为905+1，停止两child路线）后新明确授权的一次metadata transform，不是自动retry。脚本先冻结，再只执行一次；同样固定30秒/输出总计≤2MB、原archive/baseline/v9 source pins、standalone stdlib，不import旧model/parser、不decode WL、不重算leaf/energy/margin，不写proof/sourcevariant或运行Lean。

唯一选择规则：从root10向下，numeric leaves≤256即取整个subtree，否则递归两child；得到完整maximal frontier后只选numeric leaves≥64成员。位置由归档拓扑独立计算，不预填pos。Root给的20个frontier成员、五块75/90/196/224/236合821及parent剩余85作为结果核对约束，若不符即停止，不换规则或重试。

按当前COV false BAD、source PR次序和归档branch axis/cut，使用已注明出处的同一几何split公式重建root10全部1895个normalized M0状态，逐一核canonical JSON+LF SHA。只输出root+五selected的完整73Nat/M0状态；frontier另输出20个成员的pos/end/counts/height/path/depth/originalfuel=128-depth及拓扑分区证据，不输出全部状态或任何margin。

这仍不是实际parent Lean stEq或proof PASS。五块为不交的archive subtree仅是拓扑/几何证据；正常parent walkCutR fuel128仍必须真实检查剩余85个numeric leaves，不能将小叶stub、换任意end或用metadata免除证明。所有actual state/M/cursor/新的consumer均须独立Lean确认。v1、所有frozen source/DRAFT/失败收据、root状态与计数保持不变。
