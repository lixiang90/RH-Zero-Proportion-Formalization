固定已接受W9A2九点窗口及其原证书数据。Core的完整quantitative walk与Localization.located_state处理每个相邻gap至少17/20的实数窗口，包括根外与反射分支：返回24个保留叶之一的两个朝向，或good状态G，并同时给出实际窗口能量下界。状态共48+1个。Graph.StateAt、edge_from_locations通过同一十点配置的共享跨度验证真实相邻窗口转移；37条叶间边加97条涉及G的边共134条，其余2267个有向叶状态对由严格不交的闭区间界排除。

令A=10²⁰，d(s)=cost(s)/A，P(s)=potential(s)/(5A)。原始整数有限证书Graph.edge_potential为

```
622387738726 + potential(t) − potential(s) ≤ 5 cost(s)  (Edge s t),
0 ≤ potential(s) ≤ 2504722000690,  potential(G)=0.
```

取精确证书值μ=622387738726/5，b=893029029923108825/A，Δ=μ/A，c=b+Δ=4465145772003282851/(5A)，C=2504722000690/(5A)。Localization给Eᵢ≥b+d(Sᵢ)，边证书除以5A给Δ+P(Sᵢ₊₁)−P(Sᵢ)≤d(Sᵢ)。结合后

```
Eᵢ ≥ c + P(Sᵢ₊₁) − P(Sᵢ),
Σᵢ<N Eᵢ ≥ cN + P(SN) − P(S0) ≥ cN − C.
```

这是Counting.sum_range_coboundary_lower及summed_of_state中的真实能量结论；末端使用all_to_good接到G。m个分离点有N=m−8个九点窗口。C只是一段的固定边界损失。

Counting.matching_defect_bound_summed保留原近点pair付款，将全部未配对点放入唯一none标签的分离remainder。只有这一标签支付C；hcharge在整个matching partition求和后恰为BR+8c+C。这里B=454741897490/10¹⁴。在该定理的实际谱界、核逼近误差δ及跨度R前提下，所得Gram defect界为

```
(c−32δ)m − BR − 8c − C ≤ defect.
```

C≤c将固定项吸收到9c；matching_defect_bound_effective同时使用36δ的保守误差系数，使原计数接口的边界参数由9改为10，九点窗口本身不变。actual_defect_estimate_effective把核逼近与分离谱界实例化到实际ζ零点配置，而非给最终结论另加矩阵、状态word或局部floor假设。

Counting.ratio与Final.ratio_exact使用同一W9A2解析常数

```
H = 6721237468782417141365717707344332375586 / 10⁴⁰,
κ = (H−B)/(1−c)
  = 3337881639516708570682858853672166187793
    /4955348542279967171490000000000000000000.
```

该分数严格超过冻结W9A2基准（同分子，分母4955348548503844558750000000000000000000）。v9后续实际验证须另留收据；此处仅保留原数学说明。Final.actual_dyadic、actual_cumulative分别得到：对每个ε>0，存在T₀，对所有T≥T₀，

```
(κ−ε) Ncount(T,2T) ≤ N0star(T,2T),
(κ−ε) Ncount(0,T) ≤ N0star(0,T).
```

后一个结论使用原cumulative_of_dyadic、Riemann–von Mangoldt接口与N0star可加性。最终两式无RH、未证局部floor或数值模型前提。以上数学说明沿用历史冻结材料，不是v9新数学核查或proof验收。固定v9相对v8的完整字节投影和两份独立静态审查已链接；它们不替代Lean正常kernel typechecking、独立内核或官网验收。Root报告资源门在启动时运行中，原outer23402、parent32660、child54436；本材料不查询该进程或输出，后续终态未知，不称通过或上传ready。v6 cold3200失败/Nano中断/首投timeout、v7官网Lean137失败与v8两次本地资源失败/官网Lean137失败均保全，不被新v9材料翻为PASS。未来实际资源、数学或官网结果须另立证据，不覆盖本DRAFT。
