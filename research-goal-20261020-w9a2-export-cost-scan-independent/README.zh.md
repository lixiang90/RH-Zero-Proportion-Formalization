本次结构扫描真实失败：child1，外层记录20.563s且非timeout；result在20.422s报告Name-table budget exceeded，采样自身峰RSS56147968B（53.55MiB）。

停止原因是scanner把所有namespace的名称逐条展开成完整Python字符串，累计sys.getsizeof(resolved)+16估算超过固定32MiB名称表门；在新名称append前抛错。它不是256MiB RSS上限触发，也不是Lean内存测量。共享前缀被重复展开的存储策略解释了此scanner容量门的含义，但没有终止名称/offset/计数，不能定位来源或给出定量归因。

EOF、完整677MB hash、完整字节计数和任何排名均未生成。不能由此推出大data/proofsize、哪个声明/namespace、Lean137/OOM或v8编译内存瓶颈。原始外层session53230/008e11真实exit1来自root直接报告；本包独立读取的小outer文件确认child1，不冒充自行读到原始工具结果。

仅核小runner/result/outer/空stdout与stderr，未读大NDJSON。原README当时未生成，按令未等待。没有更改原收据、runner、proof、state、counter或Git，没有设计v2/加预算/重扫。
