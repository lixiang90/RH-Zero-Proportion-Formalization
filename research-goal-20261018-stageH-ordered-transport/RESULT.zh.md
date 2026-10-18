# H 单次运行结果（生产器，待独审）

按 root 固定 gate `2533ebb71be8f21d3ce9306a54e12250229b962974f6f86e2a02b450eb977eb9`
唯一启动 parent49856、child35720。工具调用在约7.1秒直接返回 terminal，
没有活 session 需要续 poll；wrapper5.930秒、producer5.568秒，exit0。
没有guard触发，没有重试，没有failure.json。预先未见python/lean/nanoda
进程；一次只读CIM查询不可访问，改用Get-Process核空，没有由此运行H。

全部19,838个G未解index已按原顺序提交，producer counts为：

- Empty：4,460。
- unresolved：15,378。

这些是生产器结果，尚未执行独立audit。候选在生产器内都核了原155行
非负整数权、完整十坐标balance和严格负cost；独立作者仍须逐证核查。
known feasible Gindex2417的自检未失败；没有把无负witness说成非空。

`certificates.bin` 148,841B；`remaining-indices.u32.bin` 61,512B。
两流、原stdout/stderr、launch/child/terminal、started和result全部保留。
完整输入index序列SHA与已提交序列SHA相同，为
`017cd322572854b6d1c4446b5e2049f6da86a3291884364dfacd3a866240f1f9`。
全部输入起止SHA保持一致；完整原前缀SHA为
`56038d08ec6260a8ca72bf1587abd9b9d65691b043c953d8bae8ad33348a3539`。

没有新LP、FS、核值、标量采样、Lean、导出或Nano。只消去部分固定外包
几何组合，未解集仍非空，未证明新global floor或无条件新比例。
原始binary证据字节数不是Lean单文件源码字节数；2MB source与完整3200秒
网站流程仍未知，不能由本次Python用时推出。独立重放另由cover owner执行，
本包不会调用它，也不会改已冻结的G/5ray/准备包。
