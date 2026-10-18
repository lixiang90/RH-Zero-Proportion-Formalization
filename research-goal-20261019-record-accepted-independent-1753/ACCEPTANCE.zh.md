# 已接受成果的独立公开证据

实际观察时间为 **2026-10-18 17:54:28.806891 UTC**，不是推定的接受发生时间。官网排行榜 API 返回 HTTP 200、Age 0、X-Vercel-Cache MISS；当前公开纪录为 `lixiang90-single-exception-overlap-20261018`，作者 Li Xiang，GitHub `lixiang90`，状态 `kernel-verified`，`formalVerification=true`。

精确纪录为
`3337839448633819172184136761695440236797 / 4955319193827760237900000000000000000000`，就是本次候选 κ。其 proofUrl 固定到公开仓库 commit `6bc7f07fb939e066ac2923493d9a01cca553fe87`：
https://github.com/josusanmartin/riemann/blob/6bc7f07fb939e066ac2923493d9a01cca553fe87/submissions/lixiang90-single-exception-overlap-20261018/proof/Solution.lean

公开证明源原始字节为 **1,979,280 B**，SHA256 为 `024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81`，与用户实际上传 v3 文件逐字节完全相等。以 ECMAScript String.trim 的空白集合正规化后也完全相等；未使用 native-v4 文件替代。

公开 submission.json 为 1,533 B，SHA256 `7b44f4ce8138381653826e3dfbffefc7b00d867072c400b265a358f656908f56`。按固定上传规则，对 `submission.json\0`、manifest 原字节、`proof/Solution.lean\0`、solution 原字节依次求 SHA256，得到：
`23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f`。
它与用户报告的运行 digest 完全相同，因此公开接受条目与本次 v3 任务强绑定，不只是另一个同分结果。本成果已经晋级，不再把“严格超过自身 κ”当成原用户目标。

原公开 manifest 摘要中的 local cold pending 是提交时保留的历史原文，未改写；它不能覆盖目前官网 `kernel-verified` 状态。本轮没有公开 elapsed 或私有 job 明细，不能自行声称其具体耗时。已保存三次只读 HTTP 响应及原始 body：排行榜、接受源码和 submission manifest；未运行任何编译器、生成器、求解器或新数学搜索，未修改旧冻结包、根方向或轮数。

最初的 `files.json`（SHA256 `71f1ba7aaf1ba70b0edf1526103bdf0f1684a4b9c06fbcde3ac5e8a3edb0ebf2`）保持原样；新增 digest 证据由 `accepted-files.json` 覆盖交付。
