# 已官网通过：单例外相邻窗口法

**67.3587173312944342020759392480%**，精确比例为
`3337839448633819172184136761695440236797/4955319193827760237900000000000000000000`。

官方记录：[lixiang90-single-exception-overlap-20261018](https://github.com/josusanmartin/riemann/blob/6bc7f07fb939e066ac2923493d9a01cca553fe87/submissions/lixiang90-single-exception-overlap-20261018/submission.json)；
[已接受的完整 Lean 源码](https://github.com/josusanmartin/riemann/blob/6bc7f07fb939e066ac2923493d9a01cca553fe87/submissions/lixiang90-single-exception-overlap-20261018/proof/Solution.lean)。
作者 **Li Xiang / lixiang90**，官方状态 **kernel-verified**、
formalVerification=true。冻结的独立HTTP证据于
2026-10-18T17:54:28.806891+00:00 观察到本候选已经成为公开纪录。

本目录 `proof/Solution.lean` 是上述官方 raw 源码的逐字节归档：
**1979280 UTF-8 bytes**，SHA256 `024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81`。
它与用户原上传v3相同，规范submission+proof digest是 `23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f`，与用户job一致。
去尾空白后的文本少一个byte；该纯文本规范化比对关系另在原始独审保存；本归档保留完整raw字节。

数学新增是相邻九点窗口的唯一例外不兼容，以及只支付一次边界亏损的求和/计数转移；
见 `MATHEMATICS.zh.md`。相对提交前基准的精确增益见 `strict-improvement.json`。
现在网站R等于本候选，是本次已晋级的结果，不需无穷追赶自己的新纪录。

官网接受是该v3按固定官方验证pipeline通过的权威证据，包括单源≤2MB与固定3200秒
验收政策。公开record/submission未披露实际耗时，本材料不捏造耗时。此前本地v0的
3200秒超时、v3各核分别通过的诊断均原样保留；不回写为本地统一PASS。
独立运行中的native-v4不作为本次最终交付，也不以其状态替代官网v3的接受证据。

`official/`保留官方submission原字节、接受快照/HTTP收据和源码身份核对；原网站
method/summary按发布原文保留，其中上传当时的pending句子不代表当前状态。当前
状态以kernel-verified的官方API记录为准。数学说明采用准确的“九点/八gap”术语。

旧pending材料不覆写。工程仓库的最终GitHub同步与字节审计由root另保存回执；
官方接受proof本身已由所链接的immutable GitHub commit公开。此归档不再次上传。
