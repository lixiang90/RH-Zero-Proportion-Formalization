本包只读抓取当前 public main 固定提交 `1135c0386310a0a038004d3b0fe64d0237e47dce` 的 97 个源码文件，以及当前官网匿名 `/submit` 页面实际引用的 9 个 JavaScript 文件。固定提交的 Git blob SHA1、文件长度、SHA256 与前后 HEAD 均已核对。仅 HTTPS GET，未执行远程代码，未读登录会话，未 POST，未编译或运行证明。

结论：保留 draft-v5 的原始 1,830,001 字节，SHA256 `650ad1762ee36ba1ddf5f6a027900b20f0f85ba087ac099fd2c99a54eaf6ae13`。当前部署的客户端使用原始 `solution` state 构造正式提交 JSON；`replace(/\r\n?/g,"\n").trim()` 只用于与非竞争 FlowTest 比较，没有赋回 state。当前 main 的服务端 schema 也没有给 solution 加 trim，后续摘要、E2B 写入和存档均使用原值。可读依据、原始响应、时间、SHA 与精确字节片段见 `review.json`。

公开署名在当前部署 JavaScript 中没有 readOnly 属性，仅在 busy 时 disabled；当前 main 源码相同。这里没有读取已登录用户的 DOM 状态。GitHub 身份来自服务端会话，公开署名是独立的 displayName。

单文件源码含 221 处 CRLF 和恰一个末尾 LF（Graph 原模块 222 处，flatten 去 import 行后少一处）。文件上传路径将 `file.text()` 原样写入 React state；手动编辑路径读取 textarea.value，实际上传前应核对真实 JSON wire 中解码后的 source bytes/SHA，避免 DOM 输入的换行变化。官网 proofDigest 是带标签的 manifest+source 摘要，不等于单独源码 SHA256。此包没有实际上传，亦未证明当前服务端部署提交号；服务端说明以固定 main commit 为证据边界，当前客户端则是实际部署 GET 证据。

更正旧证据范围：旧 accepted 的 `official/comparison.json` 显示 public raw 与 local raw 都是 1,979,280 字节且 SHA 完全一致；1,979,279 字节是平行 trim 比较预览。其 `UI_normalization` 字段描述比较过程，不能证明服务端实际 trim。已有冻结 prepared 材料包未修改，其中历史 normalization preview 须按本更正理解。没有据此创建 normalized 源码或 draft-v6。
