本包仅记录一次官方公共GitHub API请求及未完成的本地收据准备，不是成功的最新纪录鲜核。

唯一GET为https://api.github.com/repos/josusanmartin/riemann/contents/data/records.json?ref=main，禁用redirect、未发送Authorization或默认用户凭据，30秒/2MiB上限，无重试。工具1148dc实际exit1；已有fetch-observation记录2026-10-20T18:05:49.7063205Z启动、HTTP200/OK，elapsed1.2736426秒。

错误发生在本地读取响应Date时：PowerShell已解包日期对象，而脚本仍调用.Value.ToString，导致null-method异常。它发生在保存API正文、解码records.json、提取或重算blob SHA及精确Fraction比较之前；不能描述为远端HTTP失败，也不能把200当作账本内容已核同。当前没有账本正文、actual blob SHA、最大纪录R、missing-exact行数或K>R的此次结论。旧blob6f0e457cfc200238626c230ef731f5d7ebb0a3a1仍仅是既有历史观察。

严格保留本次未完成状态，不自动再GET，不执行旧脚本、Lean、数值/证明核查、Git、私有官网API、owner、quota、查询或提交。即使将来重新授权成功的规划鲜核，也不替代最终上传前的鲜核。
