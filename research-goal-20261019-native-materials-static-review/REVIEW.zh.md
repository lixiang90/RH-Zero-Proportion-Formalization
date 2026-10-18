# Post-PASS collector：独立静态复核

复核最终 collect_once.py SHA
`a22f6dd7d690e9714349262672c5b7ecc14ad7728611bc29dc0b41c8a3a7cda0`
和 prepared `4c9239ec89cbef146a71c18d44e341eca38bda9592a7c92febd2ce1720fef349`，
并对照冻结 fullcold v2 runner 的字段/写入顺序。没有import/调用collector，未读取
活动Linux job或把 session84529 判为已完成；本报告不能授权或代替实际收集。

**静态结论：未发现确定的成功阻碍或漏掉关键终结条件。**

- 入口要求root在gates新建确认文件，SHA、实际session84529/exit0、实际工具原output
  中唯一最终JSON、三收据原SHA、source原SHA均齐。模板默认false/null，不能直接当
  成功输入。日志里局部PASS或生成源存在均不足以启动收集。
- verification所有proof布尔值、10阶段顺序/exit/日志/资源、4冷编译源/olean、两export
  原SHA、Comparator三成功文本、完整Nano0配置/Checked/公理子集均交叉核对。阶段
  started/terminal只比较共有字段，与runner先写terminal后添加hash/RSS字段的实际
  schema一致，避免把额外字段差异误判为失败。
- deadline和mirror终结须同verification SHA互相一致、真实终结stdout总elapsed≤3200；
  失败文件必须不存在。不能将单独Nano诊断或旧v0失败拼装为本次统一成功。
- 原native安装、gate、prepared、source/runtime closure、symlink解析及全部proof bound
  重新核；original_pins与bound重叠时还先要求expected相等，防merge覆盖冲突。
- actual v4 source、两份generationmetadata、原overlay和最终proof receipt多向对应；
  source必须UTF-8且≤2MB。score及比较纪录不换版本，不更改用户正在网站测试的v3。
- 仅复制白名单小日志/收据/规格和actual source，拒绝ELF魔数，文件类型/单文件/总量
  受限；不复制NDJSON、olean、shared library、SDK或cache。原大export只重核原处hash。
- 目标目录exclusive，成功后材料manifest只锁其实际文件；失败保留partial并写失败收据，
  没有自动resume/重试/覆盖。网站仍pending、submitted/officialacceptance均false。
  材料整理在proof终结后，未并入或改写原3200秒收据。

此结论仅针对已冻结代码及上述合同。真实terminal确认和collector实际成功仍待root
持有的句柄及其之后的唯一授权执行；没有增加新关，也不声称网站接受或重跑证明。
