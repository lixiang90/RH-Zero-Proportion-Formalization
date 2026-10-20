# 未来公开 records 只读 helper；未执行

本包只准备 `read_public_records.py`、本文和pre-execution清单；不执行、import、AST或联网。原PowerShell请求虽报告HTTP200，但Date转换先于保存body而失败，不能提供fresh R；这份不同脚本供root日后另立的一次最终提交读取门，原失败不翻成功。

未来CLI（仅说明，不在本任务执行）：`python -B read_public_records.py --output NEW_LEAF`。leaf必须是简单新名称，写到workspace固定前缀 `research-goal-20261021-w9a2-record-read-output/NEW_LEAF`。已有目录拒绝，绝不删除/覆盖。helper只调用一次GET，固定GitHub contents API `https://api.github.com/repos/josusanmartin/riemann/contents/data/records.json?ref=main` 加nonce和no-cache；不跟随redirect、不自动retry、不发认证header，不触及官网auth/quota/提交。

HTTP body上限2,000,000 B，socket按剩余30秒设置timeout并检查总采纳时限。先以xb创建raw文件，边读边保存，finally flush/fsync；完整raw body保存后才解析response/API/records JSON。HTTP Date只保留plain string（缺失为空字符串），从不Date转换。HTTP错误、timeout、base64/schema/hash/比较错误保留已有raw与小receipt；超过2MB时只保留标记明确的有界前缀，不把截断body当完整数据。DNS、OS fsync及print不宣称硬实时；root仍须真实outer0及整个调用≤30秒。落盘正收据不能代替实际退出。

校验contents type/path/base64/size，计算 `SHA1(b"blob "+size+b"\0"+decoded)` 必须等于API sha；保存原decoded JSON后再检查records。仅实现本任务需要的list/id/track/status/boolean与positive canonical exactRational（≤200 digits）验证，不冒充完整Zod/date校验。原本地records.ts SHA `1fab4d48…740c7` / fixedcommit1135c038的当前选取规则是：按原array顺序取critical-line最后kernel-verified，若无则最后published；不按日期或小数排序。helper不是fresh服务器规则源码读取。

分析列出全部critical-line kernel-verified的exact最大值、当前last eligible及缺失exact的完整index/id列表。固定K为3337881639516708570682858853672166187793/4955348542279967171490000000000000000000。只有当前有exact且K严格大于它，并严格大于所有可用的critical-line kernel-verified exact，才可使该限定比较门通过。其它无exact记录保持unknown，不用decimal或expression推断，永不宣称已精确比较所有无exact记录或已完成全目标。先前37 eligible/36 exact仅是历史，不硬编码成当前事实。analysis限制256KB，若异常多的输出超限则失败，不截断未知项。

fresh输出包括response.raw.json、通过blob身份后保存的records.decoded.json、通过结构检查后的analysis.json与receipt.json。获取/验证失败不会生成新纪录事实；HTTP状态和partial-body范围照实记录。无Lean、数值模型、kernel、export、旧脚本、Git或全仓库遍历。准备清单的false表示当前未授权执行，root未来授权无需改动冻结代码或清单。
