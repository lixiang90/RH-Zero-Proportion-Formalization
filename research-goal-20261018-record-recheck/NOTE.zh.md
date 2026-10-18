# 2026-10-18 06:47 UTC独立纪录复查

新leaderboard HTTP请求在06:47:40.704062 UTC完成，HTTP200、Age0、
X-Vercel-Cache MISS。GitHub main ref、head commit、固定commit的records.json
及proof目录元数据随后独立读取，最后06:47:50.331214 UTC完成。
原始响应bytes/SHA及Date/cache/request-ID等头信息记录于receipt.json。

截至该次观察，网站和公开main一致，未发现高于本地基准的accepted纪录：

  3337839448633819172184136761695440236797 /
  4955319193847235264050000000000000000000
  = 67.3587173310297059918152909095% （网站报告值）。

id为critical-strip-exclusion-attempt-1；accept commit
0c038980cbfaa3ee9fc539d751c32c454d85a319，UTC2026-10-18T03:40:45Z。
evidence/proof commit为cfc7ce6113199b7d5f262812d81089778e84335c。
固定原源码链接：
https://github.com/josusanmartin/riemann/blob/cfc7ce6113199b7d5f262812d81089778e84335c/submissions/critical-strip-exclusion-attempt-1/proof/Solution.lean

没有重下载大型Lean源码。远端proof目录返回size=1,818,411及Git blob
SHA1=7735df37ffb167a1dcd76c53d00ffd55e7d33fbe，与本地raw snapshot的
Git blob hash和bytes完全匹配；本地SHA256仍f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。
所以当前模型对应同一份源码，不需因本次提示自动换核/阈值或作废B–F。
本结论有明确观察时点，不保证之后不会出现新纪录。

先用web工具的GitHub directory页面出现上月缓存，不以它为最新证据；
随后GitHub连接器main/commits已显示上述identity，再由本脚本fresh HTTP
独立核对。canonical getCurrentRecord逻辑取最后一条kernel-verified记录；
还比较所有有explicit exactRational的条目，当前确为其中最高。
1条legacy entry的exactRational为空；首个metadata尝试因此TypeError，
没有写收据，技术修复后第二次只读获取成功。attempt1-failure明确保留，
不把第二次称首次，也没有数学重试/参数扫描。

未运行Lean、LP、叶解码、核值查询或任何新数学测试。网站kernel-verified
状态是上游记录，不是本次本地双内核重放声明。旧冻结包没有改动。
