# 无效进程观察，不可作为执行依据

原tool59b532的Get-CimInstance报告“无法从客户端中访问CIM资源”。PowerShell非终止错误后，未加ErrorAction Stop的原脚本仍把空数组写成无其它进程；ownership-invalid-cim.json仅保留这次错误产物，不是有效观察。

root已作废该记录且未开启编译。新执行gate只能绑定另一次成功查询所得ownership.json；不把CIM错误/空数组推断为独占。
