# v10 新完整单文件资源 runner 准备

仅将已实际运行的v9 runner中的版本身份v9换成v10，工作目录、schema、源目录约束随之改为新的唯一v10路径，其他字节完全不变；反投影逐字恢复原068691fc…。固定3200秒/-M6500/-j1/tstack262144/7GiB PeakWorkingSet以及-o/-i/-c/--json保留，无自动重试或增加资源。

本目录只准备代码，不授权执行。新的完整源码和反投影独审尚待；root须另冻结enabled gate并鲜核本工作区无活编译进程，才可启动一次。只缓存可信Challenge定义及历史包库，拒绝缓存用户Core/Candidate；因此与上一条已PASS的rc10开发pilot范围不同。Lean将正常检查全部完整新源，scope里的no kernel仅表示不启动额外export/Comparator/nanoda，不否认普通Lean类型核检查。

v9实际资源失败仍保留。任何新本地PASS也不能代替官网Linux原资源/3200秒完整双内核与公开接受。旧源、证书、原receipt均不改；goal active。
