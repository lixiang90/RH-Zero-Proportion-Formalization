# rc10 五 cut packet 的窄范围独审

结论：固定packet的字段、身份和内部拓扑一致；未发现阻断已授权五块source准备的确定矛盾。此结论不是Lean stEq、cursor proof、构建或资源PASS。

实际读取packet.json（32064B，SHA211b8b2ebf8e2a1ccfc3e22ef9ab658acb80cf86a977d072cec50cb9f7e663a4）、生产脚本正文、其小收据/manifest及固定v9源7552bbb8…（1861120B）。metadata-v2/files.json为6fccb81eab262452bbecb559a6a40313499d442f862822116bc522ff2dfd9c9f，6成员当前bytes/SHA全匹配；脚本ef205711…与pre-execution身份一致。没有执行/导入生产脚本、流读archive、解WL、重算叶/energy/margin、运行Lean或修改源/state/Git。

独立对六份packet数组重算紧凑ASCII JSON加末LF的SHA：全部同时等于各自canonical字段和archive_event.state_sha256。每份恰73个非负整数，最后M=0，36对lo<=hi。字段序逐项等于v9的St（10654–10660），含8组l/u、按当前PR顺序28组A/B及M。PR、COV所有false区间和rc10 indices 0,0,1,0,1,0,0,0均从当前源逐项对照；root经matC的span bounds与packet根数组一致。rootCl原span为0/W，fLe/fUe是max/min相邻gap和，当前和均在W内（9123–9124、9458–9461、9582–9583、12704）。此处是小literal/geometry一致性检查，未执行Lean定义。

|cut|pos|end|depth|fuel|numeric|
|---|---:|---:|---:|---:|---:|
|0|406|75052|16|112|224|
|1|75052|97737|16|112|75|
|2|97737|167809|14|114|236|
|3|175794|234493|14|114|196|
|4|234493|258792|14|114|90|

每份fuel=128-depth，至少为该archive子树height；pos/end与同一packet事件和summary一致且0<pos<end<=270277。20个frontier成员的根路径均从1开始、长度depth+1、末尾为pos，互不为祖先，游标区间按preorder不重叠。全部numeric之和906；按>=64选择的五个之和821，父剩85。全部成员<=256，五个选中结果及顺序与固定规则一致。

只读生产脚本确认：先按完整archive子树postorder累计counts和left=pos+8/left.end=right/right.end=parent.end；从root按<=256停止的唯一top-down规则构造frontier，再筛>=64。全1895归一geometry hash核对、父numeric>256的maximal性和实际0.4494992秒exit0来自已冻结生产收据及代码断言；本独审不重流archive，不把它们说成第二次独立replay。无需扩大metadata工作。

五个hint只是proof输入。每块必须用原raw walkCut、空cuts、表内fuel/pos/end运行原decide +kernel，再由walkCut_ok建立当前Covered(toCl s_i)。五次cutsOk_cons后，父walkCutR fuel128/pos1须自行检查完整73字段并返回270277，经rcOfC保持原rc10命题。父剩85 numeric不由metadata替代；旧整root rc10不能充当子块proof。当前配方静态类型链无已知缺口，但尚无新Lean终态。来源数组与实际父归约状态的等同性仍由未来父stEq检查负责，不能从archive SHA跨越该门。
