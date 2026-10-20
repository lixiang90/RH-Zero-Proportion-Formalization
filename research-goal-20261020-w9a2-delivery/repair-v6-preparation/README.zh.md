此准备包从冻结 draft-v5 与 Counting-repair-v1（0a648832…，39项）生成新的 draft-v6。唯一源码差分是 Counting 的158、178、205行将三个 bare wfun 限定为 Zeta23Ext.Bridge.wfun，模块与flat都增加51字节，精确正反投影。其他四模块、全部wrapper、trusted输入、importplan、数据和数值保持原字节。公开三type继续与官方trusted模板仅空白归一相等。

输出 Solution.lean 为1,830,052字节，SHA256 a517df6aebde6d136f8b83e06c8be10b3413b8430390f52bd47f04e06f0dce26；files.json 为5bba5e728410d748a347b1ad864b56a147f2dc54db263f9be2a62dc892bfbd87，body_segments按新字节偏移完整重建，余量169,948字节。CRLF仍221处且末尾LF保留，不做规范化。

生成器只读、逐文件核两个输入manifest并重建纯文本；无compiler/exporter/kernel/optimizer/subprocess/network调用。source-review记录的是生成时的静态范围；新普通模块实际PASS的后续收据由root另存，并由新版prepared-v6材料引用，不改此包source-review。v5的原production68653已实际exit1，旧collector不能执行；v6完整单文件/双内核/3200秒/官网仍待新真实生产收据。所有旧draft、runtime、runner、canonical源和方向计数均保持原样。
