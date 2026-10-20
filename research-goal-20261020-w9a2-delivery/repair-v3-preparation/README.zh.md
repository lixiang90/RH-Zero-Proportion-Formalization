本包独立逐字审查root封存的graph-repair-v2，并从frozen draft-v2生成NEW draft-v3；未运行任何compiler、exporter、kernel、solver或下载。原canonical及draft-v0/v1/v2均保留。

输入repair manifest SHA为 `5e5162d27f6e99347c425b954135db00f4e729b53ba4a430c2b26b4a8eb186a9`，10项bytes/SHA独立核同。新Graph为17,372B、SHA `2e259252f7fa993954bd52c4a6d6ec58594116a500a576910d6fa671d6521966`。相对prior frozen v2仅reverse_span proof第151行将separate simp包成`(try simp only [Fin.reduceFinMk])`，增加6字节且保CRLF；处理部分case已无Fin.mk时simp报no progress。没有定理statement、数据、edge/exclusion/StateAt/cost/threshold变化；正反唯一行投影逐字核同。此处不声称修复后普通验证必然成功。

Core、Localization、Counting、Final与整个wrapper、trusted输入均逐字从draft-v2复制；三个public statement types仍等原wrapper，去除空白后等captured official。新Solution为1,829,993B，SHA `1d4630caf44a11f0532d1c93a9029d9b6ede2039a37f8ee0e420736fcccfdeba`；余量170,007B。draft-v3/files.json SHA为 `6440e71dd49ef31704f2c331d03af83abfd8bf9eabeca54c479bac44e755c8cb`（18项）。v2flat↔v3flat也恰为同一proof行+6B。

初版纯文本生成器误假设live canonical Graph等于prior draft-v2 Graph，在任何draft-v3目录/文件创建前以assert拒绝。该未封初稿保存为initial-generator-refused-v0-assumption.py.txt。正式新生成器改为核live canonical仍固定v0 SHA a2e4…，并在结束时复核不变，随后只执行一次成功文本生成。没有compiler尝试、自动proof修复、旧冻结文件改写或主轮计数变化。

普通stage v0/v1/v2的真实失败都应保留；Core/Prefix单独PASS只供开发预检。最终production仍须完整fresh source/lib、零candidate olean复用、原完整3200秒/Comparator/双内核合同。官网材料作者按用户明确授权为Li Xiang；实际验证和提交由root执行，本包未声称完成原纪录目标。
