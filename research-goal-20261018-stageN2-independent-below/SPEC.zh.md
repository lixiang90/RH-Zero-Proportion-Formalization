# N2 固定首 Below 的独立审计准备

固定 N2 final manifest SHA `327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f`。这里只准备源码/AST/字节哈希，不执行数学。root 另 gate 前不能 import 或调用任何 audit/parser，不运行 solver、RREF、点/核或 Lean。

数学 scope 仅固定 Gindex1322606 = cells278/665、rev/id：从我方 ownA 原源 parser/packing 及冻结 v1 的独立 FS/geometry helper 重建两个原 cell 的 cursor/FS/semantic/82 个原正质量 anchor guards、原 lb、全部155几何与所有原组件；按相同物理 span 汇成42组，独立核51变量/52坐标、305行的原 primal 可行与 objective<固定target，并核两窗旧 M0 floor。若原记录含 dual，亦重新核其全部非负/full52/成本，但 Below 不依赖有效 dual 或最优性。producer model JSON hash不当证明；独立 row 语义另算hash。

只 import 我方冻结 `stageN-independent-v1/audit_once.py` helper 及我方 ownA parser；后者使用我方 ownpacking。不 import N/N2/M/I/J producer，不重新求解/修点/换support或新选FS。helper仅被调用构造固定原源 rows 和核已保存原 primal，没有执行其旧675审计入口。

附带完整 metadata scope：N2 全2375个 commit 的 canonical LF、ordinal、originalH升序membership、previous/body SHA链、累计类别/旧新调用数；三个新gzip stream的每个member/hash/CRC/EOF及每commit的增量前缀hash/member边界；旧676 recovery wrapper到冻结原member、旧native和新native/intents/model引用；原/新component cache引用及零重复旧LP索引。明确 combined=2373 Lower+1已有M deduction+1首Below、old675+new1699 calls=2374，未覆盖完整15378。

这些metadata引用核验不等于重审其他 Lower 数学。其他2374记录只做metadata/引用检查；不能写全Lower数学通过或全域floor。旧675与retained676已有独立审计是依赖，原历史不改写。固定 Below 仅证明这个 pooled 原组件下界模型不能统一达到目标，不是真实 F 或 RH 新比例的反例。

N2 new record不含 row_count/stateSHA时，直接由原 cells/source重建并核305行，不信缺省字段或另造 producer metadata。root gate同时钉 prepared、producer final 与端点。一个child、无重试；初建议hard300s/20MB输出。commit前缀增量hash总读一遍文件，完整gzip约19MB原包，数学只两个FS；内存保留member JSON，峰值未实测。完整 source≤2m、正式 Lean与全局方向不由本审计解决。

root gate 后唯一CLI：

`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageN2-independent-below/run_once.py --launch-authorized-once --gate <ROOT_GATE> --gate-sha256 <ROOT_GATE_SHA256>`
