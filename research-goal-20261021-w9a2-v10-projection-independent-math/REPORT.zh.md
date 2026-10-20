# v10 全大根分块源码的独立静审

PASS_STATIC：冻结producer规则、实际source模板及全raw投影无已知确定阻断。未运行producer、流读归档、解WL、重算能量/余量、运行Lean/compiler/kernel/export；不是新proof或资源PASS。

实际v10为1914823B，SHA86e3f46c90648f98d540d01edd45268d89504b45f7fb9d5d8e53d8582d41e14d。按22个新byte offset剔除helper+新root行并放回原root行，内存中逐字还原v9的1861120B/SHA7552bbb8…8c99。每个原行同时与实际v9对应byte offset一致。故插入/替换范围外所有字节保留，包括数学fraction/K、许可归属、数据、全部其他proof与三个公开根。135个zfNat64的bitlength+payload逐项精确相等，221CRLF及单个末LF保留；source余量85177B。

22根为2,3,4,5,6,8,9,10,11,12,13,14,33,34,35,36,37,38,40,41,42,43。它们恰为packet中numeric>256的根；其余26根的原rcOf行保持raw。48个根name/type、RC indices与end均保留。每个helper使用独占v10_rN_前缀，置于原WDN已定义后的同Data namespace、原rcN之前。

对全部22 helper block，独立依据固定packet重建已通过pilot的源码模板，并与实际源逐字及替换hash核同。51份state各73Nat、M0、canonical紧凑JSON+LF hash与packet相等；fuel=128-depth，至少该archive子树height；pos/end正确。所有子目标均原raw walkCut/空cuts、decide +kernel；各非0经原walkCut_ok产生当前Covered(toCl s)，按相同顺序cutsOk_cons；父唯一walkCutR fuel128/pos1，原完整RC入口、M0和原end，经rcOfC保持原根命题。新块没有旧rcN/run、native、axiom或checker替代调用；实际父完整St匹配仍是待执行义务。

固定规则为仅大根、top-down maximal frontier<=256，再选>=64。packet的frontier阈值、选择、区间不重叠与分区和逐根核一致：51块数值叶合8424，改变根的父剩余1804。最大cut为256；父并非<=256，root37剩290、root5剩263，均正常保留给父原检查。没有据此变更规则或隐藏剩余。共73个新的子/父cursor +kernel义务替换22个旧whole-root义务，26个小根仍原检查；不推断总时间或峰内存下降。

静读producer de56b349…确认：固定输入、全部24504 geometry/M0 state hash及48源端点先核后生成，NEW目录/xb无覆盖，30秒和2MB source/2MB metadata/4MB total停止门，无Lean/数值模型import/WL decoder。producer实际exit0/1.775秒由root报告；全24504 hash不是本审查的第二次archive replay。实际prepared两manifest及所有列出成员当前bytes/SHA核同，关键pin列于input-pins.json。

审计小修正：首次完整模板和raw逆投影已过，随后packed计数正则漏掉bitlength参数而停止；只修审计匹配式后135项精确相等。未修改或重跑producer/source。冻结结果现在停止；root须另行冻结单文件实际资源门，不能借cached Core pilot宣称全文件或官网通过。
