# G 完整四流、逐项关闭证据与保守未解集：独立审查

本包一次完整独审通过，覆盖全部5,635,876个固定 cases，未抽样、未重做
BF/几何搜索或只核计数。结论是生产 G 的每项 claimed closure 都有正确
原始证据，19838项仍为保守 unresolved；这不是新的全域 joint floor。

生产 manifest SHA 为
`93d7b1af5248aac7867e81bed3f1866b5d9c844c622f0a0ca01f28db2656972b`。
root gate SHA 为
`1ff39dcea19f6db3fa4b49c8036dfc8b7a22728e00994ef8147173011395acb7`，
路径 `research-goal-20261016/gates/stageG-complete-classification-20261018.json`。
source 仍是1,818,411B，SHA
`f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf`。
生产源、原 B/C/D/F 包和治理文件均未改。

## 唯一独立执行与输入来源

`audit_complete.py` 只用标准库和我方冻结 A 的实际 source parser，不
import 生产 classify/replay/geometry/BF Python。B 的完整1187原 states /
Mi 从我方已经逐叶、逐原 FS 独审并冻结的 B 数据链读取，不使用 G 复制
的几何或分类计数作判据。B 独审 manifest 为
`e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288`。
每个完整 state SHA、原 Mi>=0、tau margin=Mi-T<0、原 pair 顺序与
source 全36跨度重新匹配；反射映射和反射两次恒等也独立检查。

执行前只有 schema/syntax 审阅。唯一实际独审 PID46076，5.2077129秒，
工具 chunke28dd4 真实 exit0，无失败或重试。receipt SHA 为
`291f15a57642f8be1e0556671e41e5d4791d29380fb2fc057640c089976b5ce7`。
全部绑定输入 bytes/SHA 运行前后相同。生产自己的 replay 曾在打开
流文件时 TypeError、尚未验证 case；失败源和历史记录保持原样，本包
独立完成全部验证，不把那次失败改写为成功。

## 逐每项证据的独立核验

固定 index为 `q=((i*1187+j)*4+chart)`；chart0..3依次为 id/id、
id/rev、rev/id、rev/rev。每个 source pair 的四 chart 恰在同一 status
字节，低两位为chart0。独审按真实索引序读满全部状态。

* paid：直接用原 Mi+Mj 与由 source scales 构造的
  T=kappa*(tauN-c9N) 比较，保留 equality。scalar条件与chart无关，
  因此一次原 pair 的 exact付款同时验证该字节的四 chart，强制四个
  status均为paid。没有改成Nat floor或别的余量。
* strict_projection：每项读取给定共享 spanID和direction，从原 B
  bounds及该chart的逆映射独立取值，核严格 lower>另一upper。
  对应两原 edges 权和为20*(upper-lower)<0；全部3507051项都核，
  接触端点不会排除。没有重新搜索28span来相信生产分类。
* other_strict_cycle：每条记录由原source的153 edge IDs直接解码，
  核长度1..10、IDs合法、首尾连续闭合及 signed 总权严格负。
  全295条都核，没有BF/Floyd或选择另一个cycle。
* unresolved：仅表示没有提供排除证书。独审不要求重做 feasibility，
  也不声称其盒非空、ordered交集非空或实际低能。

所有非paid状态都另外核 exact Mi+Mj<T。全局 F 个例仅在新index4768
注记为 unresolved，未计入 G closure。

## 完整分类结果与原始流身份

| chart | paid | strict_projection | other_strict_cycle | unresolved |
| --- | ---: | ---: | ---: | ---: |
| id/id | 527173 | 877065 | 62 | 4669 |
| id/rev | 527173 | 876315 | 136 | 5345 |
| rev/id | 527173 | 876606 | 35 | 5155 |
| rev/rev | 527173 | 877065 | 62 | 4669 |
| 全部 | 2108692 | 3507051 | 295 | 19838 |

687个8192-case满frame及7972-case尾frame共688frame。每帧独立核
canonical JSON、body SHA、previous-commit hashchain、连续index、
四流byte offsets和prefix SHA、raw SHA，以及恰一个完整gzip member。
每帧计数从实际status/证据重新计算，再与log/prefix/summary匹配。

unresolved bitmap从每个status=3独立重建每一位，然后逐字节匹配，
包括尾部4个padding零位；没有相信生产bitmap或只核其hash。
四流与commit log均核完整文件EOF，数据不包含未访问suffix。
状态流1,408,969B，bitmap704,485B；projection原始3,507,051B /
encoded1,328,952B；cycles原始1,571B / encoded15,240B。
每帧包含一个gzip member（包括空payload），不是每record一个member。

关键身份：

    prefix SHA   afaf3c0a3d33585164fabc4722cf04ecd34a0d48a6513b5a1a7e5d174a8322cf
    status SHA   dd1ba64fb4202dd23a904830762b9a1ce23d83f0321ea5b2d12a8813d1b83c64
    bitmap SHA   fd103f69ee92c5a918ded4c8a06662642b7ef652398204957620f1105bd2a9b1
    summary SHA  f2be52b6daedf040b1199fb4894199bd5a586240a273eda074cb6b2f7f80e329

## 未解集的语义与完成边界

可选首unresolved sample为index2417，id/rev。只有该保存样本的全部
153条约束与两侧actual Ordered均另行独立核真；它不证明其余19837项
非空，不推断任意实际F9低于tau。该样本同时说明纯Ordered-empty层
无法关闭全部G未解；至少此样本不能由几何空性排除。后续如分析能量
下界或别的证书，须另行授权并完整证明。

G得到完整保守残留表，而非全局候选floor成功。仍需处理未解项、证明
source analytic强floor/affine域桥、真实product coverage、WCert及计数
matching，并完成2MB单源与ordinary/export/Nano总时间验收。仅原始
status+bitmap已约2.11MB，不能直接当网站Lean source；压缩研究证据
通过20MB限额也不填补网站源码和运行预算。

本包无新核值、新FS、点拟合、优化器、LP、BF/新几何搜索或Lean。
未更新root计数或旧冻包。new global floor / 无条件纪录 / upload-ready
均为false，完整source/runtime预算仍unknown。
