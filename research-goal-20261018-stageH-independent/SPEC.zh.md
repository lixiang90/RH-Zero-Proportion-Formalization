# H 独立审计器：仅准备，不执行

本目录只准备 stdlib 审计器和静态 AST/pins；未调用任何数学审计入口。
producer 由 lean_cover_goal 另包负责。独审不 import H/C/G producer Python，
不重做 Floyd/BF、路径/运输、unit assignment、LP、FS、核值或 Lean。
发现器采用多少 rays/assignments 均不是本 checker 的可靠性前提。

## 固定输入和行模型

G producer manifest 为 `93d7b1af5248aac7867e81bed3f1866b5d9c844c622f0a0ca01f28db2656972b`。
G 独审 manifest 为 `af09979447c2054f1daaa5a19e6abc59d04decee7752dfc53fe66c0643e30dc6`，
receipt 为 `291f15a57642f8be1e0556671e41e5d4791d29380fb2fc057640c089976b5ce7`。
全部 G range 5,635,876 的 status/bitmap 自行逐位核对，独立提取恰好
19,838 个 status=3 的原序号，严格升序、不漏不重。不重新判几何。
index 仍是 `((i*1187+j)*4+chart)`，chart 为 id/id、id/rev、rev/id、rev/rev。

从冻结新 source f82a4914...736cf 的 PR literal 及 B 原 state 直接重建每条
所需原行，保留 36-span 原顺序、完整 10 坐标和 X=20*32768*p 实坐标：

* 0..71 左窗，72..143 右窗，每 span 先 upper 后 lower；右窗 offset=1。
* 144+r 为 `X_r-X_(r+1)<=-17*32768`，即实 sep=17/20。
* 153/154 是两原 Ordered 四点行，RHS=0。
  id normal 分别为 `-e0+e1+e7-e8`、`-e1+e2+e8-e9`；
  chart 的反射只将对应 normal 乘 -1。

每条 Empty 记录只核：sourceRowIDs 在 0..154 内严格升序唯一，给出的
整数权严格正，完整十坐标加权和为零，原整数 RHS 加权和严格负。
这给出真实约束之和 `0<=负整数`，不需要相信任何发现算法的最优性。
零成本不能排除。未给 Empty 证书只保守记录 unresolved，不声称非空。

G 已独审的原 index 2417 有满足 153 行及两 Ordered 的点，故 H 必须把它
保留为 unresolved；本审计只引用该固定 receipt，不另找或评价点。

## HRC1 证据和前缀

`certificates.bin` 首五字节为 ASCII `HRC1\n`。每 record：

1. uint32LE 原 G index，必须等于上述固定序列的下一项；
2. tag:uint8，0 表示 unresolved，无 payload；
3. tag=1 表示 Empty，接 count:canonical ULEB128（1..155），再接 count
   个 `(rowID:uint8, weight:canonical positive ULEB128)`，严格 rowID 升序。

producer 每 256 record publish 原子 `prefix.json`；审计不信任发现器搜索，
仅验证已发布字节、所有 claimed Empty 和精确 EOF。完整必须恰有
19,838 records，不额外删除 known F 或其他 index。

prefix 固定字段：committed_records、committed_bytes、certificate_path、
certificate_prefix_sha256、counts:{Empty,unresolved}、
input_index_sequence_sha256、committed_index_sequence_sha256、last_G_index、
remaining_indices_path、committed_remaining_bytes、remaining_indices_prefix_sha256。
index-sequence SHA 是逐 uint32LE index 的拼接 SHA。remaining stream 恰为
当前已处理 tag0 indices 的 uint32LE 拼接，不包括未访问 suffix。

result.json 固定 complete_G_unresolved_classification、expected_records=19838、
total_G_cases=5635876、prefix_sha256、counts、上述 committed_* 和输入起止 SHA。
完整时 certificate 与 remaining 两流都必须精确 EOF；partial 必须显式
`--prefix-only`，只认 published bytes，未处理 suffix 永不计入未解或闭合。
完整处理不等于全闭合；unresolved 仍是全域目标缺口。

## 后续书面授权接口

root 另行不可变 gate 需要这些独审字段：

* independent_result_audit_calls_authorized=1；
* independent_audit_script_path/sha256（本 audit_h.py 最终准备 SHA）；
* stageG_producer_manifest_sha256；
* stageG_independent_manifest_path/sha256、stageG_independent_receipt_path/sha256。

只有 H producer 完成并冻结、root 明确授权后才执行：

```text
C:/Python314/python.exe research-goal-20261018-stageH-independent/audit_h.py --verify-authorized-H-result --gate <root gate相对路径> --gate-sha256 <SHA> --producer-manifest <H manifest相对路径> --producer-manifest-sha256 <SHA> --write-receipt
```

当前没有运行结果。若以后失败，保留原失败，不自动修复重跑。
本独审不证明全域新 floor、无条件零点比例、网站源码或 3200s 预算。
