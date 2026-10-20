本包将已封存的 `core-repair-v1` 与原 `draft-v0` 合并为新 `draft-v1`。仅进行字节审核与文本生成；未运行 Lean、exporter、Comparator、默认内核、nanoda、数值搜索或安装。旧 source、draft-v0 与原 delivery manifest 均保留并复核。

输入为 `research-goal-20261020-w9a2-core-repair-v1/files.json`，SHA256 `9aafa909450a60295a0864982d8f3f596217fba54c8e04eeeb3a21eede8f5114`。全部 14 项 SHA/bytes 独立核同。完整 Core 的唯一差异位于 `AMW.Cert.PC9QB6M.qTargetFrom_sound` 第 10752 行，为 simp only 清单加入现有定理 `Bool.false_eq_true`。增加 20 个 UTF-8 字节；旧、新源可用唯一行替换双向逐字回投。定理 statement、整个 Data namespace、其余全部 Core 字节及 old Prefix + new suffix = new full 均核同。SDK Bool 源中该定理的类型是 `(false = true) = False`；此处未推断修复后一定编译通过。

Graph、Localization、Counting、Final、整个 public wrapper、原官网模板、ledger 快照及 trusted 源均从 `draft-v0` 冻结副本读取。三个 public statement 对 captured 官网模板仅去除空白后逐字相同。Header 按 AST 读取原 generator 的字节常量，并与已封 `verification-preparation-v1` runner 的常量核同；没有 import 或执行这两个 Python 模块。

输出 `../draft-v1/Solution.lean` 为 1,829,955 字节，SHA256 `8928832f3503d39ad6786ae26a394299779d3a53b7c590e7ca7df793ae7614f3`。距离 2,000,000 字节上限余 170,045 字节。`../draft-v1/files.json` SHA256 为 `bde018dbebf0664f5cbc002100d777bd2bcead0a8ce6e2fb75d3d12145999c10`，绑定 18 项文件；包含完整冻结输入、源绑定、独立字节审核与 flat 单行 diff。原 flat 向新 flat 的唯一变化仍是上述 +20 字节 proof 行；反向替换逐字得到原 1,829,935 字节 flat。

生成器命令已经仅以文本模式执行过一次：

```powershell
C:\Python312\python.exe -B -X utf8 research-goal-20261020-w9a2-delivery/repair-v1-preparation/generate_draft_v1.py --freeze-once
```

输出目录已存在时生成器拒绝覆盖。不要再运行此命令。真实完整验收由 root 的新 gate 选择 `draft-v1` 路径、上述 manifest/Solution hash 与 bytes。冻结 full runner v1 不需更改；它会在统一 3200 秒 deadline 内重新生成 exact source、trusted spec 及 challenge，再执行原完整链。此处旧 ledger 只用于准备；真实 gate 仍须 fresh exact record 检查、完整 runtime 来源与 loader 闭包、新建 source/lib、锁定 CoreAudit、两个 native exporter、默认 Lean replay、serial nanoda、三份 fsynced receipt、最终完整 hash 和外层真实 exit0。

修复后的 ordinary、Comparator、两个内核、3200 秒实测、官网接受和原始无条件零点比例新纪录目标，均仍未由本包完成或声称。主轮计数未改动。
