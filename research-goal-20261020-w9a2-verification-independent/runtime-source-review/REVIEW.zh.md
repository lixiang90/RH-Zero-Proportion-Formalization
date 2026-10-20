# 运行时闭包助手 revision2 独立静审

结果 `PASS_STATIC_EXECUTION_STILL_REQUIRED`。审查对象为准备清单 `6c22815d8d200bca43e92886a926daf1ecdb3d6840f0080a7bd85179dbfe72f7`（46 项），assemble.py `550762bc42b133ae6290407526b4bce2d54cd71d432a06ea2038965ebf997aa9`，cache_binding.py `76d5d5add51c61bfa21a7d51bb4ef912dbe1e95a6eac681cc239ffd947c9cd62`。58 个读取输入前后长度和 SHA256 相同。旧准备版本全部保全；本目录保存两个相对 archive-pre-review-v0 的完整差分。

本审查不 import 或执行助手、assembler、SDK DLL、Lean、导出器或内核。只读取源码、AST、清单和现有收据，并与当前 SDK/Mathlib 的源定义比对。

借用哈希对象布局符合当前 x64 lean.h：header 为 8 字节，ByteArray 为 24 字节头加原始数据，String 为 32 字节头加 UTF8 数据和 NUL。size/capacity 包含 NUL，length 是 Unicode 标量数。两个导出声明均为 borrowed 参数，代码只传调用者拥有的常量缓冲区。mix 逐式匹配 lean_uint64_mix_hash，包括 `k ^= m`；list 初值 7、UInt64 identity、Lake 初值 1723、Cache generation5、相对路径分量和逐 import 顺序均与当前源码一致。实际官方 SDK archive SHA 和逐 member 比较在 SDKHash 的 DLL 加载之前；这仍需实际执行成功才能确认。

已检查的缺口修复包括：outputs 字典递归遍历、精确 CRLF 归一、import header 对 public section/public meta section 的原子回退、旧 Comparator 收据引用 nested exporter checkout 的实际源码路径、固定 Comparator/exporter/Nano commit、历史 Python 已加载文件的当前 SHA、各包固定配置 Git blob，以及拒绝 Python -O。最新差分仅含这些来源/控制补强，没有新数学或 proof 执行。

Mathlib 缓存按固定源码及导入闭包重算官方当前 Cache.Hashing 文件名键，核对应 ltar header 的 Lake depHash，再核 trace 描述的实际 olean/private/server/ir/ir.sig 数据哈希与 sidecar。范围明确采用当前项目的本地缓存协议，没有把 HEAD、basename 或普通编译 PASS 当作来源，也不声称官方缓存签名。Zeta 旧 trace 的 9 类输入、源码、选项、包名、模块名、导入 art 哈希、递归 legacy 哈希和完整 depHash 都由算法逐项核验。

旧四 Comparator olean 与 nested Export.Parse.olean 的实际 SHA 已由历史 same-SDK CoreAudit 收据逐项钉住。源码字节、规范 LF Git blob 和旧实际路径桥保留。原生 exporter 和 NanoDa 同 SHA 的旧 source-bound 记录、固定源码和构建记录可复用；本审查未发现因文件年龄而必须重建它们的理由。

应用 PE 闭包包含实际 Python 扩展、历史同工具链 Lean 加载路径及解析出的应用依赖。Windows System32/API-set 被明确列作主线程批准的安装系统边界；不要求递归加载 84 个 OS 可选 delay imports。包/工具 overlay 为新建干净目录，不借用候选 user module。

没有剩余已知的确定代码 blocker。实际 opaque hash 控制样本、全缓存核验、复制、DLL/ELF 真实字节与最终收据均仍须执行并由主线程确认真实 terminal exit 0；此静态报告不证明 complete runtime closure、当前候选内核验收或网站接受。
