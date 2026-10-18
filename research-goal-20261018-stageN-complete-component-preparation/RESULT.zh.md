# N 唯一执行：持久化替换失败，未完成全域

root gate 为 `stageN-complete-pooled-component-20261018.json`，SHA256 `8bc67b572594e68af94a2f6ebac787942f7a061d7c7167bb8c8eb38ab5223d09`。准备源、参数、原source、输入与外部 runtime 均未修改。

唯一 launcher 实际 parent PID47764、child PID32868，工具 session1259。child terminal exit1，launcher 记录71.6254713999806秒，未触1800秒或160MB hard资源上限。`terminal.json` 与 stdout/stderr 文件均由实际运行保存；没有重启或重试。

失败位于 `os.replace(prefix.json.tmp,prefix.json)`，WinError5/PermissionError。不是已知数学检查失败。进度读取曾用 Windows `Get-Content` 读取 live prefix；缺少 delete-sharing 的短暂 reader 可能阻止 replace，但没有保存到具体锁所有者的证据，所以这里只记录可能原因，不作确定归因。

只承认已 atomic 发布的 prefix：675条，包含674个新的 pooled-envelope Lower 和1个既有 M deduction。其最后 Gindex 为433464，真实调用记录前缀为674次。675次 LP 已实际开始并有原始 native 记录；第676条 Gindex436241 的证据和计数先已落盘，随后 prefix 替换失败。failure 中 in-memory committed_records676 不等于 accepted published675。保留 `prefix.json.tmp` 和 gzip 尾部，但不将它们升级成已发布证明。

已发布675条全部仍待另行独立数学重放。没有完成15,378项，没有得到首个 exact Below，没有全域结论；未访问后缀不归入 unresolved 或 closed。下一个独立检查如获授权，必须按 published byte offsets/hash 读取，不直接把 gzip EOF 全部内容当 accepted 前缀。

终止后 launcher 再核全部输入/runtime hash，均与开始相同。此后只做字节/元数据封存，不导入数学 producer，不重放 FS、模型、证书或求解器。`freeze_result.py` 只记录全文件与 committed byte-prefix 的 hash，完整原始尾部保存不删。

本包没有实际 Lean、无条件新比例、网站2MB源码/3200秒通过或提交就绪声明。该基础设施故障也不证明 pooled 方法不能完成全域。
