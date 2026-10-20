本包封存一次固定 v10 完整单文件资源编译的真实未通过终态，不是新编译或重试。原工作目录为 tmp/w9a2-20261021/v10-resource-v1；六个小文件原样复制到 work/，清单记录各自字节数及 SHA256，原件保持不变。

Root 报告原 session52977 的 write_stdin 工具 b5f2ab 实际 outer exit1；现有 child/terminal 记录为 parent51828、child3292、child exit1。root-outer-observation.json 明确这是 root 提供的原工具结果摘要转录，不是封存代理对原句柄的观察，也不是原工具 raw payload 下载。Root 随后先误读 stdout.log、再由92eeef正确读取 stdout.jsonl，仅属终态后 metadata 文件名修正，不是编译失败原因。

terminal.json 的 SHA256 为6a4f47836286ed5e3dd5c1c2e6f92dbb693df1f7100ba0c64851cee3fd006253，elapsed711.7030000000013秒，25次内存采样；实际 peak RSS6815944704B，peak process commit11880390656B（只作诊断）。runner 的 RSS stop=false、timeout=false，compiler_resource_gate_passed=false，candidate_compile_and_C_generation_completed=false。未宣称三个成功输出存在，也不把失败说明为3200秒超时或7GiB own-child停止。

stdout.jsonl 为8379B，SHA256 1d681ad8ce6cea19a7bdf97b4e873af7047427d49e66d4032c15bc5184b5c1ea；其中10条warning、1条information、4条error均可逐行解析。13611:2、13793:2两条明确报告decide的Decidable实例可被elaborator约简，但kernel发生excessive memory consumption；16954:8、17030:8两条报告同一kernel内存错误。位置来自日志，不在本任务进一步定位源码声明。stderr.log为空，不能据此声称stderr abort。上述记录不确认OS OOM、不构成数学反例，也不证明其余完整源码或独立内核通过。

源与gate身份仅引用现有terminal中的pin：source1914823B/SHA86e3f46c90648f98d540d01edd45268d89504b45f7fb9d5d8e53d8582d41e14d；gate SHA96847d97642be0c1a6c56c6191275f157c6907af659f7902ca1c8b2d0e8ee0ba。本封存未重新散列大源码、SDK、包库、runtime闭包或输出树。资源门仍是Windows -j1/-M6500/7GiB peak RSS/3200秒的单次compiler/C生成诊断，与官网Linux资源限制、--setup及完整双核流程不等价。

冻结DRAFT-v10中的pending启动快照是历史记录，保持原字节；本终态另行封存。无Lean、compiler、export、额外kernel、进程查询、网络、网站、重试、Git或状态/计数动作；官方未通过、独立双核未完成，完整goal仍未完成。
