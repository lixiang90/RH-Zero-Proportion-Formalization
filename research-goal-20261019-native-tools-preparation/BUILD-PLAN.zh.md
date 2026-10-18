# 原生可信验证工具：静态构建计划

本包没有运行 Lake/Lean/C compiler/linker，没有生成候选源、导出或数学重放。只读 SDK 文件盘点的 WSL Python 句柄66513和33815均已exit0；SDK内容/链接配置摘录保存在 sdk-details.json。`build_native_once.py` 是待root审查和单独gate的安装脚本，当前prepared不授权执行。

## 官方路径与性能假设

官网固定ref0c038980cbfaa3ee9fc539d751c32c454d85a319的 install-verifier-tools.sh（SHA80abf99b…）明确运行 `lake build comparator lean4export`，之后以原生可执行文件工作。锁定 Comparator/Main.lean:134–150 的safeExport直接调用whichLean4Export，而不是lean --run源。此前本地cold-v0只生成工具oleans，再用 `lean --run ExporterMain.lean/CoreAudit.lean`；Export/Comparator运行时目录没有对应.c/.o/.a/.so。原生化可能减少自定义JSON解析、比较及driver代码的解释成本，但这不是已经测出的原因或速度保证。默认Lean kernel自身的固有成本也不会由此消失。

## 工具与源码闭包

新项目只复制锁定归档的九个现有可信源：Export、Export.Parse、ExporterMain（原Main逐字节）、Comparator、Comparator.Axioms/Compare/Util、ComparatorMain（仅保留来源，不作为本轮target）、原 tools/ComparatorCoreAudit.lean。CoreAudit的SHA固定7e88e84d…，完整statement/dependency/primitive比较、标准三公理闭包和env.replay代码均不改。包LICENSE原字节各保留一份。

独立lakefile没有require；新lake-manifest.json的packages为空。仅两个原生targets：lean4export root=ExporterMain且supportInterpreter=true；coreaudit root=CoreAudit且supportInterpreter=false。后者与官方comparator的默认设置相同。所有源import只能为上述九模块或Lean，不引入Mathlib/Zeta23/ChallengeDeps/用户源/用户olean，也不触发项目Git依赖或网络fetch。使用固定SDK的绝对lake路径，PATH不含elan代理，环境不继承LEAN_PATH、CC/CFLAGS、LD_PRELOAD或用户build设置。

SDK Lake源码证据：LeanExeConfig.lean:68、77–82规定supportInterpreter及oExportFacet；LeanExe.lean:84–114在Linux为exporter加-rdynamic，仍静态链接Lean；Build/Executable.lean:22–31通过linkInfoExport/NoExport和buildLeanExeSync构建原生对象与链接。故不手拼猜测的leanc/cc链接参数，交给同版本Lake产生.c、.o或.o.export以及ELF。

SDK盘点确认lake/leanc/bundled clang/ld.lld、lean.h、libLean.a/libInit.a/libStd.a/libleanrt.a及多种.so均存在；SDK的Lean静态库约314MB，已具备基础链接资源。尚未实际native build，所以缺失头文件、平台库或ABI/链接错误仍属待执行前置条件，不能把文件存在当构建通过。

ExporterMain仍调用importModules读取未来冷编译用户模块；SDK Environment.lean:2438–2449的默认loadExts=false、plugins=[]，这里不执行用户原生代码或其init插件。读取证明常数/类型/值不要求额外构建Mathlib/Zeta23/用户模块的C对象；仍需要之后原有可信依赖olean及fresh user/spec oleans。CoreAudit从同一导出文本构建环境并env.replay，不导入用户模块。未来完整实际流程仍须检验此接口，静态分析不代替运行。

## 独占安装与绑定

独占目录 `/var/tmp/rh-zero-20261015/tiny-native-tools-v0`，镜像 `tmp/current-s1r-tiny-20261018/native-tools-v0`，任一存在即拒绝，0自动重试。root必须确认所有compiler/proof handles真实terminal后才能写新gate。工具安装可在未来proof t0前完成，作为与官网template预装工具相同性质的可信setup；绝不在这一步编译用户证书或提前运行任何export/kernel。

脚本依次核固定release/archive/source pins，绑定SDK完整bin/include/lib、编译驱动和linker、系统C头、GCC支持/CRT对象；然后从归档复制原源和许可证，冷创建无外部包的Lake工程，用绝对 `lake -v build lean4export coreaudit` 构建。SDK lake/clang版本写log，生成C/对象/olean/ELF逐件hash。固定Lean二进制SHA、release归档SHA及原解压marker均检查；SDK/C文件在构建前后完全比对，既记录内容也记录symlink解析目标。

产物须为可执行ELF。只对可信ELF（包括SDK编译驱动）执行ldd；脚本型ldd自身只hash，不拿它作为ldd目标。记录和绑定两个新binary及其全部解析到的必要.so/ELF loader路径，拒绝not found；同时记录所有生成artifact、原源和SDK/C输入闭包。安装receipt表示可信工具已构建，proof_runs恒0，不代表候选通过。574,905,502B Lean SDK归档只作external read dependency，不能搬入Git。

## 未来冷proof的明确要求

新的proof入口仍须由根另审查/另gate。其monotonic t0必须在新工具receipt、binary、runtime.so闭包hash校验以及候选生成前开始；全部fresh用户/spec ordinary、两个完整native exports、native CoreAudit的所有检查、独立nanoda和最终hash/receipt都计入3200秒。只可省掉已经预装并全绑定的可信工具重编译，不得省用户编译或先前失败阶段。

运行native exporter时固定LEAN_SYSROOT为同一SDK，LEAN_PATH仍限定fresh lib与可信package paths；SDK Path.lean:180–187确认显式LEAN_SYSROOT可避免在PATH中找错lean。CoreAudit参数和三个roots/全部primitives完全沿用原配方。新运行应选官方同分支的nanoda num_threads=0或1串行，不通过升线程制造local时间PASS；公理白名单、hard_error和全部声明重放保持。仍不执行landrun官方隔离，不声称网站接受；官方平台/资源/attestation另待实际验收。

执行形状（本包未执行）：

```
wsl --distribution Ubuntu --exec /usr/bin/python3 /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261019-native-tools-preparation/build_native_once.py --gate /mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261016/gates/ROOT_NATIVE_SETUP_GATE.json --gate-sha256 ROOT_NATIVE_SETUP_GATE_SHA
```

这只是实现方式接近官方native+serial的具体方案。无新性能测试、无削弱检查、无旧失败转成功、无已完成声明。
