# F 一次生产执行：返回 primal 被拒绝，原始 dual 保留供另包独审

PREPARE.zh.md 和preparation.json是执行前的静态材料。实际执行由
research-goal-20261016/gates/stageF-exact-lp-20261018.json授权，SHA
02015ab778511ce8ae424e488ce95ee28f4e34990e96aa5db8c0f4608c76a90d。
root已核三份prepared脚本、E独审/static/runtime pins。本次未改脚本。

child PID51572、parent PID57748；child4.2019084秒，parent4.6882262秒，
exit1。没有达到300秒/20MB上限。模型只组装固定exceptions1/5、id/id，
原两FS/state、153DBM+两真实Ordered；C/b逐term与自然数写法已在求解
前精确一致，model.json及affine-components.json已保存。

只调用一次Sympy1.14.0._simplex primary，返回o/x/y后先durable保存到
primary-raw-result.json，随后验证155条primal。原生产脚本line182的
全部row可行检查失败，程序按约定fail-fast，未生成result.json或certificate。
failure.json/stderr.log保留完整stage和trace。primary没有抛出
InfeasibleLPError，所以条件Farkas辅助call没有触发；不能因此擅自调用
第二次LP。没有参数/solver/符号修复、没有换pair或自动重试。

close_failed_run.py只用stdlib从已经保存的返回primal算各row差，不
重新组装source模型、不import生产器/Sympy、不读取dual来恢复证书。
保存38条违例、所有数学输入的start=end hash，以及外部simplex.py
前后hash一致；该脚本未执行新优化/核值评价。它不能说明模型不可行。

verify_certificate.py要求已生成result.json和certificate.json；本次
fail-fast没有满足其前提，因此没有调用该checker，更没有伪称证书通过。
这与后续另一代理直接从rawdual独立检查是不同的执行：后者可以只验证
非负权、完整10coordinate balance和target cost，而不依赖失败primal。

## 不把生产guard的失败误当数学否定

本生产guard同时要求一个可行primal和matching dual，足以确认声称的
minimum。它在primal处拒绝，并未完成rawdual验证。单独一个精确有效
lowerdual不要求matching可行primal，仍可证明Lower；仅不能称optimal。
root已另委托代理从原sourceFS重建模型并审查rawdual，证书必须另包
封存，不改本次失败历史。本包不提前代称那项独审已通过，也不声称
这条affine路线失败、155row系统为空或目标不可能。

外部运行时只读身份（未复制安装包）：

    C:/Users/ip/AppData/Roaming/Python/Python314/site-packages/sympy/solvers/simplex.py
    bytes35276
    SHA a5e46fe38683337d14ff4c24f3166fdede8cfdca66fdaf610402e2cabef39dd6

三份prepared脚本保持原SHA：

    solve_fixed_once.py b3b1125cbae80c2bb5c5860b85bf51b8f8b14f8a9775c90fd024a15cab88340f
    run_once.py a396851c10984c08abfaa0436c20d3de87a8048c1db90c6c690507f418319844
    verify_certificate.py 5db5ff9a1de0d0e4c3326f4b385b38b1943c9c7dbc222d34e6f7aa2cdf32e05d

本包只记录一次实际生产尝试及拒绝返回值的证据，没有新的全域joint
floor、无条件零点比例或网站验收。完整source/runtime预算仍未知。
