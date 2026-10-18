# J：固定原 FS、固定九行 basis 的全 H 余项机会关（仅准备）

本包只准备一次有界执行；准备阶段不 import producer/parser/math，不提取 FS，不计算矩阵、点值、核值、LP 或 Lean。I Phase1 的原点必要关通过仍不是全域结论；I 独立审查通过及根部另行不可变 gate 均是实际执行前提。独立 J checker 的源码不是 producer 的数学输入。

## 固定范围与停止条件

输入为已冻结 H `remaining-indices.u32.bin` 的全部 15,378 个原 G 索引，严格升序。G 编号 `((i*1187+j)*4+chart)`，四朝向依次为 `id/id,id/rev,rev/id,rev/rev`。2417 必须在内，历史 F 索引 4768 不在内；后者已被 H 判空，其旧 Lower 不提供真实非空域收益的证据。

唯一 basis row IDs 为 `[9,29,36,74,84,110,130,153,154]`。每 chart 单独精确计算其固定 9×9 reduced basis；奇异则该 chart 全部保守未解，不更换行、阈值或模型。所有 H 索引都要处理，不首未解停止。一个 child，soft 270s/19,000,000B，hard 300s/20,000,000B，目录全部文件计入；partial 只承认 durable prefix，不补填后缀，不重试。异常、stdout/stderr、输入首尾哈希均保留。

目标不变：`Q=32768, SA=10^20, kappa=Q*10^10*1024`；`cN=893766123055294719`，`target=4*kappa*cN`。不选择新 FS、点、anchor、核参数、basis、optimizer 或 Lean。没有新的无条件比例、完整联合覆盖或网站单文件/3200s验证结论。

## 原叶提取与共享缓存

`original_affine_core.py` 由新静态文本生成器从已冻结 I 源 `extract_original_affine` 原函数逐字抽取，仅把固定两叶 payload 长度 lookup 替换为各 B 原 witness 的 `consumed_payload_bits`。原 I `locate_original_payload` 作为运行时依赖使用，原读窗仍为 480 bits；A/B 已逐叶约束 payload≤478 bits，不能擅改为不同解码协议。

每个 needed cell 只提取一次：保留 root/path/原 WL cursor、原 branch cuts 及右游标、全部原状态和 SHA、原 34 项 FS、活跃 PT guard、packed/semantic hash、原 compact 与打印 AST margin 相等、完整 consumed bits、原 flow 与坐标 residual 付款检查。原 L0/point 参数不能按 joint 域收紧后重解码。最终 cache 保存 Cstar/J8、原 witness/状态身份及 34 项组件 SHA；不逐 pair 复制 68 项，也不重新选择支持。

对原单窗，`delta=mslT-2D*mwT`、`D=10^9,R=1024,V=10^10`。点无关精确式：

`J_r=D*R*BS_r+Σ_{e∋r} a_e*delta_e`

`Cstar=Q*Σ a_e*mvT_e+10*Σ a_e*(mcpT_e-mcnT_e-delta_e*L0_e)`

`(kappa*SA)*A(g)=Cstar+10Q*Σ J_r*g_r`。

该 A 来自原逐项实际下界；数学可靠性仍由已冻结源分析和后续 actual Lean 消费者承担，本次 Python 分类不是 Lean 证明。原 FS/flow 身份检查不将 flow 付款再次加入 A。

反射仅在提取后的系数/几何嵌入：canonical gap r 映为 `offset+r`（id）或 `offset+7-r`（rev），span(i,j) 映为 `(offset+8-j,offset+8-i)`。prefix offset0/suffix offset1。原 profile 的实际反射定理仍是未来 formal bridge 的依赖。

## 固定 155 行与 exact Lower

物理变量 `X=20Q*p`，实数变量，不假设整数点。两窗各 36 span upper/lower 共 144 行，rhs 依次 `20U,-20L`；九条 sep 行 `X_r-X_(r+1)≤-17Q`；最后两行原 Ordered 四点 normal 独立按 chart 取符号，rhs0。不将 Ordered 当作 DBM edge。所有 full10 row normal 之和为0。

嵌入后的 `Jphys` 给 `C=2(CstarL+CstarR)`、`b=(-J0,J0-J1,...,J7-J8,J8)`，故 `C+b·X=2*kappa*SA*(A_L+A_R)`、`Σb=0`。

令 B 的九行是选定 source normal（删 X0 列），`A=B^T`。exact Gauss–Jordan 得 rank/det；fullrank 时 `d=|det A|>0`，`S=d*A^-1` 必须为整数并逐项核 `A*S=dI`。固定原 ±1 normal 的静态 minor 论证给 d≤4；脚本仍显式检查，不能由 support count9 推断 fullrank。

每 pair 计算 `n=-S*b[1:]`，必须再核 full10 `d*b+Σ n_k*normal(rowID_k)=0`。若有负 n，未解；否则保留 exact bound

`N=d*C-Σ n_k*rhs(rowID_k)`，即 `C+b·X≥N/d`。

`N≥d*target` 才为 Lower。若 `N<d*target`，仍保存 signed N/d，标签为 `valid_but_below_target`，可供后续整段累计数学研究；本包不启动这种研究。n 可大/为零，不能套 Empty primitive circuit 的 1..4 权界。

## 输出与独立重放接口

共享 `basis.json` 含四 chart 的 source normal、A、rank、det、d、S 及整数 identity；`affine-cache.jsonl` 与 `cache-index.json` 绑定原 cell 语义。二进制 `classifications.bin` 为 magic `JLB2\n`，逐 H 顺序：

- uint32LE 原 G index；一 byte tag。
- tag0 `negative_multiplier`、tag3 `singular_chart`：无额外值。
- tag1 `Lower`、tag2 `valid_but_below_target`：追加 signed numerator N 的 zigzag+canonical ULEB128，`zz(N)=2N`（N≥0）否则 `-2N-1`。d 从该 index chart 的共享 basis 读取。

不保存逐 pair μ 或矩阵；独审由原 FS 重建 b，再由共享 S/d 重建 n/μ，逐项核 n≥0/full10balance/精确 N 和标签。所有非 tag1 索引写到第二条 uint32LE `remaining-indices.u32.bin`。每 256 记录两流 fsync 后原子发布 prefix；记录 committed 字节、各类数量、两流 SHA、索引序列 SHA、cache/basis SHA。未提交缓冲不算证据。完整结果必须核两流 EOF、全部 15,378 原索引顺序和类别计数。

分类只接受候选证书，不声称 basis 最优或未解域非空；valid_but_below_target 不是 actual F 反例。即使全部 Lower，也仍缺全原决策树/反射/root外/短对计数消费者及网站源体积、普通核/导出/Nano总时间门槛。共享 cache 与 basis 提供压缩机会，不构成可提交性保证。

## 唯一未来执行命令

`C:/Python314/python.exe -B -X utf8 research-goal-20261018-stageJ-fixed-basis-preparation/run_once.py --launch-authorized-fixed-J --gate <根部新gate相对路径> --gate-sha256 <新gate SHA256>`

本包的 `preparation.json`/`prepared-files.json` 只证明 AST 和字节身份准备，尚无上述执行。
