# Stage O：CellA 整数语义独立静态审查

准备包 e6cfb7330076dccd9a11ca246c41d1ac293ac5bbf8ede2d20b91c46d60f6888f；provider `cellA_quantitative.py` SHA4a08ae8c7dd54afd5eb3282e58a3d6b1bb5e72ab498e44595b84fe795f08ac4a。唯一比较源是固定 s1R `snapshot/Solution.lean` SHAf82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf。

仅源码/代码阅读与文件哈希；没有 import/执行 provider、参数提取、FS、curvature、矩阵、solver、kernel 或 Lean。本审查没有改变任何原包/root轮数。结论是**未发现逐式转写错误**；不表示任一具体 CellA 运算、hull选择、曲率收益或后续正式命题已经通过。

## 逐式结果

- Python10–35对应source5380–5507：正分母下 `//` 为有符号 floor，`ceildiv(a,b)=-((-a)//b)` 为有符号 ceil，等价 SZ.fl/ce 对 p−n 的处理；`ndiv/ndivc` 的分母0返回0也等价Nat除0。IV四端点乘积的min/max后舍入、正C的mulc符号分支、divp按分子符号选分母端点、neg/sub/scl均一致。mulc额外检查C.lo≥0与原soundness前提相符。
- parameters37–65对应source5672–5711/5783–5790/12386：常数从实际字面提取，CE12项及CJ的符号独立保留，FA的显式12次farJ链与CE作文本身份检查。尤其G1C/G2C使用当前源字面，不用旧kernel或重新近似的γ常数。
- provider74–93对应source5745–5782/5811–5818：k、side、LLO/UHI、AD/RLO/RHI、TLZ/TUZ、BLZ/BUZ、PG/NI、E0/E1/E2/E3的Nat截断与向外舍入位置相同。CI/SI先Nat.sub再除、再加减ERRD，不能改成任意signed差；当前代码保留了这一点。CX/SX四个quadrant及side反号与Bool.rec分支一致。
- far94–117对应source5717–5738：mnum三个n=0/1/2及hden三分母正确。等号2j=k分支用hneg=(n=1)；右侧2j<k用mneg n true=(n=1)；左侧2j>k用mneg n false恒true，故负号是not sg。三分支取XL/XU顺序、Nat.sub后幂、floor/ceil及最终FA除E9正确。没有漏掉n=1反号或把n=2符号复用成n=1。
- near118–132对应source5688–5693/5791–5806：sc/s1/s2的多项式、SCDEN/S1DEN/S2DEN及ERRD倍数1/2/5完全对应；这里用SZ的signed差，代码没有错误Nat截断。B0/B2仅在nearOn启用，B1的side=true用G1、false用−G1，PIC/PI2C和CJ符号及2E9分母顺序一致。
- K0/MI/K1/N2/PP/K2（134–139）对应source5807–5824：所有mul与mulc、divp和muln顺序一致，包括K2的外负号、2·RHOC(CX·FA1)、−TAUC·SF0，以及PP内−4EI·NI、+8BI·MI；未因代数重排改变整数舍入。
- provider140对应source5827–5829：`max(0,K1.lo,−K1.hi)^2 + DZ*(K0.mul K2).lo` 正是 W2L.v，量化候选 `2*W2L.v/DZ²` 的因子/尺度正确。source7578–7602的证明给出了提取此 quantitative lower 的代数基础，但现有正式API仅暴露w2_nonneg，仍需新增同guard定量lemma和strong tangent remainder桥，不能仅靠boolean convOk声称已formalized。

## 原 REG / guard 范围

source8764–8778中ccell(a,b)需b<KB，chainOk逐相邻闭单元检查a≤b、b+1≤KB、convOk。provider目录从原rgA接原chain端点，检查同一upper界；chain去重/严格递增比源更保守，若将来遇重复端点只会准备/运行失败，不产生更强下界。当前审查没有执行266个字面单元的数值检查。

source7621–7635使convOk恰为CellA.ok、E2L>0、E3L>0及W2L≥0。provider逐项检查这些条件；没有以ok或W2L单项替代全部guard。原ccell到CellA(a,b)的身份由source8786–8791及b<KB接合。

另只读audit_once.py的cover_original_chain：hull须完整包含在一个原REG链的rgA..rgB之内，所选相邻原单元须首尾覆盖且无gap；未覆盖返回μ=0。不能仅选择若干与hull相交的单元就跳过region间隙。provider本身只允许原catalog中的(L,U)，不允许新细分、改变端点或创建anchor。

本审查不承担root所审weighted_network/row-binding的数值检查，也没有计算任何µ、coverage数量或收益。一次固定O若实际执行，仍须保存逐单元guards/整数输出、固定dual权绑定、网络exact stationarity、总付款与source/运行边界。数学成功也只是固定pair的条件余项机会；完整源≤2m、全域cover、实际Lean/axioms和网站runtime仍是独立交付义务。
