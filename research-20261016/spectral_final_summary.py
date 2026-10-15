"""Freeze a source-hash-bound research handoff, with proof limits explicit."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
p=json.loads((HERE/'spectral-w10-refined-rational.json').read_text())
ternary=json.loads((HERE/'spectral-w10-refined-full-ternary.json').read_text())
challenge=json.loads((HERE/'spectral-w10-refined-challenge.json').read_text())
compile=json.loads((HERE/'spectral-w10-refined-compile.json').read_text())
assert compile['status']=='PASSED' and compile['source_sha256']==compile['source_after_sha256']
assert hashlib.sha256((ROOT/compile['source']).read_bytes()).hexdigest()==compile['source_sha256']
assert hashlib.sha256((HERE/'spectral-w10-refined-rational.json').read_bytes()).hexdigest()==ternary['candidate_sha256']
assert 'sorryAx' not in compile['stdout']
assert ternary['completed_patterns']==3**9 and ternary['successful_optimizations']==3**9
assert min(ternary['best_observed_c_upper_bound'],challenge['best_observed_minimum'])>.00866
B=Q(p['B_exact']);c=Q(p['proposed_floor_exact']);s=Q(17,20)
b=[Q(v,p['denominator']) for v in p['b_numerators']];slack=c-s*B
current=Q(3338957652820594373879991756052499665323,4957023073704306225950000000000000000000)
kappa=Q(p['conditional_kappa_exact'])
files=['StructuralResearch20261016/W10RefinedCandidate.lean',
    'research-20261016/spectral-w10-refined-rational.json',
    'research-20261016/spectral-w10-refined-full-ternary.json',
    'research-20261016/spectral-w10-refined-full-ternary.npz',
    'research-20261016/spectral-w10-refined-challenge.json',
    'research-20261016/spectral-w10-refined-compile.json',
    'research-20261016/spectral-w10-counterexample-interval.json',
    'research-20261016/spectral-w10-rational.json',
    'research-20261016/spectral-comparison.json',
    'research-20261016/spectral_wcert_reopt.py',
    'research-20261016/spectral_w10_full_ternary.py',
    'research-20261016/spectral_w10_challenge.py',
    'research-20261016/spectral_w10_counterexample_interval.py',
    'research-20261016/spectral_verify_w10.py']
artifacts=[{'path':path,'sha256':hashlib.sha256((ROOT/path).read_bytes()).hexdigest(),
    'bytes':(ROOT/path).stat().st_size} for path in files]
report={'scope':'Frozen research handoff. NO new zeta proportion theorem or accepted record is asserted.',
    'selected_candidate':'spectral-w10-refined-rational.json',
    'model':'Fw(g)=sum_i b_i*g_i +sum_i<j a_ij*K(sum_r=i..j-1 g_r)^2',
    'new_structure':'10-point frame with rank-distance9 pair paid at coefficient2; 39positive pair coefficients; exact lag capacities<=2',
    'B_exact':str(B),'candidate_floor_exact':str(c),'floor_status':'UNPROVED',
    'conditional_percent_only':100*float(kappa),'conditional_gain_percentage_points_only':100*float(kappa-current),
    'proved_result':'W10RefinedCandidate.adm and pressure_eq; ordinary pinned Lean and3standard axioms only',
    'numerical_evidence':{'all_ternary_starting_patterns':3**9,
        'meaning':'Each discrete starting pattern was polished once by continuous local optimization; this does not enumerate all continuous minima.',
        'ternary_minimum_upper_bound':ternary['best_observed_c_upper_bound'],
        'additional_starts':challenge['starts'],'additional_minimum_upper_bound':challenge['best_observed_minimum'],
        'observed_margin':min(ternary['best_observed_c_upper_bound'],challenge['best_observed_minimum'])-float(c),
        'search_gap_lower_exact':'4/5; contains the required17/20 domain'},
    'old_candidate':'Original W10 c=.00866 REFUTED; exact rational interval counterexample has F<.0086495 with all gaps>17/20',
    'finite_certificate_domain':{'assume_for_pruning':'g_i>=17/20 and Fw<c',
        'linear_constraint':'sum b_i*g_i<c because all pair terms are nonnegative',
        'pressure_slack_exact':str(slack),'bmin_exact':str(min(b)),
        'coordinate_upper_exact':[str(s+slack/z) for z in b],
        'max_coordinate_upper':float(s+slack/min(b)),
        'total_span_upper_exact':str(9*s+slack/min(b)),
        'total_span_upper':float(9*s+slack/min(b))},
    'proof_route':'Adapt the inherited one-variable tangent library to39positive pairs and9gap variables, branch on gap/partial-span hyperplanes, export rational LP mixtures and nonnegative integer flows. Generic WCert and separated counting bridges already exist.',
    'size_limit':'No full9dimensional analytic certificate was generated or node-count estimate certified. A full Cartesian grid loses rank9information until total span is constrained; use polyhedral span branches.',
    'spectral_limit':'With normalized separated Gram spectrum<=2, Psi is quadratic and its trace is exactly the offdiagonal squared energy. The two tested uniform24/32pressure vectors fail stronger adversaries; this does not rule out every pressure choice in those families.',
    'artifacts':artifacts}
(HERE/'spectral-final-summary.json').write_text(json.dumps(report,indent=2)+'\n')
lines=[
    '本子任务最终结论：得到一个新的十点有限框架候选及已核验的参数可容许性；尚未证明新的ζ零点比例。',
    '',
    f'最终参数是 spectral-w10-refined-rational.json：B={B}，候选c={c}=.00866。若证明全域floor，条件比例为{100*float(kappa):.10f}%，比当前记录增加{100*float(kappa-current):.10f}个百分点。此条件尚未满足。',
    '结构变化是加入秩距离9的远程对支付（系数2），并重优化全部反射对称权重。39个a正项，各秩距离容量精确<=2。原九点框架已饱和秩距离1..8，不能在这些预算内免费增加奖励。',
    '',
    'W10RefinedCandidate.lean的Adm/pressure_eq已在固定Lean4.33.0-rc2通过，axioms仅propext、Classical.choice、Quot.sound；模块没有c、H或比例定理。原W10Candidate与其旧审计保持独立。',
    f'最终新权重已逐个优化全部19683个三相离散起点，最低F={ternary["best_observed_c_upper_bound"]:.14f}；另1007个四/五相DP、随机和大gap起点最低F={challenge["best_observed_minimum"]:.14f}，候选floor留约7.24e-6数值裕量。这不是全域下界证明，也不表示列尽所有连续极小点。',
    '',
    '原始十点权重的c=.00866已被中心3gap对称配置推翻；独立精确有理区间给出F<.0086495。旧文件显式REFUTED，新旧权重不可混用。旧权重若下调至c=.00864，未证条件比例仅67.3587030911%。',
    'W11/W12粗研究的条件数值见spectral-comparison；它们没有经过同等级完整起点追击，不能当作新纪录。统一24/32点谱候选的当前压力参数也被强反例压低；这只淘汰所测参数，不排除整个模型。',
    '',
    f'全域证书的紧域：对实际sep=17/20，任何Fw<c反例必满足b·g<c，单gap最大<{float(s+slack/min(b)):.9f}，总span<{float(9*s+slack/min(b)):.9f}（精确界见JSON）。',
    '建议下一步复用单变量TVal切向包络，以39个pair epigraph变量、9个gap变量及部分span超平面分支导出有理混合/整数flow。没有实际生成完整9维证书，不能预报节点数或声称可在给定时间闭合。',
    '',
    '复核命令（仓库根目录；数值结果写独立recheck前缀）：',
    'python -B -X utf8 research-20261016/spectral_w10_full_ternary.py --candidate research-20261016/spectral-w10-refined-rational.json --output-prefix spectral-w10-refined-recheck',
    'python -B -X utf8 research-20261016/spectral_w10_challenge.py --candidate research-20261016/spectral-w10-refined-rational.json --output-prefix spectral-w10-refined-recheck-challenge',
    'python -B -X utf8 research-20261016/spectral_w10_counterexample_interval.py',
    'python -B -X utf8 research-20261016/spectral_verify_w10.py --module W10RefinedCandidate --receipt spectral-w10-refined-recheck-compile.json',
    '', '文件SHA256、精确有理紧域及证明边界见spectral-final-summary.json。', '']
(HERE/'spectral-final-summary.txt').write_text('\n'.join(lines),encoding='utf8')
print(json.dumps({k:report[k] for k in ['scope','B_exact','candidate_floor_exact','floor_status','conditional_percent_only','conditional_gain_percentage_points_only']},indent=2))
