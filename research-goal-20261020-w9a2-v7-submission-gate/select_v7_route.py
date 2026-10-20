from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
review_path = 'research-goal-20261016/macro-reviews/009-20261020.zh.md'
review_sha = hashlib.sha256((root / review_path).read_bytes()).hexdigest()
state_path = root / 'research-goal-20261016/direction-state.json'
state = json.loads(state_path.read_text(encoding='utf-8-sig'))
assert state['last_review_number'] == 8
assert state['main_rounds_since_review'] == 1
state['last_review_number'] = 9
state['last_review'] = review_path
state['last_review_SHA256'] = review_sha
state['last_review_sha256'] = review_sha
state['main_rounds_since_review'] = 0
state['counter_reset_reason'] = 'Macro009 completed within the first actual diagnostic round: terminal official timeout and fixed minimal v7 source-cost diagnosis reviewed. No compaction/tool/agent round increment.'
state['main_route'] = 'Fixed proof-preserving v7: add 8 explicit noncomputable modifiers and remove 15 independent diagnostic print commands. Preserve every proof body, all data and all 48 root checks. Submit this changed source once to the official complete verifier under the existing human authorization.'
state['next_gate'] = 'Independent exact 23-edit byte projection; prepared-v7 and expected-wire-v7; root-frozen official submission gate; exact user GitHub push and fixed-commit byte check; one official v7 upload, then actual official full-chain acceptance/promotion evidence. No local compiler/export/kernel/old collector rerun.'
state['optimization_scope'] = 'Fixed W9A2 mathematics and 49-state graph frozen. Only v7 delivery-cost changes selected in macro009. No unchanged submission, new numerical family, automatic A/B or repeated local verification.'
state['new_optimization_family_authorized'] = False
state['website_submission_ready'] = False
state['v7_delivery_route'] = {
    'source': 'research-goal-20261020-w9a2-delivery/draft-v7/Solution.lean',
    'source_sha256': 'dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6',
    'source_bytes': 1829242,
    'local_Lean_or_kernel_run': False,
    'official_result': 'not-yet-submitted',
    'goal_complete': False,
}
state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
prefix = (
    '当前权威为宏观009（' + review_path + '，SHA ' + review_sha + '），review9/counter0。'
    '官网首投a517/e764已经实际terminal timeout，冻结完整用户日志和失败收据；不再等待或原样重投。'
    '本轮静态诊断已结束：固定v7只加8个显式noncomputable并删15条独立#print axioms，其他源字节、证明与数值包全部保留。'
    '新源1829242B/SHA dae01f6844642d7f9ee8180616c1f57aefc18ab8616bc8a4a46a14bf8e9fefc6。'
    '下一关是独审23处raw projection、新提交包/预期wire与root gate、精确GitHub同步，再由官网唯一一次完整执行验证新源。'
    '遵照人类不重复本地核查指令，不启动compiler/export/CoreAudit/Nano或旧collector。'
    '无测量加速或3200秒保证；双内核/实际官网接受/公开promotion证据仍待，完整无条件目标与全部验收门保留，goal active。\n\n'
)
for name in ['research-goal-20261016/DIRECTION.zh.md', 'research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    path = root / name
    old = path.read_bytes()
    path.write_bytes(prefix.encode('utf-8') + old)
print(json.dumps({'review_sha256': review_sha, 'review': 9, 'counter': 0}))
