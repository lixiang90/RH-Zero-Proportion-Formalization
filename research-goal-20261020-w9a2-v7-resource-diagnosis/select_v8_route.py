from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
review = 'research-goal-20261016/macro-reviews/010-20261020.zh.md'
digest = hashlib.sha256((root / review).read_bytes()).hexdigest()
p = root / 'research-goal-20261016/direction-state.json'
state = json.loads(p.read_text(encoding='utf-8'))
assert state['last_review_number'] == 9 and state['main_rounds_since_review'] == 1
state['last_review_number'] = 10
state['last_review'] = review
state['last_review_SHA256'] = digest
state['last_review_sha256'] = digest
state['main_rounds_since_review'] = 0
state['counter_reset_reason'] = 'Written macro010 completed in the first actual post-v7-failure resource diagnostic round. New fixed v8 and one resource-only compiler gate selected; no tool/agent/compaction increment.'
state['previous_goal_turn_classification'] = 'progress'
state['main_route'] = 'Fixed v8 adds explicit noncomputable only to PTT_0..7/PTT/PT, preserving every other raw source byte. One new-source compiler resource gate with olean/ilean/C output must be reviewed and frozen before execution; official full acceptance remains required.'
state['next_gate'] = 'Independent exact v8 10-edit projection and runner/gate audit; root-freeze precise pins and single 3200s/7GiB-peak gate; one fresh v8 compile with -o/-i/-c/--json/-j1/-M6500. No export/CoreAudit/Nano or old-source repeat. Success is only compiler resource scope; actual official Linux dual-kernel/promotion evidence still required.'
state['optimization_scope'] = 'Fixed mathematics and all proof/data bodies remain frozen. Only ten proof-only data codegen modifiers and one new v8 resource compilation selected. No numerical/checker/codec family, automatic retry or limit increase.'
state['new_optimization_family_authorized'] = False
state['website_submission_ready'] = False
state['v8_resource_route'] = {
 'source':'research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean',
 'source_sha256':'5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b',
 'source_bytes':1829382,
 'delta_from_v7_bytes':140,
 'exact_source_edits':10,
 'compiler_resource_run_started':False,
 'compiler_resource_run_passed':False,
 'official_acceptance':False,
 'goal_complete':False,
}
p.write_bytes((json.dumps(state,ensure_ascii=False,indent=2)+'\n').encode('utf-8'))
prefix = ('当前权威宏观010（'+review+'，SHA'+digest+'），review10/counter0。v7官网真实Lean137/1014s失败已封存，不再等待或原样重投；OOM未确诊。固定v8仅再给PTT_0..7/PTT/PT十个proof-only定义加显式noncomputable，1829382B/SHA5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b，所有其它证明/数据字节保留。下一关先独审projection与新resource runner，root冻结后仅一次v8的-o/-i/-c/--json编译资源测量（3200秒、-M6500、7GiB峰值阈值），不重放旧数学/Nano。Windows测量不是官网Linux8GB/--setup或整轮双内核等价；最终官网接受与公开promotion/Git一致仍待，完整无条件目标保留，goal active。\n\n')
for name in ['research-goal-20261016/DIRECTION.zh.md','research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    q=root/name
    q.write_bytes(prefix.encode('utf-8')+q.read_bytes())
print(json.dumps({'review':10,'counter':0,'review_sha256':digest}))
