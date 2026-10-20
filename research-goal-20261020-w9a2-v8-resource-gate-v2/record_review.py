"""Root metadata-only review record. No compiler, process query or large tree audit."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def raw_json(value):
    return (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode()
review_name = 'research-goal-20261016/macro-reviews/011-20261020.zh.md'
review_sha = '9b12107dcb046c6aa624667c5cf81641e61ec23f5a867dc33c3d42af6c496411'
assert sha((root/review_name).read_bytes()) == review_sha
pins = [
 ('research-goal-20261020-w9a2-v8-resource-failure-v1/files.json', '8317a845b841313d4042ae0664a9d38039e96fe05adedee868355636a13a0cf1'),
 ('research-goal-20261020-w9a2-v8-stack-static-review/files.json', 'b50f02b52b1f40ffd7df5f408596137b2cc16511169c0cd2a52b08e06f6c4121'),
 ('research-goal-20261020-w9a2-v8-import-memory-static-independent/files.json', 'c3db7c1c33ec2fcb6639680032a002f37534dab26076a759d02283b8d0a2e3c7'),
]
checked = []
for name, expected in pins:
    p = root/name
    raw = p.read_bytes()
    assert sha(raw) == expected, name
    rows = json.loads(raw)['files']
    for row in rows:
        q = root/row['path'] if row['path'].startswith(p.parent.relative_to(root).as_posix()+'/') else p.parent/row['path']
        b = q.read_bytes()
        assert len(b) == row['bytes'] and sha(b) == row['sha256'], str(q)
    checked.append({'path':name, 'sha256':expected, 'files_checked':len(rows)})
p = root/'research-goal-20261016/direction-state.json'
j = json.loads(p.read_bytes())
assert j['last_review_number'] == 10 and j['main_rounds_since_review'] == 1
j.update({'last_review_number':11, 'main_rounds_since_review':0,
    'last_review':review_name, 'last_review_path':review_name,
    'last_review_SHA256':review_sha, 'last_review_sha256':review_sha,
    'counter_reset_reason':'Written macro011 completed after the first actual post-v8-failure static diagnostic round. Exact Windows COW/source evidence distinguishes commit from RSS; new fixed measurement gate selected. No extra tool/agent/compaction round.',
    'main_route':'Same frozen v8 mathematics/source. Correct the Windows resource observation to 7GiB PeakWorkingSetSize, preserving -M6500 and3200s; report process commit separately. The prior commit-threshold failure stays failed.',
    'next_gate':'Independently review preparation-v3, then root freezes one new single-use v8-resource-v2 gate and observes actual compiler/outer exits and all three outputs. No separate old mathematical/export/Nano replay. Only after actual resource PASS, fresh record and exact GitHub source sync may one authorized v8 official submission proceed.',
    'optimization_scope':'No new source/math/checker/numerical family or parameter scans. Fixed v8, one justified metric-corrected resource measurement; original v1 stays failed and its namespace is not reused.',
    'website_submission_ready':False,
    'resource_rss_metric_review':{'review':11,'review_sha256':review_sha,'evidence':checked,
        'old_gate_reclassified_as_pass':False,'observed_peak_stop_metric':'PeakWorkingSetSize',
        'observed_peak_stop_bytes':7*1024**3,'process_commit_diagnostic_only':True,
        'compiler_memory_MiB':6500,'total_budget_seconds':3200,
        'compiler_execution_started':False,'fullchain_equivalence_claimed':False,'goal_complete':False}})
p.write_bytes(raw_json(j))
prefix = ('当前权威为宏观011（'+review_name+'，SHA '+review_sha+'），已完成书面回顾后counter1→0、review11。固定Lean primary与微软文档证明Windows FILE_MAP_COPY整view预收commit，原v8在RSS375066624B/commit7728263168B时由7GiB commit门主动停，不表示官网8GB驻留超限；原72573失败不改。线程栈是reserve，不机械降栈。下一关是独审后仅一次全新v8-resource-v2的RSS资源测量：同源5424212b…/1829382B、同3200秒/-M6500/7GiB PeakWorkingSetSize，commit只诊断，其余-o/-i/-c/--json不变，无旧数学/Nano重放。Windows仍非官网Linux全链等价；实际资源PASS后再鲜核R/Git与一次官网提交Li Xiang。全部无条件证明、双内核/推广/公开及Git目标保留，goal active。\n\n')
for name in ('research-goal-20261016/DIRECTION.zh.md', 'research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md'):
    q = root/name
    q.write_bytes(prefix.encode()+q.read_bytes())
out = Path(__file__).with_name('review-record.json')
assert not out.exists()
out.write_bytes(raw_json({'review':11,'review_sha256':review_sha,'evidence':checked,
    'counter_transition':[1,0],'compiler_runs':0,'goal_complete':False}))
print(json.dumps({'review':11,'counter':0,'review_sha256':review_sha,'all_small_evidence_files_valid':True}))
