from pathlib import Path
import json

root = Path(__file__).resolve().parents[1]
p = root / 'research-goal-20261016/direction-state.json'
state = json.loads(p.read_text(encoding='utf-8'))
assert state['last_review_number'] == 9 and state['main_rounds_since_review'] == 0
state['main_route'] = 'Exact proof-preserving v7 was actually submitted once. The official UI reports Verification running and actual bundle digest 1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771, matching the prediction. Wait for this same official job; preserve v6 timeout and all frozen inputs.'
state['next_gate'] = 'Observe this exact official v7 job to actual terminal result. Acceptance requires both-kernel attestation, matching bundle, promotion/ledger status and fixed public evidence; running or upload alone cannot complete the goal. No unchanged resubmission, local compiler/export/kernel or new optimization family.'
state['v7_delivery_route'].update({
 'official_result': 'running',
 'actual_official_proofDigest': '1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771',
 'actual_submit_clicks': 1,
 'submitted_as': 'Li Xiang',
 'submission_id': 'lixiang90-w9a2-weighted-potential-v7-20261020',
 'source_checkpoint_commit': 'cb7558bc2944358366b5aac4d187f3b3ee5a637c',
 'actual_push_exit_code': 0,
 'fixed_commit_public_source_equal': True,
 'official_acceptance': False,
 'official_kernels_complete': False,
 'goal_complete': False,
})
state['website_submission_ready'] = False
p.write_bytes((json.dumps(state, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))
prefix = (
 '官网v7已实际提交一次，当前Verification running，实际组合proofDigest '
 '1f28020dcda27176a97f8c48e9c9d3f9dc00107ce904f1a1f6706b1f43309771与预测完全相符。'
 '新源dae01f/1829242B、Li Xiang、新ID lixiang90-w9a2-weighted-potential-v7-20261020；'
 'cb7558bc2944358366b5aac4d187f3b3ee5a637c已实际push0，固定commit公开rawHTTP200逐字节等于上传源。'
 '截图submission-running.png已真实保存于research-goal-20261020-w9a2-v7-official-submission。'
 '当前只等待此任务，不再次点击Submit、不原样重投、不跑本地证明。'
 'UI静态quota组件仍显示首投后的1/3 used，不能据此声称新额度已鲜核；也不能因其滞后重复提交。'
 '官网双内核接受/推广与公开证据仍待，goal active；属于宏观009内交付等待，review9/counter0不增加。\n\n'
)
for name in ['research-goal-20261016/DIRECTION.zh.md', 'research-goal-20261020-w9a2-runtime/CONTINUATION.zh.md']:
    path = root / name
    path.write_bytes(prefix.encode('utf-8') + path.read_bytes())
print('Recorded actual official v7 running; goal active, review9/counter0; no local proof run.')
