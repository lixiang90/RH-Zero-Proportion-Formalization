"""Exact public-record comparison and evidence hashes only; no proof evaluation."""
from fractions import Fraction as F
from hashlib import sha1,sha256
import json
import os
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OLD=F(3337839448633819172184136761695440236797,4955319193847235264050000000000000000000)
def load(p):return json.loads(p.read_text(encoding='utf8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha256(p.read_bytes()).hexdigest()}
def save(name,x):
    with (HERE/name).open('x',encoding='utf8') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def score(r):return F(int(r['exactRational']['numerator']),int(r['exactRational']['denominator']))
def main():
    assert not (HERE/'files.json').exists()
    receipts={}
    for name in ['api','homepage','accepted-detail','main-commit','main-tree','main-records','main-contract','evidence-contract','main-submission']:
        p=HERE/(name+'.body');r=load(HERE/(name+'.receipt.json'))
        assert r['http_status']==200 and r['body_bytes']==p.stat().st_size and r['body_sha256']==row(p)['sha256']
        assert 'independent_fresh=' in r['requested_url'] and r['request_headers']['Cache-Control']=='no-cache, no-store, max-age=0'
        receipts[name]=r
    for name in ['api','homepage','accepted-detail']:
        assert receipts[name]['response_headers']['Age']=='0' and receipts[name]['response_headers']['X-Vercel-Cache']=='MISS'
    api=load(HERE/'api.body');current=api['current'];records=load(HERE/'main-records.body')
    assert score(current)==OLD and current['id']=='critical-strip-exclusion-attempt-1'
    exact=[r for r in records if r.get('exactRational') and r['formalVerification'] is True]
    highest=max(exact,key=score);assert score(highest)==OLD and highest['id']==current['id']
    assert all(score(r)<=OLD for r in api['records'] if r.get('exactRational'))
    for name in ['homepage','accepted-detail']:
        text=(HERE/(name+'.body')).read_text(encoding='utf8')
        assert str(OLD.numerator) in text and str(OLD.denominator) in text
    commit=load(HERE/'main-commit.body');tree=load(HERE/'main-tree.body')
    assert commit['sha']=='0c038980cbfaa3ee9fc539d751c32c454d85a319'
    assert [r['sha'] for r in commit['parents']]==['cfc7ce6113199b7d5f262812d81089778e84335c']
    assert [r['filename'] for r in commit['files']]==['data/records.json']
    # This GitHub commitish tree response identifies the resolved commit in sha/url.
    assert tree['sha']==commit['sha'] and tree['truncated'] is False
    catalogue={r['path']:r for r in tree['tree']}
    src=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean';raw=src.read_bytes()
    blob=sha1(b'blob '+str(len(raw)).encode('ascii')+b'\x00'+raw).hexdigest()
    source_path='submissions/critical-strip-exclusion-attempt-1/proof/Solution.lean'
    assert catalogue[source_path]['sha']==blob and catalogue[source_path]['size']==len(raw)
    assert current['proofUrl']=='https://github.com/josusanmartin/riemann/blob/cfc7ce6113199b7d5f262812d81089778e84335c/'+source_path
    assert (HERE/'main-contract.body').read_bytes()==(HERE/'evidence-contract.body').read_bytes()
    submission=load(HERE/'main-submission.body');assert F(int(submission['score']['numerator']),int(submission['score']['denominator']))==OLD
    candidate_path=ROOT/'research-goal-20261018-record-overlap-static/static-receipt.json'
    candidate_doc=load(candidate_path);candidate=F(candidate_doc['ratio_if_joint_floor_proven'])
    assert candidate>OLD
    out={'schema':'fresh-independent-public-record-comparison-v1','passed':True,
        'HTTP_receipts_UTC':{k:v['completed_UTC'] for k,v in receipts.items()},
        'website_api_HTTP':200,'website_api_Age':'0','website_api_cache':'MISS',
        'highest_current_exact_rational':str(OLD),'highest_current_percent_display':'67.3587173310%',
        'current_record_changed_vs_previous_R':False,'current_record':current,
        'public_main_commit':commit['sha'],'public_main_commit_UTC':commit['commit']['committer']['date'],
        'public_main_parent':commit['parents'][0]['sha'],'main_commit_changed_files':['data/records.json'],
        'main_exact_records_checked':len(exact),'main_highest_id':highest['id'],
        'source_proof_path':source_path,'source_proof_git_blob':blob,'source_snapshot':row(src),
        'main_proof_blob_matches_frozen_source':True,
        'main_vs_frozen_evidence_contract_identical':True,'contract_sha256':row(HERE/'main-contract.body')['sha256'],
        'source_or_verification_protocol_changed_vs_frozen_evidence_commit':False,
        'frozen_conditional_candidate_rational':str(candidate),'candidate_minus_current_exact':str(candidate-OLD),
        'candidate_strictly_exceeds_current':True,'candidate_unconditional_Lean_or_global_proof_claimed':False,
        'user_acceptance_now_strict_current_improvement_only':True,
        'new_optimization_kernel_Lean_P_mathematics_executed':False}
    save('comparison.json',out)
    note='''# 新鲜网站纪录独立核对\n\n2026-10-18 11:54:03.764713 UTC，随机nonce与Cache-Control:no-cache/no-store的独立直连API返回HTTP200、Age0、X-Vercel-Cache MISS。首页与最新接受详情也独立取得Age0/MISS。最高仍67.3587173310%，exactR=3337839448633819172184136761695440236797/4955319193847235264050000000000000000000；没有发现更高公开accepted记录。\n\n公开main=0c038980cbfaa3ee9fc539d751c32c454d85a319，2026-10-18T03:40:45Z，唯一父为cfc7ce6113199b7d5f262812d81089778e84335c，唯一改动data/records.json。main记录最高与API相同；当前accepted仍critical-strip-exclusion-attempt-1。main proof blob与固定f82a4914…源字节Git身份一致，main和cfc evidence的challenge/contract.json完全相同，未见源/验证协议变化。\n\n已冻结joint候选的条件比例精确高于当前R，精确差见comparison.json。用户新验收仅要求严格超过当前纪录，放弃额外1e-6幅度，不改变非平凡数学改进/无条件完整形式化义务。候选尚不是全域或Lean已证明纪录。未执行新优化、核、Lean或P数学；未修改旧包/根状态。所有HTTP源URL、随机nonce、起终UTC、响应头、原始body均保留。\n'''
    with (HERE/'NOTE.zh.md').open('x',encoding='utf8') as f:f.write(note)
    deps=[row(src),row(candidate_path)]
    manifest={'schema':'fresh-independent-public-record-evidence-files-v1',
        'files':[row(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='files.json'],
        'read_only_dependencies':deps,'network_read_only':True,'proof_source_executed':False,
        'new_math_family_or_optimization':False}
    save('files.json',manifest)
    print(json.dumps({'manifest':row(HERE/'files.json'),'comparison':row(HERE/'comparison.json'),
        'highest_exact':str(OLD),'candidate_strictly_greater':True,'main_commit':commit['sha']}))
if __name__=='__main__':main()
