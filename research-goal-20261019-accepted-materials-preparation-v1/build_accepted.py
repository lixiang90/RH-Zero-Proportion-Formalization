"""Exclusive accepted-v3 materials builder; preparation does not execute it.

Reads frozen official HTTP evidence, never fetches, compiles or submits.
"""
import argparse
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OFFICIAL=ROOT/'research-goal-20261019-record-accepted-independent-1753'
PREPARED=HERE/'prepared-files.json'
DEST=ROOT/'submission/single-exception-overlap-accepted-20261019'
LOCAL=ROOT/'research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean'
OLD=ROOT/'submission/single-exception-overlap-20261019'
SOURCE_SHA='024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'
JOB_DIGEST='23e3dd765aa27de76938e056f13d3e0f08d849d0e7c39c6f78c62e7640c0a10f'
OFFICIAL_PIN='71f1ba7aaf1ba70b0edf1526103bdf0f1684a4b9c06fbcde3ac5e8a3edb0ebf2'

def sha(data):return hashlib.sha256(data).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}

def write(path,obj):
    with path.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,ensure_ascii=False,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def copy_bytes(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('xb') as f:f.write(data);f.flush();os.fsync(f.fileno())

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--build-authorized-accepted-v3',action='store_true',required=True)
    ap.add_argument('--prepared-sha256',required=True)
    args=ap.parse_args()
    assert __debug__ and sha(PREPARED.read_bytes())==args.prepared_sha256
    prep=load(PREPARED)
    bound={}
    for r in prep['files']+prep['dependencies']:
        p=ROOT/r['path'];assert row(p)==r,r['path'];bound[str(p)]=r['sha256']
    assert not DEST.exists(),'New accepted materials only; no overwrite or retry'
    assert sha((OFFICIAL/'files.json').read_bytes())==OFFICIAL_PIN
    official=load(OFFICIAL/'files.json')
    for r in official['files']:
        p=ROOT/r['path'];assert row(p)==r;bound[str(p)]=r['sha256']
    comparison=load(OFFICIAL/'comparison.json')
    record=comparison['current_public_record']
    metadata=load(OFFICIAL/'accepted-submission.json.body')
    score={'numerator':'3337839448633819172184136761695440236797',
           'denominator':'4955319193827760237900000000000000000000'}
    assert record['id']=='lixiang90-single-exception-overlap-20261018'
    assert record['status']=='kernel-verified' and record['formalVerification'] is True
    assert record['author']=='Li Xiang' and record['github']=='lixiang90'
    assert record['exactRational']==metadata['score']==score
    assert metadata['id']==record['id'] and metadata['author']=={'github':'lixiang90','displayName':'Li Xiang'}
    assert comparison['this_candidate_promoted_to_public_record'] is True
    assert comparison['native_v4_source_used_for_identity'] is False
    for name in ['leaderboard_HTTP','accepted_source_HTTP','accepted_submission_HTTP']:
        assert comparison[name]['status']==200
    raw=(OFFICIAL/'accepted-Solution.lean.body').read_bytes()
    manifest_raw=(OFFICIAL/'accepted-submission.json.body').read_bytes()
    assert raw==LOCAL.read_bytes() and len(raw)==1979280 and sha(raw)==SOURCE_SHA
    assert len(raw)<=2_000_000
    assert comparison['raw_source_byte_equal_to_uploaded_v3'] is True
    assert comparison['UI_trimmed_source_byte_equal_to_uploaded_v3'] is True
    assert comparison['public_accepted_source']=={
      'bytes':1979280,'sha256':SOURCE_SHA,'UI_trimmed_bytes':1979279,
      'UI_trimmed_sha256':'7876f01cc50bc3d0b54e6f0770dfaa1802083df1e0ef35c47930dce22ed7028c'}
    # Bind the exact user job digest without modifying either accepted byte sequence.
    digest=sha(b'submission.json\0'+manifest_raw+b'proof/Solution.lean\0'+raw)
    assert digest==JOB_DIGEST
    old_math=(OLD/'MATHEMATICS.zh.md').read_text(encoding='utf-8')
    marker='\n本材料逐source接口和纯有理ratio核对；'
    assert old_math.count(marker)==1
    math_body=old_math.split(marker)[0]
    review=load(OLD/'mathematical-review.json')
    assert review['ratio']==score['numerator']+'/'+score['denominator']
    before={p:sha(Path(p).read_bytes()) for p in bound}
    assert before==bound
    urls={'record_source_metadata':record['sourceUrl'],'accepted_proof':record['proofUrl'],
          'leaderboard':'https://www.riemannzeta.fun/','leaderboard_snapshot_url':comparison['leaderboard_HTTP']['request_url']}
    status={
      'schema':'officially-accepted-v3-material-status-v1','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
      'record_id':record['id'],'author':record['author'],'github':record['github'],
      'score':score,'scorePercent':record['scorePercent'],'status':'kernel-verified',
      'formalVerification':True,'official_website_acceptance_confirmed':True,
      'acceptance_observed_at_utc':comparison['leaderboard_HTTP']['completed_at_utc'],
      'official_source_commit':comparison['public_source_commit'],'urls':urls,
      'source':{'path':'proof/Solution.lean','bytes':len(raw),'sha256':SOURCE_SHA,
                'version':'Officially accepted user-uploaded v3; not native-v4'},
      'submitted_job_digest':digest,'canonical_job_digest_matches_user_report':True,
      'raw_source_byte_equal_to_local_v3':True,
      'UI_normalization':comparison['UI_normalization'],
      'UI_trimmed_source_byte_equal':True,
      'official_fixed_policy_verified':True,
      'source_limit_bytes':2_000_000,'fixed_pipeline_budget_seconds':3200,
      'public_elapsed_seconds':None,
      'elapsed_status':'Not disclosed by the public accepted submission/record evidence; no seconds invented',
      'local_v0_total3200_failure_preserved':True,
      'local_v3_separate_kernel_checks_remain_separate':True,
      'native_v4_not_used_as_final_delivery':True,
      'native_v4_status':'No outcome asserted here; root may cancel redundant work without classifying it as mathematical failure or PASS',
      'project_final_GitHub_byte_sync':'Pending final root audit; official accepted proof is already at the immutable linked GitHub commit',
      'current_R_equals_candidate_because_this_submission_promoted':True,
      'do_not_require_improvement_over_own_promoted_kappa':True,
      'archive_builder_compiler_network_or_submission_runs':0}
    readme=f'''# 已官网通过：单例外相邻窗口法

**{record['scorePercent']}%**，精确比例为
`{score['numerator']}/{score['denominator']}`。

官方记录：[{record['id']}]({record['sourceUrl']})；
[已接受的完整 Lean 源码]({record['proofUrl']})。
作者 **{record['author']} / {record['github']}**，官方状态 **kernel-verified**、
formalVerification=true。冻结的独立HTTP证据于
{comparison['leaderboard_HTTP']['completed_at_utc']} 观察到本候选已经成为公开纪录。

本目录 `proof/Solution.lean` 是上述官方 raw 源码的逐字节归档：
**{len(raw)} UTF-8 bytes**，SHA256 `{SOURCE_SHA}`。
它与用户原上传v3相同，规范submission+proof digest是 `{digest}`，与用户job一致。
去尾空白后的文本少一个byte；该纯文本规范化比对关系另在原始独审保存；本归档保留完整raw字节。

数学新增是相邻九点窗口的唯一例外不兼容，以及只支付一次边界亏损的求和/计数转移；
见 `MATHEMATICS.zh.md`。相对提交前基准的精确增益见 `strict-improvement.json`。
现在网站R等于本候选，是本次已晋级的结果，不需无穷追赶自己的新纪录。

官网接受是该v3按固定官方验证pipeline通过的权威证据，包括单源≤2MB与固定3200秒
验收政策。公开record/submission未披露实际耗时，本材料不捏造耗时。此前本地v0的
3200秒超时、v3各核分别通过的诊断均原样保留；不回写为本地统一PASS。
独立运行中的native-v4不作为本次最终交付，也不以其状态替代官网v3的接受证据。

`official/`保留官方submission原字节、接受快照/HTTP收据和源码身份核对；原网站
method/summary按发布原文保留，其中上传当时的pending句子不代表当前状态。当前
状态以kernel-verified的官方API记录为准。数学说明采用准确的“九点/八gap”术语。

旧pending材料不覆写。工程仓库的最终GitHub同步与字节审计由root另保存回执；
官方接受proof本身已由所链接的immutable GitHub commit公开。此归档不再次上传。
'''
    final_math=math_body+'''\n\n本候选已由官网验证并成为上述公开纪录，原始接受证据与完整raw源码见本目录。
该状态对应用户已上传的v3，不是替代native-v4。本材料不改变原本地失败或诊断历史，
不声称公开证据提供了具体耗时；数学证明没有Riemann假设或未证局部floor前提。
'''
    DEST.mkdir()
    try:
        copy_bytes(DEST/'proof/Solution.lean',raw)
        archive_names=['accepted-submission.json.body','accepted-submission.json.http.json',
          'accepted-Solution.lean.http.json','leaderboard.body','leaderboard.http.json','comparison.json','files.json']
        for name in archive_names:copy_bytes(DEST/'official'/name,(OFFICIAL/name).read_bytes())
        copy_bytes(DEST/'official/local-kernel-checks-historical.json',
          (ROOT/'research-goal-20261019-tiny-kernel-evidence/checks.json').read_bytes())
        copy_bytes(DEST/'README.zh.md',readme.encode())
        copy_bytes(DEST/'MATHEMATICS.zh.md',final_math.encode())
        write(DEST/'acceptance-status.json',status)
        write(DEST/'strict-improvement.json',{
          'candidate':review['ratio'],'previous_record':review['baseline'],
          'exact_gain':review['ratio_gain_exact'],'gain_percentage_points_decimal':review['percentage_point_gain_decimal'],
          'basis':'Frozen exact ratio review and accepted official source identity',
          'current_equals_candidate_is_own_promotion':True})
        write(DEST/'provenance.json',{'official_evidence_manifest_sha256':OFFICIAL_PIN,
          'builder_prepared_sha256':args.prepared_sha256,'source_sha256':SOURCE_SHA,
          'canonical_job_digest':digest,'source_copied_without_normalization':True,
          'old_materials_not_modified':True,'no_new_compile_network_or_upload':True,
          'official_record_raw_method_and_summary_preserved':True})
        assert {p:sha(Path(p).read_bytes()) for p in bound}==bound
        assert sha((DEST/'proof/Solution.lean').read_bytes())==SOURCE_SHA
        files=[{'path':p.relative_to(DEST).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}
               for p in sorted(DEST.rglob('*')) if p.is_file()]
        write(DEST/'files.json',{'schema':'official-accepted-v3-final-materials-v1','files':files,
          'official_record_id':record['id'],'official_acceptance_confirmed':True,
          'source_sha256':SOURCE_SHA,'project_GitHub_final_sync_receipt':'pending root final audit',
          'builder_prepared_sha256':args.prepared_sha256})
        print(json.dumps({'accepted_materials_created':True,'source_sha256':SOURCE_SHA,
          'manifest_sha256':sha((DEST/'files.json').read_bytes()),'network_or_compile_runs':0}))
    except BaseException as e:
        write(DEST/'ARCHIVE-FAILED.json',{'failed':True,'error_type':type(e).__name__,'error':str(e)})
        raise

if __name__=='__main__':main()
