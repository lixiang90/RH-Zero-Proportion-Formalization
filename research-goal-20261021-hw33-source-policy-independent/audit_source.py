"""Independent byte/metadata audit; never imports or evaluates Lean/project code."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import re
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent.parent
OUT = Path(__file__).resolve().parent
BASE = ROOT / 'research-goal-20261021-attempt030-api-source-v1/Solution.lean'
DRAFT = ROOT / 'research-goal-20261021-hw33-delivery/draft-v12'
PROBE = ROOT / 'research-goal-20261021-attempt030-h33-arithmetic-probe-preparation-v2'
POLICY = ROOT / 'research-goal-20261020-w9a2-source-normalization-review/source/src/lib'

def pin(p):
    b = p.read_bytes()
    return {'path': str(p.relative_to(ROOT)).replace('\\', '/'),
            'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}

paths = [BASE, DRAFT/'Solution.lean', DRAFT/'projection.json', DRAFT/'files.json',
         ROOT/'research-goal-20261021-hw33-source-preparation-v1/prepare.py',
         PROBE/'FloorProbe.lean', PROBE/'preparation.json', PROBE/'files.json']
paths += [POLICY/n for n in ['challenge.ts', 'direct-submission.ts',
                            'github-promotion.ts', 'attestation.ts', 'records.ts']]
before = [pin(p) for p in paths]
old = BASE.read_bytes()
new = (DRAFT/'Solution.lean').read_bytes()
projection = json.loads((DRAFT/'projection.json').read_bytes())
assert len(old) == 1798336
assert hashlib.sha256(old).hexdigest() == 'c2f3b3d0d1e2d0a3fab63320092b0ac10aace2d501376431bb08e487ae673ad7'
assert len(new) == 1799144
assert hashlib.sha256(new).hexdigest() == 'a3b0ee880a647539e4bdb65a31e693de5b8e2e5ad085ec46ebbd031319a848cb'

h0 = '67212374687824171413662471723172'
h1 = '672123746878241714136624717231727'
r0 = '2187514111273670128882891873424900096 / 3247536873076144967761579035576953125'
r1 = '10937570556368350644414459367124615168 / 16237684365380724838807895177884765625'
rules = [(h0+' / 10 ^ 32', h1+' / 10 ^ 33', 4),
         (h0+' / '+str(10**32), h1+' / '+str(10**33), 16), (r0,r1,5)]
spans = []
for a,b,count in rules:
    aa,bb = a.encode(),b.encode()
    matches = list(re.finditer(re.escape(aa),old))
    assert len(matches) == count
    spans.extend({'offset':m.start(),'old':a,'new':b} for m in matches)
spans.sort(key=lambda s:s['offset'])
assert spans == projection['spans']
assert len(spans) == 25
for a,b in zip(spans,spans[1:]):
    assert a['offset']+len(a['old'].encode()) <= b['offset']
notice = ('''/-
Copyright (c) 2026 Li Xiang. SPDX-License-Identifier: Apache-2.0
Changes by Li Xiang with Codex, 2026-10-21: derived from Samuel Lavery
(samlavery), official attempt-030, commit 94954faf2713ae9628d6fbca0ae24fe64370507c.
All original attribution and license notices are retained below.
Only the terminal HW rational floor is sharpened from 67212374687824171413662471723172/10^32
to 672123746878241714136624717231727/10^33, using the same original rational bounds
on pi, sqrt(2)/2, cosine and sine. The same certificate, window, weights,
tables and actual dyadic/cumulative counting proofs are retained.
The sharper constant is propagated through those proofs and the final score.
No additional verification or official acceptance is claimed by this notice.
-/
''').encode()
assert len(notice) == 762
# Rebuild independently from disjoint ORIGINAL slices (not the producer's algorithm).
parts = [notice]
cursor = 0
for s in spans:
    at=s['offset']; a=s['old'].encode(); b=s['new'].encode()
    assert old[at:at+len(a)] == a
    parts.extend([old[cursor:at],b]); cursor=at+len(a)
parts.append(old[cursor:])
assert b''.join(parts) == new
# Reverse ACTUAL new bytes, independently locating shifted spans right-to-left.
shift = len(notice)
shifted = []
for s in spans:
    shifted.append((s['offset']+shift,s['old'].encode(),s['new'].encode()))
    shift += len(s['new'].encode())-len(s['old'].encode())
reverse = new
for at,a,b in reversed(shifted):
    assert reverse[at:at+len(b)] == b
    reverse = reverse[:at]+a+reverse[at+len(b):]
assert reverse[:len(notice)] == notice
assert reverse[len(notice):] == old
assert shift == len(new)-len(old) == 808
assert len(new) < 2000000

def comments(data):
    """Finite source scanner for nested Lean comments and escaped double strings."""
    result=[]; i=0
    while i<len(data):
        if data[i:i+2] == b'/-':
            start=i; depth=1; i+=2
            while depth:
                assert i<len(data)
                if data[i:i+2]==b'/-': depth+=1; i+=2
                elif data[i:i+2]==b'-/': depth-=1; i+=2
                else: i+=1
            result.append((start,i,data[start:i]))
        elif data[i:i+2] == b'--':
            start=i; end=data.find(b'\n',i)
            i=len(data) if end<0 else end
            result.append((start,i,data[start:i]))
        elif data[i:i+1] == b'"':
            i+=1
            while i<len(data):
                if data[i:i+1]==b'\\': i+=2
                elif data[i:i+1]==b'"': i+=1; break
                else: i+=1
        else: i+=1
    return result
oc,nc=comments(old),comments(new)
assert [x[2] for x in nc[1:]] == [x[2] for x in oc]
assert nc[0][2] == notice[:-1]
for s in spans:
    a=s['offset']; b=a+len(s['old'].encode())
    assert all(b<=x or a>=y for x,y,_ in oc)

names=['candidate_strict_improvement','candidate_critical_line_bound',
       'candidate_critical_line_bound_cumulative']
headers={}
for name in names:
    pattern=rb'^theorem '+name.encode()+rb'\s*:(.*?) := by'
    a=re.search(pattern,old,re.M|re.S); b=re.search(pattern,new,re.M|re.S)
    assert a and b and a.group()==b.group()
    headers[name]=a.group().decode()
imports=lambda b:re.findall(rb'^import [^\n]+$',b,re.M)
assert imports(old)==imports(new)
start=old.index(b'namespace AMW.Cert.PC9WF\n')
stop=old.index(b'end AMW.Cert.PC9WFData',start)+len(b'end AMW.Cert.PC9WFData')
cert=old[start:stop]
assert new.count(cert)==1
assert all(s['offset']>=stop or s['offset']+len(s['old'].encode())<=start for s in spans)
cert_pin={'original_start':start,'bytes':len(cert),'sha256':hashlib.sha256(cert).hexdigest(),
          'exact_contiguous_in_new':True}

def verify_manifest(directory):
    manifest=json.loads((directory/'files.json').read_bytes())
    for row in manifest['files']:
        p=directory/row['path']; b=p.read_bytes()
        assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256']
    return {'manifest':pin(directory/'files.json'),'member_count':len(manifest['files'])}
manifests=[verify_manifest(DRAFT),verify_manifest(PROBE)]

H0,H1=Fraction(int(h0),10**32),Fraction(int(h1),10**33)
R0,R1=[Fraction(*map(int,r.split(' / '))) for r in (r0,r1)]
c=Fraction(74913604925068882530357668923,8388608000000000000000000000000)
B=Fraction(38146515192197939200000000000,8388608000000000000000000000000)
assert H1-H0==Fraction(7,10**33)
assert (H0-B)/(1-c)==R0 and (H1-B)/(1-c)==R1
assert R1-R0==Fraction(114688,16237684365380724838807895177884765625)>0
def displayed(x,digits):
    q=x.numerator*10**digits//x.denominator
    return str(q//10**digits)+'.'+str(q%10**digits).zfill(digits)
assert displayed(R0,30)==displayed(R1,30)
assert displayed(100*R0,28)==displayed(100*R1,28)

# Static probe copy/target checks only: no Lean parsing, evaluation or proof check.
probe=(PROBE/'FloorProbe.lean').read_bytes().replace(b'\r\n',b'\n')
def decl(data,name):
    p=re.compile(rb'^(?:def|theorem) '+re.escape(name.encode())+rb'(?=\s|:)',re.M)
    m=p.search(data); assert m
    tail=data[m.start():]
    nxt=re.search(rb'\n(?:def|theorem|lemma|namespace|end) ',tail[1:])
    return tail[:nxt.start()+1] if nxt else tail
for name in ['cAMn','cAM','dAM','PAMhi']:
    assert decl(old,name).strip()==decl(probe,name).strip(),name
assert decl(old,'floor_numeric').replace(rules[0][0].encode(),rules[0][1].encode()).strip()==decl(probe,'floor_numeric').strip()
ratio=decl(probe,'h33_ratio_exact')
strict=decl(probe,'h33_strict_improvement')
assert r1.encode() in ratio and r0.encode() in strict and r1.encode() in strict
assert ratio.rstrip().endswith(b'norm_num') and strict.rstrip().endswith(b'norm_num')

after=[pin(p) for p in paths]
assert before==after
spans_report=[]
for s in spans:
    prefix=old[:s['offset']]
    declarations=list(re.finditer(rb'^(?:(?:private|protected|noncomputable) )*(?:theorem|lemma|def) ([^\s:]+)',prefix,re.M))
    spans_report.append({**s,'original_line':prefix.count(b'\n')+1,
                         'enclosing_explicit_declaration':declarations[-1].group(1).decode()})
report={'schema':'independent-hw33-source-policy-metadata-audit-v1',
        'observed_at_utc':datetime.now(timezone.utc).isoformat(),
        'complete_independent_source_projection_checks':1,
        'source_projection':{'forward_exact':True,'inverse_exact':True,'spans':spans_report,
         'literal_replacement_counts':[4,16,5],'notice_bytes':762,'replacement_net_bytes':46,
         'total_increase':808,'source_bytes':len(new),'limit_bytes':2000000,
         'original_comment_count':len(oc),'all_original_comments_in_order_exact':True,
         'spans_outside_comments':True,'CRLF_before':old.count(b'\r\n'),'CRLF_after':new.count(b'\r\n'),
         'all_other_original_bytes_exact':True,'imports_exact':True,
         'public_theorem_type_headers_exact':headers,'certificate_interval':cert_pin},
        'exact_score_metadata':{'oldH':str(H0),'newH':str(H1),'H_gain':str(H1-H0),
         'oldR':str(R0),'newR':str(R1),'strict_gain':str(R1-R0),
         'same_c_B_ratio_identity':True,'display30_both':displayed(R1,30),
         'percent28_both':displayed(100*R1,28),'binary64_equal':float(R0)==float(R1)},
        'probe_static_only':{'copied_four_definitions_exact':True,
         'floor_numeric_only_target_literal_changed':True,'ratio_strict_targets_match':True,
         'Lean_checked':False},
        'verified_small_manifests':manifests,'inputs_unchanged_during_audit':True,
        'Lean_runs':0,'project_parser_or_decoder_runs':0,'leaf_or_walk_numeric_replay_runs':0,
        'network_requests':0,'official_acceptance_checked':False}
(OUT/'audit-result.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
(OUT/'input-pins.json').write_text(json.dumps({'schema':'read-input-pins-v1','files':before},indent=2)+'\n',encoding='utf-8')
print(json.dumps({'audit':'PASS_METADATA','spans':25,'forward':True,'inverse':True,
                  'notice_bytes':762,'source_bytes':len(new),'comments_preserved':len(oc),
                  'gain':str(R1-R0),'probe_static_only':True}))
