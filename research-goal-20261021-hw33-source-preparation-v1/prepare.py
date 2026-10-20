"""One exact arithmetic sharpening of the frozen attempt-030 source.
No certificate traversal, optimizer, Lean, network or trusted-spec replacement.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib, json, re

ROOT=Path(__file__).resolve().parent.parent
BASE=ROOT/'research-goal-20261021-attempt030-api-source-v1/Solution.lean'
OUT=ROOT/'research-goal-20261021-hw33-delivery/draft-v12'
SHA='c2f3b3d0d1e2d0a3fab63320092b0ac10aace2d501376431bb08e487ae673ad7'
H0='67212374687824171413662471723172'
H1='672123746878241714136624717231727'
R0='2187514111273670128882891873424900096 / 3247536873076144967761579035576953125'
R1='10937570556368350644414459367124615168 / 16237684365380724838807895177884765625'

def pin(b): return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def main():
    assert not OUT.exists()
    original=BASE.read_bytes()
    assert len(original)==1798336 and hashlib.sha256(original).hexdigest()==SHA
    text=original.decode('utf-8')
    coefficients={int(i):int(v) for i,v in re.findall(r'\| (\d+) => (-?\d+)',text[text.index('def cAMn'):text.index('def cAM (')])}
    assert list(coefficients)==list(range(13))
    pi=F(3141592653589793238462643383280,10**30)
    cosine=F(76024459707563015125354719862329,10**32)
    root_half=F(70710678118654752440084436210484,10**32)
    sine=F(64963693908006244412947861604410,10**32)
    P=sum((F(coefficients[n+1],10**9)**2*(F(1,2)-1/(4*pi*pi*(n+1)**2)) for n in range(12)),F(0))
    E=F(3,2)-cosine/(2*root_half*sine)-P/(2*sine*sine)
    oldH=F(int(H0),10**32);newH=F(int(H1),10**33)
    assert E.numerator*10**33//E.denominator==int(H1) and oldH<newH<=E
    c=F(74913604925068882530357668923,8388608000000000000000000000000)
    B=F(38146515192197939200000000000,8388608000000000000000000000000)
    oldR=F(*map(int,R0.split(' / ')));newR=F(*map(int,R1.split(' / ')))
    assert (oldH-B)/(1-c)==oldR and (newH-B)/(1-c)==newR and newR-oldR==F(114688,newR.denominator)
    # Exact ASCII spellings below occur only in executable declarations.
    # Historical notices spell 10^32 with superscripts and are not replaced.
    rules=[(H0+' / 10 ^ 32',H1+' / 10 ^ 33',4),
           (H0+' / '+str(10**32),H1+' / '+str(10**33),16),
           (R0,R1,5)]
    spans=[]
    for old,new,count in rules:
        actual=text.count(old)
        assert actual==count,(old,actual,count)
        for m in re.finditer(re.escape(old),text):
            spans.append({'offset':len(text[:m.start()].encode()),'old':old,'new':new})
    spans.sort(key=lambda item:item['offset'])
    assert all(a['offset']+len(a['old'].encode())<=b['offset'] for a,b in zip(spans,spans[1:]))
    transformed=original
    for item in reversed(spans):
        at=item['offset'];old=item['old'].encode();new=item['new'].encode()
        assert transformed[at:at+len(old)]==old
        transformed=transformed[:at]+new+transformed[at+len(old):]
    # Do not search-and-replace rounded constants used by the original enclosures.
    notice=(' /-\nCopyright (c) 2026 Li Xiang. SPDX-License-Identifier: Apache-2.0\n'
            'Changes by Li Xiang with Codex, 2026-10-21: derived from Samuel Lavery\n'
            '(samlavery), official attempt-030, commit 94954faf2713ae9628d6fbca0ae24fe64370507c.\n'
            'All original attribution and license notices are retained below.\n'
            'Only the terminal HW rational floor is sharpened from '+H0+'/10^32\n'
            'to '+H1+'/10^33, using the same original rational bounds\n'
            'on pi, sqrt(2)/2, cosine and sine. The same certificate, window, weights,\n'
            'tables and actual dyadic/cumulative counting proofs are retained.\n'
            'The sharper constant is propagated through those proofs and the final score.\n'
            'No additional verification or official acceptance is claimed by this notice.\n'
            '-/\n').lstrip().encode()
    final=notice+transformed
    assert len(final)<=2000000
    inverse=transformed
    for item in spans:
        # Offsets in the original are restored from left to right.
        at=item['offset'];new=item['new'].encode();old=item['old'].encode()
        assert inverse[at:at+len(new)]==new
        inverse=inverse[:at]+old+inverse[at+len(new):]
    assert inverse==original
    OUT.mkdir(parents=True)
    (OUT/'Solution.lean').write_bytes(final)
    report={'schema':'one-decimal-HW-sharpening-source-v1','original':pin(original),'source':pin(final),
            'notice_bytes':len(notice),'spans':spans,'span_count':len(spans),'inverse_byte_equal':True,
            'E':str(E),'oldH':str(oldH),'newH':str(newH),'rational_floor_residual':str(E-newH),
            'oldR':str(oldR),'newR':str(newR),'strict_gain':str(newR-oldR),
            'certificate_and_all_other_original_bytes_unchanged':True,
            'CRLF_before':original.count(b'\r\n'),'CRLF_after':final.count(b'\r\n'),
            'Lean_executed':False,'official_accepted':False}
    (OUT/'projection.json').write_bytes((json.dumps(report,indent=2)+'\n').encode())
    manifest={'schema':'hw33-draft-source-files-v1','files':[{'path':name,**pin((OUT/name).read_bytes())} for name in ['Solution.lean','projection.json']]}
    (OUT/'files.json').write_bytes((json.dumps(manifest,indent=2)+'\n').encode())
    print(json.dumps({k:report[k] for k in ['source','span_count','inverse_byte_equal','newH','newR','strict_gain','Lean_executed']}))

if __name__=='__main__': main()
