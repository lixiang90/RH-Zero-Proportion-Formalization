"""Consolidate successful review/dependency oleans into the shared W10 root."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[1]
OUT=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    if not __debug__: raise RuntimeError('Assertions required')
    receipt=json.loads((OUT/'review-lean-verification.json').read_text())
    assert receipt['passed'] and len(receipt['modules'])==5
    runtime=json.loads((ROOT/'verification/gram-defect-20261015/setup/runtime.json').read_text())
    library=runtime['runtime_root']+'/w10-cert/lib'
    def call(args):
        r=subprocess.run(['wsl.exe','--distribution','Ubuntu','--exec']+args,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        assert r.returncode==0,(args,r.stdout,r.stderr)
        return r.stdout
    def remote_sha(path):
        r=re.findall(rb'(?<![0-9a-f])([0-9a-f]{64})  ',call(['sha256sum',path]))
        assert len(r)==1;return r[0].decode()
    rows=[]
    for r in receipt['modules']:
        name=r['module'];src=ROOT/(name.replace('.','/')+'.lean')
        assert sha(src)==r['source_sha256'] and remote_sha(r['olean'])==r['olean_sha256']
        target=library+'/'+name.replace('.','/')+'.olean'
        call(['cp',r['olean'],target]);assert remote_sha(target)==r['olean_sha256']
        rows.append({'module':name,'source_sha256':r['source_sha256'],'olean':target,'olean_sha256':r['olean_sha256']})
    original=receipt['modules'][0]['olean'].split('/StructuralW10Cert20261016/')[0]
    counting=json.loads((ROOT/'research-20261016/window-coboundary-counting-verification.json').read_text())
    wc=json.loads((ROOT/'research-20261016/spectral-w10-refined-compile.json').read_text())
    deps=[r['module'] for r in counting['compiled_modules']]+['StructuralResearch20261016.W10RefinedCandidate']
    call(['mkdir','-p',library+'/StructuralResearch20261016'])
    for name in deps:
        old=original+'/'+name.replace('.','/')+'.olean';digest=remote_sha(old)
        src=ROOT/(name.replace('.','/')+'.lean')
        if name.endswith('.W10RefinedCandidate'): assert sha(src)==wc['source_sha256']==wc['source_after_sha256']
        else:
            r=next(r for r in counting['compiled_modules'] if r['module']==name)
            assert sha(src)==r['source_sha256'] and digest==r['olean_sha256']
        target=library+'/'+name.replace('.','/')+'.olean'
        call(['cp',old,target]);assert remote_sha(target)==digest
        rows.append({'module':name,'source_sha256':sha(src),'olean':target,'olean_sha256':digest})
    result={'passed':True,'scope':'Exact byte copy of already successful review oleans and their frozen namespace dependencies; no new theorem is evaluated here',
        'library_root':library,'review_receipt_sha256':sha(OUT/'review-lean-verification.json'),'modules':rows}
    (OUT/'review-merged-lib.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'passed':True,'library_root':library,'modules':len(rows)}))

if __name__=='__main__':main()
