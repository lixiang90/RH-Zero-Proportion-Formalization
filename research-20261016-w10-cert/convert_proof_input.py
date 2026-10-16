"""Stream and parallelise the existing four-round relative leaf codec.

Reused low/high payloads are decoded and rechecked against the final cell.
This prepares exact data, not a Lean global proof or website submission.
"""
from pathlib import Path
import argparse,concurrent.futures,gzip,hashlib,json,shutil,time
import relative_codec as codec
from reduce_proof_input import Stream,sha
HERE=Path(__file__).parent
HELPERS=['convert_proof_input.py','relative_codec.py','compact_thin.py','tree_flow.py','generate.py','reduce_proof_input.py']
POINT={p:(l,u) for p,l,u,*_ in codec.thin.g.PT}
CHAR={v:i for i,v in enumerate(codec.ALPHABET)}

def accepted(path,metadata):
    source=Stream(path);source.eat('{');first=True
    while source.peek()!='}':
        if not first:source.eat(',')
        key=source.value();source.eat(':')
        if key=='accepted':yield from source.array()
        elif key=='branches':
            for _ in source.array():pass
        else:metadata[key]=source.value()
        first=False
    source.eat('}');assert source.peek()=='';source.close()

def validate_points(fs,lo,hi):
    g=codec.thin.g
    for (i,j,a),(kind,m,p,r) in zip(g.TERMS,fs):
        z=g.LOOK[i,j]
        for mass,point in zip(g.f.weights(kind,m),(p,r)):
            if mass:
                left,right=POINT[point];assert left<=lo[z]<=point<=hi[z]<=right

def convert_batch(batch,rounds):
    result=[];bits=reused=0
    for row,old in batch:
        path=row['path'];rec=row['result']
        if 'FS' not in rec:
            assert rec.get('empty')
            packed={'path':path,'kind':'reflection' if rec.get('reflection') else 'empty','violation_axis':rec.get('violation_axis')}
            if old is not None:assert old['kind']==packed['kind']
        else:
            lo=rec['certificate']['lower_bounds'];hi=rec['certificate']['upper_bounds']
            if old is not None:
                payload=0
                for char in old['text']:payload=payload*92+CHAR[char]
                word,code=divmod(payload,10**8)
                assert word==int(old['support_hex'],16) and code==old['tree_code']
                fs=codec.unpack_relative(word,lo,hi);validate_points(fs,lo,hi)
                total=codec.tree.value(fs,lo,hi,codec.tree.moves(fs,code))
                assert total==int(old['after_numerator'])>=codec.thin.THRESH
                same,numbits=codec.pack_relative(fs,lo,hi);assert same==word
                packed={k:old[k] for k in ('path','kind','text','support_hex','tree_code','after_numerator','source_bytes')}
                assert packed['kind']=='numeric' and packed['source_bytes']==len(packed['text'].encode())
                bits+=numbits;reused+=1
            else:
                c=codec.prepare(rec,rounds);validate_points(c['FS'],lo,hi)
                assert int(c['after_numerator'])>=codec.thin.THRESH
                packed={'path':path,'kind':'numeric','text':c['text'],'support_hex':c['support_hex'],
                    'tree_code':c['tree_code'],'after_numerator':c['after_numerator'],'source_bytes':c['text_source_bytes']}
                bits+=c['support_bits']
        result.append(packed)
    return result,bits,reused

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=3);ap.add_argument('--rounds',type=int,default=4)
    args=ap.parse_args();source=HERE/'ordered-proof-input.json';dest=HERE/'ordered-compact.json'
    checkpoint=HERE/'ordered-compact.checkpoint.json';assert not dest.exists(),'Immutable compact output already exists'
    started=time.monotonic();source_sha=sha(source);helpers={name:sha(HERE/name) for name in HELPERS}
    reduction=json.loads((HERE/'proof-input-reduction-manifest.json').read_text());assert reduction['reduced']['sha256']==source_sha
    reuse={};reuse_files={}
    for name in ['ordered-0-compact.json','ordered-2-compact.json']+([checkpoint.name] if checkpoint.exists() else []):
        path=HERE/name;reuse_files[name]=sha(path);data=json.loads(path.read_text())
        if name==checkpoint.name:assert data['receipt']['input_sha256']==source_sha
        for row in data['leaves']:
            assert row['path'] not in reuse or reuse[row['path']]==row;reuse[row['path']]=row
    metadata={};iterator=iter(accepted(source,metadata));leaves=[];fsbits=reused=0;active={};exhausted=False;next_save=10000
    def receipt(complete):
        nums=[z for z in leaves if z['kind']=='numeric'];payload=sum(z['source_bytes'] for z in nums)
        return {'scope':__doc__,'input':str(source),'input_sha256':source_sha,'input_closed':True,
            'complete_leaf_conversion':complete,'accepted_count':len(leaves),'numeric_count':len(nums),
            'unresolved_count':0,'rounds':args.rounds,'relative_FS_bits':fsbits,'base92_payload_source_bytes':payload,
            'average_numeric_source_bytes':payload/max(1,len(nums)),'reused_numeric_count':reused,
            'all_numeric_integer_checks_passed':True,'elapsed_seconds':time.monotonic()-started,
            'helpers_sha256':helpers,'reuse_inputs_sha256':reuse_files,
            'encoding':'Original four-round thin/reflow + relative FS + Pruefer + base92; unchanged integer checker.'}
    def save(path,complete):
        doc={'receipt':receipt(complete),'leaves':sorted(leaves,key=lambda z:z['path'])}
        tmp=path.with_suffix('.partial')
        with tmp.open('w',encoding='utf8',newline='\n') as out:json.dump(doc,out,separators=(',',':'));out.write('\n')
        tmp.replace(path)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        while not exhausted or active:
            while not exhausted and len(active)<2*args.workers:
                batch=[]
                for _ in range(128):
                    try:row=next(iterator)
                    except StopIteration:exhausted=True;break
                    batch.append((row,reuse.get(row['path'])))
                if batch:active[pool.submit(convert_batch,batch,args.rounds)]=True
            if not active:break
            done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                del active[future];rows,b,r=future.result();leaves.extend(rows);fsbits+=b;reused+=r
            if len(leaves)>=next_save:
                save(checkpoint,False);print(json.dumps(receipt(False)),flush=True);next_save+=10000
    assert metadata['complete_finite_partition'] and not metadata['unresolved'] and not metadata['unresolved_count']
    assert len(leaves)==metadata['accepted_count']==len({z['path'] for z in leaves})
    assert sha(codec.thin.g.PAR)==metadata['parameter_sha256']
    assert sha(codec.thin.g.f.SRC)==metadata['source_sha256']
    assert sha(source)==source_sha and helpers=={name:sha(HERE/name) for name in HELPERS}
    # Reuse inputs are immutable except the rolling conversion checkpoint.
    for name,value in reuse_files.items():
        if name!=checkpoint.name:assert sha(HERE/name)==value
    save(dest,True);packed=dest.with_suffix('.json.gz')
    with dest.open('rb') as inp,packed.open('wb') as out:
        with gzip.GzipFile(filename='',mode='wb',fileobj=out,compresslevel=9,mtime=0) as handle:shutil.copyfileobj(inp,handle,1<<20)
    final={'receipt':receipt(True),'output':{'path':dest.name,'sha256':sha(dest),'bytes':dest.stat().st_size},
        'gzip':{'path':packed.name,'sha256':sha(packed),'bytes':packed.stat().st_size},'source_unchanged':True,'helpers_unchanged':True}
    (HERE/'compact-conversion-manifest.json').write_text(json.dumps(final,indent=2)+'\n');print(json.dumps(final),flush=True)
if __name__=='__main__':main()
