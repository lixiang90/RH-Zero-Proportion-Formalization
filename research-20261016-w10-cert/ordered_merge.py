"""Merge disjoint ordered-search prefixes and replay their exact geometry."""
from pathlib import Path
import argparse, gzip, hashlib, json, shutil, time
import ordered_generate as o

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=Path(__file__).with_name('ordered-complete.json'))
    ap.add_argument('--inputs',nargs='+',type=Path);args=ap.parse_args();here=Path(__file__).parent
    paths=args.inputs or [here/'ordered-master.json']+[here/f'ordered-{i}.json' for i in range(3)]
    started=time.monotonic();branches={};leaves={};frontier={};inputs=[]
    for p in paths:
        raw=p.read_bytes();x=json.loads(raw);inputs.append({'path':str(p),'sha256':hashlib.sha256(raw).hexdigest()})
        assert x['normalize_rounds']==2
        for r in x['branches']:
            assert r['path'] not in branches and r['path'] not in leaves;branches[r['path']]=r
        for r in x['accepted']:
            assert r['path'] not in branches and r['path'] not in leaves;leaves[r['path']]=r
        for r in x['unresolved']:
            assert r['path'] not in frontier or frontier[r['path']]==r;frontier[r['path']]=r
    frontier={p:r for p,r in frontier.items() if p not in branches and p not in leaves}
    used=set();todo=[('r',o.g.root())];empty=0;maxdepth=0
    while todo:
        p,s=todo.pop();maxdepth=max(maxdepth,len(p)-1)
        assert p not in used;used.add(p)
        if p in frontier:
            assert list(s)==frontier[p]['state'],('frontier geometry mismatch',p);continue
        norm,cuts=o.normalize(s)
        if p in branches:
            r=branches[p]
            if 'normalize_cuts' in r:assert r['normalize_cuts']==cuts
            a=r['axis'];q=r['cut'];assert 0<=a<45 and norm[0][a]<q<norm[1][a],('bad split',p,a,q)
            todo.append((p+'1',o.rawsplit(norm,a,q,False)));todo.append((p+'0',o.rawsplit(norm,a,q,True)))
        elif p in leaves:
            r=leaves[p];rec=r['result'];assert r['normalize_cuts']==cuts
            cert=rec.get('certificate')
            if cert:assert (cert['lower_bounds'],cert['upper_bounds'])==norm,('leaf geometry mismatch',p)
            if rec.get('empty'):
                assert any(l>u for l,u in zip(*norm)) or norm[1][8]<norm[0][0],('false empty leaf',p);empty+=1
            else:
                assert int(rec['mcheck_numerator'])>=o.g.TARGET and rec['mcheck_numerator']==rec['floor_numerator']
        else:raise AssertionError(('missing node',p))
    assert used==set(branches)|set(leaves)|set(frontier),'Unreachable or overlapping data'
    out={'scope':'Merged exact-integer discovery certificate; full Lean theorem still requires kernel replay',
        'format':'ordered-mcheckGX-1024','normalize_rounds':2,'root':o.g.root(),'target':'433/50000',
        'parameter_sha256':hashlib.sha256(o.g.PAR.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(o.g.f.SRC.read_bytes()).hexdigest(),
        'checked':len(branches)+len(leaves),'accepted_count':len(leaves),'unresolved_count':len(frontier),
        'complete_finite_partition':not frontier,'geometry_replayed':True,'maxdepth':maxdepth,
        'empty_leaves':empty,'numeric_leaves':len(leaves)-empty,'inputs':inputs,
        'terms':o.g.TERMS,'denominator':str(o.g.DEN),'SC':o.g.SC,'mixture_denominator':o.g.LD,
        'elapsed_seconds':time.monotonic()-started,'branches':[branches[p] for p in sorted(branches)],
        'accepted':[leaves[p] for p in sorted(leaves)],'unresolved':[frontier[p] for p in sorted(frontier)]}
    # The final data can be hundreds of megabytes; avoid a second full JSON
    # string and a second full decompressed byte copy in memory.
    with args.output.open('w',encoding='utf8',newline='\n') as handle:
        json.dump(out,handle,separators=(',',':'));handle.write('\n')
    packed_path=args.output.with_suffix('.json.gz')
    with args.output.open('rb') as source,packed_path.open('wb') as target:
        with gzip.GzipFile(filename='',mode='wb',fileobj=target,compresslevel=9,mtime=0) as packed:
            shutil.copyfileobj(source,packed,1<<20)
    def digest(path):
        value=hashlib.sha256()
        with path.open('rb') as stream:
            while chunk:=stream.read(1<<20):value.update(chunk)
        return value.hexdigest()
    report={k:out[k] for k in ['checked','accepted_count','unresolved_count','complete_finite_partition',
        'geometry_replayed','maxdepth','empty_leaves','numeric_leaves','elapsed_seconds']}
    report['branches']=len(branches)
    print(json.dumps(report),flush=True)
    print(json.dumps({'json_bytes':args.output.stat().st_size,'gzip_bytes':packed_path.stat().st_size,
        'sha256':digest(args.output),'gzip_sha256':digest(packed_path)}),flush=True)
    return report
if __name__=='__main__':main()
