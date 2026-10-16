"""Capture one targeted negative-curvature proof and its compact main ancestry."""
from pathlib import Path
import gzip,hashlib,json
from cover_compact_checkpoint import Stream
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    raw=(HERE/'cover-targeted-quadratic-gradient.json').read_bytes();probe=json.loads(raw)
    verified=json.loads((HERE/'cover-targeted-curvature-replay.json').read_bytes());assert verified['all_passed'] and verified['input_sha256']==sha(raw)
    successful=[r for r in probe['results'] if r['uniform_negative_curvature_certificate']];assert len(successful)==1
    row=successful[0];path=row['path'];needed={path[:k] for k in range(1,len(path))}
    snapraw=(HERE/'cover-current-frontier-20261017b.json').read_bytes();assert sha(snapraw)==probe['snapshot_sha256']
    state=next(r['state'] for r in json.loads(snapraw)['frontier'] if r['path']==path)
    stream=Stream(HERE/'window-compact-obbt-cover.json');stream.token('{');meta={};branches={};newton={};obbt={};desc=[];accepted=0
    def mapping(out):
        stream.token('{')
        while stream.peek()!='}':
            p=stream.value();stream.token(':');value=stream.value()
            if p in needed:out[p]=value
            if stream.peek()!=',':break
            stream.token(',')
        stream.token('}')
    while stream.peek()!='}':
        key=stream.value();stream.token(':')
        if key=='accepted':
            def leaf(r):
                nonlocal accepted
                if r['path'].startswith(path):accepted+=1
            stream.array(leaf)
        elif key=='branches':
            def branch(r):
                if r['path'] in needed:branches[r['path']]=r
                if r['path'].startswith(path):desc.append(r)
            stream.array(branch)
        elif key=='contractions':mapping(newton)
        elif key=='sublevel_contractions':mapping(obbt)
        elif key in ['unresolved','tangent_data']:stream.value()
        else:meta[key]=stream.value()
        if stream.peek()!=',':break
        stream.token(',')
    stream.token('}');assert stream.peek()=='';stream.file.close();assert set(branches)==needed
    data={'scope':__doc__,'checkpoint_sha256':stream.sha.hexdigest(),'checkpoint_bytes':stream.size,'checkpoint_checked':meta['checked'],
      'target':meta['target'],'root':meta['root'],'path':path,'cell':state,'ancestor_branches':branches,'ancestor_OBBT':obbt,'ancestor_Newton':newton,
      'curvature':row['uniform_negative_curvature_certificate'],'reported_descendant_branches':desc,'reported_accepted_descendants':accepted,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    content=(json.dumps(data,separators=(',',':'))+'\n').encode();packed=gzip.compress(content,compresslevel=9,mtime=0)
    folder=HERE/'cover-targeted-curvature-evidence';folder.mkdir(exist_ok=True);(folder/'proof.json.gz').write_bytes(packed)
    pins={p.replace('\\','/'):v for p,v in meta['input_sha256'].items()}
    for name in ['cover_correlated_curvature_verify.py','cover_targeted_curvature_archive_replay.py','cover_sublevel_obbt_verify.py']:
        pins['research-goal-20261016/'+name]=sha((HERE/name).read_bytes())
    header={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'sources':pins,'file':'proof.json.gz','bytes':len(packed),'sha256':sha(packed),
      'uncompressed_sha256':sha(content),'target':meta['target'],'path':path,'ancestor_nodes':len(needed),
      'reported_source_descendant_branches':len(desc),'descendant_contractions_replayed':False,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False}
    (folder/'manifest.json').write_text(json.dumps(header,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in header.items() if k!='sources'}),flush=True)
if __name__=='__main__':main()
