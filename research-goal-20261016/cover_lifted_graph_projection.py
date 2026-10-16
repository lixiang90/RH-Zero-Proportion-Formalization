"""Freeze completed old subtrees below the thirteen graph parents, share-delete safe."""
from pathlib import Path
import gzip,hashlib,json,time
from cover_compact_checkpoint import Stream
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()


def main():
    start=time.monotonic();proofraw=(HERE/'cover-lifted-graph64.json').read_bytes();proof=json.loads(proofraw);positive={r['path']:r for r in proof['rows'] if r['graph']}
    packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();frozen=json.loads(gzip.decompress(packed));assert sha(packed)==proof['receipt']['input_sha256']
    prefix_length={len(p) for p in positive};assert len(prefix_length)==1;prefix_length=prefix_length.pop()
    def inside(p):return p[:prefix_length] in positive
    ancestors={p[:k] for p in positive for k in range(1,len(p))};old={'accepted':[],'branches':[],'OBBT':{},'Newton':{}};source={'branches':{},'OBBT':{},'Newton':{}}
    stream=Stream(HERE/'window-compact-obbt-cover.json');stream.token('{');meta={};pending=[]
    def mapping(out,prior):
        stream.token('{')
        while stream.peek()!='}':
            p=stream.value();stream.token(':');row=stream.value()
            if inside(p):out[p]=row
            elif p in ancestors:prior[p]=row
            if stream.peek()!=',':break
            stream.token(',')
        stream.token('}')
    def branch(row):
        p=row['path']
        if inside(p):old['branches'].append(row)
        elif p in ancestors:source['branches'][p]=row
    while stream.peek()!='}':
        key=stream.value();stream.token(':')
        if key=='accepted':stream.array(lambda r:old['accepted'].append(r) if inside(r['path']) else None)
        elif key=='branches':stream.array(branch)
        elif key=='sublevel_contractions':mapping(old['OBBT'],source['OBBT'])
        elif key=='contractions':mapping(old['Newton'],source['Newton'])
        elif key=='unresolved':stream.array(lambda r:pending.append(r) if inside(r['path']) else None)
        elif key=='tangent_data':stream.value()
        else:meta[key]=stream.value()
        if stream.peek()!=',':break
        stream.token(',')
    stream.token('}');assert stream.peek()=='';stream.file.close();assert not pending
    assert meta['target']==frozen['target']=='11/1250' and meta['root']==frozen['root'];assert set(source['branches'])==ancestors
    for name,digest in meta['input_sha256'].items():assert sha((ROOT/name).read_bytes())==digest,name
    source.update({k:meta[k] for k in ['root','target','input_sha256']});source['cases']=[r for r in frozen['cases'] if r['path'] in positive]
    replacements=[{'path':p,'depth':len(p)-1,'kind':'lifted_graph','result':r['graph']} for p,r in positive.items()]
    oldraw=(json.dumps(old,separators=(',',':'))+'\n').encode();newraw=(json.dumps(replacements,separators=(',',':'))+'\n').encode()
    counts={'old_branches':len(old['branches']),'old_leaves':len(old['accepted']),'new_graph_leaves':len(replacements),
      'old_OBBT_paths':len(old['OBBT']),'old_OBBT_bounds':sum(len(r['b']) for r in old['OBBT'].values()),
      'old_Newton_paths':len(old['Newton']),'old_Newton_steps':sum(len(r) for r in old['Newton'].values()),
      'old_subtrees_raw_bytes':len(oldraw),'old_subtrees_gzip_bytes':len(gzip.compress(oldraw,mtime=0)),
      'new_leaves_raw_bytes':len(newraw),'new_leaves_gzip_bytes':len(gzip.compress(newraw,mtime=0))}
    out={'schema':'lifted-graph-local-replacement-v1','source':source,'old_subtrees':old,'replacements':replacements,
      'source_checkpoint_sha256':stream.sha.hexdigest(),'source_checkpoint_bytes':stream.size,'source_checked':meta['checked'],
      'graph64_proof_sha256':sha(proofraw),'counts':counts,'complete_global_cover':False,'new_zero_proportion_proven':False}
    raw=(json.dumps(out,separators=(',',':'))+'\n').encode();compressed=gzip.compress(raw,mtime=0);target=HERE/'cover-lifted-graph-replacement.input.json.gz';target.write_bytes(compressed)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(compressed),'compressed_bytes':len(compressed),
      'uncompressed_sha256':sha(raw),'uncompressed_bytes':len(raw),'source_checkpoint_sha256':stream.sha.hexdigest(),'source_checked':meta['checked'],
      'counts':counts,'independent_replay_passed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-lifted-graph-replacement-snapshot.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
