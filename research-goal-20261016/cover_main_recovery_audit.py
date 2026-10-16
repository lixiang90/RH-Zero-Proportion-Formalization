"""Read-only structural/guard audit of one stable main-search checkpoint.

This checks complete JSON, path-tree accounting, frontier DBM closure and
frozen source guards. It does not replay all 880k analytic certificates.
No search state, checkpoint or existing source is modified.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib,json,time
from cover_compact_checkpoint import Stream
HERE=Path(__file__).parent;ROOT=HERE.parent
PAIRS=[(i,i+1)for i in range(9)]+[(i,j)for i in range(9)for j in range(i+2,10)]


def array(stream,callback):
    stream.token('[')
    if stream.peek()!=']':
        while True:
            callback(stream.value())
            if stream.peek()!=',':break
            stream.token(',')
    stream.token(']')


def mapping(stream,callback):
    stream.token('{')
    if stream.peek()!='}':
        while True:
            key=stream.value();stream.token(':');callback(key,stream.value())
            if stream.peek()!=',':break
            stream.token(',')
    stream.token('}')


def main():
    start=time.monotonic();path=HERE/'window-compact-obbt-cover.json';stream=Stream(path);stream.token('{')
    meta={};leaves=set();branches={};kinds=Counter();depths=Counter();recent=[];axes=Counter();contractionkeys=set();sublevelkeys=set();steps=bounds=0
    def leaf(row):
        p=row['path'];assert p not in leaves and row['depth']==len(p)-1;leaves.add(p);kinds[row['kind']]+=1;depths[row['depth']]+=1
    def branch(row):
        p=row['path'];assert p not in branches and 0<=row['axis']<45 and isinstance(row['cut'],int)
        branches[p]=(row['axis'],row['cut']);recent.append(row);axes[row['axis']]+=1
        if len(recent)>5000:recent.pop(0)
    def contraction(p,rows):
        nonlocal steps
        assert p not in contractionkeys;contractionkeys.add(p);steps+=len(rows)
    def sublevel(p,row):
        nonlocal bounds
        assert p not in sublevelkeys;sublevelkeys.add(p);bounds+=len(row['b'])
    while stream.peek()!='}':
        key=stream.value();assert key not in meta;stream.token(':')
        if key=='accepted':array(stream,leaf);meta[key]='streamed'
        elif key=='branches':array(stream,branch);meta[key]='streamed'
        elif key=='contractions':mapping(stream,contraction);meta[key]='streamed'
        elif key=='sublevel_contractions':mapping(stream,sublevel);meta[key]='streamed'
        elif key=='tangent_data':
            count=[0];array(stream,lambda r:count.__setitem__(0,count[0]+1));meta[key]={'streamed_rows':count[0]}
        else:meta[key]=stream.value()
        if stream.peek()!=',':break
        stream.token(',')
    stream.token('}');assert stream.peek()=='';stream.file.close()
    frontier=meta['unresolved'];pending={r['path']for r in frontier};assert len(pending)==len(frontier)==meta['unresolved_count']
    assert len(leaves)==meta['accepted_count'] and dict(kinds)=={k:v for k,v in meta['counts'].items()if v}
    assert not(leaves&set(branches)or leaves&pending or set(branches)&pending)
    processed=leaves|set(branches);allnodes=processed|pending
    assert len(processed)==meta['checked'] and len(branches)==len(leaves)+len(pending)-1 and 'r'in allnodes
    assert all(p=='r'or p[:-1]in branches for p in allnodes)
    assert all(p+'0'in allnodes and p+'1'in allnodes for p in branches)
    assert contractionkeys<=processed and sublevelkeys<=processed
    assert len(contractionkeys)==meta['contraction_paths'] and steps==meta['contraction_steps']
    assert len(sublevelkeys)==meta['sublevel_contraction_paths'] and bounds==meta['sublevel_bounds']
    guards={}
    for p,digest in meta['input_sha256'].items():
        actual=hashlib.sha256((ROOT/p).read_bytes()).hexdigest();assert actual==digest,p;guards[p]=actual
    frontier_summary=[]
    for row in frontier:
        lo,hi=row['state'];assert row['depth']==len(row['path'])-1 and len(lo)==len(hi)==45
        assert all(isinstance(v,int)for v in lo+hi)and all(l<=u for l,u in zip(lo,hi))
        matrix=[[0]*10 for _ in range(10)]
        for (i,j),l,u in zip(PAIRS,lo,hi):matrix[i][j]=u;matrix[j][i]=-l
        assert all(matrix[i][j]<=matrix[i][k]+matrix[k][j]for i in range(10)for j in range(10)for k in range(10))
        correlation=[]
        for z,(i,j)in enumerate(PAIRS):
            if j-i>1:correlation.append((max(lo[z]-sum(lo[i:j]),sum(hi[i:j])-hi[z]),i,j))
        frontier_summary.append({'path':row['path'],'depth':row['depth'],'free_coordinates':sum(v>31488for v in lo[:9]),
          'midpoint_integer_pattern':[(l+u+32768)//65536for l,u in zip(lo[:9],hi[:9])],
          'largest_nonadjacent_correlation_units':sorted(correlation,reverse=True)[:3]})
    prefix=recent[0]['path']
    for row in recent:
        while not row['path'].startswith(prefix):prefix=prefix[:-1]
    report={'scope':__doc__,'audit_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checkpoint_sha256':stream.sha.hexdigest(),'checkpoint_bytes':stream.size,'metadata':{k:meta[k]for k in ['pid','checked','accepted_count','counts','unresolved_count','maxdepth','seconds','resumed_from','target','contraction_paths','contraction_steps','sublevel_contraction_paths','sublevel_bounds']},
      'passed_complete_JSON_and_binary_prefix_tree':True,'checked_source_guards':guards,'branch_count':len(branches),
      'accepted_depth_counts':dict(sorted(depths.items())),'all_split_axis_counts':dict(sorted(axes.items())),
      'recent_5000_common_prefix':prefix,'recent_split_axes':dict(Counter(r['axis']for r in recent)),
      'recent_split_ranks':dict(Counter(PAIRS[r['axis']][1]-PAIRS[r['axis']][0]for r in recent)),
      'prefix_pending_binary_mass':str(sum(F(1,2**r['depth'])for r in frontier)),
      'binary_mass_is_not_geometric_volume_or_completion_fraction':True,'frontier_DBM_closure_checked':True,'frontier':frontier_summary,
      'full_semantic_leaf_and_contraction_replay_performed':False,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'seconds':time.monotonic()-start}
    out=HERE/'cover-main-recovery117500-audit.json';out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'all_structure_and_guard_checks_passed':True,'checkpoint_sha256':report['checkpoint_sha256'],
      'checkpoint_bytes':stream.size,'metadata':report['metadata'],'branch_count':len(branches),
      'recent_prefix':prefix,'recent_split_ranks':report['recent_split_ranks'],'seconds':report['seconds']}),flush=True)
if __name__=='__main__':main()
