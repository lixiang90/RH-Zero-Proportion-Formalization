"""Exact 69-basin overlap diagnostic and streaming split-growth inventory."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import hashlib,json,time
from cover_contractor_verify import close
from cover_correlated_replay import SC,a
from cover_compact_checkpoint import Stream
HERE=Path(__file__).parent

def main():
    start=time.monotonic();snapshot=HERE/'cover-current-frontier-20261017b.json';sraw=snapshot.read_bytes();source=json.loads(sraw)
    gramraw=(HERE/'cover-newwindow-gram.json').read_bytes();basins=json.loads(gramraw)['results'];rows=[]
    for original in source['frontier']:
        lo,hi=original['state'];whole=[];intersect=[];anchors=[];near=[]
        for k,basin in enumerate(basins):
            lower=[v*100 for v in lo];upper=[v*100 for v in hi];fail=0
            for scalar in basin['scalar_minorants']:
                i,j=scalar['pair'];z=a.INDEX[i,j];n=scalar['integer_center'];bl=SC*(100*n-21);bu=SC*(100*n+21)
                if lower[z]<bl or upper[z]>bu:fail+=1
                lower[z]=max(lower[z],bl);upper[z]=min(upper[z],bu)
            if not fail:whole.append(k)
            if close([lower,upper]) is not None:intersect.append(k)
            q=list(map(F,basin['anchor']))
            if all(F(lo[z],SC)<=sum(q[i:j])<=F(hi[z],SC) for z,(i,j) in enumerate(a.PAIRS)):anchors.append(k)
            near.append((fail,k))
        widths=[F(hi[k]-lo[k],SC) for k in range(9)]
        rows.append({'path':original['path'],'depth':original['depth'],'whole_basin_memberships':whole,'possible_basin_intersections_exact_DBM':intersect,
          'known_actual_anchor_points_in_cell':anchors,'fewest_failed_span_memberships':min(near)[0],
          'closest_basin_by_failed_spans':min(near)[1],'free_KKT_coordinates':sum(v>123*SC//128 for v in lo[:9]),
          'adjacent_widths':[float(v) for v in widths],'integer_midpoint_pattern':[(lo[k]+hi[k]+SC)//(2*SC) for k in range(9)]})
    stream=Stream(HERE/'window-compact-obbt-cover.json');stream.token('{');meta={};branch_counts=Counter();tail=[];accepted_depth=Counter()
    while stream.peek()!='}':
        key=stream.value();stream.token(':')
        if key=='accepted':
            def leaf(row):accepted_depth[row['depth']]+=1
            stream.array(leaf)
        elif key=='branches':
            def branch(row):branch_counts[row['axis']]+=1;tail.append(row)
            stream.array(branch);break
        else:meta[key]=stream.value()
        if stream.peek()!=',':break
        stream.token(',')
    while raw:=stream.file.read(1<<20):stream.sha.update(raw);stream.size+=len(raw)
    stream.file.close();recent=tail[-5000:];recent_axes=Counter(r['axis'] for r in recent)
    prefix=recent[0]['path'] if recent else ''
    for row in recent:
        while not row['path'].startswith(prefix):prefix=prefix[:-1]
    growth={'checkpoint_sha256':stream.sha.hexdigest(),'checkpoint_bytes':stream.size,'checked':meta['checked'],'accepted_count':meta['accepted_count'],
      'frontier_count':meta['unresolved_count'],'counts':meta['counts'],'maxdepth':meta['maxdepth'],'sublevel_paths':meta['sublevel_contraction_paths'],
      'sublevel_bounds':meta['sublevel_bounds'],'Newton_paths':meta['contraction_paths'],'Newton_steps':meta['contraction_steps'],
      'split_count':len(tail),'all_split_axis_counts':{str(k):v for k,v in sorted(branch_counts.items())},
      'recent_split_count':len(recent),'recent_common_path_prefix':prefix,
      'recent_axis_counts':{str(k):v for k,v in sorted(recent_axes.items())},
      'recent_split_rank_counts':dict(sorted(Counter(a.PAIRS[r['axis']][1]-a.PAIRS[r['axis']][0] for r in recent).items())),
      'recent_split_depth_min':min(map(lambda r:len(r['path'])-1,recent)),'recent_split_depth_max':max(map(lambda r:len(r['path'])-1,recent))}
    summary={'frontier_cells':len(rows),'cells_wholly_in_a_known_basin':sum(bool(r['whole_basin_memberships']) for r in rows),
      'cells_intersecting_any_known_basin':sum(bool(r['possible_basin_intersections_exact_DBM']) for r in rows),
      'cells_containing_known_anchor':sum(bool(r['known_actual_anchor_points_in_cell']) for r in rows),
      'deep_cells_depth_at_least_18':sum(r['depth']>=18 for r in rows),
      'deep_cells_intersecting_a_known_basin':sum(r['depth']>=18 and bool(r['possible_basin_intersections_exact_DBM']) for r in rows)}
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'snapshot_sha256':hashlib.sha256(sraw).hexdigest(),
      'snapshot_checked':source['source_checked'],'Gram_sha256':hashlib.sha256(gramraw).hexdigest(),'summary':summary,'frontier':rows,'growth':growth,
      'full_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-frontier-basin-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps({'summary':summary,'growth':growth,'seconds':out['seconds']}),flush=True)
if __name__=='__main__':main()
