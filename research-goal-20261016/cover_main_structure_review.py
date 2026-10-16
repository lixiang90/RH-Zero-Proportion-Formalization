"""Static checkpoint frontier/known-basin review and exact RLT-cone example.

Read existing frozen data only. No optimizer, kernel evaluation, sampling,
search-state mutation or Lean execution. Prefix counts are not volumes.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,sys
from cover_compact_checkpoint import open_snapshot
from cover_contractor_verify import close
HERE=Path(__file__).parent
PAIRS=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
LOOK={p:k for k,p in enumerate(PAIRS)}
sha=lambda b:hashlib.sha256(b).hexdigest()


def cone_counterexample():
    values=[F(1,2),F(1,2),F(-1,2),F(-1,2)] # x,y,z,t
    moments={(0,0):F(1,4),(0,1):F(1,4),(1,1):F(1,4),
      (0,2):F(0),(1,2):F(0),(0,3):F(-1,2),(1,3):F(-1,2)}
    # residual c + coeff.(x,y,z,t) <= 0
    rows=[([F(-1),0,0,0],F(0)),([F(1),0,0,0],F(-1)),
      ([0,F(-1),0,0],F(0)),([0,F(1),0,0],F(-1)),
      ([0,0,F(1),0],F(0)),([0,0,F(-1),0],F(-1)),
      ([0,0,0,F(1)],F(0)),([0,0,0,F(-1)],F(-1)),
      ([F(-1),F(-1),0,0],F(1)),
      ([0,0,F(1),F(1)],F(1)),([0,0,F(-1),F(-1)],F(-1))]
    rlt=[]
    for coeff,c in rows:
        residual=c+sum(a*x for a,x in zip(coeff,values));assert residual<=0
        for s in [0,1]:
            product=c*values[s]+sum(a*moments[min(s,j),max(s,j)] for j,a in enumerate(coeff))
            assert product<=0 and residual-product<=0;rlt.extend([product,residual-product])
    boxes=[(F(0),F(1)),(F(0),F(1)),(F(-1),F(0)),(F(-1),F(0))];mc=[]
    for (i,j),h in moments.items():
        l,u=boxes[i];L,U=boxes[j];x,y=values[i],values[j]
        inequalities=[l*y+L*x-l*L-h,u*y+U*x-u*U-h,h-u*y-L*x+u*L,h-l*y-U*x+l*U]
        assert max(inequalities)<=0;mc.extend(inequalities)
    assert all(moments[i,j]==values[i]*values[j] for i,j in [(0,0),(0,1),(1,1)])
    new_residual=moments[0,2]+moments[1,2]-values[2];assert new_residual==F(1,2)>0
    return {'point_means':list(map(str,values)),'lifted_moments':[[i,j,str(v)] for (i,j),v in moments.items()],
      'old_base_rows_checked':len(rows),'old_coordinate_RLT_rows_checked':len(rlt),'McCormick_rows_checked':len(mc),
      'position_moment_PSD_exact_rank_one':True,'KKT_equation':'z+t+1=0, including both coordinate products',
      'new_valid_row':'z*(x+y-1)<=0','new_lifted_residual':str(new_residual),
      'scope':'Exact cone nonredundancy counterexample, not an actual-kernel exclusion or evidence of runtime gains.'}


def main():
    audit_raw=(HERE/'cover-main-recovery117500-audit.json').read_bytes();audit=json.loads(audit_raw)
    with open_snapshot(HERE/'window-compact-obbt-recovery117500.json') as f:
        f.seek(0,2);size=f.tell();f.seek(max(0,size-(4<<20)));tail=f.read().decode()
        marker='"unresolved":';offset=tail.rfind(marker);frontier,_=json.JSONDecoder().raw_decode(tail[offset+len(marker):])
    pending={r['path'] for r in frontier};ancestors={p[:k] for p in pending for k in range(1,len(p))}
    completed=sorted({p+bit for p in ancestors for bit in '01' if p+bit not in ancestors and p+bit not in pending},key=lambda p:(len(p),p))
    gram_raw=(HERE/'cover-newwindow-gram.json').read_bytes();basins=json.loads(gram_raw)['results']
    patterns=[tuple(next(s['integer_center'] for s in b['scalar_minorants'] if s['pair']==[r,r+1]) for r in range(9)) for b in basins]
    rows=[]
    for row in frontier:
        lo,hi=row['state'];pattern=tuple((l+u+32768)//65536 for l,u in zip(lo[:9],hi[:9]));correlations=[]
        for z,(i,j) in enumerate(PAIRS):
            if j-i>1:
                correlations.extend([(lo[z]-sum(lo[i:j]),'lower',z,i,j),(sum(hi[i:j])-hi[z],'upper',z,i,j)])
        info={'path':row['path'],'depth':row['depth'],'state':row['state'],
          'free_coordinates':sum(v>31488 for v in lo[:9]),'integer_midpoint_pattern':pattern,
          'adjacent_widths':list(map(str,[F(u-l,32768) for l,u in zip(lo[:9],hi[:9])])),
          'span_width_range':[str(min(F(u-l,32768) for l,u in zip(lo,hi))),str(max(F(u-l,32768) for l,u in zip(lo,hi)))],
          'largest_correlated_span_constraints':[[str(F(n,32768)),side,z,i,j] for n,side,z,i,j in sorted(correlations,reverse=True)[:3]]}
        if row['depth']>=18:
            intersect=[];whole=[];near=[]
            for k,b in enumerate(basins):
                low=[v*100 for v in lo];up=[v*100 for v in hi];failed=0
                for s in b['scalar_minorants']:
                    z=LOOK[tuple(s['pair'])];n=s['integer_center'];L=32768*(100*n-21);U=32768*(100*n+21)
                    failed+=int(low[z]<L or up[z]>U);low[z]=max(low[z],L);up[z]=min(up[z],U)
                if not failed:whole.append(k)
                if close([low,up]) is not None:intersect.append(k)
                near.append((failed,k))
            distance=min((sum(abs(a-b) for a,b in zip(pattern,p)),k) for k,p in enumerate(patterns))
            info.update({'known_69_basin_intersections_exact':intersect,'whole_known_basin_memberships':whole,
              'fewest_failed_scalar_memberships':min(near)[0],'nearest_adjacent_integer_pattern_L1':distance[0],
              'nearest_pattern_basin':distance[1]})
        rows.append(info)
    result={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'audited_checkpoint_sha256':audit['checkpoint_sha256'],
      'audit_sha256':sha(audit_raw),'Gram_sha256':sha(gram_raw),'as_of_checked':117500,
      'maximal_completed_prefixes':completed,'pending_shallow_prefixes':[r['path'] for r in frontier if r['depth']<=8],
      'prefix_partition_is_not_domain_volume_or_completion_percentage':True,
      'recent_5000_split_ranks':audit['recent_split_ranks'],'recent_5000_common_prefix':audit['recent_5000_common_prefix'],
      'frontier':rows,'cone_counterexample':cone_counterexample(),'new_actual_cell_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    p=HERE/'cover-main117500-structure-review.json';p.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'completed_topmost_prefixes':completed,'deep_frontier_count':sum(r['depth']>=18 for r in rows),
      'deep_with_any_known_basin_intersection':sum(bool(r.get('known_69_basin_intersections_exact')) for r in rows),
      'exact_cone_counterexample':result['cone_counterexample'],'result_sha256':sha(p.read_bytes())}),flush=True)
if __name__=='__main__':main()
