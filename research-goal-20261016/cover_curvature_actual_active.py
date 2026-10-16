"""Project the three-leaf actual derivative feed to nonzero curvature weights."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent
def main():
    path=HERE/'cover-curvature-actual-feed.json';raw=path.read_bytes();doc=json.loads(raw)
    assert doc['all_original_scalar_rows_preserved'] and doc['all_active_scalar_rows_preserved']
    k2=set(doc['active_q2_grid_indices']);k4=set(doc['active_q4_grid_indices']);points=set(doc['active_point_P'])
    grids=[]
    for row in doc['grid_rows']:
        k=row['cell'];out={'k':k,'n':row['center']}
        if k in k2:out['q2']=[row['q2']['mask'],row['q2']['old_lower'],row['q2']['old_upper']]
        if k in k4:out['q4']=[row['q4']['mask'],row['q4']['old_abs_bound']]
        if len(out)>2:grids.append(out)
    ps=[]
    for row in doc['point_rows']:
        if row['P'] not in points:continue
        ps.append({'P':row['P'],'n':row['center'],'q2':[row['q2'][k] for k in ['mask','point_lower_Q','point_upper_Q']],
          'q3':[row['q3'][k] for k in ['mask','point_lower_Q','point_upper_Q']]})
    leaves=[]
    for leaf in doc['leaves']:
        rows=[]
        for row in leaf['rows']:
            if not row['active']:continue
            rows.append({'t':row['term'],'l':row['lower_gap_units'],'u':row['upper_gap_units'],'P':row['P'],
              'm0':row['m0'],'m1':row['m1'],'err':row['error'],'kind':row['kind'],
              'e0':row.get('point_value_error_units'),'e1':row.get('point_slope_error_units'),
              'B4':row.get('old_fourth_bound'),'first':row['first_grid_cell'],'last':row['last_grid_cell']})
        leaves.append({'path':leaf['path'],'d':leaf['direction'],'rows':rows})
    out={'scope':__doc__,'full_audit_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'Q':doc['Q'],'DS':doc['DS'],'SC':doc['SC'],'q2_grid_schema':['mask','lower_DS','upper_DS'],
      'q4_grid_schema':['mask','abs_bound_DS'],'point_schema':['mask','lower_Q','upper_Q'],
      'grid_rows':grids,'point_rows':ps,'leaves':leaves,'active_grid_q2':sorted(k2),'active_grid_q4':sorted(k4),'active_point_P':sorted(points),
      'ordinary_Lean_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    target=HERE/'cover-curvature-actual-active.json';target.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({'file':target.name,'bytes':target.stat().st_size,'sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
      'grid_union':len(grids),'q2_cells':len(k2),'q4_cells':len(k4),'point_rows':len(ps),'scalar_rows':sum(len(r['rows']) for r in leaves)}))
if __name__=='__main__':main()
