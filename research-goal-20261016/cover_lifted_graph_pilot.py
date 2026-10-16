"""Export the completed graph64 witness with fewest active scalar graphs."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    proofraw=(HERE/'cover-lifted-graph64.json').read_bytes();proof=json.loads(proofraw)
    packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));cases={r['path']:r for r in source['cases']}
    def size(row):
        rows=row['graph']['weighted_rows'];scalar={meta[1] for meta,w in rows if meta[0] in ['slab','facet']}
        return len(scalar),sum(meta[0]=='facet' for meta,w in rows),sum(meta[0]=='slab' for meta,w in rows),len(rows),row['path']
    row=min((r for r in proof['rows'] if r['graph']),key=size);case=cases[row['path']];cert=row['graph'];state=case['before']
    paramsraw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();params=json.loads(paramsraw);terms=[r for r in params['a_upper'] if r[2]]
    pairs=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)];index={p:k for k,p in enumerate(pairs)}
    tabraw=(HERE/'cover_newjet.json').read_bytes();table=json.loads(tabraw);width=32768//table['receipt']['grid_step']
    active=sorted({meta[1] for meta,w in cert['weighted_rows'] if meta[0] in ['slab','facet']});facet_cells=set()
    for meta,w in cert['weighted_rows']:
        if meta[0]=='facet':
            i,j,aw=terms[meta[1]];z=index[i,j];l,u=state[0][z],state[1][z];facet_cells.update(range(l//width,(max(l+1,u)+width-1)//width))
    out={'schema':'lifted-graph-pilot-v1','path':row['path'],'cell':state,'certificate':cert,
      'SC':32768,'DS':10**15,'D':10**10,'Q':str(2*32768*10**15*10**10),'target':'11/1250',
      'b_numerators':params['b_numerators'],'positive_terms':terms,'pair_order':[list(p) for p in pairs],
      'active_scalar_indices':active,'facet_grid_rows':[[k,*table['ranges'][k]] for k in sorted(facet_cells)],
      'metrics':{'active_scalars':size(row)[0],'facet_rows':size(row)[1],'slab_rows':size(row)[2],'weighted_rows':size(row)[3],
        'raw_certificate_json_bytes':len(json.dumps(cert,separators=(',',':')).encode()),'facet_grid_cells':len(facet_cells)},
      'provenance':{'full_graph64_proof_sha256':sha(proofraw),'parent64_input_gzip_sha256':sha(packed),'parameter_sha256':sha(paramsraw),'derivative_table_sha256':sha(tabraw)},
      'complete_global_cover':False,'actual_Lean_pilot_complete':False,'new_zero_proportion_proven':False}
    raw=(json.dumps(out,separators=(',',':'))+'\n').encode();path=HERE/'cover-lifted-graph-pilot.json';path.write_bytes(raw)
    print(json.dumps({'path':str(path),'sha256':sha(raw),'bytes':len(raw),'cell':row['path'],**out['metrics']}))
if __name__=='__main__':main()
