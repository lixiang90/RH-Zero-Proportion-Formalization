"""Extract floating dual hints from the two quadratic-energy moment LPs.

Only energy rows are softened by a common nonnegative energy-unit slack.
All old graph/KKT, cross-position RLT and McCormick rows remain exact model
constraints. A positive objective suggests a Farkas certificate but is not
accepted until a separate rational/integer reconstruction succeeds.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import numpy as np
from scipy.sparse import csr_matrix,vstack,hstack
import cover_cross_moment_probe as base

HERE=Path(__file__).parent;sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();assert not args.output.exists(),'Use a new output.'
    start=time.monotonic();pfile=HERE/'cover-cross-moment-energy-two.json';praw=pfile.read_bytes();packets=json.loads(praw)
    source=HERE/'cover-curvature-parent64.input.json.gz';raw=source.read_bytes();cases={c['path']:c for c in json.loads(gzip.decompress(raw))['cases']}
    table=HERE/'cover_newjet.json';taylor=base.old.context.curvature.first.TaylorOracle(table);graph=base.old.GraphOracle(table);rows=[]
    for case in packets['rows']:
        path=case['path'];state=tuple(cases[path]['before']);erows=[];ebounds=[];scales=[]
        for p in case['energy_packets']:
            row=np.zeros(base.V)
            for k,v in p['row']:row[k]=float(F(v))
            B=float(F(p['bound']));scale=max(1.,max(abs(row)),abs(B));erows.append(row/scale);ebounds.append(B/scale);scales.append(scale)
        original=base.linprog;dual={}
        def softened(c,**kw):
            nr=kw['A_ub'].shape[0]
            A=vstack([kw['A_ub'],csr_matrix(erows)],format='csr')
            column=np.r_[np.zeros(nr),[-1/s for s in scales]][:,None]
            B=np.r_[kw['b_ub'],ebounds];objective=np.r_[np.zeros(base.V),1.]
            lp=original(objective,A_ub=hstack([A,csr_matrix(column)],format='csr'),b_ub=B,
              bounds=kw['bounds']+[(0,None)],method=kw['method'])
            dual.update({'LP_status':int(lp.status),'LP_success':bool(lp.success),'base_rows':nr,'energy_rows':len(erows),'energy_row_scales':scales})
            if lp.success:
                dual.update({'minimum_energy_slack_hint':float(lp.fun),
                  'nonzero_row_dual_weights':[[k,float(-v)] for k,v in enumerate(lp.ineqlin.marginals) if -v>1e-14],
                  'minimum_softened_row_slack_hint':float(min(B-A@lp.x[:-1]-column[:,0]*lp.x[-1])),
                  'raw_primal_with_energy_slack':lp.x.tolist()})
                lp.x=lp.x[:-1]
            return lp
        base.linprog=softened
        try:result=base.solve(state,taylor,graph,0)
        finally:base.linprog=original
        rows.append({'path':path,'dual_hint':dual,'base_result':result})
        print(json.dumps({'path':path,'LP_status':dual['LP_status'],'minimum_energy_slack_hint':dual.get('minimum_energy_slack_hint'),
          'nonzero_dual_weights':len(dual.get('nonzero_row_dual_weights',[])),'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'base_model_sha256':sha(Path(base.__file__).read_bytes()),
      'energy_input_sha256':sha(praw),'parent64_input_sha256':sha(raw),'table_sha256':sha(table.read_bytes()),
      'floating_hints_only':True,'strict_certificates':0,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
