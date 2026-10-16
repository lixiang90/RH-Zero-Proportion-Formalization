"""Same two phase-KKT cases with functional sin/cos span graph facets.

Imports the unchanged initial probe and the separately frozen rational
phase-graph oracle.  No existing packet, probe, receipt or runner is edited.
All solver/PSD conclusions remain numerical hints rather than certificates.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import numpy as np
import cover_phase_kkt_probe as base
import window_phase_graph_oracle as functional
HERE=Path(__file__).parent;ROOT=HERE.parent;g=base.g;SC=base.SC
sha=lambda b:hashlib.sha256(b).hexdigest()


class Model(base.Model):
    def __init__(self,state,taylor,graph,case,phase_graph):
        super().__init__(state,taylor,graph,case);self.functional_start=len(self.rows);self.functional_count=0
        for layer in range(2):
            for z,(i,j) in enumerate(g.ALL):
                for part in [0,1]:
                    facets,nrect=phase_graph.facets(state[0][z],state[1][z],layer+1,part)
                    for sign,S,C in facets:
                        row=np.zeros(self.V);row[self.index(layer,z,part)]=sign;row[i:j]=-sign*S/functional.DS
                        self.add(row,sign*C/(SC*functional.DS),['functional_phase_graph',layer,z,part,sign,str(S),str(C)]);self.functional_count+=1
        self.functional_end=len(self.rows)


def actual_phase_completion(model,primal):
    if primal is None:return None
    x=np.zeros(model.V);x[:9]=primal['gaps'];x[9:model.P]=primal['derivatives'];x[model.R:]=primal['KKT_slacks'];prefix=np.r_[0.,np.cumsum(x[:9])]
    for layer in range(2):
        for z,(i,j) in enumerate(g.ALL):
            angle=(layer+1)*np.pi*(prefix[j]-prefix[i]);x[model.index(layer,z,0)]=np.cos(angle);x[model.index(layer,z,1)]=np.sin(angle)
    slack=np.array(model.rhs)-np.array(model.rows)@x;start=model.old_row_count;functional_start=getattr(model,'functional_start',len(model.rows));functional_end=getattr(model,'functional_end',len(model.rows))
    bad_phase=[]
    for k in range(start,len(model.rows)):
        if slack[k]<-1e-7:bad_phase.append({'row':k,'meta':model.row_meta[k],'violation_hint':float(-slack[k])})
    matrices=[{'matrix':kind,'minimum_eigenvalue_hint':float(np.linalg.eigvalsh(M)[0])} for kind,M in model.matrices(x)]
    return {'scope':'Same g and derivative primal; replace both layers by its actual linked rank-one position phases.',
      'minimum_old_graph_slack_hint':float(min(slack[:start])),'minimum_extra_slack_hint':float(min(slack[start:])),
      'minimum_functional_graph_slack_hint':float(min(slack[functional_start:functional_end])) if functional_end>functional_start else None,
      'minimum_PSD_eigenvalue_hint':min(r['minimum_eigenvalue_hint'] for r in matrices),
      'all_rows_numerically_satisfied_to_1e7':bool(min(slack)>=-1e-7),'violated_extra_rows':bad_phase,
      'gaps':x[:9].tolist(),'derivatives':x[9:model.P].tolist(),'KKT_slacks':x[model.R:].tolist(),
      'phase_layer_pair_real_imag':[[[float(x[model.index(layer,z,0)]),float(x[model.index(layer,z,1)])] for z in range(45)] for layer in range(2)],
      'not_an_exact_primal_certificate':True}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--rounds',type=int,default=20);args=ap.parse_args();assert 0<=args.rounds<=20
    args.packet=args.packet.resolve();args.output=args.output.resolve();start=time.monotonic();packetraw=args.packet.read_bytes();packet=json.loads(packetraw)
    packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));lookup={r['path']:r for r in source['cases']}
    assert packet['SC']==SC and packet['input_sha256']==sha(packed) and packet['parameters_sha256']==sha(base.old.context.w.PARAM.read_bytes())
    allowed=['r001000001000001101011101','r001000001000001110011100'];assert 1<=len(packet['cases'])<=2 and all(c['path'] in allowed for c in packet['cases'])
    taylor=base.old.context.curvature.first.TaylorOracle(HERE/'cover_newjet.json');graph=base.old.GraphOracle(HERE/'cover_newjet.json');phase_graph=functional.PhaseGraphOracle();rows=[]
    for case in packet['cases']:
        state=tuple(lookup[case['path']]['before']);model=Model(state,taylor,graph,case,phase_graph);result=model.run(args.rounds)
        completion=actual_phase_completion(model,result['final_primal']);rows.append({'path':case['path'],**result,'functional_phase_facets':model.functional_count,'actual_rank_one_phase_completion':completion})
        print(json.dumps({'path':case['path'],'status':result['status'],'iterations':len(result['history']),'functional_phase_facets':model.functional_count,
          'PSD_cuts':len(result['rational_rank_one_cuts']),'final_L1':result['history'][-1]['L1_residual_hint'],
          'actual_rank1_all_rows_hint':completion and completion['all_rows_numerically_satisfied_to_1e7'],'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'base_probe_sha256':sha(Path(base.__file__).read_bytes()),
      'functional_oracle_sha256':sha(Path(functional.__file__).read_bytes()),'packet_sha256':sha(packetraw),'packet_path':args.packet.relative_to(ROOT).as_posix(),
      'parent64_input_sha256':sha(packed),'maximum_cut_rounds_per_case':args.rounds,'cases':len(rows),'strict_certificates':0,
      'floating_hints_only':True,'uniform_packet_Lean_proven':False,'phase_graph_Lean_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
