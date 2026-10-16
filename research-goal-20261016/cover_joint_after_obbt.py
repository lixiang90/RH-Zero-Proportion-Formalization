"""Joint energy-gradient separation after sublevel/optional Newton refinement.

The joint affine derivative envelope is recomputed on the refined cell.
All successful leaves require independent replay of both prior refinements
and the final single energy-gradient integer-flow certificate.
"""
from pathlib import Path
import argparse,hashlib,json,time
import cover_energy_gradient_joint as joint
import cover_contractor_api as newton

HERE=Path(__file__).parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--newton-rounds',type=int,default=8);ap.add_argument('--output',type=Path,default=HERE/'cover-joint-after-obbt.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);target=int(doc['receipt']['target_numerator']);oracle=joint.api.make_correlated_oracle()
    counts={'OBBT_residual':0,'Newton_paths':0,'Newton_direction_closed':0,'new_value_closed':0,'new_joint_closed':0,'remaining':0};rows=[]
    for original in doc['contractions']:
        if original['result'] is not None or original['new_cell'] is None:continue
        counts['OBBT_residual']+=1;state=(original['new_cell'][0],original['new_cell'][1]);steps=[];ex=None
        if args.newton_rounds:
            state,steps,ex=newton.contract(state,args.newton_rounds,oracle)
            if steps:counts['Newton_paths']+=1
            if state is None or ex:counts['Newton_direction_closed']+=1;continue
        value=joint.w.certify(state)
        if int(value.get('floor_numerator','-1'))>=target:counts['new_value_closed']+=1;continue
        result=joint.exclusion(state,oracle,target)
        if result:
            counts['new_joint_closed']+=1
            rows.append({'path':original['path'],'cell':state,'newton_steps':steps,'result':result})
        else:counts['remaining']+=1
        if counts['OBBT_residual']%25==0:print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'source_OBBT_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'joint_engine_sha256':hashlib.sha256(Path(joint.__file__).read_bytes()).hexdigest(),'api_sources':joint.api.api_sources(oracle),
      'target_numerator':str(target),'newton_rounds':args.newton_rounds,'counts':counts,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'exclusions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
