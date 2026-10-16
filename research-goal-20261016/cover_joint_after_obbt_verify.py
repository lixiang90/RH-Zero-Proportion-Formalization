"""Replay the sublevel, Newton, and joint-separation chain without optimizers."""
from pathlib import Path
import argparse,hashlib,json,time
import cover_sublevel_obbt_verify as sublevel
import cover_contractor_verify as newton
import cover_energy_gradient_verify as joint
from cover_correlated_verify import make_table

HERE=Path(__file__).parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-joint-after-obbt.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-joint-after-obbt-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);source=args.source.read_bytes();original=json.loads(source)
    assert hashlib.sha256(source).hexdigest()==doc['receipt']['source_OBBT_sha256'];lookup={r['path']:r for r in original['contractions']}
    table=make_table(HERE/'cover_newjet.json');target=int(doc['receipt']['target_numerator']);bounds=steps=0;margins=[]
    for row in doc['exclusions']:
        prior=lookup[row['path']];assert prior['result'] is None
        sublevel.verify(prior,target,table);bounds+=len(prior['certificates']);state=prior['new_cell']
        for step in row['newton_steps']:
            assert state is not None;state=newton.verify_step(state,step,joint.energy.w.P,table);steps+=1
        assert state==row['cell']
        margins.append(int(joint.verify(state,row['result'],target,joint.energy.w.P,table)['strict_margin']))
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checked_chains':len(margins),'checked_prior_OBBT_bounds':bounds,'checked_prior_Newton_steps':steps,'all_passed':True,
      'minimum_strict_joint_margin':str(min(margins)) if margins else None,'complete_global_cover':False,
      'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
