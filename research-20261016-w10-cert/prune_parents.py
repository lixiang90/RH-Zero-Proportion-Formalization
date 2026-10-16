"""Measure bottom-up parent recertification without touching the live search."""
from pathlib import Path
import argparse, importlib.util, json, time
spec=importlib.util.spec_from_file_location('g',Path(__file__).with_name('generate.py'))
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
g.OLD=True;g.LD=1024*g.D;g.DEN=g.LD*g.WD;g.TARGET=433*(g.DEN//50000)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=Path(__file__).with_name('parallel-master.json'))
    ap.add_argument('--limit',type=int,default=100);ap.add_argument('--output',type=Path,default=Path(__file__).with_name('parent-prune-probe.json'));args=ap.parse_args()
    x=json.loads(args.input.read_text());nodes={z['path']:z for z in x['branches']};leaves={z['path']:z for z in x['accepted']}
    cherries={p for p in nodes if p+'0' in leaves and p+'1' in leaves};todo=[('r',g.root())];states={}
    while todo:
        p,s=todo.pop()
        if p in cherries:states[p]=s
        if p in nodes:
            n=nodes[p]
            for upper,bit in [(True,'0'),(False,'1')]:
                c=g.split(s,n['axis'],n['cut'],upper)
                if c is not None:todo.append((p+bit,c))
    start=time.monotonic();out=[]
    for p in sorted(states,key=lambda p:(len(p),p))[:args.limit]:
        rec=g.certify(states[p],True)
        out.append({'path':p,'accepted':rec.get('empty',False) or int(rec.get('floor_numerator','-1'))>=g.TARGET,
            'lp_floor':rec.get('lp_floor'),'mcheck_floor':rec.get('floor')})
    report={'cherries':len(cherries),'processed':len(out),'closed_by_replay':sum(z['accepted'] for z in out),
        'lp_floor_above_target':sum(z['lp_floor'] is not None and z['lp_floor']>=.00866 for z in out),'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'stats':report,'parents':out},indent=2)+'\n');print(json.dumps(report),flush=True)
if __name__=='__main__':main()
