"""Full new-window minimizer cover with exact, correlated descent directions.

Reuses valid cells from a frozen value-cover checkpoint. An accepted descent
direction is a genuine KKT exclusion only after the actual derivative table
and coercive minimum transfer have Lean proofs. Discovery is never a theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,os,time
import window_global_cover as high
import window_lower_global_cover as low
import window_direction_probe as direction
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--floor',choices=['11/1250','221/25000'],default='11/1250')
    ap.add_argument('--resume',type=Path);ap.add_argument('--max-nodes',type=int,default=2000000)
    ap.add_argument('--oracle',type=Path,default=HERE/'cover_newjet.json')
    ap.add_argument('--output',type=Path,default=HERE/'window-minimizer-cover.json');args=ap.parse_args()
    args.oracle=args.oracle.resolve();args.output=args.output.resolve()
    if args.resume:args.resume=args.resume.resolve()
    w=low if args.floor=='11/1250' else high;g=w.g
    oracle_sha=direction.install_grid(args.oracle)
    # The direction selector uses the same new parameters for both floors.
    assert direction.g.TERMS==g.TERMS and direction.g.BS==g.BS and direction.g.SEP==g.SEP
    paths=[Path(__file__),Path(w.__file__),Path(direction.__file__),Path(w.ik.__file__),w.PARAM,
           args.oracle,HERE/'window_interval_kernel.json',ROOT/'research-20261016-w10-cert/generate.py',
           ROOT/'research-20261016-followup/global_periodic_upper_bound.py']
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    todo=[(w.root(),0,'r')];accepted=[];branches=[];checked=0;depthmax=0;resumed=None
    if args.resume:
        raw=args.resume.read_bytes();old=json.loads(raw)
        for name,digest in old['input_sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest
        assert old['target']==args.floor and old['root']==[list(x) for x in w.root()]
        resumed={'path':str(args.resume.relative_to(ROOT)),'sha256':hashlib.sha256(raw).hexdigest(),'checked':old['checked']}
        todo=[(x['state'],x['depth'],x['path']) for x in old['unresolved']]
        accepted=old['accepted'];branches=old['branches'];checked=old['checked'];depthmax=old['maxdepth']
        for p,*_ in old.get('tangent_data',[]):w.USED_SUPPORTS.add(p)
    start=time.monotonic();initial=checked
    def save():
        assert hashes=={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
        out={'scope':__doc__,'input_sha256':hashes,'resumed_from':resumed,'target':args.floor,'SC':g.SC,
             'denominator':str(g.DEN),'separation':'123/128','pid':os.getpid(),'root':w.root(),
             'checked':checked,'maxdepth':depthmax,'accepted_count':len(accepted),
             'stationary_count':sum(x['kind']=='stationary' for x in accepted),'unresolved_count':len(todo),
             'seconds':time.monotonic()-start,'derivative_grid_sha256':oracle_sha,
             'analytic_obligations':['sixteen actual convex-core bounds','actual |k second derivative| <= 4',
                 'actual |w order24 derivative| <= (44/7)^24','actual Taylor derivative grid',
                 'coercive global minimizer and feasible directional KKT transfer'],
             'analytic_obligations_Lean_proven':False,'global_floor_Lean_proven':False,'new_zero_proportion_proven':False,
             'accepted':accepted,'branches':branches,'unresolved':[{'state':s,'depth':d,'path':p} for s,d,p in todo],
             'tangent_data':[[p,*w.original_support(p)] for p in sorted(w.USED_SUPPORTS)]}
        temp=args.output.with_suffix('.partial');temp.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');temp.replace(args.output)
        return out
    while todo and checked-initial<args.max_nodes:
        state,depth,path=todo.pop();checked+=1;depthmax=max(depthmax,depth)
        if state[1][8]<state[0][0]:accepted.append({'path':path,'depth':depth,'kind':'reflection'})
        else:
            # Directional exclusions usually have much smaller certificates.
            ex=direction.exclusion(state,True)
            if ex:
                ex['derivative_grid_sha256']=oracle_sha
                accepted.append({'path':path,'depth':depth,'kind':'stationary','result':ex})
            else:
                rec=w.certify(state)
                if int(rec.get('floor_numerator','-1'))>=g.TARGET:
                    accepted.append({'path':path,'depth':depth,'kind':'value','result':rec})
                else:
                    ax,q=g.cut(state,rec);assert state[0][ax]<q<state[1][ax]
                    branches.append({'path':path,'axis':ax,'cut':q})
                    for suffix,upper in [('1',False),('0',True)]:
                        child=g.split(state,ax,q,upper)
                        if child is not None:todo.append((child,depth+1,path+suffix))
        if checked%1000==0:
            out=save();print(json.dumps({k:out[k] for k in ['checked','accepted_count','stationary_count','unresolved_count','maxdepth','seconds']}),flush=True)
    out=save();print(json.dumps({k:out[k] for k in ['checked','accepted_count','stationary_count','unresolved_count','maxdepth','seconds']}),flush=True)
if __name__=='__main__':main()
