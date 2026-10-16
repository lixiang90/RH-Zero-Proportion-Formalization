"""Paired finite-move hypograph diagnostic on a fixed source region list."""
from pathlib import Path
import argparse,hashlib,json,math,time
import cover_global_cut_hypograph as h
HERE=Path(__file__).parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--frontier',action='store_true');ap.add_argument('--sample',type=int,default=47)
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-cut-hypograph.json');args=ap.parse_args();start=time.monotonic()
    source=HERE/('cover-global-cut-frontier.json' if args.frontier else 'cover-global-cut-full-contractor.json')
    raw=source.read_bytes();doc=json.loads(raw);target=int(doc['receipt']['target_numerator']);oracle=h.old.concave.ConcaveDifferenceOracle(h.base.api.make_correlated_oracle())
    counts={'paths':0,'contracted':0,'bounds':0,'closed':0,'source_closed':0,'new_only_closed':0,'source_only_closed':0,'bounds_using_global_moves':0};rows=[]
    inputs=doc['rows'] if args.frontier else doc['contractions']
    for original in inputs[:args.sample]:
        state=original['cell'] if args.frontier else original['steps'][0]['old_cell'];state=(state[0],state[1]);initial=state;steps=[];result=None
        for _ in range(2):
            state,step=h.contract_once(state,target,oracle)
            if step is None:break
            steps.append(step);counts['bounds']+=len(step['certificates']);counts['bounds_using_global_moves']+=sum(bool(c['move_models']) for c in step['certificates'])
            if state is None:result={'kind':'empty'};break
            ex=h.base.api.correlated_exclusion(state,oracle.taylor)
            if ex:result={'kind':'stationary','result':ex};break
            rec=h.w.certify(state)
            if int(rec.get('floor_numerator','-1'))>=target:result={'kind':'value','result':rec};break
        sourceclosed=bool(original['multi']['result']) if args.frontier else bool(original['result'])
        counts['paths']+=1;counts['contracted']+=bool(steps);counts['closed']+=bool(result);counts['source_closed']+=sourceclosed
        counts['new_only_closed']+=bool(result) and not sourceclosed;counts['source_only_closed']+=sourceclosed and not result
        ratio=None if state is None else math.prod((state[1][k]-state[0][k]+1)/(initial[1][k]-initial[0][k]+1) for k in range(9))
        rows.append({'path':original['path'],'cell':initial,'steps':steps,'result':result,'source_closed':sourceclosed,'volume_ratio_hint':ratio})
        print(json.dumps({**counts,'seconds':time.monotonic()-start}),flush=True)
    out={'receipt':{'scope':__doc__,'input_name':source.name,'input_kind':'frontier' if args.frontier else 'old_full_pilot',
      'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'engine_sha256':hashlib.sha256(Path(h.__file__).read_bytes()).hexdigest(),'target_numerator':str(target),'counts':counts,
      'preserves_original_global_minima_below_target':True,'preserves_all_KKT_points':False,'complete_global_cover':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
