"""Compare three floors on identical sampled original parent cells.

Each process gets its own window module, hints and OBBT engine. One parent
is processed by the existing value/direction -> OBBT -> Newton pipeline.
Remaining parents measure necessary next splits in this ONE-LEVEL probe;
they do not estimate or assert a complete global tree size.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,importlib.util,json,time
import cover_correlated_api as first
import cover_correlated_direction as engine
import cover_contractor_api as newton
import cover_sublevel_obbt_api as obbt
import cover_compact_codec as codec
HERE=Path(__file__).parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--floor',choices=['221/25000','11/1250','1757/200000'],required=True)
    ap.add_argument('--sample',type=int,default=300);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();start=time.monotonic()
    raw=(HERE/'cover-sublevel-obbt.json').read_bytes();old=json.loads(raw);allrows=old['contractions']
    selected=[allrows[k*(len(allrows)-1)//max(1,args.sample-1)] for k in range(min(args.sample,len(allrows)))]
    spec=importlib.util.spec_from_file_location('independent_floor_probe_window',HERE/'window_global_cover.py')
    w=importlib.util.module_from_spec(spec);spec.loader.exec_module(w);g=w.g;target=F(args.floor)*g.DEN;assert target.denominator==1
    target=int(target);g.TARGET=target;oracle=first.make_correlated_oracle();obbt_engine=obbt.make_engine(w)
    counts={'sample':len(selected),'pre_value':0,'pre_direction':0,'OBBT_paths':0,'OBBT_bounds':0,
      'after_OBBT_value':0,'after_OBBT_direction':0,'Newton_paths':0,'Newton_steps':0,'Newton_coordinate_bounds':0,
      'after_Newton_value':0,'after_Newton_direction':0,'empty':0,'remaining_next_splits':0}
    rows=[];rawbytes=packedbytes=0
    def classify(state):
        ex=engine.baseline.exclusion(state,True)
        if ex is None:ex=first.correlated_exclusion(state,oracle)
        if ex:return 'direction',ex,None
        rec=w.certify(state)
        if int(rec.get('floor_numerator','-1'))>=target:return 'value',rec,rec
        return None,None,rec
    for index,original in enumerate(selected,1):
        state=(original['old_cell'][0],original['old_cell'][1]);kind,rec,hint=classify(state);phase='pre';sub=None;steps=[]
        if kind is None:
            axis,_=g.cut(state,hint);refined,bounds=obbt.contract(state,target,sorted(set(list(range(9))+[axis])),obbt_engine)
            if bounds:
                counts['OBBT_paths']+=1;counts['OBBT_bounds']+=len(bounds)
                sub={'old_cell':state,'new_cell':refined,'certificates':bounds};state=refined
                if state is None:kind,phase='empty','OBBT'
                else:kind,rec,hint=classify(state);phase='after_OBBT'
        if kind is None:
            refined,steps,ex=newton.contract(state,8,oracle);state=refined
            if steps:
                counts['Newton_paths']+=1;counts['Newton_steps']+=len(steps);counts['Newton_coordinate_bounds']+=sum(len(s['certificates']) for s in steps)
            phase='after_Newton'
            if state is None:kind='empty'
            elif ex:kind,rec='direction',ex
            else:kind,rec,hint=classify(state)
        if kind=='empty':counts['empty']+=1
        elif kind is None:counts['remaining_next_splits']+=1
        else:counts[phase+'_'+kind]+=1
        proof={'path':original['path'],'phase':phase,'kind':kind,'sublevel_step':sub,'newton_steps':steps,'result':rec}
        compact={'path':original['path'],'phase':phase,'kind':kind,
          'sublevel_step':codec.pack_obbt(sub) if sub else None,'newton_steps':[codec.pack_newton(s) for s in steps]}
        if kind in ['value','direction']:
            leaf=codec.pack_leaf({'path':original['path'],'depth':len(original['path'])-1,'kind':'stationary' if kind=='direction' else kind,'result':rec})
            compact['leaf']=leaf
        rawbytes+=len(json.dumps(proof,separators=(',',':')).encode());packedbytes+=len(json.dumps(compact,separators=(',',':')).encode())
        rows.append({'path':original['path'],'phase':phase,'kind':kind,'bounds':len(sub['certificates']) if sub else 0,
          'newton_steps':len(steps),'remaining_cell':state if kind is None else None})
        if index%50==0:print(json.dumps({'done':index,**counts,'seconds':time.monotonic()-start}),flush=True)
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'selected_paths_sha256':codec.digest([r['path'] for r in selected]),'floor':args.floor,'target_numerator':str(target),
      'counts':counts,'raw_proof_bytes':rawbytes,'compact_proof_bytes':packedbytes,'rows':rows,
      'only_one_level_complexity_probe':True,'all_local_proof_witnesses_independently_replayed':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps({k:v for k,v in out.items() if k!='rows'}),flush=True)
if __name__=='__main__':main()
