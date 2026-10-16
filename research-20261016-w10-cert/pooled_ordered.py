"""Shared-queue scheduler for the unchanged exact ordered-cell search.

Every in-flight cell stays in the saved frontier until its completed result
has been collected, so interruption loses work but cannot lose coverage.
"""
from pathlib import Path
import argparse,collections,concurrent.futures,hashlib,json,os,time
import ordered_generate as o
g=o.g

def solve(row):
    path=row['path'];depth=row['depth'];s,cuts=o.normalize(row['state'])
    invalid=next((i for i,(l,u) in enumerate(zip(*s)) if u<l),None)
    rec=({'empty':True,'violation_axis':invalid,'certificate':{'lower_bounds':s[0],'upper_bounds':s[1]}}
         if invalid is not None else g.certify(s,True))
    common={'path':path,'depth':depth,'normalize_rounds':2,'normalize_cuts':cuts}
    if rec.get('empty') or int(rec.get('floor_numerator','-1'))>=g.TARGET:
        return {'leaf':{**common,'result':rec}}
    axis,cut=g.cut(s,rec)
    return {'branch':{**common,'axis':axis,'cut':cut},'children':[
        {'path':path+'0','depth':depth+1,'state':o.rawsplit(s,axis,cut,True)},
        {'path':path+'1','depth':depth+1,'state':o.rawsplit(s,axis,cut,False)}]}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--resume',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);ap.add_argument('--workers',type=int,default=3)
    args=ap.parse_args();raw=args.resume.read_bytes();doc=json.loads(raw)
    accepted=doc['accepted'];branches=doc['branches'];checked=doc['checked']
    pending={z['path']:z for z in doc['unresolved']};ready=collections.deque(doc['unresolved'])
    active={};started=time.monotonic();initial=checked
    def save():
        out={'scope':__doc__,'format':'ordered-mcheckGX-1024','normalize_rounds':2,'root':g.root(),
            'target':'433/50000','parameter_sha256':hashlib.sha256(g.PAR.read_bytes()).hexdigest(),
            'source_sha256':hashlib.sha256(g.f.SRC.read_bytes()).hexdigest(),
            'resume_sha256':hashlib.sha256(raw).hexdigest(),'pid':os.getpid(),'workers':args.workers,
            'checked':checked,'accepted_count':len(accepted),'unresolved_count':len(pending),
            'elapsed_seconds':time.monotonic()-started,'maxdepth':max((len(z['path'])-1 for z in accepted+branches),default=0),
            'terms':g.TERMS,'denominator':str(g.DEN),'SC':g.SC,'mixture_denominator':g.LD,
            'accepted':accepted,'branches':branches,'unresolved':list(pending.values())}
        tmp=args.output.with_suffix('.partial');tmp.write_text(json.dumps(out,separators=(',',':'))+'\n');tmp.replace(args.output)
        return out
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        while pending:
            while ready and len(active)<args.workers:
                row=ready.popleft();active[pool.submit(solve,row)]=row['path']
            done,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
            for future in done:
                path=active.pop(future);result=future.result();del pending[path];checked+=1
                if 'leaf' in result:accepted.append(result['leaf'])
                else:
                    branches.append(result['branch'])
                    for row in result['children']:
                        assert row['path'] not in pending;pending[row['path']]=row;ready.append(row)
                if checked%1000==0:
                    save();print(json.dumps({'checked':checked,'accepted':len(accepted),'pending':len(pending),
                        'seconds':time.monotonic()-started}),flush=True)
    out=save();print(json.dumps({k:out[k] for k in ['checked','accepted_count','unresolved_count','maxdepth','elapsed_seconds']}),flush=True)
if __name__=='__main__':main()
