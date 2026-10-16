"""Partition a paused ordered search frontier into independently resumable jobs.

The immutable master keeps every already checked node. Extra balancing nodes
are generated with the same exact geometry and checker as the search driver.
No floating result can close a node.
"""
from pathlib import Path
import argparse,json
import ordered_generate as o
g=o.g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('master',type=Path);ap.add_argument('--workers',type=int,default=3)
    args=ap.parse_args();doc=json.loads(args.master.read_text());todo=doc['unresolved']
    shallow=min(z['depth'] for z in todo)
    while any(z['depth']<shallow+2 for z in todo):
        row=min(todo,key=lambda z:z['depth']);todo.remove(row)
        path=row['path'];depth=row['depth'];state,cuts=o.normalize(row['state'])
        invalid=next((i for i,(l,u) in enumerate(zip(*state)) if u<l),None)
        rec=({'empty':True,'violation_axis':invalid,'certificate':{'lower_bounds':state[0],'upper_bounds':state[1]}}
             if invalid is not None else g.certify(state,True))
        if rec.get('empty') or int(rec.get('floor_numerator','-1'))>=g.TARGET:
            doc['accepted'].append({'path':path,'depth':depth,'normalize_rounds':2,'normalize_cuts':cuts,'result':rec})
        else:
            ax,q=g.cut(state,rec)
            doc['branches'].append({'path':path,'axis':ax,'cut':q,'normalize_rounds':2,'normalize_cuts':cuts})
            for digit,upper in [('1',False),('0',True)]:
                todo.append({'path':path+digit,'depth':depth+1,'state':o.rawsplit(state,ax,q,upper),'old_path':row.get('old_path')})
    groups=[[] for _ in range(args.workers)];weights=[0.]*args.workers
    for row in sorted(todo,key=lambda z:z['depth']):
        worker=min(range(args.workers),key=lambda i:weights[i]);groups[worker].append(row)
        weights[worker]+=2.**(-row['depth'])
    doc['checked']=len(doc['accepted'])+len(doc['branches']);doc['accepted_count']=len(doc['accepted']);doc['unresolved_count']=len(todo)
    args.master.write_text(json.dumps(doc,separators=(',',':'))+'\n')
    for i,group in enumerate(groups):
        out={**doc,'checked':0,'accepted_count':0,'accepted':[],'branches':[],'unresolved_count':len(group),'unresolved':group}
        path=args.master.with_name(args.master.stem.replace('-master','')+f'-seed-{i}.json')
        path.write_text(json.dumps(out,separators=(',',':'))+'\n')
    print(json.dumps({'master':str(args.master),'groups':[len(x) for x in groups],'depth_weights':weights}))
if __name__=='__main__':main()
