"""An isolated ordered-endpoint tightening experiment; no main data is edited."""
from pathlib import Path
import argparse, importlib.util, json, time
import independent_integer_audit as audit
spec=importlib.util.spec_from_file_location('g',Path(__file__).with_name('generate.py'))
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
g.OLD=True;g.LD=1024*g.D;g.DEN=g.LD*g.WD;g.TARGET=433*(g.DEN//50000)

def ordered(s):
    for _ in range(10):
        lo,hi=s
        if hi[8]<lo[0]:return None
        if hi[0]>hi[8]:s=g.split(s,0,hi[8],True)
        if s is None:return None
        lo,hi=s
        if lo[8]<lo[0]:s=g.split(s,8,lo[0],False)
        if s is None:return None
        if s==(lo,hi):return s
    raise AssertionError('Unexpected order-closure iterations')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-nodes',type=int,default=3000)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('ordered-probe.json'));args=ap.parse_args()
    here=Path(__file__).parent;docs=[json.loads((here/n).read_text()) for n in ['parallel-master.json','parallel-0.json','parallel-1-master.json','parallel-2.json']]
    branches={z['path']:z for x in docs for z in x['branches']};leaves={z['path']:z for x in docs for z in x['accepted']}
    size={p:1 for p in leaves}
    for p in sorted(branches,key=len,reverse=True):
        a=size.get(p+'0',0);b=size.get(p+'1',0)
        if a and b:size[p]=1+a+b
    candidates={p for p in branches if 300<=size.get(p,0)<=1000};todo=[('r',g.root())];chosen=None
    while todo:
        p,s=todo.pop()
        if p in candidates and max(s[0][0]-s[0][8],s[1][0]-s[1][8])>g.SC//4:
            chosen=(p,s);break
        if p in branches:
            z=branches[p]
            for upper,bit in [(False,'1'),(True,'0')]:
                c=audit.child([list(s[0]),list(s[1])],z['axis'],z['cut'],upper)
                if c is not None:todo.append((p+bit,(c[0],c[1])))
    assert chosen is not None,'No representative complete asymmetric subtree found'
    prefix,initial=chosen;start=time.monotonic();todo=[(initial,0)];checked=accepted=reflection=tightened=depth=0
    while todo and checked<args.max_nodes:
        s,d=todo.pop();ss=ordered(s);checked+=1;depth=max(depth,d)
        if ss is None:reflection+=1;accepted+=1;continue
        tightened+=ss!=s;rec=g.certify(ss,False)
        if rec.get('empty') or int(rec.get('floor_numerator','-1'))>=g.TARGET:accepted+=1;continue
        ax,q=g.cut(ss,rec)
        for upper in [False,True]:
            nxt=g.split(ss,ax,q,upper)
            if nxt is not None:todo.append((nxt,d+1))
    out={'scope':'Isolated research experiment only; main coverage unchanged','prefix':prefix,
        'old_complete_subtree_nodes':size[prefix],'old_initial_cell':initial,
        'ordered_nodes':checked,'accepted':accepted,'unresolved':len(todo),'tightened_nodes':tightened,
        'reflection_leaves':reflection,'new_maxdepth':depth,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='old_initial_cell'}),flush=True)
if __name__=='__main__':main()
