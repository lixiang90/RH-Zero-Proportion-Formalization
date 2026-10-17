"""One fixed bottom-up reuse of original numerical certificates.

No LP, sampling, new point, mixture, kind, table or mathematical search is
used. At most the left and right subtree representatives are tried at each
normalized parent. All actual tangent guards and integer payments are tested.
The input proof tree and every published Lean source remain unchanged.
"""
from pathlib import Path
import argparse, functools, gzip, hashlib, importlib.util, json, struct, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
AUDIT=HERE.with_name('w10-size-audit-20261017')
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

geometry=module('frozen_semantic_extract',AUDIT/'extract_semantics.py')
integer=module('frozen_integer_audit',ROOT/'research-20261016-w10-cert/independent_integer_audit.py')
meta=json.loads((AUDIT/'semantics.json').read_bytes())
for r in meta['cache_files']:assert sha((AUDIT/r['path']).read_bytes())==r['sha256']
NODES=(AUDIT/'nodes.bin').read_bytes();FS=(AUDIT/'fs.bin').read_bytes();CODES=(AUDIT/'treecodes.bin').read_bytes()
terms=meta['terms'];bs=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_bytes())['b_numerators']
points,lower=integer.load_analytic_library();SLOT=geometry.SLOT
sub=lambda a,b:max(0,a-b)

@functools.lru_cache(maxsize=4096)
def witness(index):
    return [tuple([k,m,p*32,r*32])for k,m,p,r in struct.iter_unpack('<BHHH',FS[index*273:(index+1)*273])]

@functools.lru_cache(maxsize=4096)
def moves(index):
    code=struct.unpack_from('<I',CODES,4*index)[0]
    return integer.tree_dual(witness(index),code,terms,bs,points)

def check(index,state,n):
    lo,hi=state;fs=witness(index)
    if any(l>u for l,u in zip(lo[:9],hi[:9])):return {'passed':False,'reason':'gap_box_invalid'}
    for t,((i,j,a),(kind,m,p,r))in enumerate(zip(terms,fs)):
        weights=[0,0]if kind==0 else[1024,0]if kind==1 else[m,0]if kind==2 else[1024-m,m]
        z=SLOT[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]))
        for weight,anchor in zip(weights,[p,r]):
            if weight:
                _,vl,vu=points.get(anchor,(0,0,0))
                if not(vu>0 and vl<=left<=anchor<=right<=vu):
                    return {'passed':False,'reason':'tangent_guard','term':t,
                      'required':[left,right],'certified':[vl,vu],'anchor':anchor}
    positive=[0]*9;negative=[0]*9;cp=cm=0
    for i,j,upper,weight in moves(index):
        y=int(weight);z=SLOT[i,j];base=sum(lo[i:j])
        for k in range(i,j):(negative if upper else positive)[k]+=y
        if upper:cp+=y*sub(hi[z],base);cm+=y*sub(base,hi[z])
        else:cp+=y*sub(base,lo[z]);cm+=y*sub(lo[z],base)
    value=loss=gain=0;slopes=[0]*9;mass=[0]*9
    for (i,j,a),(kind,m,p,r)in zip(terms,fs):
        w1,w2=[0,0]if kind==0 else[1024,0]if kind==1 else[m,0]if kind==2 else[1024-m,m]
        z=SLOT[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]));base=sum(lo[i:j])
        total=(1024-w1-w2)*lower(left,max(left+1,right));derivative=0
        for weight,anchor in [(w1,p),(w2,r)]:
            word=points.get(anchor,(0,0,0))[0]
            total+=weight*(word&integer.MASK);derivative+=weight*((word>>32)&integer.MASK)
            deriv=word>>64
            loss+=a*weight*sub(2000000000,deriv)*sub(anchor,base)
            gain+=a*weight*sub(deriv,2000000000)*sub(anchor,base)
        value+=a*total
        for k in range(i,j):slopes[k]+=a*derivative;mass[k]+=a*(w1+w2)
    penalty=sum(sub(hi[k],lo[k])*sub(2000000000*mass[k]+positive[k],1024000000000*bs[k]+slopes[k]+negative[k])for k in range(9))
    numerator=10240000000000*sum(bs[k]*lo[k]for k in range(9))+32768*value+10*(gain+cm)-10*(loss+cp+penalty)
    target=335544320000000000*n
    return {'passed':numerator>=target,'reason':'integer_inequality','numerator':str(numerator),'target':str(target),'margin':str(numerator-target)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--limit',type=int,default=1000,help='Number of postorder parents; zero means one complete pass.')
    ap.add_argument('--lower-pilot',action='store_true',help='Only replay the saved same 1000 parent/candidate pairs at n=86450000.')
    args=ap.parse_args();started=time.monotonic();cpu=time.process_time()
    if args.lower_pilot:
        pilot=json.loads((HERE/'pilot-original.json').read_bytes());rows=[]
        for row in pilot['trials']:
            checks=[{'index':r['index'],**check(r['index'],row['cell'],86450000)}for r in row['checks']]
            rows.append({'path':row['path'],'checks':checks,'passed':any(r['passed']for r in checks)})
        out={'scope':'One fixed lower floor on the identical original-pilot parent/candidate pairs.',
             'n':86450000,'original_pilot_sha256':sha((HERE/'pilot-original.json').read_bytes()),'parents':len(rows),
             'passed_parents':sum(r['passed']for r in rows),'rows':rows,'seconds':time.monotonic()-started,
             'new_global_tree_generated':False,'Lean_verified':False}
        (HERE/'pilot-lower.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
        print(json.dumps({k:v for k,v in out.items()if k!='rows'}),flush=True);return
    position=numeric=parents=successes=0;trials=[];paths=[]
    class PilotStop(Exception):pass
    def visit(path,state):
        nonlocal position,numeric,parents,successes
        state=geometry.normal(state);kind=NODES[position];position+=1
        if kind==1:
            axis,cut=struct.unpack_from('<BI',NODES,position);position+=5
            left=visit(path+'0',geometry.child(state,axis,cut,True))
            right=visit(path+'1',geometry.child(state,axis,cut,False))
            checks=[];chosen=None
            for rep in [left['representative'],right['representative']]:
                if rep is None:continue
                result=check(rep,state,86600000);checks.append({'index':rep,**result})
                if result['passed'] and chosen is None:chosen=rep
            parents+=1
            if args.limit:trials.append({'path':path,'cell':state,'checks':checks,'passed':chosen is not None})
            original_count=left['original_numeric']+right['original_numeric']
            if chosen is not None:
                successes+=1
                node={'path':path,'kind':'numeric','index':chosen,'representative':chosen,'original_numeric':original_count}
            else:
                rep=left['representative']if left['representative']is not None else right['representative']
                node={'path':path,'kind':'branch','axis':axis,'cut':cut,'left':left,'right':right,
                      'representative':rep,'original_numeric':original_count}
            if parents%10000==0:print(json.dumps({'parents':parents,'successful_parent_checks':successes,'seconds':time.monotonic()-started}),flush=True)
            if args.limit and parents==args.limit:raise PilotStop()
            return node
        if kind==0:
            index=numeric;numeric+=1;paths.append(path)
            return {'path':path,'kind':'numeric','index':index,'representative':index,'original_numeric':1}
        if kind==2:
            axis=NODES[position];position+=1
            return {'path':path,'kind':'empty','violation_axis':axis,'representative':None,'original_numeric':0}
        assert kind==3
        return {'path':path,'kind':'reflection','representative':None,'original_numeric':0}
    try:root_node=visit('r',meta['root'])
    except PilotStop:
        out={'scope':__doc__,'n':86600000,'parents':parents,'passed_parents':successes,'trials':trials,
             'seconds':time.monotonic()-started,'CPU_seconds':time.process_time()-cpu,
             'script_sha256':sha(Path(__file__).read_bytes()),'semantics_sha256':sha((AUDIT/'semantics.json').read_bytes()),
             'original_numeric_representative_rule':'Successful child representative, otherwise leftmost numerical representative; try both children, at most two per parent.',
             'complete_global_tree_generated':False,'Lean_verified':False}
        (HERE/'pilot-original.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
        print(json.dumps({k:v for k,v in out.items()if k!='trials'}),flush=True);return
    assert position==len(NODES)and numeric==95615 and parents==95778
    branches=[];leaves=[]
    def emit(node):
        if node['kind']=='branch':
            branches.append({k:node[k]for k in ['path','axis','cut']});emit(node['left']);emit(node['right'])
        elif node['kind']=='numeric':
            index=node['index'];leaves.append({'path':node['path'],'kind':'numeric','FS':witness(index),
               'tree_code':struct.unpack_from('<I',CODES,4*index)[0],
               'original_witness_path':paths[index],'original_numeric_covered':node['original_numeric']})
        else:leaves.append({k:node[k]for k in ['path','kind','violation_axis']if k in node})
    emit(root_node)
    out={'scope':__doc__,'root':meta['root'],'n':86600000,'target':'433/50000',
         'branches':branches,'leaves':leaves,'parents_tested':parents,'successful_parent_checks':successes,
         'retained_numeric_leaves':sum(r['kind']=='numeric'for r in leaves),'retained_leaf_count':len(leaves),
         'original_numeric_leaves':95615,'seconds':time.monotonic()-started,'CPU_seconds':time.process_time()-cpu,
         'script_sha256':sha(Path(__file__).read_bytes()),'semantics_sha256':sha((AUDIT/'semantics.json').read_bytes()),
         'complete_partition_generated':True,'independent_replay_passed':False,'Lean_verified':False}
    raw=json.dumps(out,separators=(',',':')).encode();packed=gzip.compress(raw,mtime=0)
    (HERE/'merged-tree.json.gz').write_bytes(packed)
    summary={k:v for k,v in out.items()if k not in ['branches','leaves','root']}
    summary.update({'packet_sha256':sha(packed),'packet_bytes':len(packed),'uncompressed_bytes':len(raw)})
    (HERE/'merged-summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf8')
    print(json.dumps(summary),flush=True)

if __name__=='__main__':main()
