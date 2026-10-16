"""Exact parent recertification at weaker W10 floors, preserving the full domain.

This is a finite-data experiment, not a Lean coverage proof. No inherited
source or parameter is changed. A separately parsed analytic library checks
every exported parent certificate by integer arithmetic and tangent domains.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,bisect,hashlib,importlib.util,json,sys,time

ROOT=Path(__file__).resolve().parents[1]
OLD=ROOT/'research-20261016-w10-cert'
sys.path.insert(0,str(OLD))
import ordered_generate as ordered
from reduce_proof_input import Stream,sha
g=ordered.g
spec=importlib.util.spec_from_file_location('independent_w10_auditor',OLD/'independent_integer_audit.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
POINTS,LOWER=audit.load_analytic_library()
FLOORS=[F(863,100000),F(864,100000),F(865,100000),F(1731,200000)]

def branches_only(path):
    source=Stream(path);source.eat('{');first=True
    while source.peek()!='}':
        if not first:source.eat(',')
        key=source.value();source.eat(':')
        if key=='branches':
            result={r['path']:r for r in source.array()};source.close();return result
        source.value();first=False
    raise AssertionError('Missing branch array')

def independently_check(state,record):
    """Independent Nat/sub/tangent-domain replay; does not invoke generator helpers."""
    lo,hi=state
    assert record['certificate']['lower_bounds']==lo and record['certificate']['upper_bounds']==hi
    audit.closure_valid(state)
    positive=[0]*9;negative=[0]*9;cp=cm=0
    for i,j,upper,weight in record['multiplier']['steps']:
        y=int(weight);assert y>=0 and (i,j) in audit.INDEX and j>=i+2 and isinstance(upper,bool)
        z=audit.INDEX[i,j];base=sum(lo[i:j])
        for k in range(i,j):(negative if upper else positive)[k]+=y
        if upper:cp+=y*max(hi[z]-base,0);cm+=y*max(base-hi[z],0)
        else:cp+=y*max(base-lo[z],0);cm+=y*max(lo[z]-base,0)
    dual=record['multiplier']
    assert positive==list(map(int,dual['P'])) and negative==list(map(int,dual['S']))
    assert cp==int(dual['Cp']) and cm==int(dual['Cm'])
    value=loss=gain=0;slopes=[0]*9;mass=[0]*9
    assert len(record['FS'])==39
    for (i,j,a),(kind,m,p,r) in zip(g.TERMS,record['FS']):
        assert kind in range(4) and 0<=m<=1024 and p>=0 and r>=0
        w1,w2=([0,0] if kind==0 else [1024,0] if kind==1 else [m,0] if kind==2 else [1024-m,m])
        z=audit.INDEX[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]))
        base=sum(lo[i:j]);total=(1024-w1-w2)*LOWER(left,max(left+1,right));derivative=0
        for weight,anchor in [(w1,p),(w2,r)]:
            word,l,u=POINTS.get(anchor,(0,0,0))
            if weight:assert u>0 and l<=left<=anchor<=right<=u,(i,j,anchor,l,left,right,u)
            val=word&audit.MASK;sl=(word>>32)&audit.MASK;deriv=word>>64
            total+=weight*val;derivative+=weight*sl
            loss+=a*weight*max(2000000000-deriv,0)*max(anchor-base,0)
            gain+=a*weight*max(deriv-2000000000,0)*max(anchor-base,0)
        value+=a*total
        for k in range(i,j):slopes[k]+=a*derivative;mass[k]+=a*(w1+w2)
    penalty=sum(max(hi[k]-lo[k],0)*max(2000000000*mass[k]+positive[k]-1024000000000*g.BS[k]-slopes[k]-negative[k],0) for k in range(9))
    numerator=10240000000000*sum(g.BS[k]*lo[k] for k in range(9))+32768*value+10*(gain+cm)-10*(loss+cp+penalty)
    assert numerator==int(record['floor_numerator'])==int(record['mcheck_numerator'])
    return numerator

def count_subtree(branchpaths,path):
    return bisect.bisect_left(branchpaths,path+'2')-bisect.bisect_left(branchpaths,path)+1

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=1000)
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('prune-floor-probe.json'))
    args=ap.parse_args();started=time.monotonic();source=OLD/'ordered-proof-input.json';source_sha=sha(source)
    names=['generate.py','ordered_generate.py','compact_thin.py','tree_flow.py','independent_integer_audit.py']
    helpers={name:sha(OLD/name) for name in names};branches=branches_only(source);paths=sorted(branches)
    # Equally spaced lexicographic positions sample the complete branch set,
    # rather than cherry-picking geometrically easy parents.
    selected={paths[(k*(len(paths)-1))//max(1,args.limit-1)] for k in range(min(args.limit,len(paths)))}
    needed={p[:k] for p in selected for k in range(1,len(p)+1)}
    todo=[('r',g.root())];states={}
    while todo:
        path,state=todo.pop()
        if path not in needed:continue
        state,cuts=ordered.normalize(state)
        if path in selected:states[path]=state
        node=branches[path]
        for digit,upper in [('1',False),('0',True)]:
            if path+digit in needed:todo.append((path+digit,ordered.rawsplit(state,node['axis'],node['cut'],upper)))
    rows=[]
    for n,(path,state) in enumerate(sorted(states.items()),1):
        result=g.certify(state,True);numerator=independently_check(state,result)
        # Keep only the exact checker inputs; optimizer floats choose, never certify.
        exact={key:result[key] for key in ['FS','multiplier','floor_numerator','mcheck_numerator']}
        exact['certificate']={'lower_bounds':state[0],'upper_bounds':state[1]}
        rows.append({'path':path,'depth':len(path)-1,'old_subtree_leaves':count_subtree(paths,path),
                     'exact_numerator':str(numerator),'lp_floor_float_hint':result.get('lp_floor'),
                     'passes':{str(c):numerator*c.denominator>=g.DEN*c.numerator for c in FLOORS},'result':exact})
        if n%100==0:print(json.dumps({'parents_done':n,'total':len(states),'seconds':time.monotonic()-started}),flush=True)
    h=F(6721684105641188747759983512104999330646,10**40);B=F(10999681,2500000000)
    previous=F(34191001116882886388531117129201664,50760020691785094633026544189453125)
    alternatives=[]
    for c in FLOORS:
        passed=[r for r in rows if r['passes'][str(c)]]
        top=[]
        for row in sorted(passed,key=lambda r:(len(r['path']),r['path'])):
            if not any(row['path'].startswith(t['path']) for t in top):top.append(row)
        ratio=(h-B)/(1-c)
        alternatives.append({'c':str(c),'kappa':str(ratio),'percentage_float_display':100*float(ratio),
            'strictly_beats_current_record_exact':ratio>previous,'gain_percentage_points_float_display':100*float(ratio-previous),
            'certified_sample_parents':len(passed),'sample_topmost_pruned_subtrees':len(top),
            'exact_leaf_saving_from_sample_only':sum(r['old_subtree_leaves']-1 for r in top),
            'largest_pruned_subtree':max((r['old_subtree_leaves'] for r in passed),default=0)})
    report={'scope':__doc__,'input_sha256':source_sha,'parameter_sha256':sha(g.PAR),
        'source_helpers_sha256':helpers,'probe_script_sha256':sha(Path(__file__)),
        'original_branches':len(paths),'sample_parents':len(rows),'sampling':'Equally spaced sorted branch paths',
        'denominator':str(g.DEN),'old_root_retained_conservatively':True,
        'root_budget_c':'433/50000','all_exported_parent_integer_checks_passed':True,
        'all_tangent_domains_independently_checked':True,'lean_proof_created':False,
        'c_strict_threshold_to_beat_current_record':str(1-(h-B)/previous),
        'alternatives':alternatives,'seconds':time.monotonic()-started}
    assert sha(source)==source_sha and helpers=={name:sha(OLD/name) for name in names}
    args.output.write_text(json.dumps({'stats':report,'parents':rows},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps(report),flush=True)
if __name__=='__main__':main()
