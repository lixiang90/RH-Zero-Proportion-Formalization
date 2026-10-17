"""Check the two existing child witnesses on one already-covered parent.

No solver, witness modification, or mathematical search is performed. A
positive result is only an exact-integer candidate for a later Lean check.
"""
from pathlib import Path
import hashlib, importlib.util, json
from fractions import Fraction

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
p=ROOT/'research-20261016-w10-cert/independent_integer_audit.py'
spec=importlib.util.spec_from_file_location('frozen_integer_audit',p)
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
packet=json.loads((HERE/'selected-parent.json').read_bytes())
meta=json.loads((HERE/'semantics.json').read_bytes())
parameters=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_bytes())
terms=meta['terms'];bs=parameters['b_numerators']
points,lower=audit.load_analytic_library()
lo,hi=packet['normalized_cell'];SLOT=audit.INDEX;sub=lambda a,b:max(0,a-b)
TARGET=433*(audit.SCALE//50000)

def check(fs,code):
    moves=audit.tree_dual(fs,code,terms,bs,points)
    positive=[0]*9;negative=[0]*9;cp=cm=0
    for i,j,upper,weight in moves:
        y=int(weight);z=SLOT[i,j];base=sum(lo[i:j])
        for k in range(i,j):(negative if upper else positive)[k]+=y
        if upper:cp+=y*sub(hi[z],base);cm+=y*sub(base,hi[z])
        else:cp+=y*sub(base,lo[z]);cm+=y*sub(lo[z],base)
    value=loss=gain=0;slopes=[0]*9;mass=[0]*9;invalid=[]
    for t,((i,j,a),(kind,m,p,r))in enumerate(zip(terms,fs)):
        w1,w2=[0,0]if kind==0 else[1024,0]if kind==1 else[m,0]if kind==2 else[1024-m,m]
        z=SLOT[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]));base=sum(lo[i:j])
        total=(1024-w1-w2)*lower(left,max(left+1,right));derivative=0
        for weight,anchor in [(w1,p),(w2,r)]:
            word,vl,vu=points.get(anchor,(0,0,0))
            if weight and not(vu>0 and vl<=left<=anchor<=right<=vu):
                invalid.append({'term':t,'span':[i,j],'anchor':anchor,
                  'required_interval':[left,right],'certified_interval':[vl,vu]})
            total+=weight*(word&audit.MASK);derivative+=weight*((word>>32)&audit.MASK)
            deriv=word>>64
            loss+=a*weight*sub(2000000000,deriv)*sub(anchor,base)
            gain+=a*weight*sub(deriv,2000000000)*sub(anchor,base)
        value+=a*total
        for k in range(i,j):slopes[k]+=a*derivative;mass[k]+=a*(w1+w2)
    penalty=sum(sub(hi[k],lo[k])*sub(2000000000*mass[k]+positive[k],
        1024000000000*bs[k]+slopes[k]+negative[k])for k in range(9))
    numerator=10240000000000*sum(bs[k]*lo[k]for k in range(9))+32768*value+10*(gain+cm)-10*(loss+cp+penalty)
    return {'whole_parent_tangents_valid':not invalid,'invalid_tangent_intervals':invalid,
       'numerator':str(numerator),'target':str(TARGET),'margin_numerator':str(numerator-TARGET),
       'floor_if_valid':str(Fraction(numerator,audit.SCALE)),
       'exact_uniform_checker_passed':not invalid and numerator>=TARGET}

rows=[{'child_witness':r['path'],**check(r['FS'],r['tree_code'])}for r in packet['children']]
# One explicit common-energy proposal: use the first child, replacing every
# invalid whole-parent tangent by the inherited certified interval lower bound.
# This is one deterministic candidate, not an optimizer or an anchor search.
first=packet['children'][0]
invalid_terms=sorted({r['term']for r in rows[0]['invalid_tangent_intervals']})
coarsened=[list(r)for r in first['FS']]
for t in invalid_terms:coarsened[t]=[0,0,0,0]
rows.append({'child_witness':first['path'],'deterministic_proposal':'invalid tangents replaced by old interval lower bound',
             'replaced_terms':invalid_terms,'FS':coarsened,'tree_code':first['tree_code'],
             **check(coarsened,first['tree_code'])})
out={'scope':__doc__,'parent_path':packet['path'],'parent_bounds':packet['normalized_cell'],
     'existing_children':[r['path']for r in packet['children']],'rows':rows,
     'Lean_verified':False,'new_formal_leaf_count':0,
     'analytic_library_sha256':hashlib.sha256(audit.SOURCE.read_bytes()).hexdigest(),
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(HERE/'parent-uniform-probe.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'parent':packet['path'],'rows':rows}))
