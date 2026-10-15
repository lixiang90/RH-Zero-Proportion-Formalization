"""Independently check exported rational mixtures and flows (no optimizer).

Only Python integers, the attributed packed tables, and fixed potential data
are used. This is an independent arithmetic audit, not a Lean or nanoda replay.
"""
from pathlib import Path
import ast, re, gzip, json, hashlib, time
import affine_leaf_replay as source

f=source.f; DEN=source.DEN; SC=32768; WD=10**11*SC; LD=10**12
EXPECTED_SOURCE_SHA256='153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244'

if not __debug__:
    raise RuntimeError('This assertion-based arithmetic verifier must not run with python -O')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def full_table():
    ans={}
    for j,l in re.findall(r'\.lf (\d+) (\[[^\]]*\])',f.cert):
        for k,v in ast.literal_eval(l):
            p=1024*int(j)+k
            assert p not in ans, ('duplicate packed tangent',p)
            ans[p]=v
    assert len(ans)==2993 and set(ans)==set(f.PT)
    assert all((v&((1<<96)-1))==f.PT[p] for p,v in ans.items())
    return ans

def integer(value):
    if type(value) is int:return value
    assert type(value) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)',value)
    return int(value)

def closure(lo,hi):
    # Independent all-pairs closure; its inequalities follow by addition.
    d=[[0 if i==j else 10**20 for j in range(9)] for i in range(9)]
    for (i,j),l,u in zip(f.ALL,lo,hi):d[i][j]=u;d[j][i]=-l
    for k in range(9):
        for i in range(9):
            for j in range(9):
                if d[i][k]+d[k][j]<d[i][j]:d[i][j]=d[i][k]+d[k][j]
    assert all(d[i][i]==0 for i in range(9))
    return d

def check_record(record,cells,pt,psi):
    assert type(record['leaf']) is int and 0<=record['leaf']<len(cells)
    cell=cells[record['leaf']];word=record['word'];c=record['envelope']['certificate']
    assert type(record['root']) is int and type(record['pos']) is int
    assert record['root']==cell['root'] and record['pos']==cell['pos']
    assert record['reflected'] is cell['reflected']
    assert len(word)==8 and all(type(x) is int and x in (0,1,2) for x in word)
    cut=[(278528,491520),(491520,819200),(819200,13107200)]
    lo=[10*x for x in cell['lo']];hi=[10*x for x in cell['hi']]
    for r,t in enumerate(word):lo[r]=max(lo[r],cut[t][0]);hi[r]=min(hi[r],cut[t][1])
    assert lo==c['lower_bounds'] and hi==c['upper_bounds']
    d=closure(lo,hi)
    assert c['mixture_denominator']==LD
    assert DEN%(LD*WD)==0 and DEN%(10**20*10*SC)==0
    const,gap=psi(word)
    assert all(g%10==0 for g in gap)
    coeff=[b*(DEN//(10**20*10*SC))+g//10 for b,g in zip(f.BS,gap)]
    mass=[0]*len(f.TS)
    for t,p,weight,claimed_const,claimed_slope in c['mixture']:
        assert type(t) is int and 0<=t<len(f.TS)
        assert type(p) is int and p>=-1
        weight=integer(weight);assert weight>=0;mass[t]+=weight
        i,j,a,_=f.TS[t];l=-d[j][i];u=d[i][j]
        assert 0<=l<=u
        if p==-1:
            line_const=f.lb(l//10,(u+9)//10)*10*SC;line_slope=0
        else:
            raw=pt[p]
            # pwD offset format of PTrD, distinct from PT's absolute interval.
            left=max(0,p-((raw>>96)&((1<<20)-1)));right=p+(raw>>116)
            assert left<=p<=right and right>0 and 10*left<=l<=u<=10*right
            v=raw&((1<<96)-1);sp=(v>>32)&f.MASK32;dp=v>>64
            low=sp-2000000000;width=4000000000-sp-dp;assert width>=0
            line_const=10*SC*(v&f.MASK32)-100*low*p-10*width*max(10*p-l,0)
            line_slope=10*low
        assert str(line_const)==claimed_const and str(line_slope)==claimed_slope
        fac=weight*(DEN//(LD*WD));const+=fac*line_const
        for r in range(i,j):coeff[r]+=fac*line_slope
    for amount,(_,_,a,_) in zip(mass,f.TS):assert amount*10**20<=a*LD
    assert str(const)==c['intercept'] and list(map(str,coeff))==c['gap_coefficients']
    positions=[-coeff[0]]+[coeff[r-1]-coeff[r] for r in range(1,8)]+[coeff[7]]
    assert list(map(str,positions))==c['flow']['divergence']
    div=[0]*9;cost=0;seen=set()
    for i,j,amount,upper in c['flow']['nonzero_flow']:
        assert type(i) is int and type(j) is int
        assert type(upper) is int
        assert 0<=i<9 and 0<=j<9 and i!=j and (i,j) not in seen
        seen.add((i,j));amount=integer(amount);assert amount>=0
        assert upper==d[i][j]
        div[i]+=amount;div[j]-=amount;cost+=amount*upper
    assert div==positions and str(cost)==c['flow']['cost']
    floor=const-cost
    assert str(floor)==record['envelope']['floor_numerator']
    assert floor>=4299*(DEN//500000)
    return floor

def main():
    start=time.time();base=Path(__file__).parent
    assert sha(f.SRC)==EXPECTED_SOURCE_SHA256, 'archived source pin mismatch'
    cells=source.collect();pt=full_table()
    psi,hashes=source.potential();initial=base/'affine-leaf-replay.json'
    bound_paths=[f.SRC,Path(source.__file__),Path(__file__),initial,
        base/'validate_affine_potential.json',base/'ternary_potential_oracle.json']
    bound_before={str(p):sha(p) for p in bound_paths}
    first=json.loads(initial.read_text());expected={(r['leaf'],tuple(r['word'])) for r in first['unresolved']}
    seen=set();minimum=None;files=[];counts=[]
    for name in ['tangent-certificates-part0.json.gz','tangent-certificates-part1.json.gz']:
        path=base/name
        packed=path.read_bytes()
        data=json.loads(gzip.decompress(packed).decode('utf8'))
        assert data['input_hashes']==hashes and data['unresolved_count']==0
        assert data['target']=='4299/500000' and data['checked']==len(data['results'])
        for r in data['results']:
            key=(r['leaf'],tuple(r['word']));assert key not in seen and key in expected
            seen.add(key);floor=check_record(r,cells,pt,psi)
            if minimum is None or floor<minimum[0]:minimum=(floor,r['leaf'],r['word'])
        counts.append(len(data['results']));files.append({'path':name,
            'sha256':hashlib.sha256(packed).hexdigest(),'bytes':len(packed)})
    assert seen==expected and sum(counts)==8004
    assert bound_before=={str(p):sha(p) for p in bound_paths}, 'an input changed during verification'
    assert all(sha(base/item['path'])==item['sha256'] for item in files), 'a compressed certificate changed during verification'
    from fractions import Fraction as Q
    good=Q(f.CN,10**20)+Q(17,20)*Q(sum(f.BS)-max(f.BS),10**20)-Q(69,25000)
    assert good>Q(4299,500000)
    result={'status':'independent exact arithmetic audit passed; NOT a completed Lean zero-proportion proof',
        'all_exported_certificates_passed':True,'initial_cells':first['cell_count'],
        'initial_empty_cells':first['empty_cells'],'exported_checked':len(seen),
        'part_counts':counts,'input_hashes':hashes,'initial_sha256':sha(initial),
        'bound_input_sha256':bound_before,
        'files':files,'minimum_floor':{'numerator':str(minimum[0]),'denominator':str(DEN),
            'decimal_for_display':minimum[0]/DEN,'leaf':minimum[1],'word':minimum[2]},
        'target':'4299/500000','good_gap_complement_arithmetic':{'numerator':str(good.numerator),
            'denominator':str(good.denominator)},
        'remaining_Lean_obligations':['instantiate TVal, mixture and flow data for each exceptional leaf',
            'prove all classified subcells and the initial geometric branches are covered',
            'connect the good-gap complement and the fixed potential to the summed counting interface',
            'run full statement/dependency comparison and both kernel replays on a final unconditional theorem'],
        'seconds':time.time()-start}
    (base/'independent-certificate-audit.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
