"""Independent exact audit of W10 mcheckGX cells and the exported partition.

This program imports neither the generator nor finite_margin_20261015.  It
reads the frozen rational parameters and inherited analytic table source.  Its
integer audit is supporting evidence; only the Lean checkLeaf_sound theorem
and a complete Lean cover can establish the analytic floor.
"""
from pathlib import Path
from fractions import Fraction
import argparse, ast, collections, functools, hashlib, json, re, sys, time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
SC = 32768
Q = 9
N = 10
MASK = 2**32-1
BB = 2**42
SCALE = 3355443200000000000000000000
TARGET = 433*(SCALE//50000)
PAIRS = [(i,i+1) for i in range(Q)] + [(i,j) for i in range(Q) for j in range(i+2,N)]
INDEX = {p:i for i,p in enumerate(PAIRS)}
SOURCE = ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean'
PARAMETER = ROOT/'research-20261016/spectral-w10-refined-rational.json'
STEP = int('27723537362511871605908476295798662247233181642325596381965450035666703580892695812701556801522819903482709807068884625171714348091451162793954575790575100589725652890107126812452448984028529561041497038633556695377889700159758912')

def sha(data): return hashlib.sha256(data).hexdigest()
def sub(a,b): return max(0,a-b)

def load_analytic_library():
    text=SOURCE.read_text(encoding='utf8')
    text=text[text.index('namespace AMW.Cert.PC9QB6M\n'):]
    top=int(re.search(r'^def TOP[^\n]*:= (0x[0-9a-f]+)',text,re.M).group(1),16)
    blocks={int(n):int(v,16) for n,v in re.findall(r'^def BK_(\d+)[^\n]*:= (0x[0-9a-f]+)',text,re.M)}
    points={}
    for j,table in re.findall(r'\.lf (\d+) (\[[^\]]*\])',text):
        for k,v in ast.literal_eval(table):
            p=1024*int(j)+k
            assert p not in points, ('ambiguous point',p)
            points[p]=(v & (2**96-1), max(0,p-((v>>96)&(2**20-1))),p+(v>>116))
    @functools.lru_cache(None)
    def entry(level,index):
        if level>=20: return 0
        if level>=11: return (top>>(32*((1<<sub(19,level))+index)))&MASK
        block=index>>sub(10,level)
        word=blocks.get(block,0)
        depth=level+sub(word&31,level)
        shift=sub(10,depth)
        offset=sub((1<<shift),1)+sub(index>>sub(depth,level),block<<shift)
        return (word>>(5+32*offset))&MASK
    @functools.lru_cache(None)
    def lower(left,right):
        if right<=left or right>=524289: return 0
        level=((right-left)>>5).bit_length()
        end=((right-1)>>level)+1
        index=left>>level
        values=[]
        for _ in range(14):
            advance=(STEP>>(3*(17*(index&15)+min(sub(end,index),16))))&7
            parent=index>>advance
            values.append(entry(level+advance,parent))
            index=(parent+1)<<advance
            if end<=index: return min(values)
        return 0
    return points, lower

def edge_value(state,i,j):
    if i==j: return 0
    return state[1][INDEX[i,j]] if i<j else -state[0][INDEX[j,i]]

def closure_valid(state):
    lo,hi=state
    assert len(lo)==len(hi)==45 and all(isinstance(v,int) and 0<=v<BB//8 for v in lo+hi)
    assert all(l<=u for l,u in zip(lo,hi))
    d=[[edge_value(state,i,j) for j in range(N)] for i in range(N)]
    assert all(d[i][j]<=d[i][k]+d[k][j] for i in range(N) for j in range(N) for k in range(N))

def raw_child(state,axis,cut,upper):
    # Evaluate the fixed Core cuB formula with its actual Nat subtraction.
    i,j=PAIRS[axis]
    a,b=(i,j) if upper else (j,i)
    base=BB+cut if upper else sub(BB,cut)
    # dE uses Nat subtraction before subsequent additions; retaining this
    # order also covers inconsistent intermediate normalization cells.
    def dE(e,x,y):
        if x<y: return e+state[1][INDEX[x,y]]
        if x==y: return e
        return sub(e,state[0][INDEX[y,x]])
    col=[dE(BB,x,a) for x in range(N)]
    row=[dE(base,b,x) for x in range(N)]
    lo=[max(l,sub(2*BB,col[j]+row[i])) for l,(i,j) in zip(state[0],PAIRS)]
    hi=[min(u,sub(col[i]+row[j],2*BB)) for u,(i,j) in zip(state[1],PAIRS)]
    return [lo,hi]

def child(state,axis,cut,upper):
    result=raw_child(state,axis,cut,upper)
    if any(l>u for l,u in zip(*result)): return None
    closure_valid(result)
    return result

def normalize_ordered(state):
    cuts=[]
    for _ in range(2):
        q=state[1][8]; cuts.append(q); state=raw_child(state,0,q,True)
        q=state[0][0]; cuts.append(q); state=raw_child(state,8,q,False)
    if all(l<=u for l,u in zip(*state)): closure_valid(state)
    return state,cuts

def initial_root(bs):
    sep=27852
    budget=86600000*SC-sep*sum(bs)
    up=[sep+(budget+b-1)//b for b in bs]
    lower=[(j-i)*sep for i,j in PAIRS]
    upper=[min(sum(up[i:j]),(j-i)*sep+(budget+min(bs[i:j])-1)//min(bs[i:j])) for i,j in PAIRS]
    result=[lower,upper]
    closure_valid(result)
    assert Fraction(sep,SC)<=Fraction(17,20)
    # Each exported upper bound is conservative for all pressure-bounded points.
    for (i,j),u in zip(PAIRS,upper):
        assert min(bs[i:j])*(u-(j-i)*sep)>=budget
    return result

def decode_relative(payload,state,terms):
    alphabet=''.join(chr(c) for c in range(33,127) if c not in [34,92])
    combined=0
    for char in payload['text']:
        combined=92*combined+alphabet.index(char)
    support,tree=divmod(combined,10**8)
    assert support==int(payload['support_hex'],16) and tree==payload['tree_code']
    bits=support; mask=bits%(2**39); bits//=2**39
    def take(n):
        nonlocal bits
        out=bits%(2**n); bits//=2**n; return out
    def point(t):
        i,j,_=terms[t]; z=INDEX[i,j]
        lower=max(state[0][z],sum(state[0][i:j]))
        upper=min(state[1][z],sum(state[1][i:j]))
        base=(lower+31)//32
        width=sub(upper//32,base).bit_length()
        return 32*(base+take(width))
    result=[]
    for t in range(39):
        if not(mask>>t)&1: result.append([0,0,0,0]); continue
        if take(1)==0: result.append([1,0,point(t),0]); continue
        k=2+take(1); m=take(10); p=point(t); r=0
        if k==3:
            tag=take(2)
            r=[sub(p,32),p+32,sub(p,256)][tag] if tag<3 else point(t)
        result.append([k,m,p,r])
    assert bits==0
    if 'FS' in payload: assert result==payload['FS']
    return result,tree

def tree_dual(fs,code,terms,bs,points):
    coefficients=[1024000000000*b for b in bs]
    for (i,j,a),(k,m,p,r) in zip(terms,fs):
        w1,w2=([0,0] if k==0 else [1024,0] if k==1 else [m,0] if k==2 else [1024-m,m])
        value=0
        for weight,point in [(w1,p),(w2,r)]:
            word=points.get(point,(0,0,0))[0]
            value+=weight*(((word>>32)&MASK)-2000000000)
        for z in range(i,j): coefficients[z]+=a*value
    divergence=[-coefficients[0]]+[coefficients[i-1]-coefficients[i] for i in range(1,9)]+[coefficients[8]]
    assert sum(divergence)==0 and 0<=code<10**8
    sequence=[(code//(10**i))%10 for i in range(8)]
    degree=[1+sequence.count(i) for i in range(10)]; edges=[]
    for p in sequence:
        leaf=next(i for i in range(10) if degree[i]==1)
        edges.append(tuple(sorted([leaf,p]))); degree[leaf]-=1;degree[p]-=1
    edges.append(tuple(i for i in range(10) if degree[i]==1))
    assert len(edges)==len(set(edges))==9
    rebuilt=[0]*10; moves=[]
    for a,b in edges:
        seen={a}; pending=[a]
        while pending:
            x=pending.pop()
            for e1,e2 in edges:
                if (e1,e2)==(a,b): continue
                if e1==x and e2 not in seen: seen.add(e2);pending.append(e2)
                if e2==x and e1 not in seen: seen.add(e1);pending.append(e1)
        assert b not in seen
        flow=sum(divergence[x] for x in seen)
        rebuilt[a]+=flow; rebuilt[b]-=flow
        if b>a+1: moves.append([a,b,flow>=0,str(abs(flow))])
    assert rebuilt==divergence
    return moves

def main():
    if not __debug__: raise RuntimeError('Assertions must remain enabled for this verifier')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('inputs',nargs='+',type=Path)
    parser.add_argument('--relative',nargs='*',type=Path,default=[])
    parser.add_argument('--output',type=Path,default=HERE/'independent-integer-audit.json')
    args=parser.parse_args()
    started=time.monotonic()
    raw_parameter=PARAMETER.read_bytes(); parameter=json.loads(raw_parameter)
    raw_source=SOURCE.read_bytes()
    assert sha(raw_parameter)=='ad117819d63588c55d89bd59ae7f0ad11072faaf33ffc53bf08d7eef54010e03'
    assert sha(raw_source)=='153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244'
    terms=[tuple(row) for row in parameter['a_upper'] if row[2]]
    bs=parameter['b_numerators']
    assert len(terms)==39 and len(bs)==9 and sum(bs)==43998724
    points,lower=load_analytic_library()
    branches={}; leaves={}; frontier={}; inputs=[]; ordered=None; packed={}; packed_inputs=[]; packed_empty={}
    def put(table,path,row):
        if path in table: assert table[path]==row, ('inconsistent duplicate',path)
        table[path]=row
    root=initial_root(bs)
    for path in args.inputs:
        raw=path.read_bytes(); record=json.loads(raw)
        inputs.append({'path':str(path),'sha256':sha(raw),'bytes':len(raw)})
        fmt=record.get('format','mcheckGX-1024')
        assert fmt in ['mcheckGX-1024','ordered-mcheckGX-1024']
        if ordered is None: ordered=fmt=='ordered-mcheckGX-1024'
        assert ordered==(fmt=='ordered-mcheckGX-1024')
        if ordered: assert record['normalize_rounds']==2
        assert record.get('SC',SC)==SC
        assert int(record.get('denominator',SCALE))==SCALE and record.get('target','433/50000')=='433/50000'
        assert record.get('source_sha256',sha(raw_source))==sha(raw_source)
        assert record.get('parameter_sha256',sha(raw_parameter))==sha(raw_parameter)
        assert record['root']==root and [tuple(r) for r in record.get('terms',terms)]==terms
        for row in record['branches']: put(branches,row['path'],row)
        for row in record['accepted']: put(leaves,row['path'],row)
        for row in record['unresolved']: put(frontier,row['path'],row)
    for path in args.relative:
        raw=path.read_bytes(); record=json.loads(raw)
        packed_inputs.append({'path':str(path),'sha256':sha(raw),'bytes':len(raw)})
        if 'stats' in record:
            assert record['stats']['processed']==len(record['leaves'])
        else:
            metadata=record['receipt']
            assert metadata['accepted_count']==len(record['leaves'])
            assert metadata['numeric_count']==sum(row['kind']=='numeric' for row in record['leaves'])
            assert metadata['input_sha256'] in {row['sha256'] for row in inputs}, 'Packed data must name a frozen raw input included in this audit'
        for row in record['leaves']:
            put(packed_empty if row.get('kind') in ['empty','reflection'] else packed,row['path'],row)
    assert not(set(branches)&set(leaves))
    used_branches=set(); used_leaves=set(); used_frontier=set()
    counts=collections.Counter(); minimum=None; minimum_path=None

    def verify_leaf(path,state,record):
        nonlocal minimum,minimum_path
        if record.get('empty'):
            if record.get('reflection'):
                assert state[1][8]<state[0][0], ('unproved reflection',path)
                if path in packed_empty: assert packed_empty[path]['kind']=='reflection'
                counts['reflection_leaves']+=1
            else:
                axis=record['violation_axis']
                assert 0<=axis<45 and state[1][axis]<state[0][axis], ('unproved empty',path)
                assert record['certificate']['lower_bounds']==state[0]
                assert record['certificate']['upper_bounds']==state[1]
                if path in packed_empty: assert packed_empty[path]['kind']=='empty' and packed_empty[path]['violation_axis']==axis
                counts['normalized_empty_leaves']+=1
            return
        lo,hi=state
        data=record['certificate']
        assert data['lower_bounds']==lo and data['upper_bounds']==hi, ('leaf cell mismatch',path)
        replacement=packed.get(path)
        if replacement:
            fs,tree=decode_relative(replacement,state,terms)
            dual={'steps':tree_dual(fs,tree,terms,bs,points)}
            counts['independently_decoded_relative_leaves']+=1
        else: fs=record['FS']; dual=record['multiplier']
        assert len(fs)==39
        positive=[0]*Q; negative=[0]*Q; cp=cm=0
        for i,j,upper,weight in dual['steps']:
            y=int(weight); assert y>=0 and (i,j) in INDEX and j>=i+2 and isinstance(upper,bool)
            z=INDEX[i,j]; base=sum(lo[i:j])
            for k in range(i,j): (negative if upper else positive)[k]+=y
            if upper: cp+=y*sub(hi[z],base); cm+=y*sub(base,hi[z])
            else: cp+=y*sub(base,lo[z]); cm+=y*sub(lo[z],base)
        if not replacement:
            assert positive==list(map(int,dual['P'])) and negative==list(map(int,dual['S']))
            assert cp==int(dual['Cp']) and cm==int(dual['Cm'])
        value=loss=gain=0; slopes=[0]*Q; mass=[0]*Q
        for (i,j,a),row in zip(terms,fs):
            kind,m,p,r=row
            assert kind in range(4) and 0<=m<=1024 and p>=0 and r>=0
            w1,w2=([0,0] if kind==0 else [1024,0] if kind==1 else [m,0] if kind==2 else [1024-m,m])
            z=INDEX[i,j]
            left=max(lo[z],sum(lo[i:j])); actual_right=min(hi[z],sum(hi[i:j]))
            table_right=max(left+1,actual_right)
            base=sum(lo[i:j]); total=(1024-w1-w2)*lower(left,table_right)
            derivative=0
            for weight,anchor in [(w1,p),(w2,r)]:
                word,valid_l,valid_u=points.get(anchor,(0,0,0))
                if weight:
                    assert valid_u>0 and valid_l<=left<=anchor<=actual_right<=valid_u, ('invalid tangent interval',path,i,j,row,left,actual_right,valid_l,valid_u)
                v=word&MASK; sl=(word>>32)&MASK; deriv=word>>64
                total+=weight*v
                derivative+=weight*sl
                loss+=a*weight*sub(2000000000,deriv)*sub(anchor,base)
                gain+=a*weight*sub(deriv,2000000000)*sub(anchor,base)
            value+=a*total
            for k in range(i,j): slopes[k]+=a*derivative; mass[k]+=a*(w1+w2)
        penalty=sum(sub(hi[k],lo[k])*sub(2000000000*mass[k]+positive[k],1024000000000*bs[k]+slopes[k]+negative[k]) for k in range(Q))
        numerator=10240000000000*sum(bs[k]*lo[k] for k in range(Q))+SC*value+10*(gain+cm)-10*(loss+cp+penalty)
        if replacement: assert numerator==int(replacement['after_numerator']), ('wrong packed mcheck numerator',path,numerator)
        else: assert numerator==int(record['floor_numerator'])==int(record['mcheck_numerator']), ('wrong mcheck numerator',path,numerator)
        assert numerator>=TARGET, ('failed local floor',path,numerator-TARGET)
        counts['numeric_leaves']+=1
        if minimum is None or numerator<minimum: minimum=numerator; minimum_path=path

    stack=[('r',root)]
    while stack:
        path,raw_state=stack.pop()
        state,cuts=normalize_ordered(raw_state) if ordered else (raw_state,[])
        if path in branches:
            row=branches[path]; used_branches.add(path)
            if 'normalize_cuts' in row: assert row['normalize_cuts']==cuts
            axis=row['axis']; cut=row['cut']
            assert 0<=axis<45 and state[0][axis]<cut<state[1][axis], ('bad split',path)
            for upper,bit in [(False,'1'),(True,'0')]:
                next_state=raw_child(state,axis,cut,upper) if ordered else child(state,axis,cut,upper)
                if next_state is None: counts['empty_children']+=1
                else: stack.append((path+bit,next_state))
        elif path in leaves:
            row=leaves[path]
            if 'normalize_cuts' in row: assert row['normalize_cuts']==cuts
            used_leaves.add(path); verify_leaf(path,state,row['result'])
        elif path in frontier:
            row=frontier[path]; assert row['state']==raw_state, ('frontier cell mismatch',path)
            used_frontier.add(path)
        else: raise AssertionError(('unrecorded nonempty child',path))
    assert used_branches==set(branches), ('unreachable branches',set(branches)-used_branches)
    assert used_leaves==set(leaves), ('unreachable accepted leaves',set(leaves)-used_leaves)
    assert set(packed)<=used_leaves, ('packed references missing raw leaves',set(packed)-used_leaves)
    assert set(packed_empty)<=used_leaves, ('packed empty references missing raw leaves',set(packed_empty)-used_leaves)
    assert counts['independently_decoded_relative_leaves']==len(packed)
    for row in inputs:
        row['unchanged_after_audit']=sha(Path(row['path']).read_bytes())==row['sha256']
    for row in packed_inputs:
        row['unchanged_after_audit']=sha(Path(row['path']).read_bytes())==row['sha256']
    result={
        'scope':__doc__, 'passed':True, 'seconds':time.monotonic()-started,
        'inputs':inputs,'packed_inputs':packed_inputs,'source_sha256':sha(raw_source),'parameter_sha256':sha(raw_parameter),
        'script_sha256':sha(Path(__file__).read_bytes()),
        'root_reconstructed':True,'all_partition_edges_replayed':True,
        'branches':len(used_branches),'numeric_leaves':counts['numeric_leaves'],
        'reflection_leaves':counts['reflection_leaves'],'empty_children':counts['empty_children'],
        'ordered_normalization':ordered,'normalized_empty_leaves':counts['normalized_empty_leaves'],
        'independently_decoded_relative_leaves':counts['independently_decoded_relative_leaves'],
        'independently_checked_packed_empty_leaves':len(packed_empty),
        'unresolved_frontier':len(used_frontier),'complete_finite_partition':not used_frontier,
        'minimum_integer_margin':str(minimum-TARGET) if minimum is not None else None,
        'minimum_path':minimum_path,
        'lean_complete_certificate_proven':False,'higher_kappa_proven':False,
    }
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:result[k] for k in ['passed','seconds','branches','numeric_leaves','reflection_leaves','empty_children','unresolved_frontier','complete_finite_partition','minimum_integer_margin']}))

if __name__=='__main__': main()
