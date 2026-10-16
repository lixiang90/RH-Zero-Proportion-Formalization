"""Lossless structural encoding of OBBT/Newton/value/gradient witnesses.

No optimizer is used by the decoder. Cell bounds, scalar-line coefficients,
all affine aggregates and outward rounded bounds are recomputed. A flow
stores only its directed forest, and balance determines every amount.
Each decoded proof unit must match its recorded canonical SHA256. This is
an encoding layer; the existing independent mathematical verifiers must
still check every decoded unit. No mathematical obligation is removed.
"""
from fractions import Fraction as F
import hashlib,json
from cover_correlated_replay import SC,DS,a
from cover_contractor_verify import close
from cover_flow_basis import decode

def digest(value):return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def ceil(x):return -((-x.numerator)//x.denominator)
def checked(value,sha):
    assert digest(value)==sha,'decoded proof unit differs from original'
    return value

def pack_flow(flow):
    edges=[row[:2] for row in flow['nonzero_flow']]
    assert decode(flow['divergence'],edges)==[int(row[2]) for row in flow['nonzero_flow']]
    assert sum(int(row[2])*row[3] for row in flow['nonzero_flow'])==int(flow['cost'])
    return [10*i+j for i,j in edges]

def unpack_flow(codes,coeff,state):
    assert len(coeff)==9 and all(isinstance(k,int) and 0<=k<100 for k in codes)
    desired=[-coeff[0]]+[coeff[k-1]-coeff[k] for k in range(1,9)]+[coeff[-1]]
    edges=[divmod(k,10) for k in codes];amounts=decode(desired,edges)
    rows=[[i,j,str(y),a.edge_value(state,i,j)] for (i,j),y in zip(edges,amounts)]
    return {'divergence':list(map(str,desired)),'nonzero_flow':rows,'cost':str(sum(int(y)*u for i,j,y,u in rows))}

def pack_minorant(cert):
    return [[[t,p,weight] for t,p,weight,C,slope in cert['mixture']],pack_flow(cert['flow'])]

def unpack_minorant(state,packed,w):
    g=w.g;mixture=[];C=0;coeff=[b*g.LD for b in g.BS]
    for t,p,weight0 in packed[0]:
        weight=int(weight0);assert weight>0 and 0<=t<len(g.TERMS)
        i,j,aw=g.TERMS[t];z=a.INDEX[i,j];l,u=state[0][z],state[1][z]
        if p==-1:const=w.constant_lower(l,u)*g.SC;slope=0
        else:
            assert p>=0;pl,pu,v,sl,err=w.original_support(p)
            assert pl<=l and u<=pu
            const=g.SC*v-10*sl*p-10*err*max(p-l,0);slope=10*sl
        mixture.append([t,p,str(weight),str(const),str(slope)]);C+=weight*const
        for k in range(i,j):coeff[k]+=weight*slope
    return {'lower_bounds':list(state[0]),'upper_bounds':list(state[1]),'mixture_denominator':g.LD,
      'mixture':mixture,'intercept':str(C),'gap_coefficients':list(map(str,coeff)),'flow':unpack_flow(packed[1],coeff,state)}

def pack_obbt(step):
    return {'b':[[c['axis'],c['sign'],c['multiplier_numerator'],c['multiplier_denominator'],
      pack_minorant(c['minorant']),pack_flow(c['flow'])] for c in step['certificates']],'sha256':digest(step)}

def unpack_obbt(state,packed,target,w):
    g=w.g;lower=list(state[0]);upper=list(state[1]);certs=[]
    for z,sign,p,K,minorant0,edges in packed['b']:
        assert 0<=z<45 and sign in [-1,1] and p>0 and K>0
        cert=unpack_minorant(state,minorant0,w);C=int(cert['intercept']);coeff=list(map(int,cert['gap_coefficients']));i,j=a.PAIRS[z]
        combined=[p*SC*c+(sign*K*g.DEN if i<=k<j else 0) for k,c in enumerate(coeff)]
        flow=unpack_flow(edges,combined,state);value=p*SC*C-int(flow['cost'])
        bound=F(value-p*SC*target,K*g.DEN) if sign==1 else F(p*SC*target-value,K*g.DEN)
        lo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        hi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
        lower[z]=lo;upper[z]=hi
        certs.append({'axis':z,'sign':sign,'multiplier_numerator':p,'multiplier_denominator':K,
          'flow':flow,'minimum_numerator':str(value),'bound':str(bound),'new_lower':lo,'new_upper':hi,'minorant':cert})
    result={'old_cell':[list(state[0]),list(state[1])],'new_cell':close([lower,upper]),'certificates':certs}
    return checked(result,packed['sha256'])

def pack_affine(data):return [[m0,m1,err,int(kind=='affine')] for P,m0,m1,err,kind in data]
def unpack_affine(state,packed,terms):
    assert len(packed)==len(terms)
    return [[state[0][a.INDEX[i,j]]+state[1][a.INDEX[i,j]],str(m0),str(m1),str(err),'affine' if kind else 'interval']
      for (i,j,aw),(m0,m1,err,kind) in zip(terms,packed)]

def derivative_affine(data,d,w):
    C=2*SC*sum(b*DS*v for b,v in zip(w.g.BS,d));E=0;coeff=[0]*9
    for (i,j,aw),(P,m0,m1,err,kind) in zip(w.g.TERMS,data):
        m0,m1,err=map(int,[m0,m1,err]);s=sum(d[i:j]);C+=aw*s*(2*SC*m0-m1*P);E+=2*SC*aw*abs(s)*err
        for k in range(i,j):coeff[k]+=2*aw*s*m1
    return C,E,coeff

def pack_newton(step):
    rows=step['certificates'];assert rows
    data=rows[0]['scalar_affine_data'];assert all(row['scalar_affine_data']==data for row in rows)
    return {'a':pack_affine(data),'c':[[r['coordinate'],r['direction'],pack_flow(r['minimum_flow']),pack_flow(r['maximum_flow'])] for r in rows],
      'sha256':digest(step)}

def unpack_newton(state,packed,w):
    data=unpack_affine(state,packed['a'],w.g.TERMS);lower=list(state[0]);upper=list(state[1]);certs=[]
    for i,d,minedges,maxedges in packed['c']:
        C,E,coeff=derivative_affine(data,d,w);tau=coeff[i];assert tau>0
        other=coeff.copy();other[i]=0
        minflow=unpack_flow(minedges,other,state);maxflow=unpack_flow(maxedges,[-v for v in other],state)
        minimum=-int(minflow['cost']);maximum=int(maxflow['cost'])
        lo=F(-E-C-maximum,tau);hi=F(E-C-minimum,tau)
        newlo=max(state[0][i],lo.numerator//lo.denominator);newhi=min(state[1][i],ceil(hi));lower[i]=newlo;upper[i]=newhi
        certs.append({'coordinate':i,'direction':d,'constant':str(C),'error':str(E),'coefficient':list(map(str,coeff)),
          'other_minimum':str(minimum),'other_maximum':str(maximum),'minimum_flow':minflow,'maximum_flow':maxflow,
          'lower_rational':str(lo),'upper_rational':str(hi),'new_lower':newlo,'new_upper':newhi,'scalar_affine_data':data})
    result={'old_cell':[list(state[0]),list(state[1])],'new_cell':close([lower,upper]),'certificates':certs}
    return checked(result,packed['sha256'])

def pack_leaf(row):
    result=row.get('result');kind=row['kind'];out={k:v for k,v in row.items() if k!='result'}
    if kind=='value':
        out['packed_value']={k:v for k,v in result.items() if k not in ['certificate','floor_numerator']}
        out['packed_minorant']=pack_minorant(result['certificate']);out['sha256']=digest(row)
    elif kind=='stationary' and 'scalar_affine_data' in result:
        derived=['scalar_affine_data','exact_flow','upper_numerator','denominator']
        out['packed_direction']={k:v for k,v in result.items() if k not in derived}
        out['a']=pack_affine(result['scalar_affine_data']);out['edges']=pack_flow(result['exact_flow']['flow']);out['sha256']=digest(row)
    else:return row
    return out

def unpack_leaf(state,packed,w):
    if 'packed_value' in packed:
        cert=unpack_minorant(state,packed['packed_minorant'],w)
        result={**packed['packed_value'],'floor_numerator':str(int(cert['intercept'])-int(cert['flow']['cost'])),'certificate':cert}
        row={k:v for k,v in packed.items() if k not in ['packed_value','packed_minorant','sha256']};row['result']=result
    elif 'packed_direction' in packed:
        result=packed['packed_direction'].copy();data=unpack_affine(state,packed['a'],w.g.TERMS)
        C,E,coeff=derivative_affine(data,result['direction'],w);flow=unpack_flow(packed['edges'],[-v for v in coeff],state)
        result.update(upper_numerator=str(C+E+int(flow['cost'])),denominator=str(2*SC*w.g.D*DS),scalar_affine_data=data,
          exact_flow={'constant':str(C),'error':str(E),'coefficient':list(map(str,coeff)),'negative_maximum':str(-int(flow['cost'])),'flow':flow})
        row={k:v for k,v in packed.items() if k not in ['packed_direction','a','edges','sha256']};row['result']=result
    else:return packed
    return checked(row,packed['sha256'])

def pack_document(old):
    data=old.copy();data['format']='RelevantBelow-KKT-OBBT-compact-v2'
    data['accepted']=[pack_leaf(row) for row in old['accepted']]
    data['sublevel_contractions']={p:pack_obbt(row) for p,row in old['sublevel_contractions'].items()}
    data['contractions']={p:[pack_newton(row) for row in rows] for p,rows in old['contractions'].items()}
    return data

def unpack_document(data,w):
    assert data['format']=='RelevantBelow-KKT-OBBT-compact-v2'
    old=data.copy();old['format']='RelevantBelow-KKT-OBBT-v1';obbt={};newton={};leaves={};seen=set()
    branch={r['path']:r for r in data['branches']};accepted={r['path']:r for r in data['accepted']}
    todo=[('r',[list(v) for v in w.root()])]
    while todo:
        p,state=todo.pop();seen.add(p)
        if p in data['sublevel_contractions']:
            obbt[p]=unpack_obbt(state,data['sublevel_contractions'][p],w.g.TARGET,w);state=obbt[p]['new_cell']
        if p in data['contractions']:
            newton[p]=[]
            for row in data['contractions'][p]:
                assert state is not None
                step=unpack_newton(state,row,w);newton[p].append(step);state=step['new_cell']
        if p in accepted:leaves[p]=unpack_leaf(state,accepted[p],w)
        if p in branch:
            assert state is not None;b=branch[p]
            for bit,upper in [('1',False),('0',True)]:
                child=a.child(state,b['axis'],b['cut'],upper)
                if child is not None:todo.append((p+bit,child))
    assert set(obbt)==set(data['sublevel_contractions']) and set(newton)==set(data['contractions']) and set(leaves)==set(accepted)
    old['sublevel_contractions']={p:obbt[p] for p in data['sublevel_contractions']}
    old['contractions']={p:newton[p] for p in data['contractions']}
    old['accepted']=[leaves[r['path']] for r in data['accepted']]
    return old
