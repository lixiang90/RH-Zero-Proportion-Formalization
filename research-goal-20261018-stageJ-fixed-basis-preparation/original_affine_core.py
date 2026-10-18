"""General original-cell affine extraction, text-adapted from frozen I.
Only the terminal expected-payload-length lookup is generalized to the same
original B witness; formulas/guards/semantics remain the I point-free body.
No functions run at import. Original locator is supplied only after gate.
"""
from fractions import Fraction as F
from hashlib import sha256
import json
Q=32768
R=1024
D=10**9
V=10**10
SA=10**20
KAPPA=Q*V*R
K=KAPPA*SA
CN=893616123055294719
TAU_N=893916123055294719
ORIGINAL_LOCATOR=None
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'
def locate_original_payload(cell,model,math,traces):
    assert ORIGINAL_LOCATOR is not None
    return ORIGINAL_LOCATOR(cell,model,math,traces)

def extract_original_affine(cell,model,math,traces):
    """No physical test point, offset, chart or joint tightening is an input."""
    state,word=locate_original_payload(cell,model,math,traces);lo,hi=state
    cid=cell['exception_id'];fs=[];terms=[];o=0
    jcoef=[D*R*b for b in model['BS']];cstar=0;constant=F(0)
    coefficients=[F(b,SA) for b in model['BS']]
    weighted_mv=weighted_cp=weighted_cn=0
    for ti,(i,j,a,_slot) in enumerate(model['TS']):
        L,U=math.term_bounds(state,i,j);L0=sum(lo[i:j]);uc=max(L+1,U)
        assert L0<=L<=U
        f,o=math.dec(word,o,L,U);kind,lam,p,r=f;fs.append(f)
        l1,l2=math.weights(kind,lam);lc=R-l1-l2
        assert min(l1,l2,lc)>=0 and lc+l1+l2==R
        pt=[model['PTraw'].get(v,0)&((1<<96)-1) for v in [p,r]];guards=[]
        for amount,anchor in zip([l1,l2],[p,r]):
            if not amount:continue
            assert anchor in model['PTraw'];raw=model['PTraw'][anchor]
            vl=max(0,anchor-((raw>>96)&((1<<20)-1)));vu=anchor+(raw>>116)
            assert 1<=vu and vl<=L<=anchor<=U<=vu
            guards.append({'mass':amount,'original_anchor':anchor,'valid_lower':vl,'valid_upper':vu,'guard_passed':True})
        lb=math.lb(L,uc)
        mv=lc*lb+l1*(pt[0]&math.MASK32)+l2*(pt[1]&math.MASK32)
        msl=l1*((pt[0]>>32)&math.MASK32)+l2*((pt[1]>>32)&math.MASK32);mass=l1+l2
        cp=sum(amount*max(0,(raw>>64)-2*D)*max(0,anchor-L0) for amount,raw,anchor in zip([l1,l2],pt,[p,r]))
        cn=sum(amount*max(0,2*D-(raw>>64))*max(0,anchor-L0) for amount,raw,anchor in zip([l1,l2],pt,[p,r]))
        delta=msl-2*D*mass;sigma=F(delta,D*R)
        beta=F(mv,V*R)+F(cp-cn,Q*D*R)-sigma*F(L0,Q)
        cstar+=a*(Q*mv+10*(cp-cn-delta*L0));constant+=F(a,SA)*beta
        for rr in range(i,j):jcoef[rr]+=a*delta;coefficients[rr]+=F(a,SA)*sigma
        weighted_mv+=a*mv;weighted_cp+=a*cp;weighted_cn+=a*cn
        terms.append({'term_id':ti,'edge':[i,j],'external_weight_numerator':a,'external_weight_denominator':SA,
            'original_term_bounds':[L,U],'uc_upper':uc,'original_L0':L0,'FS':list(f),
            'mass_constant':lc,'mass_first':l1,'mass_second':l2,'original_lb_table_value':lb,
            'active_mokI_guards':guards,'mvT':mv,'mslT':msl,'mwT':mass,'mcpT':cp,'mcnT':cn,
            'signed_delta':delta,'beta':str(beta),'sigma':str(sigma)})
    P,S,Cp,Cm,consumed=math.ydec(word,o,state)
    semantic={'FS':fs,'P':P,'S':S,'Cp':Cp,'Cm':Cm,'consumed_bits':consumed}
    payload={'bits':consumed,'value':str(word&((1<<consumed)-1))}
    assert sha256(canonical(semantic)).hexdigest()==cell['witness']['decoded_semantic_sha256']
    assert sha256(canonical(payload)).hexdigest()==cell['witness']['packed_payload_sha256']
    compact,readbits=math.calc(state,word);printed=math.direct_mcheck_margin(state,word)
    assert compact==printed==int(cell['original_margin']) and compact>=0
    assert readbits==consumed==cell['end']-cell['position']-2==cell['witness']['consumed_payload_bits']
    assert compact-KAPPA*(TAU_N-CN)==int(cell['tau_margin'])
    assert K*constant==cstar and coefficients==[F(v,D*R*SA) for v in jcoef]
    penalty=sum((hi[rr]-lo[rr])*max(0,P[rr]-S[rr]-jcoef[rr]) for rr in range(8))
    certified_num=V*R*sum(b*lo[rr] for rr,b in enumerate(model['BS']))
    certified_num+=Q*weighted_mv+10*(weighted_cp-weighted_cn+Cm-Cp-penalty)
    assert certified_num-KAPPA*CN==compact
    result={'cell_id':cid,'original_root':cell['root'],'original_path':cell['path'],
        'position':cell['position'],'end':cell['end'],'state_sha256':cell['state_sha256'],'witness':cell['witness'],
        'canonical_Cstar':str(cstar),'canonical_J':list(map(str,jcoef)),
        'canonical_affine_constant':str(constant),'canonical_gap_coefficients':list(map(str,coefficients)),
        'terms':terms,'original_compact_margin':str(compact),'original_printed_AST_margin':str(printed),
        'consumed_payload_bits':consumed,'original_flow':{'P':P,'S':S,'Cp':Cp,'Cm':Cm,
            'box_penalty':str(penalty),'certified_numerator':str(certified_num),'certified_denominator':str(K)},
        'point_free_extraction':True,'original_guard_state_and_cursor_unchanged':True}
    return result,state

