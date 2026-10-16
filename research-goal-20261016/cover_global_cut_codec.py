"""Lossless reconstruction of global-move hull steps from scalar data/forests.

Derived cell bounds, affine coefficients, energy minorants and flow amounts
are rebuilt before the existing independent mathematical checkers run.
Canonical per-step hashes check exact recovery; this codec proves no floor.
"""
from fractions import Fraction as F
import cover_compact_codec as c
from cover_correlated_replay import SC,DS,a
from cover_contractor_verify import close

def assemble(row,params,mixed=False):
    terms=[r for r in params['a_upper'] if r[2]];D=params['denominator'];LD=10**12 if mixed else D
    C=2*SC*DS*(LD//D)*sum(b*d for b,d in zip(params['b_numerators'],row['delta']));E=0;coeff=[0]*9
    if mixed:data=[(t,int(P),int(weight),int(m0),int(m1),int(err)) for t,P,weight,m0,m1,err in row['difference_upper_mixture']]
    else:data=[(t,int(P),terms[t][2],int(m0),int(m1),int(err)) for t,P,m0,m1,err in row['scalar_difference_data']]
    for t,P,weight,m0,m1,err in data:
        i,j,aw=terms[t];C+=weight*(2*SC*m0-m1*P);E+=2*SC*weight*err
        for r in range(i,j):coeff[r]+=2*weight*m1
    return C,E,coeff

def pack_step(step):
    mixed='models' not in step
    rows=[]
    for row in step['certificates']:
        upper=row['move_models'] if mixed else row['move_multipliers']
        rows.append([row['axis'],row['sign'],row['multiplier_denominator'],row['energy_multiplier'],upper,
          c.pack_minorant(row['energy_minorant']) if row['energy_minorant'] else None,c.pack_flow(row['flow'])])
    packed={'kind':'mixed' if mixed else 'single','bounds':rows,'semantics':step['semantics'],'sha256':c.digest(step)}
    if not mixed:packed['models']=step['models']
    return packed

def unpack_step(state,packed,target,params,w):
    mixed=packed['kind']=='mixed';assert mixed or packed['kind']=='single'
    state=[list(state[0]),list(state[1])];lower=state[0].copy();upper=state[1].copy();certs=[]
    den=2*SC*(10**12 if mixed else params['denominator'])*DS;ratio=den//w.g.DEN;assert ratio*w.g.DEN==den
    if not mixed:models=[assemble(row,params) for row in packed['models']]
    for z,sign,K,p,upper_data,energy_data,edges in packed['bounds']:
        energy=c.unpack_minorant(state,energy_data,w) if energy_data else None
        assert bool(p)==bool(energy)
        EC=int(energy['intercept']) if energy else 0;ecoeff=list(map(int,energy['gap_coefficients'])) if energy else [0]*9
        C=p*SC*ratio*EC;coeff=[p*SC*ratio*e+(sign*K*den if k==z else 0) for k,e in enumerate(ecoeff)]
        active=[(row['multiplier'],assemble(row,params,True)) for row in upper_data] if mixed else list(zip(upper_data,models))
        for gamma,(MC,ME,mc) in active:
            C-=SC*gamma*(MC+ME)
            for r in range(9):coeff[r]-=SC*gamma*mc[r]
        flow=c.unpack_flow(edges,coeff,state);minimum=C-int(flow['cost'])
        bound=F(minimum-p*SC*ratio*target,K*den) if sign==1 else F(p*SC*ratio*target-minimum,K*den)
        lo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        hi=min(upper[z],c.ceil(bound)) if sign==-1 else upper[z];lower[z]=lo;upper[z]=hi
        row={'axis':z,'sign':sign,'multiplier_denominator':K,'energy_multiplier':p,'energy_minorant':energy,
          'constant':str(C),'coefficient':list(map(str,coeff)),'minimum_numerator':str(minimum),'flow':flow,
          'bound':str(bound),'new_lower':lo,'new_upper':hi}
        row['move_models' if mixed else 'move_multipliers']=upper_data;certs.append(row)
    step={'old_cell':state,'new_cell':close([lower,upper]),'certificates':certs,'semantics':packed['semantics']}
    if not mixed:step['models']=packed['models']
    return c.checked(step,packed['sha256'])
