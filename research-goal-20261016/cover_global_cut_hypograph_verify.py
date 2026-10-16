"""Independent exact coordinate-bound replay for mixed difference hypographs."""
from fractions import Fraction as F
from cover_global_move_epigraph_verify import check_line
from cover_correlated_replay import SC,DS,a,ceil
from cover_contractor_verify import flow_bound,close
import cover_sublevel_verify as energy

def mixed_model(state,row,params,checker):
    terms=[tuple(r) for r in params['a_upper'] if r[2]];delta=row['delta'];bs=params['b_numerators'];D=params['denominator'];LD=row['difference_mixture_denominator']
    assert D==10**10 and LD==10**12
    assert len(delta)==9 and any(delta) and all(isinstance(d,int) for d in delta)
    assert all(state[0][k]+SC*delta[k]>=123*SC//128 for k in range(9))
    affected={t for t,(i,j,aw) in enumerate(terms) if sum(delta[i:j])};mass=[0]*len(terms)
    C=2*SC*DS*(LD//D)*sum(b*d for b,d in zip(bs,delta));E=0;coeff=[0]*9
    for t,P,weight,m0,m1,err in row['difference_upper_mixture']:
        weight=int(weight);assert weight>0 and t in affected;i,j,aw=terms[t];z=a.INDEX[i,j]
        cache=getattr(checker,'verified_noncentral_lines',None)
        if cache is None:cache={};checker.verified_noncentral_lines=cache
        key=(state[0][z],state[1][z],sum(delta[i:j]),int(P),int(m0),int(m1),int(err))
        if key not in cache:cache[key]=check_line(checker,*key[:3],key[3:])
        P,m0,m1,err=cache[key]
        mass[t]+=weight;C+=weight*(2*SC*m0-m1*P);E+=2*SC*weight*err
        for k in range(i,j):coeff[k]+=2*weight*m1
    assert all(mass[t]==(aw*(LD//D) if t in affected else 0) for t,(i,j,aw) in enumerate(terms))
    return C,E,coeff

def verify_step(state,step,target,params,checker):
    state=[list(state[0]),list(state[1])];a.closure_valid(state);assert step['old_cell']==state
    lower=state[0].copy();upper=state[1].copy();seen=set();den=2*SC*10**12*DS;ratio=den//energy.g.DEN;assert ratio*energy.g.DEN==den
    for cert in step['certificates']:
        z=cert['axis'];sign=cert['sign'];K=cert['multiplier_denominator'];p=cert['energy_multiplier']
        assert 0<=z<9 and sign in [-1,1] and (z,sign) not in seen;seen.add((z,sign))
        assert isinstance(K,int) and K>0 and isinstance(p,int) and p>=0
        if p:EC,ecoeff,_=energy.minorant(state,cert['energy_minorant'])
        else:assert cert['energy_minorant'] is None;EC=0;ecoeff=[0]*9
        C=p*SC*ratio*EC;coeff=[p*SC*ratio*e+(sign*K*den if k==z else 0) for k,e in enumerate(ecoeff)]
        for row in cert['move_models']:
            gamma=row['multiplier'];assert isinstance(gamma,int) and gamma>0
            MC,ME,mc=mixed_model(state,row,params,checker);C-=SC*gamma*(MC+ME)
            for r in range(9):coeff[r]-=SC*gamma*mc[r]
        assert C==int(cert['constant']) and coeff==list(map(int,cert['coefficient']))
        minimum=C+flow_bound(state,coeff,cert['flow']);assert minimum==int(cert['minimum_numerator'])
        bound=F(minimum-p*SC*ratio*target,K*den) if sign==1 else F(p*SC*ratio*target-minimum,K*den)
        assert bound==F(cert['bound'])
        lo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        hi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
        assert lo==cert['new_lower'] and hi==cert['new_upper'];lower[z]=lo;upper[z]=hi
    assert seen;refined=close([lower,upper]);assert refined==step['new_cell'];return refined
