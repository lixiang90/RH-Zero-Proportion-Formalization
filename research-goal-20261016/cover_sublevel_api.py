"""Stable target-explicit sublevel hull contraction API.

contract(state, minorant, target, axes=None) accepts an integer energy
minorant in the frozen new-window scale and an explicit target numerator.
Only the LP-selected nonnegative multipliers are used from floating point;
all returned bounds are exact graph-flow inequalities on F<target/DEN.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import numpy as np
from scipy.optimize import linprog
import cover_sublevel_contractor as prototype

g=prototype.g;K=2**20

def ceil(x):return -((-x.numerator)//x.denominator)

def contract(state,minorant,target,axes=None):
    target=int(target);C=int(minorant['intercept']);coeff=list(map(int,minorant['gap_coefficients']))
    cl=g.close(*state);assert cl is not None and cl[:2]==state
    rows=[];rhs=[]
    for z,(i,j) in enumerate(g.ALL):
        row=np.zeros(9);row[i:j]=1;rows.extend([row,-row]);rhs.extend([state[1][z]/g.SC,-state[0][z]/g.SC])
    rows.append(np.array(coeff,dtype=float)*g.SC/g.DEN);rhs.append((target-C)/g.DEN)
    lower=state[0].copy();upper=state[1].copy();certificates=[]
    if axes is None:axes=list(range(9))
    for z in axes:
        i,j=g.ALL[z]
        for sign in [1,-1]:
            objective=np.zeros(9);objective[i:j]=sign
            lp=linprog(objective,A_ub=rows,b_ub=rhs,bounds=[(None,None)]*9,method='highs')
            if not lp.success:continue
            multiplier=max(0.,-float(lp.ineqlin.marginals[-1]));p=round(multiplier*K)
            if p<=0:continue
            combined=[p*g.SC*c+(sign*K*g.DEN if i<=r<j else 0) for r,c in enumerate(coeff)]
            value,flow=g.minimize(p*g.SC*C,combined,cl[2])
            bound=F(value-p*g.SC*target,K*g.DEN) if sign==1 else F(p*g.SC*target-value,K*g.DEN)
            newlo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
            newhi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
            if newlo>lower[z] or newhi<upper[z]:
                lower[z]=newlo;upper[z]=newhi
                certificates.append({'axis':z,'sign':sign,'multiplier_numerator':p,'multiplier_denominator':K,
                  'flow':flow,'minimum_numerator':str(value),'bound':str(bound),'new_lower':newlo,'new_upper':newhi})
    if not certificates:return state,[]
    closed=g.close(lower,upper)
    return (None if closed is None else closed[:2]),certificates

def source_hashes():
    return {'sublevel_api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'prototype_sha256':hashlib.sha256(Path(prototype.__file__).read_bytes()).hexdigest(),
      'parameter_sha256':hashlib.sha256(prototype.w.PARAM.read_bytes()).hexdigest(),
      'coordinate_scale':g.SC,'energy_denominator':str(g.DEN),'multiplier_denominator':K,
      'semantics':'F < explicit target / energy_denominator'}
