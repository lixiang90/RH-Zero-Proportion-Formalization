"""Stdlib-only scalar adapter for legacy compact certificate decoders.

Legacy verifiers share window_global_cover's exact scalar support routines,
whose module also imports unused optimization libraries.  This adapter
supplies only the two rational routines and literal ledger constants needed
by the decoder, so an independent replay can run under python -S.  Canonical
proof-unit SHA checks still require every reconstructed value to match.
It installs only in the verifier process and never edits a source module.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import json,sys,types
import window_interval_kernel as ik
SC=32768;DS=10**15;D=10**10;STEP=64;CORE=6881;TMAX=1<<24
ceil=lambda x:-((-x.numerator)//x.denominator)
floor=lambda x:x.numerator//x.denominator


@lru_cache(None)
def support(p):
    n=round(F(p,SC));assert 1<=n<=16 and n*SC-CORE<=p<=n*SC+CORE
    v,d=ik.w_jet(F(p,SC),1);lower,upper=n*SC-CORE,n*SC+CORE
    if d.u<=0 and v.u+d.u*F(upper-p,SC)<=0:upper=TMAX
    if d.l>=0 and v.u+d.l*F(lower-p,SC)<=0:lower=0
    vl=floor(v.l*10**10);dl=floor(d.l*10**9);du=ceil(d.u*10**9)
    assert vl>=0 and du>=dl;return lower,upper,vl,dl,du-dl


@lru_cache(None)
def constant_lower(l,u):
    if u-l>=SC:return 0
    p=round(F(l+u,2*STEP))*STEP;k,d=ik.kernel_jet(F(p,SC),1)
    radius=F(max(abs(l-p),abs(u-p)),SC);error=max(abs(d.l),abs(d.u))*radius+2*radius*radius
    kl,ku=k.l-error,k.u+error;value=min(abs(kl),abs(ku))**2 if kl*ku>0 else F(0)
    return floor(value*10**10)


def install():
    assert 'window_global_cover' not in sys.modules,'install the scalar adapter before importing legacy verifiers'
    params=json.loads(ik.PARAM.read_bytes());pairs=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
    g=types.SimpleNamespace(SC=SC,D=D,LD=10**12,WD=SC*D,DEN=SC*D*10**12,
      BS=params['b_numerators'],TERMS=[tuple(r) for r in params['a_upper'] if r[2]],ALL=pairs,LOOK={p:i for i,p in enumerate(pairs)},SEP=123*SC//128)
    g.TARGET=11*(g.DEN//1250)
    module=types.ModuleType('window_global_cover');module.__file__=str(Path(__file__).resolve())
    module.g=g;module.PARAM=ik.PARAM;module.P=params;module.ik=ik;module.SC=SC;module.STEP=STEP;module.CORE=CORE;module.TMAX=TMAX
    module.original_support=support;module.constant_lower=constant_lower
    sys.modules['window_global_cover']=module
    return module
