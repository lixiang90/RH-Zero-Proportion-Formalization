"""Complete new-window derivative RMQ input from integer-centred Taylor jets.

Only 33 integer-centred order-23 jets are needed for 2048 cells on [0,32].
Interval Horner bounds the degree-22 Taylor polynomial for w'. The order-24
remainder follows from the autocorrelation moment bound |w^24|<=(2*pi)^24,
which remains an explicit Lean analytic obligation. This is not a theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse, hashlib, importlib.util, json, time
import window_interval_kernel as original
spec=importlib.util.spec_from_file_location('independent_new_window_jet',Path(original.__file__))
ik=importlib.util.module_from_spec(spec);spec.loader.exec_module(ik)
I=ik.I

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--step',type=int,default=64);ap.add_argument('--maximum',type=int,default=32)
    ap.add_argument('--order',type=int,default=24);ap.add_argument('--output',type=Path,default=Path(__file__).with_suffix('.json'))
    args=ap.parse_args();start=time.monotonic();tables={};rows=[]
    for n in range(args.maximum+1):
        jets=ik.w_jet(n,args.order-1)
        tables[n]=[jets[j+1]*F(1,factorial(j)) for j in range(args.order-1)]
        print(json.dumps({'center':n,'seconds':time.monotonic()-start}),flush=True)
    remainder=F(44,7)**args.order*F(1,2)**(args.order-1)/factorial(args.order-1)
    for k in range(args.step*args.maximum):
        center=round(F(2*k+1,2*args.step));x=I(F(k,args.step)-center,F(k+1,args.step)-center)
        poly=I(0)
        for c in reversed(tables[center]):poly=poly*x+c
        dl,du=poly.l-remainder,poly.u+remainder;scale=10**15
        lower=dl.numerator*scale//dl.denominator;upper=-((-du.numerator*scale)//du.denominator)
        rows.append([lower,upper])
    receipt={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'jet_helper_sha256':hashlib.sha256(Path(ik.__file__).read_bytes()).hexdigest(),'parameter_sha256':hashlib.sha256(ik.PARAM.read_bytes()).hexdigest(),
      'coefficient_numerators_1e9':[int(c*10**9) for c in ik.COEFF],'grid_step':args.step,'maximum':args.maximum,'cells':len(rows),
      'order':args.order,'denominator':10**15,'global_taylor_derivative_bound':str(F(44,7)**args.order),'remainder':str(remainder),
      'global_derivative_bound_lean_connected':False,'actual_w1_oracle_lean_connected':False,'seconds':time.monotonic()-start}
    out={'receipt':receipt,'ranges':rows,'integer_taylor_coefficients':{str(n):[[str(c.l),str(c.u)] for c in cs] for n,cs in tables.items()}}
    args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
