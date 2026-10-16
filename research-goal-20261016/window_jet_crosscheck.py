"""High-precision diagnostic cross-check, explicitly not interval verification.

Compares the new rational jet oracle against independent mpmath analytic
differentiation of shifted sinc functions, including removable poles.
The rigorous numerical evidence remains the Fraction interval certificates.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import mpmath as mp
import window_interval_kernel as ik

mp.mp.dps=100
def mf(x):return mp.mpf(x.numerator)/x.denominator
theta=mp.sqrt(2)/2
z=mp.sin(theta)/theta
def sinc(x):return mp.sinc(mp.pi*x)
def amp(x):
    a=theta/mp.pi
    val=sinc(x+a)+sinc(x-a)
    for j,c in enumerate(ik.COEFF[1:],1):val+=mf(c)*(sinc(x+j)+sinc(x-j))
    return val/(2*z)

def main():
    start=time.monotonic();rows=[]
    points=[F(0),F(123,128),F(1),F(32767,32768),F(32769,32768),F(5),F(24),F(107,16),F(16)+F(21,100)]
    for x in points:
        jets=ik.kernel_jet(x,4);values=[]
        for r,v in enumerate(jets):
            direct=mp.diff(amp,mf(x),r)
            # Conversion is only a numerical diagnostic; this boolean is never
            # used as evidence for a Lean or rational-interval theorem.
            contained=mf(v.l)<=direct<=mf(v.u)
            assert contained,(x,r,mp.nstr(direct,80),str(v.l),str(v.u))
            values.append({'order':r,'mpmath_value':mp.nstr(direct,80),'inside_Fraction_enclosure':contained})
        rows.append({'point':str(x),'derivatives':values})
    out={'scope':__doc__,'parameter_sha256':hashlib.sha256(ik.PARAM.read_bytes()).hexdigest(),
         'oracle_sha256':hashlib.sha256(Path(ik.__file__).read_bytes()).hexdigest(),
         'crosscheck_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
         'precision_decimal_digits':mp.mp.dps,'rows':rows,'all_diagnostics_passed':True,
         'Lean_proven':False,'seconds':time.monotonic()-start}
    target=Path(__file__).with_suffix('.json');target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['all_diagnostics_passed','precision_decimal_digits','seconds']}))
if __name__=='__main__':main()
