"""Stdlib-only exact audit of phase interval/payments and Gaussian PSD cut data.

This checks validity of finite constraint ingredients, not a final Farkas
certificate or a PSD-feasible primal.  Numerical LP/eigenvalue conclusions
remain hints and no global cover is asserted.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import argparse,gzip,hashlib,json,time
import window_interval_kernel as ik
HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768
PAIRS=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
sha=lambda b:hashlib.sha256(b).hexdigest()


@lru_cache(None)
def endpoint(q):
    q=F(q);q-=2*((q+1)//2)
    if q in [-1,0,1]:return F(0),F(0)
    if q==F(1,2):return F(1),F(1)
    if q==F(-1,2):return F(-1),F(-1)
    v=ik.interval.sin_interval(ik.PI*q);return max(F(-1),v.l),min(F(1),v.u)


def interval(l,u):
    if u-l>=2:return F(-1),F(1)
    ll,uu=endpoint(l),endpoint(u);lower=min(ll[0],uu[0]);upper=max(ll[1],uu[1]);f=l-F(1,2);h=u-F(1,2)
    first=-((-f).numerator//f.denominator);last=h.numerator//h.denominator
    for k in range(first,last+1):
        if k%2:lower=F(-1)
        else:upper=F(1)
    return lower,upper


def cut_coefficients(cut):
    values=cut['vector_gaussian_integers'];assert len(values)==(10 if cut['matrix'][0]=='layer' else 3)
    assert all(len(v)==2 and all(isinstance(x,int) for x in v) for v in values)
    constant=sum(a*a+b*b for a,b in values);assert constant>0 and constant==int(cut['constant']);coeff={}
    def product(i,j):
        a,b=values[i];c,d=values[j];return a*c+b*d,a*d-b*c
    def insert(layer,z,re,im):
        for i,c in [(layer*90+2*z,2*re),(layer*90+2*z+1,-2*im)]:coeff[i]=coeff.get(i,0)+c
    kind=cut['matrix']
    if kind[0]=='layer':
        assert kind[1] in [0,1]
        for z,(i,j) in enumerate(PAIRS):insert(kind[1],z,*product(i,j))
    else:
        assert kind[0]=='edge_Toeplitz' and 0<=kind[1]<45;z=kind[1];a,b=product(0,1);c,d=product(1,2)
        insert(0,z,a+c,b+d);insert(1,z,*product(0,2))
    assert [[i,str(c)] for i,c in sorted(coeff.items()) if c]==cut['phase_coefficients']
    return constant,coeff


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();start=time.monotonic()
    archive_raw=args.input.read_bytes();raw=gzip.decompress(archive_raw) if args.input.suffix=='.gz' else archive_raw
    doc=json.loads(raw);packetraw=(ROOT/doc['receipt']['packet_path']).read_bytes();assert sha(packetraw)==doc['receipt']['packet_sha256'];packet=json.loads(packetraw)
    source_raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();assert sha(source_raw)==doc['receipt']['parent64_input_sha256'];source=json.loads(gzip.decompress(source_raw));cases={r['path']:r for r in source['cases']}
    params=json.loads(ik.PARAM.read_bytes());assert sha(ik.PARAM.read_bytes())==packet['parameters_sha256'];terms=[r for r in params['a_upper'] if r[2]];pcases={r['path']:r for r in packet['cases']}
    cut_count=arc_count=payment_count=0;violations=[]
    for result in doc['rows']:
        path=result['path'];state=cases[path]['before'];case=pcases[path];assert case['cell']==state;arc={}
        for row in result['phase_arc_bounds']:
            layer,z,part=row['layer'],row['axis'],row['part'];assert layer in [0,1] and 0<=z<45 and part in [0,1]
            l=F(state[0][z]*(layer+1),SC);u=F(state[1][z]*(layer+1),SC);shift=F(1,2) if part==0 else F(0)
            wanted=interval(l+shift,u+shift);assert wanted==(F(row['lower']),F(row['upper']));arc[layer,z,part]=wanted;arc_count+=1
        assert len(arc)==180
        for t,(term,stored) in enumerate(zip(case['terms'],result['coefficient_payments'])):
            i,j,aw=terms[t];assert term['t']==stored['term']==t and term['i']==i and term['j']==j;z=PAIRS.index((i,j))
            reference=list(map(F,term['reference']));lower=list(map(F,term['lower']));upper=list(map(F,term['upper']));errors=[max(r-l,u-r) for l,r,u in zip(lower,reference,upper)]
            absolute=[F(1)]+[max(map(abs,arc[layer,z,part])) for layer,part in [(0,0),(0,1),(1,0),(1,1)]]
            assert reference==list(map(F,stored['reference'])) and errors==list(map(F,stored['component_errors'])) and absolute==list(map(F,stored['phase_absolute_bounds']))
            assert sum(e*a for e,a in zip(errors,absolute))==F(stored['total_payment']);payment_count+=1
        phase=result['final_primal']['phase_layer_pair_real_imag'] if result['final_primal'] else None
        point=[F(str(x)) for layer in phase for pair in layer for x in pair] if phase else None
        for cut in result['rational_rank_one_cuts']:
            constant,coeff=cut_coefficients(cut);cut_count+=1
            if point:violations.append(F(constant+sum(c*point[i] for i,c in coeff.items()),constant))
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'input_archive_sha256':sha(archive_raw),
      'input_path':args.input.resolve().relative_to(ROOT).as_posix(),'all_constraint_ingredient_checks_passed':True,
      'rational_phase_interval_rows':arc_count,'rational_uniform_payments':payment_count,'exact_Gaussian_integer_cut_expansions':cut_count,
      'minimum_final_primal_cut_value_as_exact_decimal_interpretation':str(min(violations)) if violations else None,
      'final_primal_PSD_verified':False,'final_Farkas_certificate_verified':False,'uniform_packet_Lean_proven':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
