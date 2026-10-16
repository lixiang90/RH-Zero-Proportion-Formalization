"""Stdlib-only independent replay of the finite rational Gram evidence.

This deliberately does not import the generator, its hull builder, its
linear solver, NumPy, SciPy, or the exploratory curvature samples. Every
piece uses one directly decoded frozen PT word. A successful replay is
still not a Lean proof or a proof that these chambers cover all gaps.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,ast,hashlib,json,re,time

HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def point_words():
    source=ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean'
    text=source.read_text(encoding='utf8');text=text[text.index('namespace AMW.Cert.PC9QB6M\n'):]
    words={}
    for block,body in re.findall(r'\.lf (\d+) (\[[^\]]*\])',text):
        for offset,v in ast.literal_eval(body):
            p=1024*int(block)+offset
            assert p not in words or words[p]==v
            words[p]=v
    return source,words

def line_of_word(p,word,L,U):
    trip=word&((1<<96)-1);left=max(0,p-((word>>96)&((1<<20)-1)));right=p+(word>>116)
    assert right and left<=L<=U<=right
    value=trip&((1<<32)-1);lo=((trip>>32)&((1<<32)-1))-2000000000
    hi=2000000000-(trip>>64);assert lo<=hi
    slope=F(lo,10**9)
    intercept=F(value,10**10)-slope*F(p,SC)-F((hi-lo)*max(p-L,0),10**9*SC)
    return slope,intercept

def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',nargs='?',default='analytic_gram_minorant.json');
    ap.add_argument('--output',default='analytic_gram_replay.json');args=ap.parse_args()
    start=time.monotonic();path=HERE/args.certificate
    par=ROOT/'research-20261016/spectral-w10-refined-rational.json';source_path=ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean'
    watched=[path,par,source_path,Path(__file__)];initial_hashes={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched}
    source,words=point_words();doc=json.loads(path.read_text())
    param=json.loads(par.read_text());D=param['denominator']
    assert sha(par)==doc['parameter_sha256'];terms=[(i,j,F(a,D)) for i,j,a in param['a_upper'] if a]
    bs=[F(b,D) for b in param['b_numerators']];radius=F(doc.get('chamber_span_radius_exact','21/100'))
    hulls={};pieces=0
    for h in doc['hulls']:
        n=h['integer_center'];lower=F(h['lower']);upper=F(h['upper']);L=h['outward_lower_SC'];U=h['outward_upper_SC']
        assert lower==max(F(17,20),n-radius) and upper==n+radius
        assert F(L,SC)<=lower<=upper<=F(U,SC)
        segments=h['segments'];last=lower
        for row in segments:
            l=F(row['lower']);r=F(row['upper']);assert l==last and l<r;last=r
            slope=F(row['slope']);intercept=F(row['intercept']);p=row['PT_point']
            if p>=0:assert (slope,intercept)==line_of_word(p,words[p],L,U)
            else:
                # All 69 successful certificates use only the zero constant.
                # A nonzero LB constant would require a separate LB replay.
                assert slope==0 and intercept==0
            pieces+=1
        assert last==upper
        hulls[n]=h
    endpoint_checks=0;results=[]
    for row in doc['results']:
        q=[F(v,row['anchor_denominator']) for v in row['anchor_numerators']]
        A=[[F(0) for _ in range(9)] for _ in range(9)];gradient=bs.copy();C=sum(x*b for x,b in zip(q,bs))
        for data,(i,j,a) in zip(row['terms'],terms,strict=True):
            assert data['pair']==[i,j];n=data['center'];h=hulls[n]
            assert n==sum(row['integer_gaps'][i:j]);t0=F(data['anchor']);assert t0==sum(q[i:j])
            assert F(h['lower'])<=t0<=F(h['upper'])
            alpha=F(data['alpha']);s=F(data['line_slope']);b=F(data['line_intercept']);epsilon=F(data['epsilon']);assert alpha>=0 and epsilon>=0
            p=data['PT_point']
            if p>=0:assert (s,b)==line_of_word(p,words[p],h['outward_lower_SC'],h['outward_upper_SC'])
            else:assert s==0 and b==0
            for segment in h['segments']:
                ss=F(segment['slope']);bb=F(segment['intercept'])
                for x in [F(segment['lower']),F(segment['upper'])]:
                    assert alpha*(x-t0)**2+s*x+b-epsilon<=ss*x+bb
                    endpoint_checks+=1
            C+=a*(s*t0+b-epsilon)
            for r in range(i,j):
                gradient[r]+=a*s
                for rr in range(i,j):A[r][rr]+=a*alpha
        declared=[[F(v) for v in r] for r in row['matrix_A']];assert A==declared
        assert gradient==list(map(F,row['gradient'])) and C==F(row['quadratic_center_value_exact'])
        L=[[F(v) for v in r] for r in row['LDL_unit_lower']];diag=list(map(F,row['LDL_positive_diagonal']))
        assert len(L)==len(diag)==9 and all(len(r)==9 for r in L) and all(v>0 for v in diag)
        assert all(L[i][i]==1 for i in range(9)) and all(L[i][j]==0 for i in range(9) for j in range(i+1,9))
        assert all(A[i][j]==sum(L[i][k]*diag[k]*L[j][k] for k in range(9)) for i in range(9) for j in range(9))
        z=list(map(F,row['A_inverse_gradient']));assert len(z)==9
        assert all(sum(A[i][j]*z[j] for j in range(9))==gradient[i] for i in range(9))
        lower=C-sum(x*y for x,y in zip(gradient,z))/4
        assert lower==F(row['Gram_lower_bound_exact'])
        assert row['passes_candidate_floor_exact']==(lower>=F(433,50000))
        results.append(lower)
    final_hashes={str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in watched};assert final_hashes==initial_hashes
    outcome={'scope':__doc__,'certificate':str(path.relative_to(ROOT)).replace('\\','/'),'certificate_sha256':sha(path),
        'initial_sha256':initial_hashes,'final_sha256':final_hashes,'all_inputs_unchanged':True,'driver_sha256':sha(Path(__file__)),
        'frozen_PT_source_sha256':sha(source),'parameter_sha256':sha(par),
        'passed':True,'exact_chambers_checked':len(results),'exact_scalar_minorants_checked':len(results)*len(terms),
        'exact_scalar_endpoint_checks':endpoint_checks,'piecewise_affine_supports_checked':pieces,
        'candidate_floor_pass_count':sum(x>=F(433,50000) for x in results),
        'minimum_Gram_lower_bound_exact':str(min(results)),
        'minimum_Gram_lower_bound_float_display_only':float(min(results)),
        'seconds':time.monotonic()-start,'scalar_real_soundness_formalized':False,
        'global_chamber_coverage_proven':False,'new_unconditional_zeta_bound_proven':False}
    (HERE/args.output).write_text(json.dumps(outcome,indent=2)+'\n',encoding='utf8')
    print(json.dumps(outcome),flush=True)

if __name__=='__main__':main()
