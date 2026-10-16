"""Emit exact algebraic diagonal lower bounds for the 69 basin polynomials.

This does not certify the PT envelopes or their global chamber coverage.
Generated Lean requires its own successful default-kernel compilation.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def lit(q):
    q=F(q)
    return f'({q.numerator} : ℝ) / {q.denominator}'

def main():
    assert __debug__
    source=HERE/'analytic_gram_minorant.json';digest=sha(source);doc=json.loads(source.read_bytes())
    par=ROOT/'research-20261016/spectral-w10-refined-rational.json';p=json.loads(par.read_bytes())
    assert sha(par)==doc['parameter_sha256']
    coeff={(i,j):F(a,p['denominator']) for i,j,a in p['a_upper'] if a}
    out=['''/- Generated algebraic basin bounds only. The analytic link and
global coverage must be checked separately before any zeta-bound claim. -/
import StructuralW10Unconditional20261016.DiagonalPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralW10Unconditional20261016.BasinPolynomials
'''];lower_bounds=[]
    for k,row in enumerate(doc['results']):
        C=F(row['quadratic_center_value_exact']);b=list(map(F,row['gradient']))
        terms={tuple(r['pair']):r for r in row['terms']}
        d=[coeff[i,i+1]*F(terms[i,i+1]['alpha']) for i in range(9)]
        assert all(x>0 for x in d)
        exact=C-sum(x*x/(4*y) for x,y in zip(b,d));assert exact>=F(433,50000)
        lower_bounds.append(str(exact))
        vector=lambda arr:'!['+', '.join(lit(v) for v in arr)+']'
        out.extend([f'def C{k} : ℝ := {lit(C)}\n',f'def b{k} : Fin 9 → ℝ := {vector(b)}\n',
            f'def d{k} : Fin 9 → ℝ := {vector(d)}\n',f'''theorem lower{k} (x : Fin 9 → ℝ) :
    (433 : ℝ)/50000 ≤ C{k}+∑ i, (b{k} i*x i+d{k} i*(x i)^2) := by
  apply DiagonalPolynomial.lower
  · intro i
    fin_cases i <;> norm_num [d{k}]
  · norm_num [C{k},b{k},d{k},Fin.sum_univ_succ]
#print axioms lower{k}
'''])
    out.extend(['end StructuralW10Unconditional20261016.BasinPolynomials\nend\n'])
    target=ROOT/'StructuralW10Unconditional20261016/BasinPolynomials.lean'
    target.write_bytes(''.join(out).encode('utf8'))
    assert sha(source)==digest
    receipt={'scope':__doc__,'input_sha256':digest,'parameter_sha256':sha(par),'script_sha256':sha(Path(__file__)),
        'output_sha256':sha(target),'source_bytes':target.stat().st_size,'polynomial_count':len(lower_bounds),
        'minimum_diagonal_lower_bound_exact':str(min(map(F,lower_bounds))),
        'lean_compilation_passed':False,'global_chamber_coverage_proven':False,'new_unconditional_zeta_bound_proven':False}
    (HERE/'basin-polynomials-generated.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    print(json.dumps(receipt),flush=True)

if __name__=='__main__':main()
