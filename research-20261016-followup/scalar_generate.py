"""Emit concrete scalar envelope certificates from the frozen rational data.

The emitted Lean must be separately compiled; this generator proves nothing.
"""
from pathlib import Path
from fractions import Fraction as F
import ast,hashlib,json,re

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).parent
OUT=ROOT/'StructuralW10Followup20261016'
SOURCE=ROOT/'research-20261016-w10-unconditional/analytic_gram_minorant.json'
UPSTREAM=ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def lit(x,typ='ℚ'):
    x=F(x)
    return f'({x.numerator} : {typ})/{x.denominator}'

def main():
    d=json.loads(SOURCE.read_bytes());text=UPSTREAM.read_text(encoding='utf8')
    text=text[text.index('namespace AMW.Cert.PC9QB6M\n'):]
    words={}
    for block,body in re.findall(r'\.lf (\d+) (\[[^\]]*\])',text):
        for k,v in ast.literal_eval(body):
            p=1024*int(block)+k
            left=max(0,p-((v>>96)&((1<<20)-1)));right=p+(v>>116)
            words[p]=(v&((1<<96)-1))+(left<<96)+(right<<120)
    header='''/- SPDX-License-Identifier: Apache-2.0
Generated concrete scalar data; check the matching kernel receipts.
No global coverage is asserted.
-/
import StructuralW10Followup20261016.scalar_Checker
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralW10Followup20261016.Scalar
'''
    out=[header]
    for h in d['hulls']:
        n=h['integer_center']
        out.append(f'def base{n} : ℚ := ({h["outward_lower_SC"]} : ℚ)/32768\n')
        out.append(f'def low{n} : ℚ := {lit(h["lower"])}\n')
        out.append(f'def top{n} : ℚ := {lit(h["upper"])}\n')
        out.append(f'def hull{n} : List Piece := [\n')
        for z,s in enumerate(h['segments']):
            p=s['PT_point'];word=words[p] if p>=0 else 0
            out.append(f'  ⟨{lit(s["upper"])}, {max(p,0)}, {word}⟩'+(',' if z+1<len(h['segments']) else '')+'\n')
        out.append(']\n')
    out.append('end StructuralW10Followup20261016.Scalar\nend\n')
    p=OUT/'scalar_Data.lean';p.write_text(''.join(out),encoding='utf8',newline='\n')
    k=min(range(len(d['results'])),key=lambda k:d['results'][k]['diagonal_only_lower_bound_float'])
    r=d['results'][k]
    out=[header.replace('scalar_Checker','scalar_Data')]
    for j,t in enumerate(r['terms']):
        al=F(t['alpha']);anchor=F(t['anchor']);s=F(t['line_slope']);c=F(t['line_intercept'])-F(t['epsilon'])
        out.append(f'def q{k}_{j} : Quad := ⟨{lit(al)}, {lit(s-2*al*anchor)}, {lit(c+al*anchor**2)}⟩\n')
        n=t['center']
        out.append(f'''theorem scalar{k}_{j} {{x : ℝ}}
    (hl : (low{n} : ℝ)≤x) (hu : x≤(top{n} : ℝ)) : evalR q{k}_{j} x≤AMW.Cert.wfun x := by
  apply check_sound q{k}_{j} base{n} top{n} low{n} hull{n}
  · norm_num [q{k}_{j}]
  · decide +kernel
  · exact (by norm_num [base{n},low{n}] : (base{n} : ℝ)≤(low{n} : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar{k}_{j}
''')
    out.append('end StructuralW10Followup20261016.Scalar\nend\n')
    p=OUT/f'scalar_Basin{k}.lean';p.write_text(''.join(out),encoding='utf8',newline='\n')
    smoke=''.join(out[:3])+''.join(out[-1:])
    # One full scalar first; the subsequent basin module contains all 39.
    p=OUT/'scalar_Smoke.lean';p.write_text(smoke,encoding='utf8',newline='\n')
    param=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_bytes())
    weights={(i,j):F(a,param['denominator']) for i,j,a in param['a_upper'] if a}
    bs=[F(b,param['denominator']) for b in param['b_numerators']]
    anchor=[F(a,r['anchor_denominator']) for a in r['anchor_numerators']]
    span=lambda i,j:'('+'+'.join(f'g {z}' for z in range(i,j))+')'
    vec=lambda arr:'!['+', '.join(arr)+']'
    pairs=[tuple(t['pair']) for t in r['terms']]
    pressure='+'.join(f'({lit(b,"ℝ")})*g {i}' for i,b in enumerate(bs))
    qsum=pressure+'+'+'+'.join(f'({lit(weights[i,j],"ℝ")})*evalR q{k}_{z} {span(i,j)}' for z,(i,j) in enumerate(pairs))
    fw=pressure+'+'+'+'.join(f'({lit(weights[i,j],"ℝ")})*AMW.Cert.wfun {span(i,j)}' for i,j in pairs)
    rest='+'.join(f'({lit(weights[i,j]*F(t["alpha"]),"ℝ")})*({span(i,j)}-({lit(t["anchor"],"ℝ")}))^2'
        for t,(i,j) in zip(r['terms'],pairs) if j>i+1)
    out=[header.replace('scalar_Checker',f'scalar_Basin{k}'),
        'import_dummy_placeholder\n']
    # Imports must precede the namespace and section commands.
    out=[out[0].replace('set_option Elab.async false',
        'import StructuralW10Unconditional20261016.BasinPolynomials\nset_option Elab.async false')]
    out.append('open scoped BigOperators\nopen Zeta23Ext.BridgeW Zeta23Ext.Bridge\nopen StructuralW10Unconditional20261016\nopen StructuralResearch20261016.W10RefinedCandidate\n')
    out.append(f'def spans{k} (g : Fin 9 → ℝ) : Fin 39 → ℝ := '+vec([span(i,j) for i,j in pairs])+'\n')
    out.append(f'def lows{k} : Fin 39 → ℚ := '+vec([f'low{t["center"]}' for t in r['terms']])+'\n')
    out.append(f'def tops{k} : Fin 39 → ℚ := '+vec([f'top{t["center"]}' for t in r['terms']])+'\n')
    out.append(f'def Basin{k} (g : Fin 9 → ℝ) : Prop := ∀ z, (lows{k} z : ℝ) ≤ spans{k} g z ∧ spans{k} g z ≤ (tops{k} z : ℝ)\n')
    out.append(f'def qsum{k} (g : Fin 9 → ℝ) : ℝ := {qsum}\n')
    out.append(f'def rest{k} (g : Fin 9 → ℝ) : ℝ := {rest}\n')
    out.append(f'def anchor{k} : Fin 9 → ℝ := '+vec([lit(x,'ℝ') for x in anchor])+'\n')
    nested='0'
    for z in reversed(range(9)):nested=f'f {z}+({nested})'
    out.append(f'theorem sum9 (f : Fin 9 → ℝ) : (∑ i, f i)={nested} := by\n  simp only [Fin.sum_univ_succ]\n  rfl\n')
    out.append(f'''theorem fw_expanded{k} (g : Fin 9 → ℝ) : Fw W g = {fw} := by
  simp [RiemannFail.cert_wfun_eq, Fw, W, a, b, aN, bN,
    ptsN, Fin.sum_univ_succ, Finset.sum_range_succ, Finset.sum_Ico_succ_top]
  ring
theorem qsum_identity{k} (g : Fin 9 → ℝ) : qsum{k} g =
    BasinPolynomials.C{k}+(∑ i, (BasinPolynomials.b{k} i*(g i-anchor{k} i)+
      BasinPolynomials.d{k} i*(g i-anchor{k} i)^2))+rest{k} g := by
  rw [sum9]
  norm_num [qsum{k},rest{k},anchor{k},evalR,{','.join(f'q{k}_{z}' for z in range(39))},
    BasinPolynomials.C{k},BasinPolynomials.b{k},BasinPolynomials.d{k},Fin.sum_univ_succ,Fin.succ]
  ring
theorem actual_Fw_basin{k} (g : Fin 9 → ℝ) (h : Basin{k} g) :
    (433 : ℝ)/50000≤Fw W g := by
''')
    for z,(i,j) in enumerate(pairs):
        n=r['terms'][z]['center']
        out.append(f'  have hh{z} : (low{n} : ℝ)≤{span(i,j)} ∧ {span(i,j)}≤(top{n} : ℝ) := by simpa [lows{k},tops{k},spans{k}] using h ⟨{z},by decide⟩\n')
        out.append(f'  have hs{z} := mul_le_mul_of_nonneg_left (scalar{k}_{z} hh{z}.1 hh{z}.2) (by norm_num : (0 : ℝ)≤({lit(weights[i,j],"ℝ")}))\n')
    out.append(f'  have hf : qsum{k} g≤Fw W g := by\n    rw [fw_expanded{k}]\n    unfold qsum{k}\n    linarith only [{",".join(f"hs{z}" for z in range(39))}]\n')
    out.append(f'  have hr : 0≤rest{k} g := by unfold rest{k}; positivity\n')
    out.append(f'  have hp := BasinPolynomials.lower{k} (fun i => g i-anchor{k} i)\n  rw [qsum_identity{k}] at hf\n  linarith only [hf,hp,hr]\n#print axioms actual_Fw_basin{k}\n')
    out.append('end StructuralW10Followup20261016.Scalar\nend\n')
    p=OUT/f'scalar_FwBasin{k}.lean';p.write_text(''.join(out),encoding='utf8',newline='\n')
    report={'scope':__doc__,'driver_sha256':sha(Path(__file__)),'input_sha256':sha(SOURCE),
        'upstream_sha256':sha(UPSTREAM),'selected_basin':k,
        'generated':{str(p.relative_to(ROOT)).replace('\\','/'):sha(p) for p in OUT.glob('scalar_*.lean')},
        'lean_compilation_passed':False,'global_coverage_proven':False}
    (HERE/'scalar-generated.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
