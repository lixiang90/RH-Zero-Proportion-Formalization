"""Write the concrete current-profile M theorem from frozen data; no Lean call."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
INPUT = ROOT/'research-goal-20261018-stageM-component-envelope-preparation'
OUT = ROOT/'StructuralS1RM20261018'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write_new(p, s):
    with p.open('x', encoding='utf-8', newline='\n') as f:
        f.write(s)


def zexpr(j, terms):
    if j < 10:
        return f'(20 * 32768 * P {j})'
    i, k = terms[j-10]['physical_span']
    return f'((QuantizedComponent.kappa : ℝ) * wfun (P {k}-P {i}))'


def main():
    assert sha(INPUT/'model.json') == '9a47b54d54995fe8565b27c4268368f8779a2cbb9bc22b9fdbd09a7a4fc6d04a'
    assert sha(INPUT/'certificate.json') == '8b9d10c8553c0b70ff8937145028a9cdd6226587d264f4ffd064dae7ad841fb9'
    m=json.loads((INPUT/'model.json').read_text(encoding='utf-8'))
    original=json.loads((INPUT/'original-components.json').read_text(encoding='utf-8'))
    converted=json.loads((HERE/'local-data-prepared.json').read_text(encoding='utf-8'))
    ids=converted['positive_original_row_ids']; terms=m['terms']
    s='''import StructuralS1RM20261018.LocalGeometry
import StructuralS1RM20261018.LocalData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.PCell AMW.Cert.Pyr AMW.Cert.PyrD
open StructuralS1RM20261018
open StructuralS1RM20261018.LocalGeometry
namespace StructuralS1RM20261018.LocalComponents
-- Actual variables, not epigraph existential witnesses. No gauge X0=0.
def actualZ (P : ℕ → ℝ) (j : Fin 78) : ℝ :=
  match j.val with
'''
    for j in range(77):
        s+=f'  | {j} => {zexpr(j,terms)}\n'
    s+=f'  | _ => {zexpr(77,terms)}\n'
    # Share the actual expanded point word once per distinct original anchor.
    point_words={}
    for rid in ids:
        r=m['rows'][rid]
        if r['kind']!='active_anchor_component': continue
        term=terms[r['term']]
        comp=next(x for x in term['components'] if x['row_id']==rid)
        p=comp['anchor']; lo,hi=comp['original_valid_interval']
        word=int(comp['trip'])+(lo<<96)+(hi<<120)
        assert p not in point_words or point_words[p]==word
        point_words[p]=word
    for p,word in sorted(point_words.items()):
        s+=f'\ntheorem pointWord{p} : AMW.Cert.PC9QB6MData.PT {p} = {word} := by decide +kernel\n'
    for k,rid in enumerate(ids):
        r=m['rows'][rid]
        s+=f'\ntheorem rowSound{k} (P : ℕ → ℝ) (h : Domain P) :\n'
        s+=f'    Sparse78.eval LocalData.row{k} (actualZ P) ≤ (LocalData.row{k}.rhs : ℝ) := by\n'
        if r['kind']=='original_span_lower':
            assert rid==59
            s+='  have hv := (h.left.2 21 (by decide)).1\n'
            s+='  norm_num [AMW.Cert.PC9QB6M.PR, pI, pJ, leftCell] at hv\n'
            s+='  rw [canonical_span P false 3 8 (by decide) (by decide)] at hv\n'
            s+='  norm_num [SC] at hv\n'
        elif r['kind']=='true_ordered_four_point':
            assert rid==154
            s+='  have hv := h.orderedRight\n'
        else:
            e=r['term']; term=terms[e]; i,j=term['physical_span']
            L0=term['original_L0']; L,U=term['original_bounds']
            s+=f'  have hr := range{e} P h\n'
            if r['kind']=='constant_component':
                old=original['original_windows'][term['window']]['terms'][term['original_term']]
                Uc=old['uc_upper']; lb=old['original_lb_table_value']
                assert U<=Uc and r['bound']==-32768*1024*lb
                s+=f'  have hUc : ({U} : ℝ)/SC ≤ ({Uc} : ℝ)/SC := by norm_num [SC]\n'
                s+=f'  have hv := QuantizedComponent.scaled_constant AMW.Cert.PC9QB6MData.lbS {L} {Uc} (P {j}-P {i}) hr.1 (hr.2.trans hUc)\n'
                s+=f'  have hlb : lb AMW.Cert.PC9QB6MData.TOP AMW.Cert.PC9QB6MData.BK {L} {Uc} = {lb} := by decide +kernel\n'
                s+='  rw [hlb] at hv\n'
            else:
                assert r['kind']=='active_anchor_component'
                comp=next(x for x in term['components'] if x['row_id']==rid)
                p=comp['anchor']; E=comp['E']; S=comp['S']
                s+=f'  have hiv : ivIn (AMW.Cert.PC9QB6MData.PT {p}) {L} {U} {p} = true := by\n'
                s+=f'    rw [pointWord{p}]\n    decide +kernel\n'
                s+='  have ht := tval_of_ivIn AMW.Cert.PC9QB6MData.ptS hiv\n'
                s+=f'  have hv := QuantizedComponent.scaled_anchor ht (show {L0} ≤ {L} by decide) (P {j}-P {i}) hr.1 hr.2\n'
                s+=f'  have hs : QuantizedComponent.slope (tf AMW.Cert.PC9QB6MData.PT) {p} = ({S} : ℤ) := by\n'
                s+=f'    norm_num [QuantizedComponent.slope, QuantizedComponent.dLo, tf, pointWord{p}, trip, lo32, hi32]\n'
                s+=f'  have he : QuantizedComponent.intercept (tf AMW.Cert.PC9QB6MData.PT) {L0} {p} = ({E} : ℤ) := by\n'
                s+=f'    norm_num [QuantizedComponent.intercept, QuantizedComponent.dLo, QuantizedComponent.dHi, tf, pointWord{p}, trip, lo32, hi32]\n'
                s+='  rw [hs, he] at hv\n'
        entries=[(j,a) for j,a in enumerate(r['position10']) if a]
        if r['epigraph_index'] is not None:
            entries.append((10+r['epigraph_index'],r['epigraph_coefficient']))
        lhs=' + '.join(f'({a} : ℝ) * {zexpr(j,terms)}' for j,a in entries)+' + 0'
        s+=f'  change {lhs} ≤ ({r["bound"]} : ℝ)\n'
        s+='  norm_num at hv ⊢\n  nlinarith [hv]\n'
    s+='''
theorem rowsSound (P : ℕ → ℝ) (h : Domain P) (i : Fin 77) :
    Sparse78.eval (LocalData.rows i) (actualZ P) ≤ ((LocalData.rows i).rhs : ℝ) := by
  fin_cases i
'''
    s+=''.join(f'  · exact rowSound{k} P h\n' for k in range(77))
    s+='\nset_option pp.fullNames true\n#print axioms rowsSound\nend StructuralS1RM20261018.LocalComponents\nend\n'
    write_new(OUT/'LocalComponents.lean',s)
    p='''import StructuralS1RM20261018.LocalComponents
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.PCell AMW.Cert.Pyr AMW.Cert.PyrD
open StructuralS1RM20261018
open StructuralS1RM20261018.LocalGeometry
open StructuralS1RM20261018.LocalComponents
namespace StructuralS1RM20261018.LocalPair
def pairEnergy (P : ℕ → ℝ) : ℝ :=
  AMW.Cert.PC9QB6M.G (P 1-P 0) (P 2-P 1) (P 3-P 2) (P 4-P 3)
    (P 5-P 4) (P 6-P 5) (P 7-P 6) (P 8-P 7) +
  AMW.Cert.PC9QB6M.G (P 2-P 1) (P 3-P 2) (P 4-P 3) (P 5-P 4)
    (P 6-P 5) (P 7-P 6) (P 8-P 7) (P 9-P 8)

theorem objective_eq (P : ℕ → ℝ) :
    (∑ j : Fin 78, (LocalData.objective j : ℝ) * actualZ P j) =
      2 * (QuantizedComponent.kappa : ℝ) *
        (Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P false) +
         Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P true)) := by
'''
    for term in terms:
        e=term['term']; i,j=term['original_span']; pi,pj=term['physical_span']; rev='false' if term['window']==0 else 'true'
        p+=f'  have hs{e} : gsum (canonicalGap P {rev}) {i} {j} = P {pj}-P {pi} :=\n'
        p+=f'    canonical_span P {rev} {i} {j} (by decide) (by decide)\n'
    p+='  norm_num [Fin.sum_univ_succ, LocalData.objective, actualZ, Fg, AMW.Cert.PC9QB6M.BS,\n'
    p+='    AMW.Cert.PC9QB6M.TS, tI, tJ, tA, Finset.sum_range_succ, canonicalGap] \n'
    p+='  simp only ['+', '.join('hs'+str(i) for i in range(68))+']\n  ring\n'
    p+='''
theorem fg_eq (P : ℕ → ℝ) :
    Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P false) +
      Fg 8 AMW.Cert.PC9QB6M.BS AMW.Cert.PC9QB6M.TS (canonicalGap P true) =
        (AMW.Cert.PC9QB6M.SA : ℝ) * pairEnergy P := by
  have hl := AMW.Cert.PC9QB6M.Fg_G (P 1-P 0) (P 2-P 1) (P 3-P 2) (P 4-P 3)
    (P 5-P 4) (P 6-P 5) (P 7-P 6) (P 8-P 7)
  have hr := AMW.Cert.PC9QB6M.Fg_G (P 9-P 8) (P 8-P 7) (P 7-P 6) (P 6-P 5)
    (P 5-P 4) (P 4-P 3) (P 3-P 2) (P 2-P 1)
  change Fg 8 _ _ (canonicalGap P false) = _ at hl
  change Fg 8 _ _ (canonicalGap P true) = _ at hr
  rw [hl, hr, AMW.Cert.PC9QB6M_G_rev]
  unfold pairEnergy
  ring

-- This theorem covers only the two literal original cells in the id/rev chart.
-- Reaching them from a global product cover remains a separate obligation.
theorem actual_pair_lower (P : ℕ → ℝ) (h : Domain P) :
    (2 * 893766123055294719 : ℝ) / AMW.Cert.PC9QB6M.SA ≤ pairEnergy P := by
  have hv := Sparse78.sound LocalData.rows LocalData.weights LocalData.den
    LocalData.objective LocalData.target LocalData.checked (actualZ P) (rowsSound P h)
  rw [objective_eq, fg_eq] at hv
  norm_num [LocalData.target, QuantizedComponent.kappa, AMW.Cert.PC9QB6M.SA] at hv ⊢
  nlinarith

set_option pp.fullNames true
#print axioms objective_eq
#print axioms fg_eq
#print axioms actual_pair_lower
end StructuralS1RM20261018.LocalPair
end
'''
    write_new(OUT/'LocalPair.lean',p)
    record={'schema':'M-current-profile-uncompiled-local-pair-v1',
        'source_dependencies': [{'path':(INPUT/name).relative_to(ROOT).as_posix(),'sha256':sha(INPUT/name)}
                                for name in ['model.json','certificate.json','original-components.json']],
        'files':[{'path':x.relative_to(ROOT).as_posix(),'bytes':x.stat().st_size,'sha256':sha(x)}
                 for x in [OUT/'LocalComponents.lean',OUT/'LocalPair.lean']],
        'actual_components':{'selected_dual_rows':77,'active_anchor_rows':47,'constant_rows':28,'geometry_rows':2,'unique_original_PT':len(point_words)},
        'new_FS_or_anchor_or_kernel_or_solver':0,'Lean_runs':0,
        'scope':'concrete actual local theorem source, uncompiled; no global cover or new kappa claim'}
    write_new(HERE/'local-pair-prepared.json',json.dumps(record,indent=2)+'\n')
    print(json.dumps(record['files']))


if __name__=='__main__':
    main()
