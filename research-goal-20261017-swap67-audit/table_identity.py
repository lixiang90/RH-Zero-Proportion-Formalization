"""Read-only table/profile/ledger identity supplement for swap67.

Compares frozen rational JSON with literal formal data, not a new Lean
proof of those data. No producer, solver, sampling or cover is executed.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse, hashlib, json, re

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OUT=HERE/'table-identity.json'


def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    names=['research-goal-20261016/window_normalized_interval.json','research-goal-20261016/cover_newjet.json',
      'research-20261016-followup/window_reweight_rational.json','StructuralGoal20261016/WindowJetTableData.lean',
      'StructuralGoal20261016/WindowKernel.lean','StructuralW10Followup20261016/NewWindows.lean',
      'StructuralW10Followup20261016/NewLedger.lean']
    guards={n:digest(ROOT/n)for n in names};w=json.loads((ROOT/names[0]).read_bytes());u=json.loads((ROOT/names[1]).read_bytes())
    pars=json.loads((ROOT/names[2]).read_bytes());assert w['parameter_sha256']==u['receipt']['parameter_sha256']==guards[names[2]]
    text=(ROOT/names[3]).read_text(encoding='utf8');block=text.split('def wValues : List (List QI) :=',1)[1].split('def K ',1)[0]
    formal=[(Q(int(a),10**30),Q(int(b),10**30))for a,b in re.findall(r'qi30\s*\((-?\d+)\)\s*\((-?\d+)\)',block)]
    actual=[tuple(map(Q,entry))for n in range(33)for entry in w['integer_w_Taylor_coefficients'][str(n)]]
    assert len(formal)==len(actual)==792 and formal==actual
    profile=(ROOT/names[5]).read_text(encoding='utf8').split('def nums24 :',1)[1].split('| _ => 0',1)[0]
    nums={int(i):int(v)for i,v in re.findall(r'\|\s*(\d+)\s*=>\s*(-?\d+)',profile)};assert set(nums)==set(range(24))
    coeff=[10**9]+[nums[i]for i in range(24)]
    assert coeff[1:]==pars['window_coefficient_numerators_1e9'] and coeff==u['receipt']['coefficient_numerators_1e9']
    kernel=(ROOT/names[4]).read_text(encoding='utf8')
    assert '(StructuralW10Followup20261016.NewWindows.nums24 n : ℝ) / 1000000000'in kernel
    ledger=(ROOT/names[6]).read_text(encoding='utf8')
    atext=ledger.split('def aN :',1)[1].split('def bN :',1)[0];btext=ledger.split('def bN :',1)[1].split('def a ',1)[0]
    aa={(int(i),int(j)):int(v)for i,j,v in re.findall(r'\|\s*(\d+),\s*(\d+)\s*=>\s*(\d+)',atext)}
    bb={int(i):int(v)for i,v in re.findall(r'\|\s*(\d+)\s*=>\s*(\d+)',btext)}
    assert sorted((i,j,v)for(i,j),v in aa.items())==sorted(tuple(v)for v in pars['a_upper'])
    assert [bb[i]for i in range(9)]==pars['b_numerators'] and pars['denominator']==10**10
    assert '(aN i j : ℝ) / 10000000000'in ledger and '(bN i : ℝ) / 10000000000'in ledger
    contained=overlap=0
    for n in range(33):
        for j in range(23):
            wl,wu=map(Q,w['integer_w_Taylor_coefficients'][str(n)][j+1]);ul,uu=map(Q,u['integer_taylor_coefficients'][str(n)][j])
            wl*=j+1;wu*=j+1;assert max(wl,ul)<=min(wu,uu),('derivative conventions disjoint',n,j)
            overlap+=1;contained+=wl<=ul<=uu<=wu
    for n,h in guards.items():assert digest(ROOT/n)==h
    result={'scope':__doc__,'passed':True,'source_sha256':digest(Path(__file__)),'input_sha256':guards,
      'formal_wValues_entries_exactly_equal_JSON':792,'profile_coefficients_exactly_equal':25,'formal_a_entries_equal':len(aa),
      'formal_b_entries_equal':len(bb),'Wprime_Taylor_intervals_overlap_W_differentiated_coefficients':overlap,
      'Wprime_intervals_contained_in_formal_coarse_W_differentiated_intervals':contained,
      'formal_data_identity_only_not_new_kernel_verification':True,'new_Lean_invocations':0,'new_zero_proportion_proven':False}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    assert __debug__
    main()
