"""Exact metadata-only check of the new common-shift rounding cutoff.

No kernel/table values, geometry records, samples, optimizer or Lean are
evaluated. Parse the published ledger independently, using Fraction only.
Default is read-only; --write-receipt writes only an absent receipt.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
LEDGER = ROOT/'StructuralW10Followup20261016/NewLedger.lean'
OUT = HERE/'metadata-replay.json'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--write-receipt', action='store_true')
    args = ap.parse_args()
    if args.write_receipt:
        assert not OUT.exists()
    initial = {p.relative_to(ROOT).as_posix():sha(p)
               for p in [Path(__file__).resolve(), LEDGER]}
    text = LEDGER.read_text(encoding='utf8')
    aa = text.split('def aN :',1)[1].split('def bN :',1)[0]
    bb = text.split('def bN :',1)[1].split('def a (',1)[0]
    pairs = [(int(i),int(j),int(v)) for i,j,v in
             re.findall(r'\| (\d+), (\d+) => (\d+)', aa)]
    bs = {int(i):F(int(v),10**10) for i,v in
          re.findall(r'\| (\d+) => (\d+)', bb)}
    assert len(pairs)==45 and len({(i,j) for i,j,v in pairs})==45
    assert set(bs)==set(range(9)) and all(v>0 for v in bs.values())
    positive = [(i,j,v) for i,j,v in pairs if v>0]
    assert len(positive)==41
    B = sum(bs.values(),F(0))
    s = F(123,128)
    delta = 1-s
    assert B==F(11055671,2500000000)
    assert delta*B==F(11055671,64000000000)
    cases=[]
    for c in [F(11,1250),F(221,25000)]:
        T=c-s*B
        assert T>0
        bounds=[]
        for i,j,_ in positive:
            bmin=min(bs[r] for r in range(i,j))
            upper=F(j-i)+T/bmin
            ceiling=-((-upper.numerator)//upper.denominator)
            assert j-i>=1 and upper<=32 and ceiling<=32
            bounds.append({'i':i,'j':j,'span_rank':j-i,
                           'min_span_b':str(bmin),
                           'strict_rounding_argument_upper':str(upper),
                           'ceiling_upper':ceiling})
        assert max(r['ceiling_upper'] for r in bounds)==32
        cases.append({'target':str(c),'pressure_excess_budget':str(T),
                      'positive_edge_count':len(bounds),
                      'maximum_ceiling_upper':32,
                      'maximum_strict_upper':str(max(F(r['strict_rounding_argument_upper'])
                                                    for r in bounds)),
                      'all_needed_integer_centres_in_1_through_32':True,
                      'bounds':bounds})
    for name,h in initial.items():
        assert sha(ROOT/name)==h
    result={'scope':__doc__,'passed':True,
            'source_sha256_start':initial,'source_sha256_end':initial,
            'B':str(B),'sep':str(s),'delta':str(delta),
            'rounding_pressure_payment':str(delta*B),
            'bmin':str(min(bs.values())), 'cases':cases,
            'kernel_evaluations':0,'new_table_entries':0,
            'tree_or_point_records_scanned':0,'solver_calls':0,
            'Lean_invocations':0,'actual_floor_or_exclusion_proven':False}
    if args.write_receipt:
        OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'cases':len(cases),
                      'positive_edges_per_case':41,'maximum_integer_centre':32,
                      'B':str(B),'deltaB':str(delta*B)}))

if __name__=='__main__':
    main()
