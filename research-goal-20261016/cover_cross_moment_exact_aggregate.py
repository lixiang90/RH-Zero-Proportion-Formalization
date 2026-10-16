"""Exact common-denominator one-row supplement; no outward rounding.

Take the already checked unrounded Friendly/global-box aggregate, clear
the LCM denominator, and check its strict minimum using integer boxes.
This is an additional read-only representation of the same two proofs.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd,lcm
import argparse,gzip,hashlib,json,time
HERE=Path(__file__).parent;sha=lambda b:hashlib.sha256(b).hexdigest()
SC=32768;DS=10**15;BOX=SC*DS;POLICY='cell-g/unit-H/global7-u-q-v1'


def bounds(state):
    result=[(int(l)*DS,int(u)*DS) for l,u in zip(state[0][:9],state[1][:9])]
    result += [(-7*BOX,7*BOX)]*41
    result += [(0,BOX) if i==j else (-BOX,BOX) for i in range(9) for j in range(i,9)]
    result += [(-7*BOX,7*BOX)]*369;assert len(result)==464;return result


def inputs():
    raw=(HERE/'cover-cross-moment-single-round.json').read_bytes();doc=json.loads(raw)
    packed=(HERE/'cover-cross-moment-global-box-evidence/proof.json.gz').read_bytes();proof=json.loads(gzip.decompress(packed))
    assert sha(packed)==doc['source_global_box_proof_gzip_sha256'] and doc['box_policy']==POLICY
    states={c['path']:c['before'] for c in proof['source']['cases']};return raw,doc,states


def generate():
    start=time.monotonic();raw,doc,states=inputs();cases=[]
    for case in doc['cases']:
        coeff=[(i,F(v)) for i,v in case['exact_sparse_coefficients']];B=F(case['exact_bound']);D0=1
        for value in [v for i,v in coeff]+[B]:D0=D0//gcd(D0,value.denominator)*value.denominator
        integers=[(i,int(v*D0)) for i,v in coeff];BI=int(B*D0);box=bounds(states[case['path']])
        assert all(F(v,D0)==a for (i,v),(j,a) in zip(integers,coeff) if i==j) and F(BI,D0)==B
        minimum=sum(min(a*box[i][0],a*box[i][1]) for i,a in integers);margin=minimum-BOX*BI;assert margin>0
        normalized=F(margin,BOX*D0*int(case['original_weight_sum']))
        record={'path':case['path'],'box_policy':POLICY,'rational_row_denominator':str(D0),'rational_row_denominator_digits':len(str(D0)),
          'integer_coefficients':[[i,str(v)] for i,v in integers],'integer_bound':str(BI),'integer_residual_constant':str(-BI),
          'box_denominator':str(BOX),'integer_box_minimum':str(minimum),'strict_integer_margin':str(margin),
          'rational_strict_margin':str(F(margin,BOX*D0)),'normalized_margin_original_weight_sum':str(normalized),
          'original_weight_sum':case['original_weight_sum'],'exact_nonzero_coefficients':len(integers),
          'source_unrounded_full_464_row_sha256':case['unrounded_full_464_row_sha256'],'requires_outward_rounding':False}
        record['integer_aggregate_json_bytes']=0
        while True:
            count=len((json.dumps(record,separators=(',',':'))+'\n').encode())
            if count==record['integer_aggregate_json_bytes']:break
            record['integer_aggregate_json_bytes']=count
        cases.append(record)
        print(json.dumps({'path':case['path'],'D0_digits':len(str(D0)),'integer_aggregate_bytes':record['integer_aggregate_json_bytes'],
          'exact_strict':True,'normalized_margin':float(normalized)}),flush=True)
    output={'schema':'global-box-exact-LCM-aggregate-v1','scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
      'source_single_round_json_sha256':sha(raw),'source_global_box_proof_gzip_sha256':doc['source_global_box_proof_gzip_sha256'],
      'box_policy':POLICY,'row_convention':'sum_i A_i*variable_i <= B; each variable lies in [L_i/boxDen,U_i/boxDen]',
      'strict_check':'boxDen*B < sum_i min(A_i*L_i,A_i*U_i)','cases':cases,'all_factors_and_energy_weights_unchanged':True,
      'rounding_operations':0,'strict_integer_systems':2,'new_cell_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    p=HERE/'cover-cross-moment-exact-aggregate.json';p.write_text(json.dumps(output,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({'exact_aggregate_bytes':p.stat().st_size,'exact_aggregate_sha256':sha(p.read_bytes())}),flush=True)


def verify():
    start=time.monotonic();raw,source,states=inputs();packed=(HERE/'cover-cross-moment-exact-aggregate.json').read_bytes();doc=json.loads(packed)
    assert doc['script_sha256']==sha(Path(__file__).read_bytes()) and doc['source_single_round_json_sha256']==sha(raw)
    lookup={r['path']:r for r in source['cases']};cases=[]
    for row in doc['cases']:
        original=lookup[row['path']];a={i:F(v) for i,v in original['exact_sparse_coefficients']};B=F(original['exact_bound']);D0=int(row['rational_row_denominator'])
        assert D0==lcm(*[v.denominator for v in list(a.values())+[B]]) and D0>0
        saved={i:int(v) for i,v in row['integer_coefficients']};assert len(saved)==len(row['integer_coefficients'])
        assert all(F(saved.get(i,0),D0)==a.get(i,F(0)) for i in range(464))
        assert F(int(row['integer_bound']),D0)==B==-F(int(row['integer_residual_constant']),D0)
        box=bounds(states[row['path']]);rational_minimum=sum(v*F(box[i][0 if v>=0 else 1],BOX) for i,v in a.items())
        exact_margin=rational_minimum-B;integer_minimum=sum(min(v*box[i][0],v*box[i][1]) for i,v in saved.items())
        integer_margin=integer_minimum-BOX*int(row['integer_bound'])
        assert exact_margin==F(row['rational_strict_margin'])==F(integer_margin,BOX*D0)>0
        assert integer_margin==int(row['strict_integer_margin']) and integer_minimum==int(row['integer_box_minimum'])
        cases.append({'path':row['path'],'minimal_common_denominator_checked':True,'all_464_exact_coefficients_and_bound_match':True,
          'D0_digits':len(str(D0)),'strict_integer_box_check':True})
    receipt={'scope':'Independent Fraction-vs-integer exact common-denominator one-row audit; no kernel, optimizer or rounding.',
      'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(packed),'source_single_round_json_sha256':sha(raw),
      'all_checks_passed':True,'cases':cases,'rounding_operations':0,'new_cell_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    p=HERE/'cover-cross-moment-exact-aggregate-replay.json';p.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'exact_LCM_replay_passed':True,'receipt_sha256':sha(p.read_bytes())}),flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--verify',action='store_true');args=ap.parse_args()
    verify() if args.verify else generate()
