"""Replay only the original new-record COV root WZ finite queries.

All Fourier and normalization data come from the new source. This is the
root-guard supplement to the already completed original-floor walk, not
a second walk or a new kernel-query experiment.
"""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os
import re
import time
import traceback

import packing_parser_v3 as parser
import root_wz_model as wz

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'root-wz-replay.json'
FAIL=HERE/'root-wz-failure.json'
START=HERE/'root-wz-started.json'
CLOSURE=ROOT/'research-goal-20261018-record-wz-static-addendum/comparison.json'
CLOSURE_SHA='47040eb82ec3c9fed91e3b67c023142ec01e604c8953cf71f410cbf0ff9556a1'


def digest(p):return sha256(p.read_bytes()).hexdigest()


def load_parameters(text):
    def number(name):
        vals=re.findall(r'(?m)^noncomputable def '+re.escape(name)+r' : ℕ := (\d+)\s*$',text)
        assert vals and len(set(vals))==1,(name,vals)
        return int(vals[0])
    params={name:number(name) for name in ['DZ','SC','PLN','PUN','E20','ERRD','E9','SW','GAM0','GAM1']}
    def pair(name):
        rows=re.findall(r'(?m)^noncomputable def '+name+r' : IV := IV.ofN (\d+) (\d+)\s*$',text)
        assert len(rows)==1,name
        return tuple(map(int,rows[0]))
    ce_text=re.search(r'noncomputable def CE : List[^\n]*:=\s*(\[[\s\S]*?\])',text)[1]
    ce=ast.literal_eval(ce_text.replace('true','True').replace('false','False'))
    assert [r[0] for r in ce]==list(range(1,13))
    cj_text=re.search(r'noncomputable def CJ \(j : ℕ\)[\s\S]*?(?=^structure Acc)',text,re.M)[0]
    cj={int(j):(int(v),sg=='true') for j,v,sg in re.findall(r'\| (\d+) => \((\d+), (true|false)\)',cj_text)}
    assert set(cj)==set(range(1,13))
    fa_text=re.search(r'noncomputable def FA \(c : CellA\)[\s\S]*?(?=^noncomputable def nearOn)',text,re.M)[0]
    fa=[(int(j),int(v),sg=='true') for j,v,sg in re.findall(r'\b(\d+) (\d+) (true|false)\)',fa_text)]
    assert fa==ce,('new_source_FA_CE_mismatch',fa,ce)
    wz.PARAMS=params;wz.DZ=params['DZ'];wz.COEFF=ce;wz.CJ=cj
    wz.SIGC=pair('SIGC');wz.RHOC=pair('RHOC')
    return {'parameters':params,'new_CE':ce,'new_CJ':cj,'new_FA0_same_order_as_CE':True,
            'new_SIGC':wz.SIGC,'new_RHOC':wz.RHOC}


def main():
    assert __debug__
    assert not any(p.exists() for p in [OUT,FAIL,START]),'refuse repeat/overwrite'
    started=time.monotonic();paths=[Path(__file__),HERE/'root_wz_model.py',HERE/'packing_parser_v3.py',parser.SOURCE,CLOSURE]
    before={p.relative_to(ROOT).as_posix():digest(p) for p in paths}
    assert digest(parser.SOURCE)==parser.SOURCE_SHA
    assert digest(CLOSURE)==CLOSURE_SHA
    begin={'pid':os.getpid(),'stage':'original_COV_WZ_started','source_and_scripts':before,
           'same_original_cN':parser.ORIGINAL_CN,'no_intervals_outside_original_COV':True}
    START.write_text(json.dumps(begin,indent=2)+'\n',encoding='utf-8');print(json.dumps(begin),flush=True)
    rows=[];last=None
    try:
        model=parser.load_model();params=load_parameters(model['text'])
        assert params['parameters']['SC']==32768 and params['parameters']['SW']==10**13
        adjacency={i:t for t in model['TS'] for i,j,a,k in [t] if j==i+1}
        assert set(adjacency)==set(range(8))
        for r,cov in enumerate(model['COV']):
            for L,U,truth in cov:
                if not truth:continue
                last={'gap':r,'lo':L,'hi':U}
                value=wz.cell_wz(L,U)
                coefficient=adjacency[r][2]
                lhs=model['CN']*params['parameters']['SW']
                rhs=coefficient*value
                assert lhs<=rhs,('original_root_WZ_guard',r,L,U,value,lhs,rhs)
                rows.append({**last,'adjacent_coefficient':coefficient,'WZ':value,
                             'left_cN_times_SW':lhs,'right_a_times_WZ':rhs,'margin':rhs-lhs,'passed':True})
        assert rows
        after={p.relative_to(ROOT).as_posix():digest(p) for p in paths};assert before==after
        out={'schema':'new-record-original-COV-WZ-finite-replay-v1','passed':True,
             'pid':os.getpid(),'seconds':time.monotonic()-started,
             'source_and_scripts_sha256_start':before,'source_and_scripts_sha256_end':after,
             'source_unchanged':True,'original_cN':model['CN'],
             'scope':'Exact integer replay of existing original-COV CellN.WZ queries and coverChk inequalities, with NEW-source CE/CJ/FA and constants. Not a new kernel query, witness search or changed threshold.',
             'parameter_identity':params,'existing_COV_true_guard_count':len(rows),
             'minimum_guard_margin':min(r['margin'] for r in rows),'all_guard_rows':rows,
             'all_original_true_COV_WZ_integer_guards_passed':True,
             'new_intervals':0,'new_kernel_anchor_queries':0,'leaf_checks':0,'solver_calls':0,'Lean_runs':0,
             'analytic_CellA_WZ_soundness_reproved':False,
             'analytic_scope':'The source CellA/CellN soundness proofs remain the analytic link; this replay checks their finite root inputs, not their Lean proof terms.',
             'new_global_floor_proven':False,'new_unconditional_zero_proportion_proven':False}
        OUT.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({k:out[k] for k in ['passed','pid','existing_COV_true_guard_count','minimum_guard_margin','seconds']}),flush=True)
    except BaseException as exc:
        out={'passed':False,'stage':'original_COV_WZ_failed','pid':os.getpid(),'error':repr(exc),
             'traceback':traceback.format_exc(),'completed_guard_rows':rows,'last_query':last,
             'source_and_scripts_sha256_start':before,'source_sha256_end':digest(parser.SOURCE),'seconds':time.monotonic()-started}
        FAIL.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out),flush=True);raise


if __name__=='__main__':main()
