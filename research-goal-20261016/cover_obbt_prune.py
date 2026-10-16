"""Delete dispensable sublevel bounds while retaining exact KKT exclusion.

Each retained bound was certified on the original cell. A candidate subset
is closed to a wider cell and receives a fresh strict directional certificate.
Only a successful exact integer-flow check accepts a deletion. The result
therefore preserves the energy-sublevel semantics and can use fewer separate
value mixtures; it does not modify any frozen discovery source or live run.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
import cover_sublevel_obbt as core
import cover_correlated_api as api
import cover_correlated_direction as engine

HERE=Path(__file__).parent;g=core.g

def ceil(x):return -((-x.numerator)//x.denominator)

def subset_cell(original,certificates):
    lower=original[0].copy();upper=original[1].copy();fixed=[]
    for cert in certificates:
        z=cert['axis'];bound=F(cert['bound'])
        if cert['sign']==1:lower[z]=max(lower[z],bound.numerator//bound.denominator)
        else:upper[z]=min(upper[z],ceil(bound))
        fixed.append({**cert,'new_lower':lower[z],'new_upper':upper[z]})
    closed=g.close(lower,upper)
    return (None if closed is None else closed[:2]),fixed

def known_direction(state,d,oracle):
    if not all(v>=0 or state[0][i]>g.SEP for i,v in enumerate(d)):return None
    data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]
    value,flow=engine.exact_upper(state,data,d)
    if value>=0:return None
    return {'kind':'correlated_direction','scalar_recipe':'correlated-v1','direction':d,'direction_scale':1,
      'upper_numerator':str(value),'denominator':str(2*g.SC*g.D*engine.DS),
      'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
      'affine_terms':sum(row[4]=='affine' for row in data),'exact_flow':flow,'lp_hint':None}

def prune(row,oracle):
    original=row['old_cell'];kept=row['certificates'].copy();state,fixed=subset_cell(original,kept)
    assert [list(v) for v in state]==row['new_cell'];result=row['result']['result'];deleted=0;attempts=0
    for cert in row['certificates']:
        candidate=[r for r in kept if r is not cert]
        if len(candidate)==len(kept):continue
        new,newcerts=subset_cell(original,candidate);attempts+=1
        if new is None:continue
        if new==state:newresult=result
        else:
            newresult=known_direction(new,result['direction'],oracle)
            if newresult is None:newresult=api.correlated_exclusion(new,oracle)
        if newresult is not None:
            kept=candidate;state=new;fixed=newcerts;result=newresult;deleted+=1
    assert kept
    state,fixed=subset_cell(original,kept)
    return {'path':row['path'],'old_cell':original,'new_cell':state,'certificates':fixed,
      'result':{'kind':'stationary','result':result},'original_bounds':len(row['certificates']),'deleted_bounds':deleted,'attempts':attempts}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--max-rows',type=int,default=1000000);ap.add_argument('--output',type=Path,default=HERE/'cover-obbt-pruned.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);oracle=api.make_correlated_oracle();rows=[];before=after=0
    selected=[r for r in doc['contractions'] if r['result'] is not None and r['result']['kind']=='stationary'][:args.max_rows]
    for n,row in enumerate(selected,1):
        result=prune(row,oracle);rows.append(result);before+=result['original_bounds'];after+=len(result['certificates'])
        if n%25==0:print(json.dumps({'rows':n,'before':before,'after':after,'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'target_numerator':doc['receipt']['target_numerator'],'api_sources':api.api_sources(oracle),'rows':len(rows),'before_bounds':before,'after_bounds':after,
      'one_bound_rows':sum(len(r['certificates'])==1 for r in rows),'two_or_fewer_bound_rows':sum(len(r['certificates'])<=2 for r in rows),
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'contractions':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
