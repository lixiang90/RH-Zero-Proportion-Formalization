"""Portable, read-only verifier for the frozen arbitrary-block embedding dual.

Normalizes the Windows separators in the original discovery input map.
The already published producer, dual, and replay bytes remain unchanged.
No solver, producer import, or original receipt overwrite is permitted.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import argparse,ast,hashlib,json,re

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def read(path):
    text=path.read_text(encoding='utf8')
    def nat(name):return int(re.search(r'^def '+name+r' : ℕ := (\d+)\s*$',text,re.M)[1])
    def lit(name):return ast.literal_eval(re.search(r'^def '+name+r' : List[^\n]* := (\[[^\n]*\])\s*$',text,re.M)[1])
    den=nat('SA');b=[F(v,den) for v in lit('BS')]
    a=[(i,j,F(v,den)) for i,j,v,_ in lit('TS')]
    assert len(b)==8 and len(a)==34 and min(b)>0
    assert all(0<=i<j<9 and v>=0 for i,j,v in a)
    assert '∀ g : Fin 8 → ℝ, (∀ i, 0 ≤ g i) →' in re.search(r'^theorem cert_AM :[^\n]+',text,re.M)[0]
    cs=re.search(r'^def cAMn[^\n]*\n(.*?)^def cAM ',text,re.M|re.S)[1]
    return a,b,F(nat('cN'),den),dict(re.findall(r'\| (\d+) => (-?\d+)',cs))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path,help='Write a new verification receipt only if absent.')
    args=parser.parse_args()
    manifest=HERE/'window-large-embedding-files.json';m=json.loads(manifest.read_bytes())
    assert sha(manifest)=='0c9805d8f2a134b9c8df61d2c4cacffc03799e99d3a3f02f78e618d97e50ebc2'
    for row in m['files']+m['dependencies']:
        p=ROOT/row['path'].replace('\\','/')
        assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
    pilotpath=HERE/'window-large-embedding-pilot.json';proofpath=HERE/'window-large-embedding-replay.json'
    pilot=json.loads(pilotpath.read_bytes());proof=json.loads(proofpath.read_bytes())
    for name,digest in pilot['inputs_sha256'].items():assert sha(ROOT/name.replace('\\','/'))==digest
    y=list(map(F,proof['rank_dual_with_zero_tail']));assert len(y)==16 and min(y)>=0
    K=F(proof['target']);H=F(proof['fixed_H'])
    assert K==F(34191001116882886388531117129201664,50760020691785094633026544189453125)+F(1,100000)
    sources=[ROOT/'GramDefect20261015/Core.lean',ROOT/'research-20261016-w10-cert/current-record-source.txt']
    families=list(map(read,sources));assert families[0][3]==families[1][3]
    minima=[];outside=[];count=0
    for a,b,c,_ in families:
        tail_margin=sum(b)+9*min(b)-K*c;assert tail_margin>0;outside.append(tail_margin)
        for rest in combinations(range(1,17),8):
            vertices=(0,)+rest
            payment=sum(weight*y[vertices[j]-vertices[i]-1] for i,j,weight in a)
            pressure=sum(b[i]*(vertices[i+1]-vertices[i]) for i in range(8))
            slack=payment-(K*c-pressure);assert slack>=0
            minima.append(slack);count+=1
    gap=K-H-2*sum(y)
    assert count==25740 and gap==F(proof['strict_goal_shortfall'])>0
    assert min(minima)==F(proof['minimum_finite_column_slack'])
    assert outside==[F(row['strict_negative_profit_margin']) for row in proof['all_omitted_columns_paid_by_pressure']]
    out={'scope':__doc__,'passed':True,'finite_columns_checked':count,
         'all_larger_blocks_covered_by_pressure':True,'strict_goal_shortfall':str(gap),
         'inputs_sha256':{str(p.relative_to(ROOT)).replace('\\','/'):sha(p)
            for p in [Path(__file__),manifest,pilotpath,proofpath]+sources},
         'frozen_original_bytes_unchanged':True,'numerical_solver_used':False,
         'new_zero_proportion_proven':False}
    if args.receipt:
        with args.receipt.open('x',encoding='utf8') as f:f.write(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,ensure_ascii=False))

if __name__=='__main__':main()
