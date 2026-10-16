"""Standard-library-only exact dual replay for the ten-embedding ledger class."""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json

HERE=Path(__file__).resolve().parent

def main():
    source=HERE/'window-embedded-old-ledger-pilot.json';proof=HERE/'window-embedded-old-ledger-dual.json'
    d=json.loads(source.read_bytes());p=json.loads(proof.read_bytes())
    assert hashlib.sha256(source.read_bytes()).hexdigest()==p['source_sha256']
    c=F(d['old_floor']);H=F(d['old_window_H']);K=F(d['target_kappa'])
    A=[[F(col['rank_masses'][s]) for col in d['embeddings']] for s in range(9)]
    y=list(map(F,p['nonnegative_rational_dual']));assert len(y)==9 and all(v>=0 for v in y)
    slacks=[sum(A[s][j]*y[s] for s in range(9))-(K*c-sum(map(F,col['pressure'])))
        for j,col in enumerate(d['embeddings'])]
    assert all(v>=0 for v in slacks) and list(map(str,slacks))==p['exact_ten_column_slacks']
    # All columns have the same total pair mass, so the capacity constraints
    # also imply a positive counting denominator for every possible mixture.
    masses=[sum(A[s][j] for s in range(9)) for j in range(10)]
    assert masses==[masses[0]]*10 and masses[0]>0
    c_upper=c*18/masses[0];assert c_upper<1
    gap=K-H-2*sum(y);assert gap>0 and gap==F(p['strict_shortfall'])
    out={'scope':__doc__,'passed':True,'columns':10,'rank_constraints':9,
        'positive_denominator_proven':True,'local_floor_upper_from_capacities':str(c_upper),
        'strict_goal_shortfall':str(gap),'uses_numerical_solver':False,
        'pilot_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'dual_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),
        'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'new_zero_proportion_proven':False}
    output=HERE/'window-embedded-old-ledger-replay.json';assert not output.exists()
    output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out))

if __name__=='__main__':main()
