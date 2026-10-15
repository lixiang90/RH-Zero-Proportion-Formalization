"""Build an exactly feasible rational Fenchel witness; it is not a global gap certificate."""
import importlib.util
import json
from pathlib import Path
import numpy as np

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('spectral_defect_frames',HERE/'spectral_defect_frames.py')
base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
report=json.loads((HERE/'spectral-defect-frames-deep.json').read_text())
result=report['results'][-1]
g=np.array(result['history'][-1]['adversarial_gaps']);n=len(g)+1
x=np.r_[0,np.cumsum(g)];G=base.kernel(x[None,:]-x[:,None])
eigen,u=np.linalg.eigh(G)
S=(u*np.minimum(2*(eigen-1),2))@u.T
den=10**6
integer=np.rint(S*den).astype(np.int64)
integer=(integer+integer.T)//2
M=2*den*np.eye(n,dtype=np.int64)-integer
row_margins=np.diag(M)-(np.sum(np.abs(M),axis=1)-np.abs(np.diag(M)))
assert np.all(row_margins>=0), row_margins.min()
# For each i<j, |M_ij|(e_i+sign(M_ij)e_j)(...)^T plus the nonnegative
# row residual on e_i e_i^T sums exactly to M: an exact integer PSD proof.
reconstructed=np.diag(row_margins.copy())
for i in range(n):
    for j in range(i+1,n):
        value=int(M[i,j])
        if value:
            v=np.zeros(n,dtype=np.int64);v[i]=1;v[j]=1 if value>0 else -1
            reconstructed += abs(value)*np.outer(v,v)
assert np.array_equal(M,reconstructed)
S=integer/den
def plane(gaps):
    points=np.r_[0,np.cumsum(gaps)]
    gram=base.kernel(points[None,:]-points[:,None])
    return float(np.sum(S*(gram-np.eye(n)))-np.sum(S*S)/4)/n
at=plane(g);exact=base.defect(g)
rng=np.random.default_rng(20261016)
residuals=[base.defect(test)-plane(test) for test in [rng.uniform(0,2,n-1) for _ in range(100)]]
record={'scope':'One supporting plane, with exact integer diagonal-dominance PSD decomposition; no global minimum',
    'n':n,'witness_gaps':g.tolist(),'denominator':den,'S_integer':integer.tolist(),
    'two_I_minus_S_diagonal_dominance_margins_integer':row_margins.tolist(),
    'exact_integer_PSD_decomposition_verified':True,'minimum_margin_scaled':float(row_margins.min()/den),
    'gram_eigenvalue_min':float(eigen.min()),'gram_eigenvalue_max':float(eigen.max()),
    'defect_per_point':exact,'Fenchel_plane_per_point':at,'rounding_gap':exact-at,
    'entrywise_error_constant_per_point':float(np.sum(np.abs(S))/n),
    'random_sanity_checks':len(residuals),'minimum_random_defect_minus_plane':float(min(residuals))}
(HERE/'spectral-dual-witness.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['S_integer','witness_gaps','two_I_minus_S_diagonal_dominance_margins_integer']},indent=2))
