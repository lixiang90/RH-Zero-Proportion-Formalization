"""One static multiwindow variance-matrix diagnostic on frozen configurations.

No optimizer, new gap configuration, parameter grid, or cover.  Evaluate
the 24-mode generalized quadratic reward/penalty at the frozen 69 coherent
anchors, two archived best points, and all legal rows of two fixed sample
files.  Floating eigendata are hints, not a global or exact matrix proof.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,os,sys,time
os.environ['OPENBLAS_NUM_THREADS']='1'
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'tmp/goal-20261016/python-sdp'))
import numpy as np
OUT=HERE/'multiwindow-diagnostic.json'
K=F(34191001116882886388531117129201664,50760020691785094633026544189453125)+F(1,100000)
SEP=F(123,128)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not OUT.exists();began=time.monotonic()
    paths=[Path(__file__),ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'research-goal-20261016/cover-newwindow-gram.json',ROOT/'research-20261016-followup/window_reweight_challenge.json',
        ROOT/'research-20261016-followup/window_profile_24_challenge.json',ROOT/'research-20261016-followup/window_profile_24.npz',
        ROOT/'research-20261016/spectral-wcert-reopt-full-ternary-samples-n10.npz',
        ROOT/'StructuralGoal20261016/WindowEnergy.lean',ROOT/'StructuralGoal20261016/WindowKernel.lean',
        ROOT/'StructuralGoal20261016/WindowMatching.lean',ROOT/'StructuralGoal20261016/WindowDiscreteEnergy.lean',
        ROOT/'StructuralGoal20261016/WindowCountingBase.lean',ROOT/'StructuralW10Followup20261016/WindowMajorantGeneral.lean']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths};params=json.loads(paths[1].read_bytes());den=params['denominator']
    pairs=[(i,j) for i,j,a in params['a_upper']];a=np.array([v/den for i,j,v in params['a_upper']]);b=np.array(params['b_numerators'])/den
    incidence=np.array([[i<=r<j for r in range(9)] for i,j in pairs],float)
    mu=np.array(params['window_coefficient_numerators_1e9'])/1e9;modes=np.arange(1,25)
    theta=np.sqrt(2)/2;Z=np.sinc(theta/np.pi);e=.5-1/(4*np.pi**2*modes**2);D=e/Z**2
    H0=1.5-np.cos(theta)/Z;Hmu=H0-np.dot(D,mu*mu)
    def bases(x):return (np.sinc(x[:,None]-modes)+np.sinc(x[:,None]+modes))/(2*Z)
    def inspect(g):
        x=incidence@g;U=bases(x);base=(np.sinc(x+theta/np.pi)+np.sinc(x-theta/np.pi))/(2*Z);kernel=base+U@mu
        Q=(U.T*a)@U;normalized=Q/np.sqrt(D[:,None]*D[None,:]);ev,vec=np.linalg.eigh(normalized)
        direction=vec[:,-1]/np.sqrt(D);direction/=np.max(np.abs(direction))
        floor=float(a@(kernel*kernel)+b@g)
        return {'energy_current_ledger_hint':floor,'current_frame_ratio_percent_hint':100*(Hmu-b.sum())/(1-floor),
            'maximum_generalized_reward_over_penalty_hint':float(ev[-1]),'maximum_target_variance_margin_hint':float(float(K)*ev[-1]-1),
            'largest_generalized_direction_hint':direction.tolist()}
    coherent=json.loads(paths[2].read_bytes())['results'];records=[]
    for k,row in enumerate(coherent):
        exact=list(map(F,row['anchor']));g=np.array(list(map(float,exact)));assert all(z>=SEP for z in exact)
        records.append({'source':'coherent_anchor','index':k,'integer_gaps':row['integer_gaps'],'gaps':list(map(str,exact)),**inspect(g)})
    for p in paths[3:5]:
        doc=json.loads(p.read_bytes());exact=[F(str(v)) for v in doc['best_gaps']];assert all(z>=SEP for z in exact)
        records.append({'source':p.relative_to(ROOT).as_posix(),'gaps':list(map(str,exact)),**inspect(np.array(list(map(float,exact))))})
    summaries=[]
    for p in paths[5:7]:
        allg=np.load(p)['gaps'];mask=np.all(allg>=float(SEP),axis=1);gaps=allg[mask];maxima=[];energies=[];best=None
        # Each configuration is exactly one existing row; illegal rows are
        # dropped, never clipped or perturbed into newly sampled points.
        for k,g in zip(np.flatnonzero(mask),gaps):
            row=inspect(g);margin=row['maximum_target_variance_margin_hint'];maxima.append(margin);energies.append(row['energy_current_ledger_hint'])
            if best is None or row['energy_current_ledger_hint']<best['energy_current_ledger_hint']:
                best={'source_row':int(k),'gaps':g.tolist(),**row}
        maxima=np.array(maxima);energies=np.array(energies);order=np.argsort(energies)[:min(100,len(gaps))]
        summaries.append({'source':p.relative_to(ROOT).as_posix(),'original_rows':len(allg),'legal_rows':len(gaps),'discarded_illegal_rows':int(np.sum(~mask)),
            'target_variance_margin_quantiles_hint':np.quantile(maxima,[0,.25,.5,.75,1]).tolist(),
            'strictly_negative_margin_count_hint':int(np.sum(maxima<0)),'positive_margin_count_hint':int(np.sum(maxima>0)),
            'lowest_100_energy_margin_range_hint':[float(np.min(maxima[order])),float(np.max(maxima[order]))],
            'lowest_energy_row':best})
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    minframe=min(records,key=lambda r:r['energy_current_ledger_hint'])
    out={'scope':__doc__,'status':'static_existing_frame_variance_diagnostic_only','source_sha256_start':pins,'source_sha256_end':final,
        'all_sources_unchanged':True,'target':str(K),'separation':str(SEP),'modes':24,
        'profile_mean_coefficients':list(map(str,[F(v,10**9) for v in params['window_coefficient_numerators_1e9']])),
        'profile_mean_l1':str(sum(F(abs(v),10**9) for v in params['window_coefficient_numerators_1e9'])),
        'profile_l1_budget':'2/25','H_mean_hint':Hmu,'normalization_Z_hint':Z,
        'matrix_meaning':'Q=sum_e a_e baseq(s_e(g))*baseq(s_e(g))^T; D=diag((1/2-1/(4*pi^2*j^2))/Z^2); margin=lambda_max(K*D^-1/2*Q*D^-1/2-I)',
        'coherent_and_archived_point_diagnostics':records,'fixed_sample_diagnostics':summaries,'lowest_explicit_energy_frame':minframe,
        'optimizer_calls':0,'Lean_invocations':0,'new_gap_configurations':0,'new_zero_proportion_proven':False,
        'global_variance_no_go_proven':False,'different_ledger_route_excluded':False,'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':out['status'],'explicit_frames':len(records),'coherent_margin_range_hint':[
        min(r['maximum_target_variance_margin_hint'] for r in records),max(r['maximum_target_variance_margin_hint'] for r in records)],
        'sample_summaries':[{k:r[k] for k in ['source','legal_rows','lowest_100_energy_margin_range_hint']} for r in summaries],
        'lowest_frame_energy_hint':minframe['energy_current_ledger_hint'],'lowest_frame_margin_hint':minframe['maximum_target_variance_margin_hint'],
        'elapsed_milliseconds':out['elapsed_milliseconds']}),flush=True)


if __name__=='__main__':main()
