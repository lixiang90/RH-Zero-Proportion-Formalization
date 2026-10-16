"""Rebuild the main ancestry and verify the targeted actual-ledger curvature bound."""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,time
import cover_compact_codec as c
import cover_sublevel_obbt_verify as obbt
import cover_contractor_verify as newton
import cover_correlated_curvature_verify as curve
from cover_correlated_replay import SC,a
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    start=time.monotonic();folder=HERE/'cover-targeted-curvature-evidence';hraw=(folder/'manifest.json').read_bytes();header=json.loads(hraw)
    for p,digest in header['sources'].items():assert sha((ROOT/p).read_bytes())==digest,p
    packed=(folder/header['file']).read_bytes();assert sha(packed)==header['sha256'] and len(packed)==header['bytes']
    raw=gzip.decompress(packed);assert sha(raw)==header['uncompressed_sha256'];doc=json.loads(raw)
    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes());bs=params['b_numerators'];sep=123*SC//128
    cn=F(doc['target'])*10**10;assert cn.denominator==1;budget=int(cn)*SC-sum(bs)*sep;up=[sep+c.ceil(F(budget,b)) for b in bs]
    state=[[(j-i)*sep for i,j in a.PAIRS],[min(sum(up[i:j]),(j-i)*sep+c.ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]]
    assert state==doc['root'];checker=curve.CurvatureReplay(json.loads((HERE/'cover_newjet.json').read_bytes()));target=F(doc['target'])*obbt.shared.g.DEN;assert target.denominator==1;target=target.numerator
    p='r';bounds=steps=0
    for bit in doc['path'][1:]:
        if p in doc['ancestor_OBBT']:
            step=c.unpack_obbt(state,doc['ancestor_OBBT'][p],target,obbt.shared.w);obbt.verify({**step,'result':None},target,checker.scalar)
            bounds+=len(step['certificates']);state=step['new_cell']
        for packedstep in doc['ancestor_Newton'].get(p,[]):
            step=c.unpack_newton(state,packedstep,obbt.shared.w);state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        b=doc['ancestor_branches'][p];z=b['axis'];cut=b['cut'];assert state[0][z]<cut<state[1][z]
        state=a.child(state,z,cut,bit=='0');assert state is not None;p+=bit
    assert p==doc['path'] and state==doc['cell'];result=curve.verify(state,doc['curvature'],params,checker)
    out={'scope':__doc__,'manifest_sha256':sha(hraw),'script_sha256':sha(Path(__file__).read_bytes()),'all_passed':True,
      'path':p,'ancestor_nodes':len(doc['ancestor_branches']),'prior_OBBT_bounds':bounds,'prior_Newton_steps':steps,**result,
      'reported_source_descendant_branches':len(doc['reported_descendant_branches']),'descendant_contractions_replayed':False,
      'original_large_checkpoint_required':False,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (folder/'independent-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
