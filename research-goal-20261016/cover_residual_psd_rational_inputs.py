"""Freeze exact old-row ingredients for stdlib replay of the rational point.

This regenerates only the immutable model ingredients, with no solver or
change to the projected moments. The full row fingerprint must match the
already completed rational projection attempt before anything is written.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,json,time
import cover_cross_moment_probe as base
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;ROOT=HERE.parent;SC=32768

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    started=time.monotonic();proofpath=HERE/'cover-residual-psd-rational-projection.json';priorpath=HERE/'cover-cross-moment-remaining-six.json'
    closedpath=HERE/'cover-bregman-closed-primal-check.json';table=HERE/'cover_newjet.json'
    watch=[proofpath,priorpath,closedpath,table,Path(__file__),Path(base.__file__),Path(base.old.__file__),Path(exact.__file__),base.g.PAR]
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in watch}
    proof=json.loads(proofpath.read_text());assert proof['status']=='strict_exact_feasible_relaxation_point'
    prior=json.loads(priorpath.read_text())['rows'][0];state=tuple(prior['cell']);closed=json.loads(closedpath.read_text())
    taylor=base.old.context.curvature.first.TaylorOracle(table);graph=base.old.GraphOracle(table)
    rr,bb,integer,meta,data,obj,stats=base.old.build(state,taylor,graph,True);ubounds=[]
    for i,j,aw in base.g.TERMS:
        z=base.g.LOOK[i,j];ff,_=graph.facets(state[0][z],state[1][z])
        ubounds.append((max(F(C,SC*base.old.DS) for sign,S,C in ff if sign==-1 and S==0),
            min(F(C,SC*base.old.DS) for sign,S,C in ff if sign==1 and S==0)))
    packets=[prior['energy_packets'][0],closed['proposed_KKT_energy_packet']]
    model=exact.inputs(state,integer,meta,ubounds,packets);digest=hashlib.sha256()
    for row in model['rows']:digest.update(json.dumps([sorted((i,str(v)) for i,v in row['coeff'].items()),str(row['bound']),row['meta']],separators=(',',':')).encode())
    assert digest.hexdigest()==proof['retained_row_serialization_sha256']
    result={'scope':__doc__,'input_sha256_start':initial,'path':prior['path'],'cell':prior['cell'],
        'old_integer_rows':[[list(ag),list(au),str(B)] for ag,au,B in integer],'old_meta':meta,
        'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
        'u_bounds':[[str(l),str(u)] for l,u in ubounds],'energy_packets':packets,
        'all_464_box_bounds':[[str(l),str(u)] for l,u in model['bounds']],
        'retained_rows':len(model['rows']),'retained_row_serialization_sha256':digest.hexdigest(),
        'scope_of_feasibility':'finite outer relaxation only; not actual Fw'}
    final={p.relative_to(ROOT).as_posix():sha(p) for p in watch};assert initial==final;result['input_sha256_end']=final;result['inputs_unchanged']='yes'
    result['elapsed_milliseconds']=int((time.monotonic()-started)*1000);path=HERE/'cover-residual-psd-rational-inputs.json';assert not path.exists()
    path.write_text(json.dumps(result,separators=(',',':'),allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'retained_rows':len(model['rows']),'old_rows':len(integer),'bytes':path.stat().st_size,'elapsed_milliseconds':result['elapsed_milliseconds']}),flush=True)

if __name__=='__main__':main()
