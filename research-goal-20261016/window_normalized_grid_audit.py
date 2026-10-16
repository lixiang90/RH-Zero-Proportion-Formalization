"""Check the original quantized KKT grid with elementary normalized jets.

The extremely narrow discovery coefficient intervals need not themselves be
proved. This tests the final outward-rounded derivative grid and third-
derivative payments directly with the coarser, Lean-friendly input recipe.
The actual coefficient consumer still requires a separate Lean proof.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,json,time
import window_normalized_interval as normalized
import cover_correlated_replay as independent
I=normalized.I;HERE=Path(__file__).resolve().parent

def main():
    start=time.monotonic();path=HERE/'window_normalized_interval.json';doc=json.loads(path.read_bytes())
    oldpath=HERE/'cover_newjet.json';old=json.loads(oldpath.read_bytes());oldscalar=independent.ScalarReplay(old)
    cs={int(n):[I(F(l),F(u)) for l,u in values] for n,values in doc['integer_w_Taylor_coefficients'].items()}
    M=F(44,7)**24;ed=M*F(1,2)**23/factorial(23);e3=M*F(1,2)**21/factorial(21);DS=10**15
    failed=[];thirdfailed=[];minimum_margin=None
    relevant_minimum_cell=(F(123,128)*64).__floor__()
    for k,(dl,du) in enumerate(old['ranges']):
        n=round(F(2*k+1,128));x=I(F(k,64)-n,F(k+1,64)-n)
        d=I(0);third=I(0)
        for j in range(22,-1,-1):d=d*x+cs[n][j+1]*(j+1)
        for j in range(20,-1,-1):third=third*x+cs[n][j+3]*((j+1)*(j+2)*(j+3))
        lower,upper=d.l-ed,d.u+ed
        margin=min(lower-F(dl,DS),F(du,DS)-upper)
        minimum_margin=margin if minimum_margin is None else min(minimum_margin,margin)
        if margin<0:failed.append({'cell':k,'old':[dl,du],'new_interval':[str(lower),str(upper)]})
        oldbound=oldscalar.third[k]
        newbound=max(abs(third.l-e3),abs(third.u+e3))
        if newbound>F(oldbound,DS):thirdfailed.append({'cell':k,'old_bound':oldbound,'new_bound':str(newbound)})
    out={'scope':__doc__,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'normalized_input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'discovery_grid_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),
      'grid_cells_checked':len(old['ranges']),'failed_derivative_cells':failed,'failed_third_bound_cells':thirdfailed,
      'all_original_derivative_grid_bounds_preserved':not failed,'all_original_third_derivative_bounds_preserved':not thirdfailed,
      'relevant_minimum_cell':relevant_minimum_cell,'actual_gap_separation':'123/128',
      'all_derivative_bounds_used_by_separated_cells_preserved':not any(r['cell']>=relevant_minimum_cell for r in failed),
      'all_third_bounds_used_by_separated_cells_preserved':not any(r['cell']>=relevant_minimum_cell for r in thirdfailed),
      'minimum_derivative_grid_margin':str(minimum_margin),'actual_Lean_consumer_proven':False,
      'global_floor_proven':False,'seconds':time.monotonic()-start}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['grid_cells_checked','all_derivative_bounds_used_by_separated_cells_preserved','all_third_bounds_used_by_separated_cells_preserved','seconds']}))
    print(json.dumps({'derivative_failures':len(failed),'third_bound_failures':len(thirdfailed)}))
if __name__=='__main__':main()
