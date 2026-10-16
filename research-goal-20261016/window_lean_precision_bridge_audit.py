"""Check frozen scalar certificates against elementary-input integer jets.

This finite audit removes any numerical need for 70-digit Machin bounds:
the same Gram constants remain valid with the enclosures explicitly stated
in WindowBasicEnclosures.lean. Formal jet/arithmetic consumers are separate.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import functools,hashlib,json,time
import window_interval_kernel as ik
HERE=Path(__file__).resolve().parent
I=ik.I

def main():
    start=time.monotonic();jet_path=HERE/'window_lean_precision_probe.json';gram_path=HERE/'cover-newwindow-gram.json'
    jets=json.loads(jet_path.read_bytes());gram=json.loads(gram_path.read_bytes())
    assert jets['all_original_curvatures_preserved']
    integers={int(n):[I(F(l),F(u)) for l,u in row] for n,row in jets['integer_w_jets'].items()}
    @functools.lru_cache(None)
    def point(p):
        n=round(p);x=p-n;jet=integers[n]
        value=I(0);derivative=I(0)
        for j in range(23,-1,-1):value=value*x+jet[j]*F(1,factorial(j))
        for j in range(22,-1,-1):derivative=derivative*x+jet[j+1]*F(1,factorial(j))
        ev=F(44,7)**24*abs(x)**24/factorial(24)
        ed=F(44,7)**24*abs(x)**23/factorial(23)
        return I(value.l-ev,value.u+ev),I(derivative.l-ed,derivative.u+ed)
    results=[];value_margin=None;slope_margin=None
    for k,row in enumerate(gram['results']):
        for s in row['scalar_minorants']:
            p=F(s['anchor']);n=s['integer_center'];v,d=point(p)
            vm=v.l-F(s['value_lower'])
            loss=F(s['slope_error_loss']);slope=F(s['slope']);radius=F(21,100)+abs(p-n)
            sm=loss-max(abs(d.l-slope),abs(d.u-slope))*radius
            assert vm>=0 and sm>=0,(k,s['pair'],str(vm),str(sm))
            value_margin=vm if value_margin is None else min(value_margin,vm)
            slope_margin=sm if slope_margin is None else min(slope_margin,sm)
            results.append({'basin':k,'pair':s['pair'],'value_margin':str(vm),'slope_loss_margin':str(sm)})
    out={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'integer_jet_input_sha256':hashlib.sha256(jet_path.read_bytes()).hexdigest(),
      'Gram_input_sha256':hashlib.sha256(gram_path.read_bytes()).hexdigest(),
      'scalar_minorants_checked':len(results),'basins_checked':len(gram['results']),
      'all_original_curvature_constants_preserved':True,'all_original_scalar_constants_preserved':True,
      'minimum_value_margin':str(value_margin),'minimum_slope_loss_margin':str(slope_margin),
      'unique_points':point.cache_info().currsize,'actual_jet_Lean_connection_proven':False,
      'global_floor_proven':False,'seconds':time.monotonic()-start,'results':results}
    target=Path(__file__).with_suffix('.json');target.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['scalar_minorants_checked','basins_checked','all_original_scalar_constants_preserved','unique_points','seconds']}))
if __name__=='__main__':main()
