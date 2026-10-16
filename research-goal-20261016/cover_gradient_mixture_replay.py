"""Stdlib-only replay of finite feasible points and floating kernel diagnostics.

This checks rational DBM feasibility exactly and recomputes actual sinc
values/derivatives with an independent math implementation. Floating
comparisons do not certify hull infeasibility or uniform cell separation.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip, hashlib, json, math, time
HERE=Path(__file__).parent; ROOT=HERE.parent; SC=32768; D=10**10
PAIRS=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
sha=lambda b:hashlib.sha256(b).hexdigest()


def sinc(x):
    if abs(x)<1e-4:
        z=math.pi*x;return 1-z*z/6+z**4/120-z**6/5040
    return math.sin(math.pi*x)/(math.pi*x)


def sincprime(x):
    if abs(x)<1e-4:return -math.pi**2*x/3+math.pi**4*x**3/30-math.pi**6*x**5/840
    return (math.pi*x*math.cos(math.pi*x)-math.sin(math.pi*x))/(math.pi*x*x)


def evaluate(point,params):
    d=[1.]+[x/10**9 for x in params['window_coefficient_numerators_1e9']]
    theta=math.sqrt(2)/2;Z=math.sin(theta)/theta;freq=[theta/math.pi]+list(range(1,25))
    gaps=[float(x/SC) for x in point];gradient=[b/D for b in params['b_numerators']];energy=sum(b*x for b,x in zip(gradient,gaps))
    for i,j,a in params['a_upper']:
        if not a:continue
        x=sum(gaps[i:j]);k=sum(c*(sinc(x+f)+sinc(x-f)) for c,f in zip(d,freq))/(2*Z)
        kp=sum(c*(sincprime(x+f)+sincprime(x-f)) for c,f in zip(d,freq))/(2*Z)
        energy+=a/D*k*k
        for r in range(i,j):gradient[r]+=a/D*2*k*kp
    return energy,gradient


def main():
    start=time.monotonic(); raw=(HERE/'cover-gradient-mixture.json').read_bytes();doc=json.loads(raw)
    source_raw=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes(); assert sha(source_raw)==doc['receipt']['input_sha256']
    source=json.loads(gzip.decompress(source_raw));lookup={r['path']:r for r in source['cases']}
    param_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();assert sha(param_raw)==doc['receipt']['parameters_sha256'];params=json.loads(param_raw)
    count=0;max_e=max_g=0.;rows=[]
    for row in doc['rows']:
        state=lookup[row['path']]['before'];assert state==row['cell'];points=[tuple(map(F,p)) for p in row['sample_points_gap_units']]
        assert len(points)<=128 and len(points)==len(set(points));energies=[];gradients=[]
        for n,point in enumerate(points):
            assert len(point)==9 and all(l<=sum(point[i:j])<=u for (i,j),l,u in zip(PAIRS,*state))
            energy,gradient=evaluate(point,params);energies.append(energy);gradients.append(gradient)
            e=abs(energy-row['sample_energies_hint'][n]); gg=max(abs(a-b) for a,b in zip(gradient,row['sample_gradients_hint'][n]));assert e<1e-12 and gg<1e-10
            max_e=max(max_e,e);max_g=max(max_g,gg);count+=1
        nearest=row.get('nearest_gradient_mixture_hint');assert nearest is not None
        selected=nearest['selected_indices'];weights=nearest['weights'];assert len(selected)==len(weights) and all(w>0 for w in weights) and abs(sum(weights)-1)<1e-8
        grad=[sum(w*gradients[n][i] for n,w in zip(selected,weights)) for i in range(9)];energy=sum(w*energies[n] for n,w in zip(selected,weights))
        assert max(abs(a-b) for a,b in zip(grad,nearest['weighted_gradient_hint']))<1e-10
        assert abs(sum(map(abs,grad))-nearest['L1_gradient_residual_hint'])<1e-9 and abs(energy-nearest['weighted_energy_hint'])<1e-12
        direction=nearest['separating_direction_hint'];dots=[sum(a*b for a,b in zip(direction,gr)) for gr in gradients]
        assert abs(min(dots)-nearest['minimum_sample_directional_derivative_hint'])<1e-10
        assert min(dots)>0 and min(energies)>.0088
        rows.append({'path':row['path'],'points_checked':len(points),'minimum_sample_energy_hint':min(energies),
          'nearest_mixture_energy_hint':energy,'nearest_mixture_gradient_L1_hint':sum(map(abs,grad)),
          'minimum_sample_directional_derivative_hint':min(dots)})
    # Check the two unsuccessful whole-cell bounds as arithmetic bounds,
    # with no strict-sign acceptance assertion borrowed from a leaf checker.
    import cover_correlated_replay as derivative
    direction_raw=(HERE/'cover-gradient-mixture-direction.json').read_bytes();direction_doc=json.loads(direction_raw)
    assert direction_doc['receipt']['input_sha256']==sha(raw)
    table_raw=(HERE/'cover_newjet.json').read_bytes();assert sha(table_raw)==direction_doc['receipt']['derivative_table_sha256']
    scalar=derivative.ScalarReplay(json.loads(table_raw));direction_rows=[]; DS=10**15; terms=[t for t in params['a_upper'] if t[2]]
    for item in direction_doc['rows']:
        state=lookup[item['path']]['before'];assert state==item['cell']; derivative.a.closure_valid(state)
        d=item['negative_direction'];assert d==[-v for v in item['positive_sample_separating_direction']]
        assert all(x>=0 or state[0][i]>123*SC//128 for i,x in enumerate(d))
        data=[scalar.check(state[0][PAIRS.index((i,j))],state[1][PAIRS.index((i,j))],r) for (i,j,a),r in zip(terms,item['scalar_affine_data'])]
        const=2*SC*sum(b*DS*x for b,x in zip(params['b_numerators'],d));error=0;coeff=[0]*9
        for (i,j,a),(P,m0,m1,err,kind) in zip(terms,data):
            c=sum(d[i:j]);const+=a*c*(2*SC*m0-m1*P);error+=2*SC*a*abs(c)*err
            for r in range(i,j):coeff[r]+=2*a*c*m1
        recorded=item['exact_flow'];assert const==int(recorded['constant']) and error==int(recorded['error']) and coeff==list(map(int,recorded['coefficient']))
        desired=[coeff[0]]+[coeff[i]-coeff[i-1] for i in range(1,9)]+[-coeff[8]];balance=[0]*10;cost=0
        for i,j,y,u in recorded['flow']['nonzero_flow']:
            y=int(y);assert y>=0 and i!=j and u==derivative.a.edge_value(state,i,j);balance[i]+=y;balance[j]-=y;cost+=y*u
        assert balance==desired==list(map(int,recorded['flow']['divergence']))
        assert cost==int(recorded['flow']['cost']) and -cost==int(recorded['negative_maximum'])
        upper=const+error+cost;assert upper==int(item['upper_numerator'])
        lower=F(-upper,2*SC*D*DS*item['direction_scale']);assert lower==F(item['correlated_whole_cell_lower'])<=0
        grid=sum(b*v*DS for b,v in zip(params['b_numerators'],item['positive_sample_separating_direction']))
        for i,j,a in terms:
            z=PAIRS.index((i,j));l,u=scalar.derivative_range(state[0][z],state[1][z]);c=sum(item['positive_sample_separating_direction'][i:j]);grid+=a*c*(l if c>=0 else u)
        assert F(grid,D*DS*item['direction_scale'])==F(item['interval_only_whole_cell_lower'])
        direction_rows.append({'path':item['path'],'correlated_whole_cell_lower':str(lower),'strict_exclusion':False})
    out={'scope':__doc__,'passed':True,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),
      'parent64_input_sha256':sha(source_raw),'parameters_sha256':sha(param_raw),'exact_rational_DBM_points_checked':count,
      'maximum_independent_energy_float_difference':max_e,'maximum_independent_gradient_float_difference':max_g,
      'origin_in_actual_gradient_hull_proven':False,'finite_sample_hull_infeasibility_exactly_proven':False,
      'whole_cell_gradient_separation_proven':False,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'direction_probe_sha256':sha(direction_raw),'derivative_table_sha256':sha(table_raw),'exact_directional_bounds_checked':len(direction_rows),
      'directional_bounds':direction_rows,'rows':rows,'seconds':time.monotonic()-start}
    (HERE/'cover-gradient-mixture-replay.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
