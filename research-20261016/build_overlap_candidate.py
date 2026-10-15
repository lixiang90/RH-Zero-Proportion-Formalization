"""Package fixed rational discovery potential and exact range/outer guards.

The finite rational guards are exact. The central continuous inequality remains
UNPROVED: its 6561 local costs were obtained with numerical optimization.
"""
import hashlib,json
from fractions import Fraction as Q
from pathlib import Path

def js(q):return {'numerator':str(q.numerator),'denominator':str(q.denominator)}

def main():
    folder=Path(__file__).resolve().parent
    pa=folder/'validate_affine_potential.json';pb=folder/'ternary_potential_oracle.json'
    ra,rb=pa.read_bytes(),pb.read_bytes();a,b=json.loads(ra),json.loads(rb)
    assert b['input_potential_sha256']==hashlib.sha256(ra).hexdigest()
    assert a['core_sha256']==b['core_sha256']
    base={int(s):r for s,r in a['potential_numerators'].items()}
    delta=b['rational_delta_numerators'];den=a['denominator']
    assert den==b['rational_delta_denominator']==10**12
    ls=[Q(17,20),Q(3,2)];us=[Q(3,2),Q(5,2)];mu=[Q(26,25),Q(197,100)]
    ranges=[]
    for state in range(2187):
        word=[state//3**i%3 for i in range(7)]
        low=high=Q(delta[state],den)
        if 2 not in word:
            binary=sum(w<<i for i,w in enumerate(word));row=base.get(binary,[0]*8)
            low+=Q(row[0],den);high+=Q(row[0],den)
            for w,v in zip(word,row[1:]):
                low+=Q(v,den)*((ls[w] if v>=0 else us[w])-mu[w])
                high+=Q(v,den)*((us[w] if v>=0 else ls[w])-mu[w])
        ranges.append((low,high))
    low=min(x[0] for x in ranges);high=max(x[1] for x in ranges);osc=high-low
    B=Q(54711,12500000);bmin=Q(27156,10**8);c=Q(4299,500000)
    pressure=Q(17,20)*B+(40-Q(17,20))*bmin
    assert pressure-osc>c and osc<c
    h=Q(6721684105641188747759983512104999330646,10**40)
    out={'status':'rational DISCOVERY candidate; central all-gap inequality UNPROVED; no improved kappa claimed',
        'core_sha256':a['core_sha256'],'base_input_sha256':hashlib.sha256(ra).hexdigest(),
        'delta_input_sha256':hashlib.sha256(rb).hexdigest(),
        'state_convention':'little endian: state=sum(class(g[i])*base**i), i=0..6',
        'class_convention':'0 if g<=3/2; 1 if 3/2<g<=5/2; 2 if 5/2<g; all g>=17/20',
        'potential_formula':'delta(ternary_state) + (u(binary_state)+sum(v[i]*(g[i]-mu[class(g[i])])) if no class2, else delta(ternary_state)',
        'common_denominator':str(den),'mu':[js(q) for q in mu],
        'binary_affine_numerators':{str(s):r for s,r in base.items()},
        'ternary_constant_numerators':{str(i):v for i,v in enumerate(delta) if v},
        'potential_lower':js(low),'potential_upper':js(high),'potential_oscillation':js(osc),
        'B':js(B),'target_c':js(c),'outer_gap_cutoff':40,'outer_pressure_lower':js(pressure),
        'outer_corrected_energy_lower':js(pressure-osc),
        'conditional_counting_parameter_n':10,
        'conditional_kappa_if_all_central_boxes_certified':js((h-B)/(1-c)),
        'numerical_graph_floor':b['rational_repaired_oracle_min']}
    path=folder/'overlap_rational_candidate.json';path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'path':str(path),'nonzero_binary':len(base),'nonzero_ternary':sum(v!=0 for v in delta),
        'potential_lower':float(low),'potential_upper':float(high),'oscillation':float(osc),
        'outer_floor':float(pressure-osc),'target_c':float(c)},indent=2))

if __name__=='__main__':main()
