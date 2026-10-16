"""Measure support point redundancy relative to a common LP primal anchor."""
from pathlib import Path
import collections,json,math,time
import numpy as np
import latent_probe as p
import relative_codec as codec
g=p.g

def main():
    here=Path(__file__).parent;doc=json.loads((here/'ordered-0.json').read_text())
    rows=[z for z in doc['accepted'] if 'FS' in z['result']];rows=[rows[i] for i in np.linspace(0,len(rows)-1,100,dtype=int)]
    out=[];delta=collections.Counter();start=time.monotonic()
    for row in rows:
        r=row['result'];lo=r['certificate']['lower_bounds'];hi=r['certificate']['upper_bounds']
        packed=codec.prepare(r,rounds=4)
        r={**r,'FS':packed['FS']}
        saved=g.TARGET
        try:g.TARGET=10**100;rec=g.certify((lo,hi))
        finally:g.TARGET=saved
        anchor=[round(v*g.SC/32)*32 for v in rec['gaps']]
        near,_=p.supports(anchor,lo,hi);fs=[];points=0;extra=0
        for (i,j,a),old,new in zip(g.TERMS,r['FS'],near):
            k,m,pp,rr=old;w1,w2=g.f.weights(k,m)
            for mass,point in [(w1,pp),(w2,rr)]:
                if mass:
                    dd=(point-sum(anchor[i:j]))//32;delta[dd]+=1;points+=1
                    extra+=1+2*(abs(dd)+1).bit_length()
            if k==3 and new[0]==3:
                if pp>rr:m=1024-m
                fs.append([3,m,new[2],new[3]])
            elif k in [1,2]:
                options=[v for v in [new[2],new[3]] if v]
                if options:
                    nearest=min(options,key=lambda v:abs(v-pp));fs.append([k,m,nearest,0])
                else:fs.append(old)
            else:fs.append(old)
        num,code=p.replay(fs,lo,hi)
        out.append({'path':row['path'],'passed_with_old_mixture':num>=g.TARGET,'points':points,'signed_gamma_delta_bits':extra,'relative_bits':packed['support_bits'],
                    'anchor_bits':sum((u-l).bit_length() for l,u in zip(lo[:9],hi[:9]))-45})
    report={'scope':__doc__,'processed':len(rows),'passed_with_old_mixture':sum(r['passed_with_old_mixture'] for r in out),
        'point_delta_counts':sorted(delta.items()),'within_1':sum(c for d,c in delta.items() if abs(d)<=1),
        'total_points':sum(delta.values()),'average_anchor_bits':sum(r['anchor_bits'] for r in out)/len(out),
        'average_delta_bits':sum(r['signed_gamma_delta_bits'] for r in out)/len(out),'average_relative_bits':sum(r['relative_bits'] for r in out)/len(out),'seconds':time.monotonic()-start}
    (here/'lp-point-delta-thin-probe.json').write_text(json.dumps({'stats':report,'leaves':out},indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='point_delta_counts'}))
if __name__=='__main__':main()
