"""Rational graph facets for actual sin/cos phases of the shared gap spans.

Each rectangle is enclosed at its two rational endpoints and all interior
sine extrema, after exact period reduction. Integer slopes are selected
from the hull; every intercept is then recomputed over every rectangle.
This new analytic interface has not been proved in Lean. It supplies
research LP rows, not an accepted exclusion or zero-proportion bound.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import argparse,gzip,hashlib,json,time
import window_interval_kernel as ik

SC=32768
DS=10**15
STEP=SC//64
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def floor(x):
    x=F(x)
    return x.numerator//x.denominator

def ceil(x):
    return -floor(-F(x))

@lru_cache(None)
def sinpi_point(x):
    x=F(x)
    q=x-2*floor((x+1)/2)
    if q in (F(-1),F(0),F(1)):
        return F(0),F(0)
    if q==F(1,2):
        return F(1),F(1)
    if q==F(-1,2):
        return F(-1),F(-1)
    v=ik.interval.sin_interval(ik.PI*q)
    lower,upper=max(F(-1),v.l),min(F(1),v.u)
    assert lower<=upper
    return lower,upper

@lru_cache(None)
def sinpi_range(l,u):
    l,u=F(l),F(u)
    assert l<=u
    if u-l>=2:
        return F(-1),F(1)
    a,b=sinpi_point(l),sinpi_point(u)
    lower,upper=min(a[0],b[0]),max(a[1],b[1])
    for k in range(ceil(l-F(1,2)),floor(u-F(1,2))+1):
        if k%2:
            lower=F(-1)
        else:
            upper=F(1)
    return lower,upper

def trig_range(l,u,multiple,part):
    assert multiple in (1,2) and part in (0,1)
    shift=F(1,2) if part==0 else F(0)
    return sinpi_range(F(l*multiple,SC)+shift,F(u*multiple,SC)+shift)

def hull(points,upper):
    result=[]
    for p in sorted(set(points)):
        while len(result)>1:
            a,b=result[-2:]
            cross=(b[0]-a[0])*(p[1]-a[1])-(b[1]-a[1])*(p[0]-a[0])
            if (cross>=0 if upper else cross<=0):
                result.pop()
            else:
                break
        result.append(p)
    return result

class PhaseGraphOracle:
    @lru_cache(None)
    def rectangles(self,l,u,multiple,part):
        assert isinstance(l,int) and isinstance(u,int) and l<=u
        if l==u:
            breaks=[l,u]
        else:
            breaks=[l]+list(range((l//STEP+1)*STEP,u,STEP))+[u]
        rows=[]
        for a,b in zip(breaks,breaks[1:]):
            lo,hi=trig_range(a,b,multiple,part)
            rows.append((a,b,floor(lo*DS),ceil(hi*DS)))
        assert rows and rows[0][0]==l and rows[-1][1]==u
        assert all(a<=b and lo<=hi for a,b,lo,hi in rows)
        assert all(a[1]==b[0] for a,b in zip(rows,rows[1:]))
        return tuple(rows)

    @lru_cache(None)
    def facets(self,l,u,multiple,part):
        """Return (sign,S,C) and rectangle count.

        sign=+1: SC*DS*f(x)-SC*S*x <= C.
        sign=-1: C <= SC*DS*f(x)-SC*S*x.
        This is valid over x in [l/SC,u/SC], f=cos(h*pi*x) if
        part=0 or sin(h*pi*x) if part=1, h=multiple.
        """
        rectangles=self.rectangles(l,u,multiple,part)
        slopes={0}
        for upper in (False,True):
            points=[]
            for a,b,lo,hi in rectangles:
                value=hi if upper else lo
                points.extend(((a,value),(b,value)))
            hh=hull(points,upper)
            for (a,v),(b,w) in zip(hh,hh[1:]):
                if a!=b:
                    slopes.add(round(F((w-v)*SC,b-a)))
        rows=[]
        for s in sorted(slopes):
            upper=max(SC*hi-s*(a if s>=0 else b) for a,b,lo,hi in rectangles)
            lower=min(SC*lo-s*(b if s>=0 else a) for a,b,lo,hi in rectangles)
            rows.extend(((1,s,upper),(-1,s,lower)))
        return tuple(rows),len(rectangles)

    def validate_rows(self,l,u,multiple,part,rows):
        rectangles=self.rectangles(l,u,multiple,part)
        for sign,s,c in rows:
            assert sign in (-1,1)
            for a,b,lo,hi in rectangles:
                if sign==1:
                    assert SC*hi-s*(a if s>=0 else b)<=c
                else:
                    assert c<=SC*lo-s*(b if s>=0 else a)
        return True

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    assert not args.output.exists(),'Use a new output; existing receipts are immutable.'
    start=time.monotonic()
    source=HERE/'cover-curvature-parent64.input.json.gz'
    selection=HERE/'cover-lifted-graph-energy8.json'
    packed=source.read_bytes()
    cases={r['path']:r for r in json.loads(gzip.decompress(packed))['cases']}
    chosen=[r['path'] for r in json.loads(selection.read_bytes())['rows'][:2]]
    oracle=PhaseGraphOracle()
    details=[]
    for path in chosen:
        lower,upper=cases[path]['before']
        query_count=rectangle_count=row_count=0
        maximum_rows=0
        for z in range(45):
            for h in (1,2):
                for part in (0,1):
                    rows,n=oracle.facets(lower[z],upper[z],h,part)
                    oracle.validate_rows(lower[z],upper[z],h,part,rows)
                    query_count+=1
                    rectangle_count+=n
                    row_count+=len(rows)
                    maximum_rows=max(maximum_rows,len(rows))
        details.append({'path':path,'queries':query_count,'rectangles':rectangle_count,
                        'facets':row_count,'maximum_facets_per_query':maximum_rows})
    result={'scope':__doc__,'source_sha256':sha(Path(__file__).read_bytes()),
      'input_sha256':sha(packed),'selection_sha256':sha(selection.read_bytes()),
      'SC':SC,'DS':DS,'grid_step':64,'cases':details,
      'all_integer_intercepts_checked':True,
      'analytic_trig_interface_Lean_proven':False,
      'strict_phase_exclusion_proven':False,'complete_global_cover':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps(result),flush=True)

if __name__=='__main__':
    main()
