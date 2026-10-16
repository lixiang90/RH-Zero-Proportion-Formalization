"""Lean-friendly centre-zero packets for the two frozen strict moment cells.

No optimizer or new sampling is used. Point value/slope packets are selected
from the already proved fixed-grid W coefficients, with coarse 1e-7 guards.
Second-derivative cells use the same integer Horner engine and 1e-6 guards.
The original integer dual weights are retained and only the energy-zero row
is rebuilt. This producer is not a Lean proof or a global cover.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
import hashlib
import json
import time
import cover_cross_moment_exact_rows as exact

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SC, FS, PD, GD = 32768, 10**30, 10**7, 10**6
M24 = F(44, 7)**24
PARAM = ROOT / "research-20261016-followup/window_reweight_rational.json"
sha = lambda raw: hashlib.sha256(raw).hexdigest()
floor = lambda x: x.numerator // x.denominator
ceil = lambda x: -((-x.numerator) // x.denominator)


def main():
    start = time.monotonic()
    strict_raw = (HERE / "cover-cross-moment-integer-two.json").read_bytes()
    strict = json.loads(strict_raw)
    norm_raw = (HERE / "window_normalized_interval.json").read_bytes()
    norm = json.loads(norm_raw)
    W = {int(n): [(int(F(l)*FS), int(F(u)*FS)) for l, u in rows]
         for n, rows in norm["integer_w_Taylor_coefficients"].items()}
    parameters = json.loads(PARAM.read_bytes())
    terms = [(i,j,a) for i,j,a in parameters["a_upper"] if a]
    bs = parameters["b_numerators"]
    pairs = [(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
    lookup = {p:k for k,p in enumerate(pairs)}
    current_raw = (HERE / "cover-curvature-actual-active.json").read_bytes()
    current = json.loads(current_raw)["grid_rows"]
    existing = {r["k"]: (i, r["q2"]) for i,r in enumerate(current) if "q2" in r}

    def jet_coeff(n, q, degree):
        return [tuple(z*factorial(j+q)//factorial(j) for z in W[n][j+q]) for j in range(degree+1)]

    def horner(n, q, degree, l, u):
        X = (floor((l-n)*FS), ceil((u-n)*FS))
        cs = jet_coeff(n,q,degree)
        lo, hi = cs[-1]
        mask = 0
        for j in range(degree-1,-1,-1):
            products = [lo*X[0],lo*X[1],hi*X[0],hi*X[1]]
            il = min(range(4),key=lambda k:products[k])
            iu = max(range(4),key=lambda k:products[k])
            mask += (il+4*iu)*16**j
            lo = cs[j][0]+products[il]//FS
            hi = cs[j][1]-((-products[iu])//FS)
        return F(lo,FS),F(hi,FS),mask

    point_rows = []
    @lru_cache(None)
    def point(p):
        n = round(p)
        assert 1 <= n <= 32 and abs(p-n) <= F(1,2)
        vl,vu,_ = horner(n,0,23,p,p)
        sl,su,_ = horner(n,1,22,p,p)
        ve = M24*abs(p-n)**24/factorial(24)
        se = M24*abs(p-n)**23/factorial(23)
        V = F(floor((vl-ve)*PD)-1,PD)
        T = F(round((sl+su)*PD/2),PD)
        epsilon = F(ceil(max(abs(sl-se-T),abs(su+se-T))*PD)+1,PD)
        assert V+ve <= vl and T-epsilon+se <= sl and su <= T+epsilon-se
        index = len(point_rows)
        point_rows.append({"n":n,"p":str(p),"value_lower":str(V),"slope":str(T),"slope_error":str(epsilon),
                           "integer_Horner_preflight":True})
        return index,V,T,epsilon

    all_grid = {}
    @lru_cache(None)
    def grid(k):
        l,u = F(k,64),F(k+1,64)
        n = round((l+u)/2)
        assert 1 <= n <= 32
        pl,pu,mask = horner(n,2,21,l,u)
        rem = M24*F(1,2)**22/factorial(22)
        L,U = F(floor((pl-rem)*GD)-1,GD),F(ceil((pu+rem)*GD)+1,GD)
        assert L+rem <= pl and pu <= U-rem
        if k in existing:
            _,(_,oldL,oldU) = existing[k]
            assert L <= F(oldL,10**15) and F(oldU,10**15) <= U
        row = {"k":k,"n":n,"mask":str(mask),"lower":str(L),"upper":str(U),
               "reuse_current_q2": k in existing,
               "current_index": existing[k][0] if k in existing else None}
        all_grid[k] = row
        return L,U

    rows = []
    for case in strict["rows"]:
        state = case["cell"]
        packet = case["energy_packets"][0]
        p = list(map(F,packet["centre"]))
        lo = [F(v,SC) for v in state[0][:9]]
        hi = [F(v,SC) for v in state[1][:9]]
        mid = [(a+b)/2 for a,b in zip(lo,hi)]
        rad = [(b-a)/2 for a,b in zip(lo,hi)]
        assert all(r>0 for r in rad)
        fLo = sum(F(b,10**10)*x for b,x in zip(bs,p))
        gm = [F(b,10**10) for b in bs]
        ge = [F(0)]*9
        pindices, lowers, ranges = [],[],[]
        for i,j,a in terms:
            z = lookup[i,j]
            index,V,T,e = point(sum(p[i:j]))
            pindices.append(index)
            a = F(a,10**10)
            fLo += a*V
            for r in range(i,j):
                gm[r] += a*T
                ge[r] += a*e
            first = state[0][z]//512
            last = (max(state[0][z]+1,state[1][z])+511)//512-1
            L = min(grid(k)[0] for k in range(first,last+1))
            lowers.append(L)
            ranges.append([first,last])
        payment = sum(e*max(abs(l-c),abs(u-c)) for e,l,u,c in zip(ge,lo,hi,p))
        constant = fLo-payment+sum(v*(m-c) for v,m,c in zip(gm,mid,p))
        linear = [v*r for v,r in zip(gm,rad)]
        quad = {pair:F(0) for pair in exact.PAIRS}
        for (i,j,a),L in zip(terms,lowers):
            aL = F(a,10**10)*L
            delta = sum(mid[i:j])-sum(p[i:j])
            constant += aL*delta*delta/2
            for r in range(i,j):
                linear[r] += aL*delta*rad[r]
                for s in range(r,j):
                    quad[r,s] += aL*rad[r]*rad[s]/(2 if r==s else 1)
        coeff = {}
        for r in range(9):
            coeff[r] = linear[r]/rad[r]
            constant -= linear[r]*mid[r]/rad[r]
        for pair,value in quad.items():
            if value:
                coeff[exact.hindex(*pair)] = value
        bound = F(11,1250)-constant
        new_packet = {"centre":list(map(str,p)),"F_lower":str(fLo),"gradient_midpoint":list(map(str,gm)),
                      "gradient_error":list(map(str,ge)),"uniform_gradient_error_payment":str(payment),
                      "whole_span_second_lower":list(map(str,lowers)),"quadratic_constant":str(constant),
                      "row":[[i,str(v)] for i,v in sorted(coeff.items()) if v],"bound":str(bound),
                      "point_indices":pindices,"grid_ranges":ranges}
        old_selected = case["selected_integer_rows"]
        energy = [r for r in old_selected if r["meta"]==["energy",0]]
        assert len(energy)==1 and not any(r["meta"]==["energy",1] for r in old_selected)
        bounds = [tuple(map(F,row)) for row in case["box_bounds"]]
        denominator = int(case["integerization_denominator"])
        replacement = exact.integerize({"coeff":coeff,"bound":bound,"meta":["energy",0]},bounds,denominator)
        integers,weighted = [],[]
        for i,old in enumerate(old_selected):
            integers.append(replacement if old["meta"]==["energy",0] else {
                "coeff":{k:int(v) for k,v in old["integer_coefficients"]},"bound":int(old["integer_bound"]),
                "denominator":denominator,"meta":old["meta"]})
            weighted.append((i,int(old["weight"])))
        aggregate = exact.verify_aggregate(integers,weighted,bounds)
        assert aggregate["strict_exclusion"], case["path"]
        normalized = aggregate["strict_margin"]/(denominator*sum(mu for _,mu in weighted))
        row = {"path":case["path"],"energy0":new_packet,"replacement_integer_row":replacement,
               "preserved_dual_weights":True,"selected_rows":len(old_selected),"aggregate":aggregate,
               "normalized_strict_margin":str(normalized),"normalized_strict_margin_float":float(normalized)}
        rows.append(row)
        print(json.dumps({"path":case["path"],"strict":True,"normalized_strict_margin":float(normalized)}),flush=True)
    missing = [row for k,row in sorted(all_grid.items()) if not row["reuse_current_q2"]]
    plan = {"point_rows":len(point_rows),"point_check_blocks_at_16":(len(point_rows)+15)//16,
            "required_q2_cells":len(all_grid),"reused_q2_cells":len(all_grid)-len(missing),
            "new_q2_cells":len(missing),"new_q2_blocks_at_32":(len(missing)+31)//32,
            "new_q4_cells":0,"ordinary_Lean_started":False}
    out = {"scope":__doc__,"inputs_sha256":{"strict_original":sha(strict_raw),"normalized_W":sha(norm_raw),
            "existing_curvature_grid":sha(current_raw),"parameters":sha(PARAM.read_bytes())},
           "script_sha256":sha(Path(__file__).read_bytes()),"plan":plan,"point_rows":point_rows,
           "new_q2_rows":missing,"all_q2_cells":sorted(all_grid),"rows":rows,
           "original_certificate_changed":False,"strict_integer_systems":2,
           "actual_Lean_exclusions":0,"complete_global_cover":False,"new_zero_proportion_proven":False,
           "seconds":time.monotonic()-start}
    target = HERE / "window-moment-friendly-packets.json"
    target.write_text(json.dumps(out,default=str,separators=(",",":"))+"\n")
    print(json.dumps({"output":target.name,"sha256":sha(target.read_bytes()),"plan":plan,"seconds":out["seconds"]}),flush=True)


if __name__ == "__main__":
    main()
