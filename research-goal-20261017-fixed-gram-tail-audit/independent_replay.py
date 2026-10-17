"""Independent pure-stdlib replay of the fixed retained interval/Gram ray.

No producer imports, optimizer, eigenvalue computation, sampled point,
transcendental calculation or Lean. Rebuild all active normalized scalar
slacks, integer-factor column squares, exact atom floor/ceil endpoints,
and every explicit moment-box payment. Default read-only;
--write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from array import array
import argparse,collections,gzip,hashlib,json,sys,time
from selection_replay import verify as verify_selection
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;RAY=ROOT/'research-goal-20261017-fixed-gram-tail'
OUT=HERE/'independent-replay.json';DS=10**30;D=10**12
CERT_SHA='7c8d083cec89942c19642a8206156a2f77879e3c1278d21c56bf3f2da2233332'
RAY_SHA='b51724e37d219705828d08a5af8db3d1588563d22908fe75b9dc29261e944d21'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(a,b,s=F(1)):
    for k,v in b.items():
        z=a.get(k,F(0))+s*v
        if z:a[k]=z
        else:a.pop(k,None)
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();cp=RAY/'retained-enclosure-certificate.json';qp=RAY/'retained-ray.json.gz'
    assert digest(cp)==CERT_SHA and digest(qp)==RAY_SHA
    cert=json.loads(cp.read_bytes());ray=json.loads(gzip.decompress(qp.read_bytes()))
    producer=json.loads((RAY/'retained-combination.json').read_bytes())
    assert cert['schema']=='deterministically-retained-Gram-ray-exact-atom-enclosure-v1'and cert['quantized_ray_sha256']==RAY_SHA
    assert digest(RAY/'retained-combination.json')=='b1f71eb6ce65e961b50e3941106c446c99294e10d39478a1765f2d920257fdde'
    inputs={**cert['source_sha256'],cp.relative_to(ROOT).as_posix():CERT_SHA,
        (RAY/'retained-combination.json').relative_to(ROOT).as_posix():digest(RAY/'retained-combination.json'),
        Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert producer['source_sha256_start']==producer['source_sha256_end']==cert['source_sha256']and producer['all_inputs_unchanged']
    for name,h in inputs.items():assert digest(ROOT/name)==h,('changed mathematical input',name)
    selection=verify_selection();assert selection['passed']
    inputs.update(selection['source_sha256'])
    assert ray['scalar_row_count']==14564 and ray['moment_column_count']==5004 and ray['unbounded_slack_column']==5004
    assert ray['scalar_weight_denominator']==cert['scalar_weight_denominator']==cert['Gram_factor_denominator']==D
    assert cert['fixed_interval_denominator']==DS and cert['forced_zero_scalar_rows']==ray['forced_zero_scalar_rows']==[5793,5794]
    weights=ray['scalar_weight_numerators'];assert len(weights)==14564 and all(type(w)is int and w>=0 for w in weights)
    assert weights[5793]==weights[5794]==0 and sum(w>0 for w in weights)==14562
    model=json.loads(gzip.decompress((ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz').read_bytes()))
    old=json.loads(gzip.decompress((ROOT/'research-goal-20261017-quartic/quartic-model.json.gz').read_bytes()))
    family=json.loads(gzip.decompress((ROOT/'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz').read_bytes()))
    oldrows=old['linear_rows']+family['additional_linear_rows'];del family
    actual=json.loads(gzip.decompress((ROOT/'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz').read_bytes()))
    rowhash=json.loads((ROOT/'research-goal-20261017-actual-sextic-cone/new-row-hashes.json').read_bytes())
    mon=[m for degree in range(7)for m in combinations_with_replacement(range(9),degree)];index={m:k for k,m in enumerate(mon)}
    assert len(mon)==5005 and list(map(list,mon))==model['monomials']==actual['monomials']and list(map(list,mon[:715]))==old['monomials']
    assert len(oldrows)==5803 and len(model['blocks'])==len(ray['PSD_factors'])==73
    lower=[0]*5005;upper=[0]*5005;atoms=0;nonintegral=0;sections=[]
    def put(k,n,d):
        nonlocal atoms,nonintegral
        assert type(k)is int and 0<=k<=5004 and type(n)is int and type(d)is int and d>0
        if n==0:return
        scaled=DS*n;lo=scaled//d;hi=-((-scaled)//d)
        assert lo*d<=scaled<=hi*d and hi-lo in(0,1)
        lower[k]+=lo;upper[k]+=hi;atoms+=1;nonintegral+=hi-lo
    def rat(k,w,a,scale=F(1),sign=1):
        put(k,sign*w*a.numerator*scale.denominator,D*a.denominator*scale.numerator)
    start=atoms;oldboxes={};active=collections.Counter();slack_occurrences=[]
    for rid,row in enumerate(oldrows):
        w=weights[rid];scale=F(row['scale']);assert scale>0
        if any(k==714 for k,v in row['coefficients']):
            slack_occurrences.append(rid);assert rid in[5793,5794]and w==0;continue
        assert all(0<=k<714 for k,v in row['coefficients'])
        if row['meta'][0]=='redundant_cube_moment_box':
            assert len(row['coefficients'])==1 and scale==1;k,v=row['coefficients'][0];v=F(v);assert v in[-1,1]
            assert(k,int(v))not in oldboxes;oldboxes[k,int(v)]=(rid,F(row['bound']))
        if w:
            active[row['meta'][0]]+=1;rat(0,w,F(row['bound']),scale)
            for k,v in row['coefficients']:rat(k+1,w,F(v),scale,-1)
    assert slack_occurrences==[5793,5794]
    sections.append({'section':'old5803_scalar_rows','atoms':atoms-start});start=atoms;boxes=[]
    def even(mid):return all(mon[mid].count(v)%2==0 for v in set(mon[mid]))
    for col in range(714):
        lr,lb=oldboxes[col,-1];ur,ub=oldboxes[col,1];lo=0 if even(col+1)else -1
        assert lb==-lo and ub==1;boxes.append({'monomial_id':col+1,'lower':lo,'upper':1,'lower_scalar_row':lr,'upper_scalar_row':ur})
    rid=5803
    for offset,(col,lo,hi)in enumerate(model['new_moment_boxes']):
        assert col==714+offset and hi==1 and lo==(0 if even(col+1)else -1)
        boxes.append({'monomial_id':col+1,'lower':lo,'upper':hi,'lower_scalar_row':rid,'upper_scalar_row':rid+1})
        for a,b in[(-1,-lo),(1,hi)]:put(0,weights[rid]*b,D);put(col+1,-weights[rid]*a,D);rid+=1
    assert rid==14383 and len(boxes)==5004 and boxes==cert['explicit_monomial_boxes']
    sections.append({'section':'8580_added_moment_boxes','atoms':atoms-start});start=atoms
    print(json.dumps({'phase':'independent_old_rows_and_all5004_boxes_checked','atoms':atoms}),flush=True)
    # Rebuild actual rows by rational linear combinations of the frozen span powers.
    powers=[{k:F(v)for k,v in item['terms']}for item in actual['span_powers']]
    L={k:F(v)for k,v in actual['pressure_polynomial']};P=[{0:F(b)}for b in actual['pressure_coefficients_b']];E=[{}for _ in range(9)]
    incidents=actual['coordinate_incident_edges'];edge_atoms=[]
    for eid,e in enumerate(actual['edges']):
        parts=[]
        for field in['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']:
            poly={}
            for degree,v in enumerate(e[field]):add(poly,powers[e['power_ids'][degree]],F(e['weight'])*F(v))
            parts.append(poly)
        edge_atoms.append(parts);add(L,parts[0])
    for coordinate,edges in enumerate(incidents):
        for eid in edges:add(P[coordinate],edge_atoms[eid][1]);add(E[coordinate],edge_atoms[eid][2])
    stream=hashlib.sha256();assert len(actual['new_scalar_rows'])==len(rowhash['rows'])==181
    for descriptor,record in zip(actual['new_scalar_rows'],rowhash['rows']):
        j=descriptor['id'];assert j==record['row'];w=weights[14383+j];assert w>0
        if descriptor['kind']=='absolute_energy_L6':
            q={k:-v for k,v in L.items()};q[0]=q.get(0,F(0))+F(descriptor['bound']);meta=['actual_sextic_absolute_energy_unsoftened']
        else:
            r=descriptor['coordinate'];test=descriptor['test_monomial_id'];sgn=descriptor['sign'];q=E[r].copy()
            shifted={index[tuple(sorted(mon[k]+mon[test]))]:v for k,v in P[r].items()};add(q,shifted,F(sgn));meta=['actual_sextic_free_KKT',r,test,sgn]
        b=q.get(0,F(0));scale=max([F(1,1000),abs(b)]+[abs(v)for k,v in q.items()if k]);assert scale==F(record['scale'])>0
        coef=[[k-1,str(-v)]for k,v in sorted(q.items())if k];assert len(coef)==5004 and all(0<=k<5004 for k,v in coef)
        canonical={'coefficients':coef,'bound':str(b),'scale':str(scale),'meta':meta}
        encoded=json.dumps(canonical,sort_keys=True,separators=(',',':')).encode();assert hashlib.sha256(encoded).hexdigest()==record['exact_canonical_row_sha256']
        assert str(b)==record['bound']and meta==record['meta'];stream.update(encoded+b'\n')
        for k,a in q.items():rat(k,w,a,scale)
    assert stream.hexdigest()==rowhash['exact_canonical_rows_JSONL_sha256']
    sections.append({'section':'181_actual_sextic_rows','atoms':atoms-start});start=atoms
    del actual,powers,edge_atoms,L,P,E,q,coef,old,oldrows
    print(json.dumps({'phase':'independent_all181_actual_sextic_rows_rebuilt','atoms':atoms}),flush=True)
    target=array('H');target.frombytes((ROOT/'research-goal-20261017-degree6-static/degree6-targets.bin').read_bytes())
    entries=array('I');entries.frombytes((ROOT/'research-goal-20261017-degree6-static/degree6-entryplans.bin').read_bytes())
    if sys.byteorder!='little':target.byteswap();entries.byteswap()
    assert len(target)==1416525 and len(entries)==96580
    plans=model['entry_plans'];planmap={(q,s):(off,count)for q,s,off,count in plans};assert len(planmap)==len(plans)
    gramrecords=[];targetchecks=0;factor_squares=0;pair_checks=0
    for bid,(block,factor)in enumerate(zip(model['blocks'],ray['PSD_factors'])):
        n=block['size'];qid=block['multiplier_id'];rank=factor['column_count'];ints=factor['factor_numerators_by_row']
        assert factor['block_id']==bid and factor['multiplier_id']==qid and factor['size']==n and factor['factor_denominator']==D
        assert len(ints)==n and all(len(row)==rank and all(type(v)is int for v in row)for row in ints)
        basis=block['basis_monomial_ids'];assert basis==list(range(n))and 0<rank<=n
        # Build SOS directly as the sum of squared COLUMN polynomials of L.
        # No eigenvalue or floating Gram matrix is consulted.
        products=[[index[tuple(sorted(mon[i]+mon[j]))]for j in range(i,n)]for i in range(n)]
        sos={}
        for column in range(rank):
            vector=[row[column]for row in ints];factor_squares+=1
            for i,a in enumerate(vector):
                if a==0:continue
                for j in range(i,n):
                    value=a*vector[j]*(1 if i==j else 2)
                    if value:
                        mid=products[i][j-i];sos[mid]=sos.get(mid,0)+value
        sos={k:v for k,v in sos.items()if v};assert sos
        local=0
        for j in range(n):
            for i in range(j,n):
                q,s,off,count=plans[entries[block['entry_plan_offset']+local]]
                assert q==qid and s==index[tuple(sorted(mon[i]+mon[j]))];local+=1;pair_checks+=1
        assert local==block['lower_triangle_entries']==n*(n+1)//2
        terms=[(k,F(v))for k,v in model['multipliers'][qid]['terms']]
        div=max([F(1)]+[abs(v)for _,v in terms]);assert div==F(factor['positive_rational_block_divisor'])>0
        blockstart=atoms
        for s,value in sos.items():
            off,count=planmap[qid,s];assert count==len(terms)
            for j,(k,a)in enumerate(terms):
                mid=index[tuple(sorted(mon[s]+mon[k]))];assert target[off+j]==mid;targetchecks+=1
                put(mid,value*a.numerator*div.denominator,D*D*a.denominator*div.numerator)
        rec={'block_id':bid,'size':n,'factor_columns':rank,'integer_Gram_nonzero':True,'exact_grouped_SOS_monomials':len(sos),
            'enclosed_atoms':atoms-blockstart,'positive_rational_divisor':str(div),'multiplier_id':qid}
        assert rec==cert['PSD_block_records'][bid];gramrecords.append(rec)
        if(bid+1)%15==0:print(json.dumps({'phase':'independent_column_SOS_blocks','blocks':bid+1,'atoms':atoms}),flush=True)
    sections.append({'section':'73_integer_Gram_trace_polynomials','atoms':atoms-start})
    assert len(gramrecords)==73 and pair_checks==96580
    assert sections==cert['enclosure_sections']and atoms==cert['enclosed_nonzero_atoms']==2548856
    assert nonintegral==cert['nonintegral_atom_enclosures']and targetchecks==cert['exact_Gram_target_identities_checked']==1416525
    assert lower==cert['coefficient_lower_numerators']and upper==cert['coefficient_upper_numerators']and all(a<=b for a,b in zip(lower,upper))
    payment=[];odd=all_even=0
    for row in boxes:
        mid=row['monomial_id']
        if even(mid):cost=max(0,upper[mid]);all_even+=1
        else:cost=max(abs(lower[mid]),abs(upper[mid]));odd+=1
        assert cost==max(lower[mid]*row['lower'],lower[mid]*row['upper'],upper[mid]*row['lower'],upper[mid]*row['upper']);payment.append(cost)
    assert payment==cert['monomial_box_worst_product_upper_numerators']
    total=upper[0]+sum(payment);assert total==cert['constant_upper_numerator']==-954861379977679627115791937265<0
    margin=F(-total,DS);assert str(margin)==cert['strict_margin']and cert['strict_negative_constant_upper']
    assert dict(active)==cert['active_old_scalar_metadata_counts']and not cert['literal_exact_coefficient_cancellation_claimed']
    for name,h in inputs.items():assert digest(ROOT/name)==h
    result={'scope':__doc__,'passed':True,'source_sha256_start':inputs,'source_sha256_end':inputs,'all_mathematical_inputs_unchanged':True,
        'mutable_current_governance_not_a_mathematical_premise':True,'selection_audit':selection,
        'certificate_sha256':CERT_SHA,'quantized_ray_sha256':RAY_SHA,'Dlambda':D,'DL':D,'DS':DS,
        'nonnegative_scalar_weights_checked':14564,'positive_scalar_weights':14562,'forced_zero_rows':[5793,5794],
        'unbounded_solver_slack_coefficient_exactly_zero':True,'constant_plus_moment_coefficients_checked':5005,
        'scalar_row_count':14564,'new_actual_sextic_rows_rebuilt':181,'all_new_actual_rows_positive_weight':True,
        'integer_Gram_blocks_checked':73,'integer_factor_column_squares':factor_squares,'lower_triangle_trace_offdiagonal_checks':pair_checks,
        'exact_basis_product_target_checks':targetchecks,'nonzero_atoms_enclosed':atoms,'nonintegral_atom_enclosures':nonintegral,
        'enclosure_sections':sections,'all5005_lower_and_upper_endpoints_match':True,'explicit_boxes_checked':5004,
        'odd_or_mixed_parity_boxes_minus1_to1':odd,'all_even_boxes_0_to1':all_even,'all5004_box_payments_match':True,
        'constant_upper_numerator':total,'constant_upper_denominator':DS,'strict_negative_upper':True,'strict_margin':str(margin),
        'proof_semantics':'Nonnegative scalar slacks plus integer-Gram PSD traces give H>=0; verified coefficient intervals and explicit moment boxes give H<=strict_negative_upper.',
        'literal_exact_residual_cancellation_claimed':False,'active_old_scalar_dependencies':dict(active),
        'active_old_analytic_dependencies':['180 inherited quartic KKT/error inequalities','8 normalized-W global-swap quartic necessary inequalities','old quadratic-energy sublevel PSD localizer','all inherited geometry and span-product PSD multipliers'],
        'fixed_cell_already_closed_in_historical_baseline':True,'new_frontier_closure_claimed':False,'scope_of_proof':'Exact infeasibility of the fixed enhanced degree6 polynomial/moment system on one selected cell, conditional on its actual analytic-to-polynomial premises.',
        'actual_analytic_literal_instances_Lean_proved_here':False,'actual_cell_exclusion_proven_in_Lean':False,
        'historical_full_cover_replayed':False,'global_root_cover_completed':False,'producer_imports':0,'solver_calls':0,'eigh_calls':0,'new_points':0,'Lean_invocations':0,
        'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'atoms':atoms,'Gram_blocks':73,'coefficient_intervals':5005,'boxes':5004,'strict_margin':str(margin),
        'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':result['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
