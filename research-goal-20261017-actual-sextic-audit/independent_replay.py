"""One independent stdlib replay of the frozen actual-sextic STATIC packet.

No producer/helper import, solver, Lean, new anchor or moment evaluation.
Rebuild exact normalized-W point intervals, whole-cell seventh-derivative
intervals, all scalar envelope coefficients, multinomial span powers and
the compact degree-six target stream. This checks a conditional STATIC
representation; concrete analytic Lean instances and exclusion stay open.
Default read-only; --write-receipt creates one absent receipt.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial
from array import array
import argparse
import gzip
import hashlib
import json
import re
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SOURCE=ROOT/'research-goal-20261017-actual-sextic-static'
OUT=HERE/'independent-replay.json'
SC=32768
DS=10**15


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def read_gzip(p):return json.loads(gzip.decompress(p.read_bytes()))


def nearest(x):
    n=x.numerator//x.denominator
    dl=x-n;du=n+1-x
    return n if dl<du or (dl==du and n%2==0) else n+1


def imul(a,b):
    values=[x*y for x in a for y in b]
    return min(values),max(values)


def iadd(a,b):return a[0]+b[0],a[1]+b[1]


def jet_at(table,q,delta,M24):
    # Direct sum of fixed-scalar intervals, independently of Horner order.
    value=(F(0),F(0))
    for j in range(q,24):
        scalar=F(factorial(j),factorial(j-q))*delta**(j-q)
        value=iadd(value,imul(table[j],(scalar,scalar)))
    rem=M24*abs(delta)**(24-q)/factorial(24-q)
    return value[0]-rem,value[1]+rem


def seventh_grid(table,k,M24):
    n=nearest(F(2*k+1,128))
    x=F(k,64)-n,F(k+1,64)-n
    assert 1<=n<=32 and -F(1,2)<=x[0]<=x[1]<=F(1,2)
    value=(F(0),F(0))
    for j in range(23,6,-1):
        c=F(factorial(j),factorial(j-7))
        value=iadd(imul(value,x),(table[n][j][0]*c,table[n][j][1]*c))
    rem=M24*F(1,2)**17/factorial(17)
    lo,hi=value[0]-rem,value[1]+rem
    raw=max(abs(lo),abs(hi))*DS
    ticks=(raw.numerator+raw.denominator-1)//raw.denominator
    return n,lo,hi,F(ticks,DS)


def affine_power(constant,coefficients,k,monomial_index):
    # Closed multinomial formula; no repeated polynomial multiplication.
    out={}
    axes=sorted(coefficients)
    for degree in range(k+1):
        for m in combinations_with_replacement(axes,degree):
            value=F(factorial(k),factorial(k-degree))*constant**(k-degree)
            for r in set(m):
                count=m.count(r)
                value*=coefficients[r]**count/factorial(count)
            if value:out[m]=value
    return [[monomial_index[m],str(v)] for m,v in sorted(out.items(),key=lambda z:monomial_index[z[0]])]


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists(),'Receipt is immutable; choose a new path.'
    began=time.monotonic()
    packet_path=SOURCE/'actual-sextic.json.gz';map_path=SOURCE/'sextic-shifts.bin';build_path=SOURCE/'sextic-build.json'
    data=read_gzip(packet_path);build=json.loads(build_path.read_bytes())
    assert data['source_sha256_start']==data['source_sha256_end']
    paths=[Path(__file__),packet_path,map_path,build_path]
    for name,h in data['source_sha256_start'].items():
        p=ROOT/name;assert sha(p)==h
        if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert initial[packet_path.relative_to(ROOT).as_posix()]=='e9a1194205d9d52dfbbae2a33e3a353f6c63dd40c8013d4280cf21e7c30e48b5'
    assert initial[map_path.relative_to(ROOT).as_posix()]=='f6ee22d84f5ae0eb80b2d97b7cb3469b66cfbb79942207aefeebb4d2d95de627'
    raw=gzip.decompress(packet_path.read_bytes())
    assert len(raw)==build['packet_uncompressed_bytes']==3433971
    assert hashlib.sha256(raw).hexdigest()==build['packet_uncompressed_sha256']
    for rec in [build['packet'],build['shift_target_indices'],data['shift_target_indices']]:
        p=ROOT/rec['path'];assert p.stat().st_size==rec['bytes'] and sha(p)==rec['sha256']
    base=read_gzip(ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz')
    old=read_gzip(ROOT/'research-goal-20261017-quartic/quartic-model.json.gz')
    mon=[tuple(m) for m in data['monomials']]
    expected=[m for degree in range(7) for m in combinations_with_replacement(range(9),degree)]
    assert mon==expected==[tuple(m) for m in base['monomials']]
    assert len(mon)==5005 and list(map(list,mon[:715]))==old['monomials']
    index={m:k for k,m in enumerate(mon)}
    assert data['nonconstant_moment_columns']==data['energy_slack_column']==5004
    assert data['path']==base['path']==old['path']=='r001000001000100110011001'
    assert F(data['target'])==F(11,1250) and F(data['SEP'])==F(123,128)
    state=old['cell'];assert len(state)==2 and all(len(s)==45 for s in state)
    center=[F(state[0][r]+state[1][r],2*SC) for r in range(9)]
    radius=[F(state[1][r]-state[0][r],2*SC) for r in range(9)]
    assert center==list(map(F,data['normalized_gap_center']))==list(map(F,old['normalized_gap_center']))
    assert radius==list(map(F,data['normalized_gap_radius']))==list(map(F,old['normalized_gap_radius']))
    assert min(radius)>0
    margins=[state[0][r]-SC*F(123,128) for r in range(9)]
    assert min(margins)>0 and margins==data['all_nine_original_free_margins_SC_units']
    oldrec=data['retain_old_static_model'];assert sha(ROOT/oldrec['path'])==oldrec['sha256']
    assert oldrec['all_old_rows_and_73_PSD_retained'] is True
    assert len(base['blocks'])==73
    assert base['old_row_adapter']['rows']+2*len(base['new_moment_boxes'])==14383

    params=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    ledger=[(i,j,F(a,params['denominator'])) for i,j,a in params['a_upper'] if a]
    assert len(ledger)==41 and all(w>0 for i,j,w in ledger)
    span_axes=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
    axis={edge:k for k,edge in enumerate(span_axes)}
    pressure=list(map(lambda n:F(n,params['denominator']),params['b_numerators']))
    assert pressure==list(map(F,data['pressure_coefficients_b'])) and min(pressure)>0
    pressure_poly={():sum(b*c for b,c in zip(pressure,center))}
    pressure_poly.update({(r,):pressure[r]*radius[r] for r in range(9)})
    packed_pressure=[[index[m],str(v)] for m,v in sorted(pressure_poly.items(),key=lambda z:index[z[0]]) if v]
    assert packed_pressure==data['pressure_polynomial']

    wdoc=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())
    table={int(n):[tuple(map(F,q)) for q in row] for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
    assert sorted(table)==list(range(33)) and all(len(row)==24 for row in table.values())
    source=(ROOT/'StructuralGoal20261016/WindowJetTableData.lean').read_text(encoding='utf8')
    assert 'def qi30 (l u : ℤ) : QI := ((l:ℚ)/10^30,(u:ℚ)/10^30)' in source
    literal=source.split('def wValues :',1)[1].split('\ndef W ',1)[0]
    pairs=re.findall(r'qi30\s+\((-?\d+)\)\s+\((-?\d+)\)',literal)
    assert len(pairs)==33*24
    literal_table=[(F(int(l),10**30),F(int(u),10**30)) for l,u in pairs]
    assert literal_table==[q for n in range(33) for q in table[n]]
    M24=F(44,7)**24;assert M24==F(data['global_absolute_w24_bound'])
    assert [data[k] for k in ['point_Taylor_terms','point_Taylor_degree','w7_Taylor_degree','w7_Taylor_terms','w7_remainder_power']]==[24,23,16,17,17]
    grids={row['cell']:row for row in data['whole_grid_w7_cells']};assert len(grids)==658
    bounds={}
    for k,row in grids.items():
        n,lo,hi,B=seventh_grid(table,k,M24)
        assert n==row['nearest_integer']
        assert (lo,hi)==(F(row['actual_w7_lower']),F(row['actual_w7_upper']))
        assert B==F(row['absolute_bound']) and B>=max(abs(lo),abs(hi))
        bounds[k]=B

    edges=data['edges'];powers=data['span_powers'];assert len(edges)==41 and len(powers)==287
    used_cells=set();point_count=0;term_count=0
    for eid,(edge,(i,j,weight)) in enumerate(zip(edges,ledger)):
        assert edge['id']==eid and edge['edge']==[i,j] and F(edge['weight'])==weight
        a=axis[i,j];l,u=state[0][a],state[1][a]
        assert a==edge['original_span_axis'] and [l,u]==edge['whole_span_integer_bounds']
        assert [F(l,SC),F(u,SC)]==list(map(F,edge['whole_span_rational_bounds']))
        p=F(l+u,2*SC);R=F(u-l,2*SC);n=nearest(p);delta=p-n
        assert p==F(edge['anchor']) and R==F(edge['radius_about_anchor']) and R>0
        assert 1<=n<=32 and abs(delta)<=F(1,2) and n==edge['integer_jet_anchor']
        actual=[jet_at(table[n],q,delta,M24) for q in range(7)]
        assert actual==[tuple(map(F,q)) for q in edge['point_intervals_orders_0_to_6']]
        mu=[(l+u)/2 for l,u in actual];eps=[(u-l)/2 for l,u in actual]
        assert mu==list(map(F,edge['point_derivative_midpoints']))
        assert eps==list(map(F,edge['point_derivative_errors'])) and min(eps)>=0
        point_count+=7
        ks=list(range(l//512,(u+511)//512));used_cells.update(ks)
        assert ks==edge['whole_span_w7_grid_cells'] and set(ks)<=set(grids)
        M7=max(bounds[k] for k in ks);assert M7==F(edge['whole_span_absolute_w7_bound'])
        T=[mu[q]/factorial(q) for q in range(7)]
        A=[eps[0]+eps[1]*R,0,eps[2]/2+eps[3]*R/6,0,eps[4]/24+eps[5]*R/120,0,eps[6]/720+M7*R/5040]
        U=[mu[q+1]/factorial(q) for q in range(6)]
        E=[eps[1]+eps[2]*R,0,eps[3]/2+eps[4]*R/6,0,eps[5]/24+eps[6]*R/120,0,M7/720]
        for name,values in [('central_T6_coefficients_in_d',T),('energy_A6_coefficients_in_d',A),
                            ('absolute_L6_coefficients_in_d',[t-a for t,a in zip(T,A)]),
                            ('derivative_U5_coefficients_in_d',U),('derivative_E6_coefficients_in_d',E)]:
            assert list(map(F,edge[name]))==values
        assert min(A+E)>=0 and all(U[q]==(q+1)*T[q+1] for q in range(6))
        constant=sum(center[i:j])-p;coeff={r:radius[r] for r in range(i,j)}
        assert edge['power_ids']==list(range(eid*7,eid*7+7))
        for degree,pid in enumerate(edge['power_ids']):
            expected_power=affine_power(constant,coeff,degree,index)
            row=powers[pid]
            assert row['id']==pid and row['edge']==eid and row['degree']==degree
            assert row['terms']==expected_power
            term_count+=len(expected_power)
        assert edge['d_polynomial']==powers[edge['power_ids'][1]]['terms']
    assert used_cells==set(grids) and point_count==287 and term_count==41794

    targets=array('H');targets.frombytes(map_path.read_bytes())
    if sys.byteorder!='little':targets.byteswap()
    plans=data['shift_plans'];assert len(plans)==2501
    expected_keys=[(row['id'],test) for row in powers for test in (range(10) if row['degree']<=5 else [0])]
    assert len(expected_keys)==len(plans)
    offset=0;lookup={};maximum_degree=0
    for pid,(plan,key) in enumerate(zip(plans,expected_keys)):
        power_id,test,start,count=plan
        assert key==(power_id,test) and start==offset
        terms=powers[power_id]['terms'];assert count==len(terms)
        expected_targets=[index[tuple(sorted(mon[k]+mon[test]))] for k,_ in terms]
        assert list(targets[start:start+count])==expected_targets and len(set(expected_targets))==count
        maximum_degree=max(maximum_degree,max(len(mon[k]) for k in expected_targets))
        offset+=count;assert key not in lookup;lookup[key]=pid
    assert offset==len(targets)==206278 and maximum_degree==6
    incident=[[eid for eid,(i,j,w) in enumerate(ledger) if i<=r<j] for r in range(9)]
    assert incident==data['coordinate_incident_edges']
    expected_rows=[{'id':0,'kind':'absolute_energy_L6','sense':'less_or_equal','bound':'11/1250','maximum_degree':6,'diagnostic_slack_column':None}]
    for r in range(9):
        for test in range(10):
            for sign in [-1,1]:
                expected_rows.append({'id':len(expected_rows),'kind':'free_gradient_E6_plus_sign_test_P5',
                    'coordinate':r,'test_monomial_id':test,'sign':sign,'sense':'greater_or_equal',
                    'bound':'0','maximum_degree':6,'diagnostic_slack_column':None})
    assert expected_rows==data['new_scalar_rows'] and len(expected_rows)==181
    used_plans=set()
    for edge in edges:
        used_plans.update(lookup[pid,0] for pid in edge['power_ids'])
    for row in expected_rows[1:]:
        for eid in incident[row['coordinate']]:
            pids=edges[eid]['power_ids']
            # Only P5 is shifted; the even nonnegative error E6 is not.
            used_plans.update(lookup[pids[k],row['test_monomial_id']] for k in range(6))
            used_plans.update(lookup[pids[k],0] for k in [0,2,4,6])
    assert used_plans==set(range(len(plans)))
    assert data['old_scalar_rows']==14383 and data['combined_scalar_rows']==14564 and data['new_PSD_blocks']==0
    assert data['gradient_row_definition']=='E6[r]+sign*(momentMonomial[test]*P5[r])>=0; E6 is NOT multiplied by test'
    assert data['unsoftened_absolute_energy_row'] is True
    for key in ['new_energy_uses_old_F0','new_envelopes_use_old_wprime_literals','actual_analytic_instances_newly_Lean_proved',
                'strict_new_inequality_violation_proven','cell_exclusion_proven','new_zero_proportion_proven']:
        assert data[key] is False
    assert not any(name.split('.')[0] in ['numpy','scipy','scs'] for name in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    report={'scope':__doc__,'status':'actual_sextic_STATIC_independent_exact_representation_replay_passed',
        'source_sha256_start':initial,'source_sha256_end':final,'all_inputs_unchanged':True,
        'positive_original_ledger_edges_checked':41,'free_original_coordinates_checked':9,
        'normalized_W_literal_coefficients_identical':792,'point_derivative_intervals_checked':point_count,
        'point_derivative_orders':[0,1,2,3,4,5,6],'point_interval_method':'direct fixed-scalar interval sum, not producer Horner',
        'whole_grid_q7_degree16_cells_checked':len(grids),'whole_grid_remainder_power':17,'whole_grid_remainder_factorial':17,
        'scalar_envelope_packets_checked':41,'absolute_L6_and_U5_E6_checked':True,
        'odd_errors_paid_by_R_times_adjacent_even_power':True,'span_powers_multinomial_checked':len(powers),
        'span_power_coefficient_terms_checked':term_count,'canonical_monomials':len(mon),
        'shift_plans_checked':len(plans),'shift_target_references_checked':offset,
        'target_maps_injective':True,'target_stream_fully_consumed':True,'all_plans_used_by_rows':True,
        'maximum_target_degree':maximum_degree,'new_unsoftened_energy_rows':1,'new_free_KKT_M0_rows':180,
        'only_P5_multiplied_by_test_not_E6':True,'new_degree8_localizers':0,
        'old_scalar_rows_retained_by_hash':14383,'old_PSD_blocks_retained_by_hash':73,
        'producer_imported':False,'pure_stdlib':True,'new_anchors_selected':0,
        'new_actual_function_samples':0,'new_point_or_moment_evaluations':0,'solver_calls':0,'Lean_invocations':0,
        'concrete_analytic_Lean_instances_proved':False,'old_exact714_extension_decided':False,
        'strict_projection_shrink_proved':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:report[k] for k in ['status','point_derivative_intervals_checked',
        'whole_grid_q7_degree16_cells_checked','span_power_coefficient_terms_checked','shift_plans_checked',
        'shift_target_references_checked','elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
