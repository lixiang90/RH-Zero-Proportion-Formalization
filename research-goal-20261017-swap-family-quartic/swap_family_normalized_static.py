"""The complete eight adjacent swaps, with normalized-W fifth derivatives.

Reuse the parent's SAME nine normalized variables and 714 moments. Add
exactly eight unsoftened necessary rows, one for every adjacent swap.
The frozen 5795 old scalar rows and 47 PSD blocks are referenced intact.
Use the normalized actual-w coefficient table for BOTH point jets0..4
and degree18 Taylor enclosures of w5. No old w-prime coefficient packet
is used by the NEW rows. The frozen base retains its explicit premises.
No optimizer, parameter selection, new actual scalar table, or Lean.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import gzip,hashlib,importlib.util,json,time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
PARENT=ROOT/'research-goal-20261017-quartic';OLD=ROOT/'research-goal-20261016'
SINGLE=ROOT/'research-goal-20261017-swap67-quartic'
OUT=HERE/'swap-family-normalized.json.gz';RECEIPT=HERE/'swap-family-normalized-build.json';SC=32768;DS=10**15
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
LOOK={e:k for k,e in enumerate(ALL)}
spec=importlib.util.spec_from_file_location('frozen_swap67_helpers',SINGLE/'swap67_quartic_static.py')
helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
add=helpers.add;mul=helpers.mul;scale=helpers.scale;Interval=helpers.Interval

class NormalizedIntegerJet(helpers.IntegerJet):
    def __init__(self,wdoc):
        self.w={int(n):[Interval(*v) for v in row] for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
        assert len(self.w)==33 and set(map(len,self.w.values()))=={24}
        self.M24=F(44,7)**24;self.cache={}
    def jets(self,p):
        assert 1<=round(p)<=32
        return super().jets(p)
    def fifth_cell(self,k):
        if k not in self.cache:
            n=round(F(2*k+1,128));assert 1<=n<=32
            d=Interval(F(k,64)-n,F(k+1,64)-n);assert F(-1,2)<=d.l<=d.u<=F(1,2)
            value=Interval(0)
            # W[n,j] encloses w^(j)(n)/j!, so the fifth derivative
            # has degree18 with j!/(j-5)! times this coefficient.
            for j in range(23,4,-1):value=value*d+self.w[n][j]*F(factorial(j),factorial(j-5))
            rem=self.M24*F(1,2)**19/factorial(19)
            raw=max(abs(value.l-rem),abs(value.u+rem))*DS
            self.cache[k]=F(-((-raw.numerator)//raw.denominator),DS)
        return self.cache[k]

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert not OUT.exists() and not RECEIPT.exists();began=time.monotonic()
    paths=[Path(__file__),SINGLE/'swap67_quartic_static.py',SINGLE/'swap67-quartic-files.json',
        PARENT/'quartic-model.json.gz',PARENT/'quartic-files.json',PARENT/'quartic-exact-primal.json',
        PARENT/'quartic-result-replay.json',OLD/'window_normalized_interval.json',OLD/'window_normalized_interval.py',
        ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'StructuralGoal20261016/WindowMinimizerCover.lean',ROOT/'StructuralGoal20261016/WindowGlobalCompetitor.lean',
        ROOT/'research-goal-20261016/window_global_competitor_formal_index.json',
        ROOT/'StructuralGoal20261016/WindowCellDerivative.lean',ROOT/'StructuralGoal20261016/WindowRawCoefficients.lean',
        ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean',ROOT/'StructuralGoal20261016/WindowJetTableData.lean',
        HERE/'swap_family_quartic_static.py',HERE/'swap-family-quartic.json.gz',HERE/'swap-family-quartic-build.json']
    pins={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    parent=json.loads(gzip.decompress(paths[3].read_bytes()));prior=json.loads(paths[6].read_bytes())
    for manifestpath in [paths[2],paths[4]]:
        manifest=json.loads(manifestpath.read_bytes())
        for row in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/row['path'])==row['sha256']
    proof=json.loads(paths[5].read_bytes());wdoc=json.loads(paths[7].read_bytes());params=json.loads(paths[9].read_bytes())
    assert wdoc['source_sha256']==sha(paths[8]) and wdoc['parameter_sha256']==sha(paths[9])
    assert prior['status']=='strict_exact_shared_quartic_outer_relaxation_independently_verified'
    assert proof['status']=='strict_exact_shared_quartic_outer_relaxation_feasible' and parent['path']==proof['path']=='r001000001000100110011001'
    assert len(parent['linear_rows'])==5795 and parent['PSD_sizes']==[55]+[10]*46 and parent['slack_index']==714
    mon=[tuple(m) for m in parent['monomials']];mi={m:k for k,m in enumerate(mon)};mom=[F(1)]+list(map(F,proof['rational_714_moments']))
    assert len(mon)==len(mom)==715 and mon[0]==()
    def pack(p):return [[mi[m],str(v)] for m,v in sorted(p.items(),key=lambda z:mi[z[0]])]
    def expect(p):return sum(v*mom[mi[m]] for m,v in p.items())
    state=parent['cell'];center=list(map(F,parent['normalized_gap_center']));radius=list(map(F,parent['normalized_gap_radius']))
    assert all(F(l,SC)>F(123,128) for l in state[0][:9])
    gap=[{():center[r],(r,):radius[r]} for r in range(9)]
    def polynomial(indices):
        ans={}
        for r in indices:ans=add(ans,gap[r])
        return ans
    def bounds(i,j):
        if i==j:return (0,0)
        assert i<j;k=LOOK[i,j];return state[0][k],state[1][k]
    def image_bounds(i,j,r,perm):
        v=r+1;indices=perm[i:j];sources=[{'identity':'sum_permuted_gap_boxes','lower':sum(state[0][s] for s in indices),'upper':sum(state[1][s] for s in indices)}]
        if j==v:
            l,u=bounds(i,r);sources.append({'identity':'span(i,r)+g(r+1)','lower':l+state[0][r+1],'upper':u+state[1][r+1]})
            l,u=bounds(i,r+2);sources.append({'identity':'span(i,r+2)-gr','lower':l-state[1][r],'upper':u-state[0][r]})
        else:
            assert i==v;l,u=bounds(r+2,j);sources.append({'identity':'gr+span(r+2,j)','lower':state[0][r]+l,'upper':state[1][r]+u})
            l,u=bounds(r,j);sources.append({'identity':'span(r,j)-g(r+1)','lower':l-state[1][r+1],'upper':u-state[0][r+1]})
        l=max(s['lower'] for s in sources);u=min(s['upper'] for s in sources);assert l<u
        return l,u,sources
    oracle=NormalizedIntegerJet(wdoc);packets=[];packet_lookup={};upper_lookup={};lower_lookup={}
    def scalar_packet(poly,l,u):
        key=(tuple(sorted(poly.items())),l,u)
        if key in packet_lookup:return packet_lookup[key]
        p=F(l+u,2*SC);R=F(u-l,2*SC);assert F(l,SC)<=p<=F(u,SC)
        n,jets=oracle.jets(p);mu=[(v.l+v.u)/2 for v in jets];eps=[(v.u-v.l)/2 for v in jets]
        M5,ks=oracle.fifth(l,u);d=add(poly,{():p},F(-1));powers=[{():F(1)}]
        for _ in range(4):powers.append(mul(powers[-1],d))
        central={}
        for k in range(5):central=add(central,powers[k],mu[k]/factorial(k))
        error={():eps[0]+eps[1]*R}
        error=add(error,powers[2],eps[2]/2+eps[3]*R/6)
        error=add(error,powers[4],eps[4]/24+M5*R/120)
        upper=add(central,error);lower=add(central,error,F(-1));pid=len(packets)
        packets.append({'id':pid,'whole_span_integer_bounds':[l,u],'whole_span_rational_bounds':[str(F(l,SC)),str(F(u,SC))],
            'anchor':str(p),'integer_jet_anchor':n,'anchor_is_whole_span_midpoint':True,'radius_about_anchor':str(R),
            'anchor_derivative_intervals_orders_0_to_4':[[str(v.l),str(v.u)] for v in jets],
            'anchor_derivative_midpoints':list(map(str,mu)),'anchor_derivative_errors':list(map(str,eps)),
            'whole_span_absolute_w5_bound':str(M5),'whole_span_w5_grid_cells':ks,'span_polynomial':pack(poly),
            'd_polynomial':pack(d),'central_quartic':pack(central),'nonnegative_error_polynomial':pack(error),
            'scalar_upper_quartic':pack(upper),'scalar_lower_quartic':pack(lower)})
        packet_lookup[key]=pid;upper_lookup[pid]=upper;lower_lookup[pid]=lower
        return pid
    den=params['denominator'];maps=[];rows=[]
    for r in range(8):
        v=r+1;perm=list(range(9));perm[r],perm[r+1]=r+1,r
        pressure=scale(add(gap[r+1],gap[r],F(-1)),F(params['b_numerators'][r]-params['b_numerators'][r+1],den))
        upper=pressure;changed=[];cancelled=[]
        for i,j,a in params['a_upper']:
            if not a:continue
            assert a>0;oldpoly=polynomial(range(i,j));newpoly=polynomial(perm[i:j])
            if i!=v and j!=v:
                assert oldpoly==newpoly;cancelled.append([i,j]);continue
            l,u=bounds(i,j);oldid=scalar_packet(oldpoly,l,u)
            l,u,sources=image_bounds(i,j,r,perm);newid=scalar_packet(newpoly,l,u)
            weight=F(a,den);difference=scale(add(upper_lookup[newid],lower_lookup[oldid],F(-1)),weight);upper=add(upper,difference)
            changed.append({'edge':[i,j],'weight':str(weight),'image_bound_sources':sources,'old_scalar_packet':oldid,'new_scalar_packet':newid,
                'weighted_difference_upper_quartic':pack(difference),'expected_weighted_difference_upper':str(expect(difference))})
        assert len(changed)+len(cancelled)==41
        constant=upper.get((),F(0));coeff=[(mi[m]-1,-a) for m,a in sorted(upper.items(),key=lambda z:mi[z[0]]) if m]
        divisor=max([F(1,1000),abs(constant)]+[abs(a) for _,a in coeff])
        rows.append({'coefficients':[[k,str(a)] for k,a in coeff],'bound':str(constant),'scale':str(divisor),
            'meta':['unsoftened_global_adjacent_swap_necessary',r,r+1]})
        maps.append({'swap_zero_based':[r,r+1],'moved_vertex':v,'permutation':perm,'unchanged_edges_cancelled':cancelled,
            'changed_edge_packets':changed,'pressure_difference_polynomial':pack(pressure),'difference_upper_quartic':pack(upper),
            'expected_upper_difference_at_old_exact714':str(expect(upper)),'old_exact714_separated':expect(upper)<0})
    assert len(maps)==len(rows)==8 and sum(len(m['changed_edge_packets']) for m in maps)==68
    # Geometry/anchors/error strategy are fixed as before. The coefficient
    # source is changed for formal table identity, never optimized.
    single=json.loads((SINGLE/'swap67-quartic-static.json').read_bytes())
    same67=maps[6]['difference_upper_quartic']==single['difference_upper_quartic']
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==pins
    doc={'scope':__doc__,'status':'complete_fixed_eight_adjacent_swaps_normalized_W_rows_constructed',
        'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,'path':parent['path'],
        'parent_model':'research-goal-20261017-quartic/quartic-model.json.gz','parent_model_sha256':sha(paths[3]),
        'old_model_referenced_intact':True,'old_scalar_rows':5795,'new_unsoftened_scalar_rows':8,'combined_scalar_rows':5803,
        'old_PSD_blocks':47,'PSD_sizes':parent['PSD_sizes'],'scalar_variables_including_energy_slack':715,'slack_index':714,
        'target':parent['target'],'SEP':'123/128','scale':SC,'normalized_gap_center':list(map(str,center)),
        'normalized_gap_radius':list(map(str,radius)),'monomials':[list(m) for m in mon],
        'scalar_packets':packets,'maps':maps,'additional_linear_rows':rows,'w5_grid_cells_rebuilt':len(oracle.cache),
        'all_eight_conditions_simultaneous':True,'swap67_matches_frozen_single_row_exactly':same67,
        'new_row_point_and_fifth_derivative_coefficient_source':'normalized integer_w_Taylor_coefficients only',
        'new_row_old_wprime_coefficients_used':False,'w5_Taylor_degree':18,'w5_Taylor_terms':19,'w5_remainder_power':19,
        'available_actual_API':'WindowCellDerivative.interval with q=5,d=18 and explicit finite check; no concrete check receipt claimed here',
        'actual_analytic_inputs_newly_Lean_proved':False,'actual_w_scalar_sampling_positions_added':0,
        'new_integer_Taylor_tables':0,'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    raw=json.dumps(doc,separators=(',',':'),allow_nan=False).encode();compressed=gzip.compress(raw,compresslevel=9,mtime=0);OUT.write_bytes(compressed)
    receipt={'scope':__doc__,'status':doc['status'],'source_sha256_start':pins,'source_sha256_end':final,'all_sources_unchanged':True,
        'packet_compressed_sha256':sha(OUT),'packet_uncompressed_sha256':hashlib.sha256(raw).hexdigest(),
        'packet_compressed_bytes':len(compressed),'packet_uncompressed_bytes':len(raw),'scalar_packets':len(packets),
        'changed_edge_occurrences':68,'new_unsoftened_rows':8,'combined_scalar_rows':5803,'old_PSD_blocks':47,
        'all_old_rows_and_PSD_unchanged':True,'old_exact714_expectations':[m['expected_upper_difference_at_old_exact714'] for m in maps],
        'old_exact714_separated_by_maps':[m['swap_zero_based'] for m in maps if m['old_exact714_separated']],
        'new_row_old_wprime_coefficients_used':False,'swap67_matches_frozen_single_row_exactly':same67,
        'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    RECEIPT.write_text(json.dumps(receipt,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'status':doc['status'],'scalar_packets':len(packets),'w5_grid_cells':len(oracle.cache),
        'compressed_bytes':len(compressed),'raw_bytes':len(raw),'old_exact714_expectations':[float(F(v)) for v in receipt['old_exact714_expectations']],
        'elapsed_milliseconds':receipt['elapsed_milliseconds']}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
