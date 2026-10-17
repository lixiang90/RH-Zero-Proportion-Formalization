"""Independent exact gate for eight normalized-W adjacent-swap rows.

Only the eight new rows and their shared scalar packets are reconstructed.
The frozen5795 rows/47 PSD blocks are hash-bound and referenced unchanged;
their old proof is not repeated. No producer import, optimizer or Lean.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import factorial
import argparse, gzip, hashlib, importlib.util, json, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
FOLDER=ROOT/'research-goal-20261017-swap-family-quartic'
PACKET=FOLDER/'swap-family-normalized.json.gz';BUILD=FOLDER/'swap-family-normalized-build.json'
OUT=HERE/'independent-replay.json';SC=32768;DS=10**15
PACKET_SHA='293ef092f90b1a18e96cf45552afb55a76ebc7b94324126ef04ea567504c248a'
BUILD_SHA='c5bad610e22c4c99559453bbe14c9b5377ea9fc9acf12fd71381103142baadbe'
HELPER=ROOT/'research-goal-20261017-swap67-audit/independent_replay.py'
HELPER_SHA='1f1bafc9b1eb072d450ffe36da7a45ec2f4dec46868cf9fbda8700e0ed1e17cf'


def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();assert digest(PACKET)==PACKET_SHA and digest(BUILD)==BUILD_SHA and digest(HELPER)==HELPER_SHA
    spec=importlib.util.spec_from_file_location('frozen_independent_polynomial_primitives',HELPER)
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
    add,scale,mul=h.plus,h.scaled,h.times
    raw=gzip.decompress(PACKET.read_bytes());p=json.loads(raw);build=json.loads(BUILD.read_bytes())
    assert build['packet_compressed_sha256']==PACKET_SHA and build['packet_uncompressed_sha256']==hashlib.sha256(raw).hexdigest()
    assert build['packet_compressed_bytes']==PACKET.stat().st_size and build['packet_uncompressed_bytes']==len(raw)
    inputs={**p['source_sha256_start'],PACKET.relative_to(ROOT).as_posix():PACKET_SHA,BUILD.relative_to(ROOT).as_posix():BUILD_SHA,
      HELPER.relative_to(ROOT).as_posix():HELPER_SHA,Path(__file__).relative_to(ROOT).as_posix():digest(Path(__file__))}
    assert p['source_sha256_start']==p['source_sha256_end']==build['source_sha256_start']==build['source_sha256_end']
    for n,sha in inputs.items():assert digest(ROOT/n)==sha,('source changed',n)
    modelpath=ROOT/p['parent_model'];assert digest(modelpath)==p['parent_model_sha256']
    model=json.loads(gzip.decompress(modelpath.read_bytes()))
    assert p['parent_model']=='research-goal-20261017-quartic/quartic-model.json.gz'
    assert len(model['linear_rows'])==p['old_scalar_rows']==5795
    assert len(model['PSD_blocks'])==p['old_PSD_blocks']==47 and model['PSD_sizes']==p['PSD_sizes']==[55]+[10]*46
    assert model['slack_index']==p['slack_index']==714 and p['scalar_variables_including_energy_slack']==715
    assert p['new_unsoftened_scalar_rows']==8 and p['combined_scalar_rows']==5803 and len(p['maps'])==len(p['additional_linear_rows'])==8
    assert p['old_model_referenced_intact'] and p['target']==model['target']=='11/1250'
    assert p['new_row_old_wprime_coefficients_used'] is False and p['w5_Taylor_degree']==18 and p['w5_Taylor_terms']==19 and p['w5_remainder_power']==19
    primal=json.loads((ROOT/'research-goal-20261017-quartic/quartic-exact-primal.json').read_bytes())
    assert primal['status']=='strict_exact_shared_quartic_outer_relaxation_feasible' and p['path']==model['path']==primal['path']
    mon=[m for d in range(5)for m in combinations_with_replacement(range(9),d)]
    assert mon==list(map(tuple,p['monomials']))==list(map(tuple,model['monomials'])) and len(mon)==715
    mi={m:i for i,m in enumerate(mon)};mom=[F(1)]+list(map(F,primal['rational_714_moments']));assert len(mom)==715
    def pack(poly):return [[mi[m],str(v)]for m,v in sorted(poly.items(),key=lambda kv:mi[kv[0]])]
    def expect(poly):return sum((v*mom[mi[m]]for m,v in poly.items()),F(0))
    center=list(map(F,model['normalized_gap_center']));radius=list(map(F,model['normalized_gap_radius']));state=model['cell']
    assert p['normalized_gap_center']==model['normalized_gap_center'] and p['normalized_gap_radius']==model['normalized_gap_radius']
    assert all(center[r]==F(state[0][r]+state[1][r],2*SC) and radius[r]==F(state[1][r]-state[0][r],2*SC)>0 for r in range(9))
    assert F(p['SEP'])==F(123,128) and all(F(state[0][r],SC)>F(123,128) for r in range(9))
    gap=[{():center[r],(r,):radius[r]}for r in range(9)]
    def poly(ids):
        ans={}
        for r in ids:ans=add(ans,gap[r])
        return ans
    def bound(i,j):
        if i==j:return 0,0
        z=h.SLOT[i,j];return state[0][z],state[1][z]
    def image(i,j,r,perm):
        ids=perm[i:j];rows=[{'identity':'sum_permuted_gap_boxes','lower':sum(state[0][s]for s in ids),'upper':sum(state[1][s]for s in ids)}]
        if j==r+1:
            l,u=bound(i,r);rows.append({'identity':'span(i,r)+g(r+1)','lower':l+state[0][r+1],'upper':u+state[1][r+1]})
            l,u=bound(i,r+2);rows.append({'identity':'span(i,r+2)-gr','lower':l-state[1][r],'upper':u-state[0][r]})
        else:
            assert i==r+1;l,u=bound(r+2,j);rows.append({'identity':'gr+span(r+2,j)','lower':state[0][r]+l,'upper':state[1][r]+u})
            l,u=bound(r,j);rows.append({'identity':'span(r,j)-g(r+1)','lower':l-state[1][r+1],'upper':u-state[0][r+1]})
        return max(s['lower']for s in rows),min(s['upper']for s in rows),rows
    wdoc=json.loads((ROOT/'research-goal-20261016/window_normalized_interval.json').read_bytes())
    pars=json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    assert wdoc['parameter_sha256']==digest(ROOT/'research-20261016-followup/window_reweight_rational.json')
    wt={int(n):[tuple(map(F,v))for v in row]for n,row in wdoc['integer_w_Taylor_coefficients'].items()}
    assert set(wt)==set(range(33)) and all(len(row)==24 for row in wt.values())
    M24=F(44,7)**24;grids={};checked={};keys={}
    def grid5(k):
        if k not in grids:
            n=round(F(2*k+1,128));d=(F(k,64)-n,F(k+1,64)-n);assert 1<=n<=32 and -F(1,2)<=d[0]<=d[1]<=F(1,2)
            val=(F(0),F(0))
            for j in reversed(range(5,24)):val=h.iadd(h.imul(val,d),h.iscale(wt[n][j],F(factorial(j),factorial(j-5))))
            rem=M24*F(1,2)**19/factorial(19);z=max(abs(val[0]-rem),abs(val[1]+rem))*DS
            grids[k]=F((z.numerator+z.denominator-1)//z.denominator,DS)
        return grids[k]
    assert len(p['scalar_packets'])==87 and [s['id']for s in p['scalar_packets']]==list(range(87))
    def scalar(pid,span,l,u):
        key=(tuple(sorted(span.items())),l,u)
        if pid in checked:
            assert checked[pid][0]==key;return checked[pid][1:]
        assert key not in keys;keys[key]=pid
        s=p['scalar_packets'][pid];assert s['whole_span_integer_bounds']==[l,u] and 0<=l<u<=32*SC
        assert s['whole_span_rational_bounds']==[str(F(l,SC)),str(F(u,SC))]
        anchor=F(l+u,2*SC);R=F(u-l,2*SC);n=round(anchor);delta=anchor-n
        assert 1<=n<=32 and abs(delta)<=F(1,2) and F(s['anchor'])==anchor and s['integer_jet_anchor']==n and F(s['radius_about_anchor'])==R
        jets=[]
        for j in range(5):
            val=(F(0),F(0))
            for k in range(j,24):val=h.iadd(val,h.iscale(wt[n][k],F(factorial(k),factorial(k-j))*delta**(k-j)))
            rem=M24*abs(delta)**(24-j)/factorial(24-j);jets.append((val[0]-rem,val[1]+rem))
        assert [[str(a),str(b)]for a,b in jets]==s['anchor_derivative_intervals_orders_0_to_4']
        mu=[(a+b)/2 for a,b in jets];eps=[(b-a)/2 for a,b in jets];assert all(e>=0 for e in eps)
        assert mu==list(map(F,s['anchor_derivative_midpoints'])) and eps==list(map(F,s['anchor_derivative_errors']))
        cells=list(range(l//512,(u+511)//512));assert cells==s['whole_span_w5_grid_cells'];M5=max(grid5(k)for k in cells)
        assert M5==F(s['whole_span_absolute_w5_bound'])
        d=add(span,{():anchor},F(-1));powers=[{():F(1)}]
        for j in range(4):powers.append(mul(powers[-1],d))
        central={}
        for j in range(5):central=add(central,powers[j],mu[j]/factorial(j))
        c0=eps[0]+eps[1]*R;c2=eps[2]/2+eps[3]*R/6;c4=eps[4]/24+M5*R/120;assert min(c0,c2,c4)>=0
        error=add(add({():c0},powers[2],c2),powers[4],c4);up=add(central,error);low=add(central,error,F(-1))
        for name,v in [('span_polynomial',span),('d_polynomial',d),('central_quartic',central),('nonnegative_error_polynomial',error),('scalar_upper_quartic',up),('scalar_lower_quartic',low)]:assert s[name]==pack(v)
        checked[pid]=(key,up,low);return up,low
    results=[];edgecount=0;all_totals=[]
    for r,(mapping,row)in enumerate(zip(p['maps'],p['additional_linear_rows'])):
        perm=list(range(9));perm[r],perm[r+1]=r+1,r
        assert mapping['swap_zero_based']==[r,r+1] and mapping['moved_vertex']==r+1 and mapping['permutation']==perm
        pressure=scale(add(gap[r+1],gap[r],F(-1)),F(pars['b_numerators'][r]-pars['b_numerators'][r+1],pars['denominator']))
        assert pack(pressure)==mapping['pressure_difference_polynomial'];total=pressure;changed=[];cancel=[]
        byedge={tuple(e['edge']):e for e in mapping['changed_edge_packets']}
        for i,j,a in pars['a_upper']:
            assert a>=0
            if not a:continue
            before=poly(range(i,j));after=poly(perm[i:j])
            if before==after:cancel.append([i,j]);continue
            changed.append([i,j]);e=byedge[i,j];w=F(a,pars['denominator']);assert F(e['weight'])==w>0
            l,u=bound(i,j);_,oldlow=scalar(e['old_scalar_packet'],before,l,u)
            l,u,sources=image(i,j,r,perm);assert sources==e['image_bound_sources'];newup,_=scalar(e['new_scalar_packet'],after,l,u)
            diff=scale(add(newup,oldlow,F(-1)),w);assert pack(diff)==e['weighted_difference_upper_quartic']
            assert expect(diff)==F(e['expected_weighted_difference_upper']);total=add(total,diff)
        assert len(changed)+len(cancel)==41 and cancel==mapping['unchanged_edges_cancelled'] and set(byedge)==set(map(tuple,changed))
        assert pack(total)==mapping['difference_upper_quartic'];expected=expect(total)
        assert expected==F(mapping['expected_upper_difference_at_old_exact714']) and mapping['old_exact714_separated']==(expected<0)
        constant=total.get((),F(0));coeff=[[mi[m]-1,str(-v)]for m,v in sorted(total.items(),key=lambda kv:mi[kv[0]])if m]
        assert row['coefficients']==coeff and all(0<=k<714 for k,_ in coeff)
        assert F(row['bound'])==constant and row['meta']==['unsoftened_global_adjacent_swap_necessary',r,r+1]
        divisor=max([F(1,1000),abs(constant)]+[abs(F(v))for _,v in coeff]);assert F(row['scale'])==divisor>0
        # -sum(nonconstant D*z)<=D_constant is exactly D>=0, with no slack coefficient.
        results.append({'swap':[r,r+1],'changed':len(changed),'cancelled':len(cancel),'polynomial_terms':len(total),
          'expected_at_old_exact714':str(expected),'old_exact714_violates':expected<0,'linear_variable_max':max(k for k,_ in coeff)})
        edgecount+=len(changed);all_totals.append(total)
    assert set(checked)==set(range(87)) and len(grids)==p['w5_grid_cells_rebuilt']==622 and edgecount==68
    single=json.loads((ROOT/'research-goal-20261017-swap67-quartic/swap67-quartic-static.json').read_bytes())
    same67=pack(all_totals[6])==single['difference_upper_quartic'];assert same67==p['swap67_matches_frozen_single_row_exactly'] is True
    assert [m['swap']for m in results if m['old_exact714_violates']]==build['old_exact714_separated_by_maps']
    assert [m['expected_at_old_exact714']for m in results]==build['old_exact714_expectations']
    for n,sha in inputs.items():assert digest(ROOT/n)==sha
    receipt={'scope':__doc__,'passed':True,'packet_sha256':PACKET_SHA,'build_sha256':BUILD_SHA,'source_sha256':digest(Path(__file__)),
      'source_sha256_start':inputs,'source_sha256_end':inputs,'all_sources_unchanged':True,
      'old_parent_model_sha256':p['parent_model_sha256'],'old_5795_rows_and_47_PSD_referenced_unchanged':True,
      'old_full_proof_reexecuted':False,'old_scalar_rows':5795,'new_unsoftened_rows':8,'combined_scalar_rows':5803,
      'old_PSD_blocks':47,'moment_monomials':715,'nonconstant_moment_variables':714,'energy_slack_index':714,
      'new_rows_have_no_energy_slack_coefficient':True,'scalar_packets_rebuilt':87,'changed_edge_occurrences':68,
      'selected_normalized_W_fifth_derivative_grid_cells':622,'new_row_old_wprime_coefficients_used':False,
      'same_nine_normalized_variables_and_whole_image_DBM_bounds':True,'upper_minus_lower_error_directions_checked':True,
      'all_eight_new_necessary_row_signs_and_positive_scales_checked':True,'swap67_matches_frozen_single_exactly':True,
      'maps':results,'actual_global_Orthant_minimum_necessary_conditions_not_cell_local_KKT':True,
      'producer_imports':0,'solver_calls':0,'Lean_invocations':0,'cell_exclusion_proven':False,'new_zero_proportion_proven':False,
      'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(receipt,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'packet_sha256':PACKET_SHA,'eight_maps':8,'scalar_packets':87,'grid_cells':622,
      'old_exact714_violated_maps':[m['swap']for m in results if m['old_exact714_violates']],
      'source_sha256':digest(Path(__file__)),'receipt_sha256':digest(OUT)if args.write_receipt else None,'seconds':receipt['seconds']}),flush=True)


if __name__=='__main__':
    assert __debug__
    main()
