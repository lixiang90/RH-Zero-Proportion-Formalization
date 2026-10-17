"""One coherent actual-sextic STATIC packet, retaining the frozen old model.

41 original positive ledger edges, deterministic whole-span midpoint
anchors, normalized actual-W jets0..6 and q7,d16 whole-grid w7 bounds.
Absolute L6 avoids old F0 and w-prime literals. P5/E6 and E6+/-yP5 are
181 unsoftened degree<=6 scalar/M0 rows, never degree8 M1 blocks.
No solver, new point fit, kernel sampling, anchor scan or Lean invocation.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
from array import array
import ctypes,gzip,hashlib,json,os,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
STATIC=ROOT/'research-goal-20261017-degree6-static';OLD=ROOT/'research-goal-20261016'
OUT=HERE/'actual-sextic.json.gz';MAP=HERE/'sextic-shifts.bin';RECEIPT=HERE/'sextic-build.json'
SC=32768;DS=10**15;C=F(11,1250);RSS_LIMIT=1536*1024**2;FILE_LIMIT=40*1024**2
ALL=[(i,i+1) for i in range(9)]+[(i,j) for i in range(9) for j in range(i+2,10)]
SLOT={e:k for k,e in enumerate(ALL)}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rec(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}
def add(p,q,c=F(1)):
    out=p.copy()
    for m,a in q.items():
        z=out.get(m,F(0))+c*a
        if z:out[m]=z
        else:out.pop(m,None)
    return out
def mul(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():
            t=tuple(sorted(m+n));assert len(t)<=6;out=add(out,{t:a*b})
    return out
class I:
    def __init__(self,l,u=None):self.l=F(l);self.u=F(l if u is None else u);assert self.l<=self.u
    def __add__(self,x):
        if not isinstance(x,I):x=I(x)
        return I(self.l+x.l,self.u+x.u)
    __radd__=__add__
    def __mul__(self,x):
        if not isinstance(x,I):x=I(x)
        z=[self.l*x.l,self.l*x.u,self.u*x.l,self.u*x.u];return I(min(z),max(z))
    __rmul__=__mul__
class NormalizedW:
    def __init__(self,doc):
        self.cs={int(n):[I(*v) for v in row] for n,row in doc['integer_w_Taylor_coefficients'].items()}
        assert len(self.cs)==33 and set(map(len,self.cs.values()))=={24}
        self.M24=F(44,7)**24;self.grid={}
    def point(self,p):
        n=round(p);delta=p-n;assert 1<=n<=32 and abs(delta)<=F(1,2);values=[]
        for j in range(7):
            value=I(0)
            for k in range(23,j-1,-1):value=value*delta+self.cs[n][k]*F(factorial(k),factorial(k-j))
            rem=self.M24*abs(delta)**(24-j)/factorial(24-j);values.append(I(value.l-rem,value.u+rem))
        return n,values
    def seventh_cell(self,k):
        if k not in self.grid:
            n=round(F(2*k+1,128));assert 1<=n<=32
            delta=I(F(k,64)-n,F(k+1,64)-n);assert F(-1,2)<=delta.l<=delta.u<=F(1,2)
            value=I(0)
            for j in range(23,6,-1):value=value*delta+self.cs[n][j]*F(factorial(j),factorial(j-7))
            rem=self.M24*F(1,2)**17/factorial(17);lo,hi=value.l-rem,value.u+rem
            raw=max(abs(lo),abs(hi))*DS;bound=F(-((-raw.numerator)//raw.denominator),DS)
            self.grid[k]={'cell':k,'nearest_integer':n,'actual_w7_lower':str(lo),'actual_w7_upper':str(hi),'absolute_bound':str(bound)}
        return F(self.grid[k]['absolute_bound'])
    def whole(self,l,u):
        assert 0<=l<u<=32*SC;ks=list(range(l//512,(u+511)//512));assert ks
        return max(self.seventh_cell(k) for k in ks),ks
def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi')
    p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD];m=PMC();m.cb=ctypes.sizeof(m)
    assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}

def main():
    assert not any(p.exists() for p in [OUT,MAP,RECEIPT]);began=time.monotonic()
    paths=[Path(__file__),STATIC/'degree6-files.json',STATIC/'degree6-model.json.gz',STATIC/'degree6-build.json',
        ROOT/'research-goal-20261017-quartic/quartic-model.json.gz',OLD/'window_normalized_interval.json',
        OLD/'window_normalized_interval.py',ROOT/'research-20261016-followup/window_reweight_rational.json',
        ROOT/'StructuralGoal20261016/WindowJetTableData.lean',ROOT/'StructuralGoal20261016/WindowRawCoefficients.lean',
        ROOT/'StructuralGoal20261016/WindowCellDerivative.lean',ROOT/'research-goal-20261017-sextic-envelope-plan/plan-files.json',
        ROOT/'research-goal-20261017-sextic-envelope-plan/PLAN.md']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    report={'scope':__doc__,'phase':'before_loading','source_sha256_start':initial,'memory_snapshots':[],
        'RSS_guard_bytes':RSS_LIMIT,'single_file_uncompressed_guard_bytes':FILE_LIMIT,
        'solver_calls':0,'Lean_invocations':0,'new_points_or_fits':0,'new_actual_sampling_positions':0,
        'new_analytic_instances_Lean_proved':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
    def save(phase):
        m=memory();m['phase']=phase;m['elapsed_milliseconds']=int((time.monotonic()-began)*1000);report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
        report.update({'phase':phase,'source_sha256_end':final,'all_sources_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        RECEIPT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
        if m['peak_working_set_bytes']>RSS_LIMIT:raise MemoryError('1.5GiB working-set guard')
    save('before_loading')
    try:
        manifest=json.loads(paths[1].read_bytes())
        for r in manifest['package_files']+manifest['dependency_files']:assert sha(ROOT/r['path'])==r['sha256']
        raw=gzip.decompress(paths[2].read_bytes());base=json.loads(raw);bb=json.loads(paths[3].read_bytes())
        assert hashlib.sha256(raw).hexdigest()==bb['model_uncompressed_sha256'];del raw
        # Only geometry/prefix fields are used from the old quartic packet;
        # old F0, edge jets and old w-prime literal data are NEVER read.
        old=json.loads(gzip.decompress(paths[4].read_bytes()));state=old['cell'];center=list(map(F,old['normalized_gap_center']));radius=list(map(F,old['normalized_gap_radius']))
        assert old['path']==base['path']=='r001000001000100110011001' and base['target']=='11/1250'
        assert base['nonconstant_moment_columns']==5004 and base['energy_slack_column']==5004
        mon=[tuple(m) for m in base['monomials']];mi={m:k for k,m in enumerate(mon)}
        assert len(mon)==5005 and [list(m) for m in mon[:715]]==old['monomials']
        margins=[l-31488 for l in state[0][:9]];assert min(margins)>0
        wdoc=json.loads(paths[5].read_bytes());params=json.loads(paths[7].read_bytes())
        assert wdoc['source_sha256']==sha(paths[6]) and wdoc['parameter_sha256']==sha(paths[7])
        terms=[(i,j,a) for i,j,a in params['a_upper'] if a];assert len(terms)==41 and all(a>0 for _,_,a in terms)
        den=params['denominator'];oracle=NormalizedW(wdoc)
        def pack(p):return [[mi[m],str(a)] for m,a in sorted(p.items(),key=lambda z:mi[z[0]])]
        pressure={};b=[F(a,den) for a in params['b_numerators']]
        for r in range(9):pressure=add(pressure,{():b[r]*center[r],(r,):b[r]*radius[r]})
        powers=[];edges=[]
        for eid,(i,j,a) in enumerate(terms):
            axis=SLOT[i,j];l,u=state[0][axis],state[1][axis];p=F(l+u,2*SC);R=F(u-l,2*SC)
            assert F(l,SC)<=p<=F(u,SC) and R>0
            n,jets=oracle.point(p);mu=[(q.l+q.u)/2 for q in jets];eps=[(q.u-q.l)/2 for q in jets];assert all(e>=0 for e in eps)
            M7,ks=oracle.whole(l,u);assert M7>=0
            d={():sum(center[i:j])-p,**{(r,):radius[r] for r in range(i,j)}};d={m:v for m,v in d.items() if v}
            edgepowers=[{():F(1)}]
            for _ in range(6):edgepowers.append(mul(edgepowers[-1],d))
            pids=[]
            for k,power in enumerate(edgepowers):
                pids.append(len(powers));powers.append({'id':len(powers),'edge':eid,'degree':k,'terms':pack(power)})
            T=[mu[k]/factorial(k) for k in range(7)]
            A=[eps[0]+eps[1]*R,F(0),eps[2]/2+eps[3]*R/6,F(0),eps[4]/24+eps[5]*R/120,F(0),eps[6]/720+M7*R/5040]
            L=[t-e for t,e in zip(T,A)];U=[mu[k+1]/factorial(k) for k in range(6)]
            E=[eps[1]+eps[2]*R,F(0),eps[3]/2+eps[4]*R/6,F(0),eps[5]/24+eps[6]*R/120,F(0),M7/720]
            assert all(v>=0 for v in A+E) and all(U[k]==(k+1)*T[k+1] for k in range(6))
            edges.append({'id':eid,'edge':[i,j],'weight':str(F(a,den)),'original_span_axis':axis,
                'whole_span_integer_bounds':[l,u],'whole_span_rational_bounds':[str(F(l,SC)),str(F(u,SC))],
                'anchor':str(p),'anchor_policy':'fixed whole-span midpoint','integer_jet_anchor':n,'radius_about_anchor':str(R),
                'point_intervals_orders_0_to_6':[[str(q.l),str(q.u)] for q in jets],
                'point_derivative_midpoints':list(map(str,mu)),'point_derivative_errors':list(map(str,eps)),
                'whole_span_absolute_w7_bound':str(M7),'whole_span_w7_grid_cells':ks,'d_polynomial':pack(d),'power_ids':pids,
                'central_T6_coefficients_in_d':list(map(str,T)),'energy_A6_coefficients_in_d':list(map(str,A)),
                'absolute_L6_coefficients_in_d':list(map(str,L)),'derivative_U5_coefficients_in_d':list(map(str,U)),
                'derivative_E6_coefficients_in_d':list(map(str,E))})
        assert len(powers)==287
        save('all_41_absolute_sextic_scalar_packets_and_spanpowers_constructed')
        # Moment target maps for all unshifted powers and all y_s*U5 powers.
        # This is exactly the information needed by the181 scalar/M0 rows.
        target=array('H');plans=[];plan_lookup={}
        for power in powers:
            shifts=range(10) if power['degree']<=5 else [0]
            for shift in shifts:
                suffix=mon[shift];offset=len(target)
                ids=[mi[tuple(sorted(mon[k]+suffix))] for k,_ in power['terms']]
                assert len(ids)==len(set(ids)) and all(len(mon[k])<=6 for k in ids)
                target.extend(ids);pid=len(plans);plans.append([power['id'],shift,offset,len(ids)]);plan_lookup[power['id'],shift]=pid
        assert len(plans)==2501
        if sys.byteorder!='little':target.byteswap()
        assert len(target)*2<FILE_LIMIT;MAP.write_bytes(target.tobytes())
        incident=[[e['id'] for e in edges if e['edge'][0]<=r<e['edge'][1]] for r in range(9)]
        rows=[{'id':0,'kind':'absolute_energy_L6','sense':'less_or_equal','bound':str(C),'maximum_degree':6,'diagnostic_slack_column':None}]
        for r in range(9):
            for test in range(10):
                for sign in [-1,1]:
                    rows.append({'id':len(rows),'kind':'free_gradient_E6_plus_sign_test_P5','coordinate':r,
                        'test_monomial_id':test,'sign':sign,'sense':'greater_or_equal','bound':'0','maximum_degree':6,'diagnostic_slack_column':None})
        assert len(rows)==181 and len([r for r in rows if r['kind'].startswith('free_gradient')])==180
        assert all(r['diagnostic_slack_column'] is None for r in rows)
        # Every actual multiplication used by a row must have a stored plan;
        # derivative coefficients use only powers0..5, even error0,2,4,6.
        for e in edges:
            assert all((pid,0) in plan_lookup for pid in e['power_ids'])
            for test in range(10):assert all((e['power_ids'][k],test) in plan_lookup for k in range(6))
        save('all_181_unsoftened_rows_and_degree6_target_maps_constructed')
        doc={'scope':__doc__,'format_version':1,'status':'coherent_absolute_sextic_scalar_packet_statically_constructed',
            'source_sha256_start':initial,'source_sha256_end':initial,'all_sources_unchanged':True,'path':base['path'],'target':str(C),'SEP':'123/128',
            'retain_old_static_model':{**rec(paths[2]),'manifest':rec(paths[1]),'all_old_rows_and_73_PSD_retained':True},
            'underlying_real_variables':9,'monomials':[list(m) for m in mon],'nonconstant_moment_columns':5004,'energy_slack_column':5004,
            'same_old_715_monomial_prefix':True,'normalized_gap_center':list(map(str,center)),'normalized_gap_radius':list(map(str,radius)),
            'all_nine_original_free_margins_SC_units':margins,'new_scalar_kernel_source':'normalized integer_w_Taylor_coefficients only',
            'new_energy_uses_old_F0':False,'new_envelopes_use_old_wprime_literals':False,'global_absolute_w24_bound':str(oracle.M24),
            'point_Taylor_terms':24,'point_Taylor_degree':23,'w7_Taylor_degree':16,'w7_Taylor_terms':17,'w7_remainder_power':17,
            'whole_grid_w7_cells':[oracle.grid[k] for k in sorted(oracle.grid)],'edges':edges,'span_powers':powers,
            'pressure_polynomial':pack(pressure),'pressure_coefficients_b':list(map(str,b)),'coordinate_incident_edges':incident,
            'shift_plans':plans,'shift_plan_schema':['spanPowerID','testMonomialID','targetOffset','termCount'],
            'shift_target_indices':{**rec(MAP),'encoding':'little-endian uint16 canonical MOMENT IDs, constant0; otherID maps toID-1 column'},
            'spanpower_coefficients_stored_once':True,'same_shared_y_moments_not_independent_edge_moments':True,
            'new_scalar_rows':rows,'new_PSD_blocks':0,'new_row_localizer_basis':'M0 only; degree6 times M1 would be degree8 and is forbidden',
            'aggregate_L6_definition':'pressure+sum_edge weight*sum_k absolute_L6_coefficients[k]*span_power(edge,k)',
            'aggregate_P5_definition':'P5[r]=b[r]+sum_incident weight*sum_k derivative_U5_coefficients[k]*span_power(edge,k)',
            'aggregate_E6_definition':'E6[r]=sum_incident weight*sum_k derivative_E6_coefficients[k]*span_power(edge,k)',
            'gradient_row_definition':'E6[r]+sign*(momentMonomial[test]*P5[r])>=0; E6 is NOT multiplied by test',
            'unsoftened_absolute_energy_row':True,'old_scalar_rows':14383,'new_scalar_row_count':181,'combined_scalar_rows':14564,
            'whole_span_and_actual_point_enclosures_remain_explicit_analytic_instances':True,
            'actual_analytic_instances_newly_Lean_proved':False,'new_points_or_fits':0,'new_actual_sampling_positions':0,
            'solver_calls':0,'Lean_invocations':0,'strict_new_inequality_violation_proven':False,'cell_exclusion_proven':False,'new_zero_proportion_proven':False}
        rawhash=hashlib.sha256();rawcount=0;partial=OUT.with_suffix(OUT.suffix+'.partial');assert not partial.exists()
        with partial.open('wb') as sink:
            with gzip.GzipFile(fileobj=sink,mode='wb',compresslevel=9,mtime=0) as stream:
                for chunk in json.JSONEncoder(separators=(',',':'),allow_nan=False).iterencode(doc):
                    data=chunk.encode();rawcount+=len(data)
                    if rawcount>FILE_LIMIT:raise MemoryError('40MiB raw packet guard exceeded')
                    rawhash.update(data);stream.write(data)
        partial.replace(OUT)
        report.update({'path':base['path'],'target':str(C),'old_model_retained':True,'new_positive_edges':41,
            'new_scalar_rows':181,'new_energy_row_unsoftened':True,'combined_scalar_rows':14564,'new_PSD_blocks':0,
            'canonical_moments':5005,'old_monomial_prefix':715,'energy_slack_column':5004,'span_powers':len(powers),
            'span_power_coefficient_terms':sum(len(p['terms']) for p in powers),'shift_plans':len(plans),'shift_target_references':len(target),
            'whole_grid_w7_cells':len(oracle.grid),'point_jet_orders':[0,1,2,3,4,5,6],
            'normalized_W_only_for_new_envelopes':True,'old_F0_used_by_new_energy':False,'old_wprime_used_by_new_envelopes':False,
            'packet':rec(OUT),'packet_uncompressed_bytes':rawcount,'packet_uncompressed_sha256':rawhash.hexdigest(),'shift_target_indices':rec(MAP),
            'resource_gate_passed':True,'new_point_or_moment_evaluations':0,'strict_new_inequality_violation_proven':False})
        assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
        save('complete_coherent_actual_sextic_STATIC_packet_resource_gate_passed')
    except BaseException as exc:
        report['resource_gate_passed']=False;report['exception']=repr(exc);save('sextic_static_stopped_without_solver');raise
    print(json.dumps({k:report[k] for k in ['phase','new_positive_edges','new_scalar_rows','span_powers','span_power_coefficient_terms',
        'shift_plans','shift_target_references','whole_grid_w7_cells','packet_uncompressed_bytes','elapsed_milliseconds']}),flush=True)
    print(json.dumps({'peak_working_set_bytes':max(m['peak_working_set_bytes'] for m in report['memory_snapshots']),
        'packet_gzip_bytes':OUT.stat().st_size,'shift_bytes':MAP.stat().st_size}),flush=True)
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
