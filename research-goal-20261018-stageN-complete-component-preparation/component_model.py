"""N generic original-component integer helpers; definitions only at import."""
from fractions import Fraction as F

Q=32768
R=1024
D=10**9
V=10**10
SA=10**20
KAPPA=Q*V*R
OBJECTIVE_SCALE=2*KAPPA*SA
CN=893616123055294719
C_N=893766123055294719
TARGET=4*KAPPA*C_N
NCOLS=77
CHARTS=('id/id','id/rev','rev/id','rev/rev')

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def incidence(i,j):
    a=[0]*10;a[i]-=1;a[j]+=1;return a
def mapped_span(i,j,offset,reverse):
    return (offset+8-j,offset+8-i) if reverse else (offset+i,offset+j)
def mapped_gap(r,offset,reverse):return offset+(7-r if reverse else r)
def integer(value):
    value=F(value);assert value.denominator==1;return value.numerator
def raw_vector(row,group_count):
    v=list(row['position10'][1:])+[0]*group_count
    if row['epigraph_index'] is not None:v[9+row['epigraph_index']]=row['epigraph_coefficient']
    return v
def objective(model):return model['objective_position10'][1:]+model['objective_epigraph']
def objective_full(model):return model['objective_position10']+model['objective_epigraph']

def assemble_unpooled(original_windows,cells,source_model,all_spans,chart):
    """Called only after the future gate. No new FS/anchor/kernel is selected."""
    assert 0<=chart<4 and len(original_windows)==2
    cell_ids=tuple(w['cell_id'] for w in original_windows)
    reverses=(chart>=2,chart%2==1)
    placements=list(zip(cell_ids,[0,1],reverses))
    assert len(source_model['TS'])==34 and len(source_model['BS'])==8 and len(all_spans)==36
    rows=[];terms=[];pressure=[0]*10;mixed_position=[0]*10;mixed_constant=F(0)
    def add(pos,tidx,tc,bound,kind,metadata):
        assert len(pos)==10 and sum(pos)==0 and all(type(v) is int for v in pos)
        assert type(bound) is int and ((tidx is None and tc==0) or (0<=tidx<68 and tc==-1))
        rows.append({'row_id':len(rows),'position10':pos,'epigraph_index':tidx,
            'epigraph_coefficient':tc,'bound':bound,'kind':kind,**metadata})
        return len(rows)-1
    for wi,(cid,offset,reverse) in enumerate(placements):
        state=cells[cid]['state'];lower=state['L']+state['A'];upper=state['U']+state['B']
        for slot,((i,j),l,u) in enumerate(zip(all_spans,lower,upper)):
            ii,jj=mapped_span(i,j,offset,reverse);a=incidence(ii,jj)
            add(a,None,0,20*u,'original_span_upper',{'window':wi,'original_span_slot':slot})
            add([-v for v in a],None,0,-20*l,'original_span_lower',{'window':wi,'original_span_slot':slot})
    for r in range(9):add(incidence(r+1,r),None,0,-17*Q,'original_separation',{'gap':r})
    for wi,(offset,reverse) in enumerate(zip([0,1],reverses)):
        sign=-1 if reverse else 1;a=[0]*10
        for i,v in [(offset,-1),(offset+1,1),(offset+7,1),(offset+8,-1)]:a[i]+=sign*v
        add(a,None,0,0,'true_ordered_four_point',{'window':wi,'reverse':reverse})
    assert len(rows)==155
    for wi,(window,offset,reverse) in enumerate(zip(original_windows,[0,1],reverses)):
        cid=window['cell_id']
        for r,bs in enumerate(source_model['BS']):
            k=mapped_gap(r,offset,reverse);a=incidence(k,k+1)
            for v in range(10):pressure[v]+=D*R*bs*a[v]
        for term in window['terms']:
            e=len(terms);ti=term['term_id'];i,j=term['edge'];a=term['external_weight_numerator']
            assert tuple(source_model['TS'][ti][:3])==(i,j,a) and a>0
            ii,jj=mapped_span(i,j,offset,reverse);normal=incidence(ii,jj)
            L,U=term['original_term_bounds'];L0=term['original_L0'];uc=term['uc_upper']
            assert L0<=L<=U<=uc and uc==max(L+1,U)
            lb=term['original_lb_table_value'];assert type(lb) is int and lb>=0
            const=Q*R*lb
            components=[{'kind':'constant','E':const,'S':0,'row_id':add([0]*10,e,-1,-const,
                'constant_component',{'term':e,'window':wi,'original_term':ti})}]
            slot_components={}
            for slot,(amount,anchor) in enumerate(zip([term['mass_first'],term['mass_second']],term['FS'][2:])):
                if not amount:continue
                assert amount>0 and anchor in source_model['PTraw'];raw=source_model['PTraw'][anchor]
                vl=max(0,anchor-((raw>>96)&((1<<20)-1)));vu=anchor+(raw>>116)
                assert 1<=vu and vl<=L<=anchor<=U<=vu
                trip=raw&((1<<96)-1);v=trip&((1<<32)-1)
                dlo=((trip>>32)&((1<<32)-1))-2*D;dhi=2*D-(trip>>64)
                E=Q*R*v-10*R*(dlo*L0+dhi*(anchor-L0));S=(R//2)*dlo
                rid=add([S*x for x in normal],e,-1,-E,'active_anchor_component',
                    {'term':e,'window':wi,'original_term':ti,'original_slot':slot,'anchor':anchor})
                comp={'kind':'active_anchor','original_slot':slot,'original_mass':amount,'anchor':anchor,
                    'trip':str(trip),'value_lower_numerator':v,'derivative_lower_numerator':dlo,
                    'derivative_upper_numerator':dhi,'original_valid_interval':[vl,vu],
                    'E':E,'S':S,'row_id':rid}
                components.append(comp);slot_components[slot]=comp
            lc,l1,l2=term['mass_constant'],term['mass_first'],term['mass_second']
            assert min(lc,l1,l2)>=0 and lc+l1+l2==R
            meanE=F(lc*const,R);meanS=F(0)
            for slot,mass in enumerate([l1,l2]):
                if mass:meanE+=F(mass*slot_components[slot]['E'],R);meanS+=F(mass*slot_components[slot]['S'],R)
            assert meanE==KAPPA*F(term['beta']) and meanS==F(KAPPA,20*Q)*F(term['sigma'])
            mixed_constant+=2*a*meanE
            for v in range(10):mixed_position[v]+=integer(2*a*meanS*normal[v])
            terms.append({'term':e,'window':wi,'original_cell':cid,'original_term':ti,'original_span':[i,j],
                'physical_span':[ii,jj],'weight_numerator':a,'original_L0':L0,'original_bounds':[L,U],
                'original_FS':term['FS'],'original_masses':[lc,l1,l2],'component_rows':[x['row_id'] for x in components],
                'components':components,'original_mixture_intercept':str(meanE),'original_mixture_slope':str(meanS),
                'component_convex_combination_equals_original_FS':True})
    assert len(terms)==68 and all(t['component_rows'] for t in terms)
    original_physical=[0]*9
    for window,offset,reverse in zip(original_windows,[0,1],reverses):
        for r,value in enumerate(window['canonical_J']):original_physical[mapped_gap(r,offset,reverse)]+=int(value)
    old_b=[-original_physical[0]]+[original_physical[r-1]-original_physical[r] for r in range(1,9)]+[original_physical[8]]
    assert [p+m for p,m in zip(pressure,mixed_position)]==old_b
    assert mixed_constant==2*sum(int(w['canonical_Cstar']) for w in original_windows)
    return {'schema':'N-original-component-integer-epigraph-model-v1','fixed_cells':list(cell_ids),'chart':CHARTS[chart],
        'columns':['X'+str(i) for i in range(1,10)]+['T'+str(i) for i in range(68)],'columns_count':NCOLS,
        'rows':rows,'geometry_rows':155,'terms':terms,'objective_position10':pressure,'pressure_BS8':source_model['BS'],
        'objective_epigraph68':[2*t['weight_numerator'] for t in terms],'objective_constant':0,'target':TARGET,
        'scales':{'Q':Q,'R':R,'D':D,'V':V,'SA':SA,'kappa':KAPPA,'objective_scale':OBJECTIVE_SCALE},
        'candidate_c_numerator':C_N,'gauge_X0':0,'all_variable_bounds_free':True,
        'actual_lower_bound_scope':'The component epigraph minimum lower-bounds Fleft+Fright; a model low point is not actual energy.',
        'original_mixture_identity_checked':True,'new_FS_or_anchors_or_kernel_queries':0}

def assemble(original_windows,cells,source_model,all_spans,chart):
    """Pool identical physical spans; every retained line bounds the same w."""
    old=assemble_unpooled(original_windows,cells,source_model,all_spans,chart)
    groups=[];lookup={};mapping={};original=old['terms']
    for term in original:
        span=tuple(term['physical_span'])
        if span not in lookup:
            gid=len(groups);lookup[span]=gid
            groups.append({'term':gid,'physical_span':list(span),'weight_numerator':0,
                'original_members':[],'component_rows':[],'components':[]})
        gid=lookup[span];mapping[term['term']]=gid;term['shared_group']=gid
        group=groups[gid];group['weight_numerator']+=term['weight_numerator']
        group['original_members'].append({'original_term68':term['term'],'window':term['window'],
            'cell_id':term['original_cell'],'original_term':term['original_term'],
            'weight_numerator':term['weight_numerator']})
        group['component_rows'].extend(term['component_rows'])
        group['components'].extend(term['components'])
    rows=[]
    for row in old['rows']:
        row=dict(row)
        if row['epigraph_index'] is not None:
            row['original_term68']=row['epigraph_index'];row['epigraph_index']=mapping[row['epigraph_index']]
        rows.append(row)
    model={k:v for k,v in old.items() if k not in ['terms','objective_epigraph68','columns','columns_count']}
    model.update({'schema':'N-physical-span-pooled-component-envelope-v1','rows':rows,'terms':groups,
        'original_terms68':original,'original_term_to_shared_group':[mapping[e] for e in range(68)],
        'objective_epigraph':[2*g['weight_numerator'] for g in groups],
        'columns':['X'+str(i) for i in range(1,10)]+['T'+str(i) for i in range(len(groups))],
        'columns_count':9+len(groups),'full_balance_coordinates':10+len(groups),
        'group_count':len(groups),'physical_span_pooling':True,'original_component_rows_not_deduplicated':True,
        'all_variable_bounds_free':True})
    assert len(groups)==len(lookup) and sum(len(g['original_members']) for g in groups)==68
    return model

def epigraph_point(model,X):
    assert len(X)==10 and X[0]==0
    x=list(map(F,X[1:]))+[F(0)]*len(model['terms'])
    for term in model['terms']:
        x[9+term['term']]=max(dot(model['rows'][r]['position10'],X)-model['rows'][r]['bound'] for r in term['component_rows'])
    return x
def exact_rref(matrix,rhs,variables,free_values):
    """One deterministic exact linear solve, not an optimizer or basis search."""
    assert len(matrix)==len(rhs) and len(free_values)==variables
    aug=[[F(v) for v in row]+[F(b)] for row,b in zip(matrix,rhs)]
    assert all(len(row)==variables+1 for row in aug)
    pivots=[];rank=0
    for col in range(variables):
        pivot=next((r for r in range(rank,len(aug)) if aug[r][col]),None)
        if pivot is None:continue
        aug[rank],aug[pivot]=aug[pivot],aug[rank]
        value=aug[rank][col];aug[rank]=[v/value for v in aug[rank]]
        for r in range(len(aug)):
            if r!=rank and aug[r][col]:
                value=aug[r][col];aug[r]=[v-value*w for v,w in zip(aug[r],aug[rank])]
        pivots.append(col);rank+=1
    if any(all(v==0 for v in row[:variables]) and row[-1]!=0 for row in aug):return None,rank
    result=list(map(F,free_values));free=[i for i in range(variables) if i not in pivots]
    for r,col in enumerate(pivots):result[col]=aug[r][-1]-sum(aug[r][j]*result[j] for j in free)
    assert all(dot(row,result)==b for row,b in zip(matrix,rhs))
    return result,rank

def sparse_position(row):
    return [(j,a) for j,a in enumerate(row['position10']) if a]

def sparse_primal_check(model,x,cells=None):
    """Every raw inequality, with zero products omitted algebraically."""
    assert len(x)==model['columns_count']
    X=[F(0)]+list(map(F,x[:9]));bad=[]
    for row in model['rows']:
        lhs=sum(a*X[j] for j,a in sparse_position(row))
        if row['epigraph_index'] is not None:lhs-=x[9+row['epigraph_index']]
        if lhs>row['bound']:bad.append(row['row_id'])
    value=sum(a*X[j] for j,a in enumerate(model['objective_position10']) if a)
    value+=sum(a*x[9+j] for j,a in enumerate(model['objective_epigraph']) if a)
    window_checks=[]
    if not bad and cells is not None:
        revs=(model['chart'].split('/')[0]=='rev',model['chart'].split('/')[1]=='rev')
        for wi,(cid,off,rev) in enumerate(zip(model['fixed_cells'],[0,1],revs)):
            pressure=F(0)
            for r,bs in enumerate(model['pressure_BS8']):
                k=mapped_gap(r,off,rev);pressure+=D*R*bs*(X[k+1]-X[k])
            wvalue=pressure+sum(2*t['weight_numerator']*x[9+t['shared_group']] for t in model['original_terms68'] if t['window']==wi)
            floor=2*KAPPA*CN+2*int(cells[cid]['original_margin'])
            assert wvalue>=floor,('component_mixture_or_original_flow_wiring',cid)
            window_checks.append({'cell_id':cid,'twice_K_window_value':str(wvalue),
                'twice_K_original_flow_floor':str(floor),'surplus':str(wvalue-floor)})
        assert sum(F(r['twice_K_window_value']) for r in window_checks)==value
    return {'valid':not bad,'violated_row_ids':bad,'raw_objective':str(value),
        'all_raw_rows_checked':len(model['rows']),'perwindow_original_margin_checks':window_checks}

def sparse_dual_check(model,mu):
    """Full 10 position plus every pooled epigraph coordinate, not only a minor."""
    assert len(mu)==len(model['rows'])
    balance=list(map(F,objective_full(model)));negative=[];bound=F(0)
    for rid,(weight,row) in enumerate(zip(mu,model['rows'])):
        if weight<0:negative.append(rid)
        if not weight:continue
        for j,a in sparse_position(row):balance[j]+=weight*a
        if row['epigraph_index'] is not None:balance[10+row['epigraph_index']]-=weight
        bound-=weight*row['bound']
    return {'valid':not negative and all(v==0 for v in balance),'negative_row_ids':negative,
        'full_balance':list(map(str,balance)),'raw_lower_bound':str(bound),
        'raw_minus_target':str(bound-model['target'])}

def native_arrays(model,np):
    """Closed-form sparse native scaling; no dense Fraction zero arithmetic."""
    selected=list(range(155))
    for group in model['terms']:
        best={}
        for comp in group['components']:
            slope=comp['S']
            if slope not in best or (comp['E'],-comp['row_id'])>(best[slope]['E'],-best[slope]['row_id']):best[slope]=comp
        selected.extend(c['row_id'] for c in best.values())
    selected=sorted(selected)
    # Native only: equal S lower E is dominated for every X. All original rows
    # remain in model, primal validation and full-coordinate dual validation.
    A=np.zeros((len(selected),model['columns_count']),dtype=float);b=np.zeros(len(selected),dtype=float)
    for native_rid,rid in enumerate(selected):
        row=model['rows'][rid];tid=row['epigraph_index']
        if tid is None:
            for j,a in sparse_position(row):
                if j:A[native_rid,j-1]=float(a)
            b[native_rid]=float(F(row['bound'],20*Q))
        else:
            # S*(20Q)/kappa=dlo/D, including the zero constant slope.
            for j,a in sparse_position(row):
                if j:A[native_rid,j-1]=float(F(a*20*Q,KAPPA))
            A[native_rid,9+tid]=-1.0;b[native_rid]=float(F(row['bound'],KAPPA))
    c=np.zeros(model['columns_count'],dtype=float)
    for j,a in enumerate(model['objective_position10']):
        if j and a:c[j-1]=float(F(a*20*Q,OBJECTIVE_SCALE))
    for j,a in enumerate(model['objective_epigraph']):c[9+j]=float(F(a,2*SA))
    assert np.isfinite(A).all() and np.isfinite(b).all() and np.isfinite(c).all()
    return c,A,b,selected
