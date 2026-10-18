"""M original-component integer model helpers; definitions only at import."""
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
CELL_IDS=(0,604)
CHART='id/rev'

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def incidence(i,j):
    a=[0]*10;a[i]-=1;a[j]+=1;return a
def mapped_span(i,j,offset,reverse):
    return (offset+8-j,offset+8-i) if reverse else (offset+i,offset+j)
def mapped_gap(r,offset,reverse):return offset+(7-r if reverse else r)
def integer(value):
    value=F(value);assert value.denominator==1;return value.numerator
def dense77(row):
    v=list(row['position10'][1:])+[0]*68
    if row['epigraph_index'] is not None:v[9+row['epigraph_index']]=row['epigraph_coefficient']
    assert len(v)==NCOLS;return v
def full78(row):return [row['position10'][0]]+dense77(row)
def row_value(row,x):return dot(dense77(row),x)
def objective(model):return model['objective_position10'][1:]+model['objective_epigraph68']
def objective78(model):return model['objective_position10']+model['objective_epigraph68']

def assemble(original_windows,cells,source_model,all_spans):
    """Called only after the future gate. No new FS/anchor/kernel is selected."""
    assert tuple(w['cell_id'] for w in original_windows)==CELL_IDS
    assert len(source_model['TS'])==34 and len(source_model['BS'])==8 and len(all_spans)==36
    rows=[];terms=[];pressure=[0]*10;mixed_position=[0]*10;mixed_constant=F(0)
    def add(pos,tidx,tc,bound,kind,metadata):
        assert len(pos)==10 and sum(pos)==0 and all(type(v) is int for v in pos)
        assert type(bound) is int and ((tidx is None and tc==0) or (0<=tidx<68 and tc==-1))
        rows.append({'row_id':len(rows),'position10':pos,'epigraph_index':tidx,
            'epigraph_coefficient':tc,'bound':bound,'kind':kind,**metadata})
        return len(rows)-1
    for wi,(cid,offset,reverse) in enumerate([(0,0,False),(604,1,True)]):
        state=cells[cid]['state'];lower=state['L']+state['A'];upper=state['U']+state['B']
        for slot,((i,j),l,u) in enumerate(zip(all_spans,lower,upper)):
            ii,jj=mapped_span(i,j,offset,reverse);a=incidence(ii,jj)
            add(a,None,0,20*u,'original_span_upper',{'window':wi,'original_span_slot':slot})
            add([-v for v in a],None,0,-20*l,'original_span_lower',{'window':wi,'original_span_slot':slot})
    for r in range(9):add(incidence(r+1,r),None,0,-17*Q,'original_separation',{'gap':r})
    for wi,(offset,reverse) in enumerate([(0,False),(1,True)]):
        sign=-1 if reverse else 1;a=[0]*10
        for i,v in [(offset,-1),(offset+1,1),(offset+7,1),(offset+8,-1)]:a[i]+=sign*v
        add(a,None,0,0,'true_ordered_four_point',{'window':wi,'reverse':reverse})
    assert len(rows)==155
    for wi,(window,offset,reverse) in enumerate(zip(original_windows,[0,1],[False,True])):
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
    for window,offset,reverse in zip(original_windows,[0,1],[False,True]):
        for r,value in enumerate(window['canonical_J']):original_physical[mapped_gap(r,offset,reverse)]+=int(value)
    old_b=[-original_physical[0]]+[original_physical[r-1]-original_physical[r] for r in range(1,9)]+[original_physical[8]]
    assert [p+m for p,m in zip(pressure,mixed_position)]==old_b
    assert mixed_constant==2*sum(int(w['canonical_Cstar']) for w in original_windows)
    return {'schema':'M-original-component-integer-epigraph-model-v1','fixed_cells':list(CELL_IDS),'chart':CHART,
        'columns':['X'+str(i) for i in range(1,10)]+['T'+str(i) for i in range(68)],'columns_count':NCOLS,
        'rows':rows,'geometry_rows':155,'terms':terms,'objective_position10':pressure,
        'objective_epigraph68':[2*t['weight_numerator'] for t in terms],'objective_constant':0,'target':TARGET,
        'scales':{'Q':Q,'R':R,'D':D,'V':V,'SA':SA,'kappa':KAPPA,'objective_scale':OBJECTIVE_SCALE},
        'candidate_c_numerator':C_N,'gauge_X0':0,'all_variable_bounds_free':True,
        'actual_lower_bound_scope':'The component epigraph minimum lower-bounds Fleft+Fright; a model low point is not actual energy.',
        'original_mixture_identity_checked':True,'new_FS_or_anchors_or_kernel_queries':0}

def epigraph_point(model,X):
    assert len(X)==10 and X[0]==0
    x=list(map(F,X[1:]))+[F(0)]*68
    for term in model['terms']:
        x[9+term['term']]=max(dot(model['rows'][r]['position10'],X)-model['rows'][r]['bound'] for r in term['component_rows'])
    return x
def primal_check(model,x):
    assert len(x)==77
    violations=[r['row_id'] for r in model['rows'] if row_value(r,x)>r['bound']]
    return {'valid':not violations,'violated_row_ids':violations,'raw_objective':str(dot(objective(model),x))}
def dual_check(model,mu):
    assert len(mu)==len(model['rows'])
    negative=[i for i,v in enumerate(mu) if v<0]
    balance=[F(v) for v in objective78(model)]
    for weight,row in zip(mu,model['rows']):
        for j,v in enumerate(full78(row)):balance[j]+=weight*v
    bound=-sum(v*r['bound'] for v,r in zip(mu,model['rows']))
    return {'valid':not negative and all(v==0 for v in balance),'negative_row_ids':negative,
        'full78_balance':list(map(str,balance)),'raw_lower_bound':str(bound),
        'raw_minus_target':str(bound-model['target'])}

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
