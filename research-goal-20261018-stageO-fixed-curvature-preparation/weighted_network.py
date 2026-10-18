"""Prepared exact scalar variance and one rational Laplace solve; definitions."""
from fractions import Fraction as F

def variance_clamp(rows,intervals):
    totals={};receipt=[]
    for r in rows:
        key=tuple(r['physical_span']);c=F(r['c_raw']);q=F(r['q_physical']);assert c>=0
        t=totals.setdefault(key,[F(0),F(0),F(0)])
        t[0]+=c;t[1]+=c*q;t[2]+=c*q*q
    payment=F(0)
    for edge,(C,B,A) in sorted(totals.items()):
        if not C:continue
        qbar=B/C;V=A-B*B/C;assert V>=0
        lo,hi=intervals[edge];assert lo<=hi
        point=min(hi,max(lo,qbar));value=V+C*(point-qbar)**2;payment+=value
        receipt.append({'physical_span':list(edge),'C':str(C),'qbar':str(qbar),'variance':str(V),
            'closed_interval':list(map(str,[lo,hi])),'clamp':str(point),'uniform_payment':str(value)})
    return payment,receipt

def solve_square(A,b):
    """One fixed exact elimination; no optimization, support or tolerance trial."""
    n=len(b);assert len(A)==n and all(len(row)==n for row in A)
    aug=[[F(x) for x in row]+[F(rhs)] for row,rhs in zip(A,b)]
    for k in range(n):
        pivot=next((i for i in range(k,n) if aug[i][k]),None)
        assert pivot is not None,'positive_graph_reduced_Laplacian_unexpected_singularity'
        aug[k],aug[pivot]=aug[pivot],aug[k];v=aug[k][k];aug[k]=[x/v for x in aug[k]]
        for i in range(n):
            if i!=k and aug[i][k]:
                v=aug[i][k];aug[i]=[x-v*y for x,y in zip(aug[i],aug[k])]
    out=[aug[i][-1] for i in range(n)]
    assert all(sum(x*y for x,y in zip(row,out))==rhs for row,rhs in zip(A,b))
    return out

def laplace_payment(rows):
    L=[[F(0) for _ in range(10)] for _ in range(10)];rhs=[F(0)]*10;adj=[set() for _ in range(10)]
    for r in rows:
        c=F(r['c_raw']);assert c>=0
        if not c:continue
        i,j=r['physical_span'];q=F(r['q_physical']);assert 0<=i<j<10
        L[i][i]+=c;L[j][j]+=c;L[i][j]-=c;L[j][i]-=c
        rhs[i]-=c*q;rhs[j]+=c*q;adj[i].add(j);adj[j].add(i)
    components=[];seen=set()
    for i in range(10):
        if i in seen:continue
        todo=[i];comp=[];seen.add(i)
        while todo:
            v=todo.pop();comp.append(v)
            for w in sorted(adj[v]):
                if w not in seen:seen.add(w);todo.append(w)
        components.append(sorted(comp))
    gauges={c[0] for c in components};free=[i for i in range(10) if i not in gauges]
    # One block-diagonal reduced system; no per-gauge trial or regularization.
    values=solve_square([[L[i][j] for j in free] for i in free],[rhs[i] for i in free])
    point=[F(0)]*10
    for i,v in zip(free,values):point[i]=v
    residual=[sum(L[i][j]*point[j] for j in range(10))-rhs[i] for i in range(10)]
    assert all(v==0 for v in residual)
    value=sum(F(r['c_raw'])*(point[r['physical_span'][1]]-point[r['physical_span'][0]]-F(r['q_physical']))**2 for r in rows)
    assert value>=0
    return value,{'positive_graph_components':components,'gauge_vertex_per_component':sorted(gauges),
        'p_star':list(map(str,point)),'full10_stationarity_residual':list(map(str,residual)),
        'exact_linear_system_dimension':len(free),'linear_solve_calls':1,
        'Q_p_star':str(value),'identity':'Q(p)=Q(p_star)+sum c_r*(B_r*(p-p_star))^2',
        'p_star_is_not_a_new_kernel_anchor_or_actual_energy_evaluation':True}
