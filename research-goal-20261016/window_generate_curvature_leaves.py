"""Connect the three frozen negative-curvature leaves to actual scalar checks.

This writes new unproved Lean sources. No existing PASS source is changed.
Inactive edge rows are given a global upper bound; their integer mass is
zero, so the checked flow coefficient and strict margin remain identical.
"""
from pathlib import Path
import gzip,json,hashlib
from cover_correlated_replay import a as geom
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
active=HERE/'cover-curvature-actual-active.json'
assert hashlib.sha256(active.read_bytes()).hexdigest()=='21edc54bd8ef52690d33acc6991853e8e5625c4e84149df3fac4fa6da5875bbb'
feed=json.loads(active.read_bytes());points={x['P']:x for x in feed['point_rows']}
folder=HERE/'cover-targeted-curvature-evidence'
base=json.loads(gzip.decompress((folder/'proof.json.gz').read_bytes()))
extension=json.loads((folder/'cross-extension.json').read_bytes())
cases=[base]+extension['cases'];terms=[r for r in json.loads((ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes())['a_upper'] if r[2]]
SC=32768;DS=10**15
data='''/- SPDX-License-Identifier: Apache-2.0
Three frozen cells, directions and compact actual scalar/flow packets.
All data are untrusted and rechecked by the consumer modules.
-/
import StructuralGoal20261016.WindowCurvatureScalar
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureLeafData
open WindowDirectionalFlow (Row)
open WindowCurvatureScalar (Packet inactiveRow defaultPacket)
'''
summary=[];modules=[]
for ix,(case,projected) in enumerate(zip(cases,feed['leaves'])):
    assert case['path']==projected['path']
    d=projected['d'];stored=case['curvature'];rmap={x['t']:x for x in projected['rows']}
    fullrows=[];packets=[];C=0;E=0;q=[0]*9
    for t,(i,j,aw) in enumerate(terms):
        s=sum(d[i:j]);mass=aw*s*s
        if t not in rmap:
            assert s==0
            fullrows.append('inactiveRow');packets.append('defaultPacket')
            P,m0,m1,err=0,40*DS,0,0
        else:
            assert s!=0
            r=rmap[t];P,m0,m1,err=(int(r[k]) for k in ['P','m0','m1','err'])
            fullrows.append(f'⟨({P}),({m0}),({m1}),({err})⟩')
            if r['kind']=='affine':kind,n,B4=2,points[P]['n'],r['B4']
            else:kind,n,B4=1,0,0;assert m1==0
            packets.append(f"⟨{kind},{n},{r['first']},{r['last']},({B4})⟩")
        C+=mass*(2*SC*m0-m1*P);E+=2*SC*mass*err
        for k in range(i,j):q[k]+=2*mass*m1
    old=stored['exact_flow']
    assert C==int(old['constant']) and E==int(old['error']) and q==list(map(int,old['coefficient']))
    lower,upper=case['cell'];matrix=[[0]*10 for _ in range(10)]
    for (i,j),z in geom.INDEX.items():matrix[i][j]=upper[z];matrix[j][i]=-lower[z]
    assert all(matrix[r+1][r]<-31488 for r,v in enumerate(d) if v)
    flow=old['flow'];edges=[(i,j)for i,j,amount,cost in flow['nonzero_flow']]
    amountmatrix=[[0]*10 for _ in range(10)]
    for i,j,amount,cost in flow['nonzero_flow']:
        assert matrix[i][j]==cost
        amountmatrix[i][j]=int(amount)
    divergence=[q[0]]+[q[r]-q[r-1]for r in range(1,9)]+[-q[8]]
    assert [sum(amountmatrix[i])-sum(row[i]for row in amountmatrix)for i in range(10)]==divergence
    cost=sum(amountmatrix[i][j]*matrix[i][j] for i in range(10)for j in range(10))
    margin=-C-E-cost;assert margin>=1
    data+=f'\n/- {case["path"]}: strict integer margin {margin}. -/\n'
    data+=f'def cell{ix:02} : DifferenceCell.Cell 10 := !['+',\n '.join('!['+','.join(f'({v})'for v in r)+']'for r in matrix)+']\n'
    data+=f'def direction{ix:02} : Fin 9 → ℤ := !['+','.join(str(v)for v in d)+']\n'
    data+=f'def rows{ix:02} : Fin 41 → Row := !['+',\n '.join(fullrows)+']\n'
    data+=f'def packets{ix:02} : Fin 41 → Packet := !['+',\n '.join(packets)+']\n'
    data+=f'def edges{ix:02} : List FlowBasisCodec.Edge := ['+','.join(f'({i},{j})'for i,j in edges)+']\n'
    name=f'WindowCurvatureLeaf{ix:02}'
    src=f'''/- SPDX-License-Identifier: Apache-2.0
Actual second-variation exclusion on frozen cell {case['path']}.
This is local to that cell and does not assert completion of a global cover.
-/
import StructuralGoal20261016.WindowCurvatureLeafData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowCurvatureLeaves
open WindowCurvatureLeafData
theorem scalar{ix:02} : WindowCurvatureScalar.allCheck cell{ix:02} rows{ix:02} packets{ix:02} = true := by
 decide +kernel
theorem support{ix:02} : WindowCurvatureScalar.supportCheck cell{ix:02} direction{ix:02} = true := by
 decide +kernel
theorem flow{ix:02} : WindowCurvatureFlow.check cell{ix:02} edges{ix:02} direction{ix:02} rows{ix:02} = true := by
 decide +kernel
theorem exclude{ix:02} {{g : Fin 9 → ℝ}}
 (hg : WindowMinimizerCover.Relevant ((123:ℝ)/128) g)
 (hcell : WindowDifferenceCell.Contains cell{ix:02} g) : False :=
 WindowCurvatureScalar.exclude scalar{ix:02} support{ix:02} flow{ix:02} hg hcell
set_option pp.fullNames true
#print axioms scalar{ix:02}
#print axioms support{ix:02}
#print axioms flow{ix:02}
#print axioms exclude{ix:02}
end StructuralGoal20261016.WindowCurvatureLeaves
'''
    (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(src,encoding='utf8',newline='\n')
    modules.append(f'StructuralGoal20261016.{name}')
    summary.append({'path':case['path'],'active_rows':len(rmap),'strict_integer_margin':str(margin),'ordinary_Lean_proven':False})
data+='end StructuralGoal20261016.WindowCurvatureLeafData\n'
(ROOT/'StructuralGoal20261016/WindowCurvatureLeafData.lean').write_text(data,encoding='utf8',newline='\n')
(HERE/'window_curvature_leaf_modules.json').write_text(json.dumps(modules,indent=2)+'\n',encoding='utf8')
(HERE/'window_curvature_leaf_generation.json').write_text(json.dumps({'scope':__doc__,'source_active_sha256':hashlib.sha256(active.read_bytes()).hexdigest(),'cases':summary,'data_bytes':len(data.encode()),'complete_global_cover':False},indent=2)+'\n',encoding='utf8')
print(json.dumps({'cases':summary,'data_bytes':len(data.encode())}))
