"""Independently reconstruct pinned ninth-span data using exact integers.

This checks the generated Lean literals and actual old packed tables without
importing either certificate generator. It does not compile Lean or replace
the continuous mathematical soundness proof. Assertions are mandatory.
"""
from pathlib import Path
import argparse, ast, datetime, functools, hashlib, json, re, sys
from fractions import Fraction
if not __debug__:
 raise SystemExit('Assertions must remain enabled: run Python without -O or -OO.')
sys.set_int_max_str_digits(0)
parser=argparse.ArgumentParser(description='Independent exact literal/data review of the ninth-span Lean certificate; no Lean compilation or optimization.')
parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
parser.add_argument('--output',type=Path)
args=parser.parse_args()
R=args.root
files=['RecordProportion/NinthSpanFiniteData.lean','RecordProportion/NinthSpanFinite.lean','RecordProportion/NinthSpanPoints.lean','RecordProportion/NinthSpanLocal.lean','RecordProportion/NinthSpan.lean','RecordProportion/NinthSpanAnalytic.lean','RecordProportion/NinthSpanPathSoundness.lean','RecordProportion/FiniteCertificateData.lean','RecordProportion/FiniteCertificate.lean','scripts/generate_ninth_span_certificate.py','output/am-ninth-span-certificate.json','output/am-ninth-span-point-catalog.json','output/am-expanded-nine-point-certificate.json']
hashes={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files}
canonical=lambda b:b.replace(b'\r\n',b'\n').replace(b'\r',b'\n')
pins={'output/am-ninth-span-certificate.json':'9fc7f9d8a00ebbc3e2f8ff236b247af5ac3173c3942ec72b9180c4473a65cf96','output/am-ninth-span-point-catalog.json':'cda8ce5fce3d0a639975f54e57b1991c7d5a2a2cb112df4e3dd13237a954fb27','output/am-expanded-nine-point-certificate.json':'3a3c8b24015162a4835f5c1d8633a4f9f8bdace26d711631dd6374c689bce04f'}
for p,pin in pins.items():assert hashlib.sha256(canonical((R/p).read_bytes())).hexdigest()==pin
new_text=(R/files[0]).read_text(encoding='utf-8')
point_text=(R/files[2]).read_text(encoding='utf-8')
old_text=(R/'RecordProportion/FiniteCertificateData.lean').read_text(encoding='utf-8')
A='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
def decode(s):
 n=0
 for c in s:n=64*n+A.index(c)
 return n
def literal(s,name):
 pos=s.index('def '+name+' ')
 pos=s.index(':=',pos)+2
 start=s.index('[',pos)
 depth=1;i=start+1
 while depth:
  if s[i]=='[':depth+=1
  elif s[i]==']':depth-=1
  i+=1
 raw=s[start:i]
 raw=re.sub(r'n64%\s*"([A-Za-z0-9+/]+)"',lambda m:str(decode(m[1])),raw)
 raw=raw.replace('#','').replace('⟨','(').replace('⟩',')')
 raw=re.sub(r'\btrue\b','True',raw);raw=re.sub(r'\bfalse\b','False',raw)
 return ast.literal_eval(raw)
def chunks(s,name):
 pos=s.index('def '+name+' ');end=s.find('\n\n',pos)
 return [decode(v) for v in re.findall(r'n64%\s*"([A-Za-z0-9+/]+)"',s[pos:end])]
def bits(n,p,w):return (n>>p)&((1<<w)-1)
branches=literal(new_text,'branches');patches=literal(new_text,'patches');routes=literal(new_text,'repRoutes')
catalog=literal(point_text,'catalog')
point_chunks=literal(old_text,'pointChunks');cells=literal(old_text,'cells');packets=literal(old_text,'pairPacks')
terms=literal(old_text,'terms');squares=literal(old_text,'squareSpans');spans=[(i,i+1) for i in range(7)]+literal(old_text,'longSpans')
point_packets=[bits(point_chunks[i//64],116*(i%64),116) for i in range(1089)]
positions=[bits(p,0,20) for p in point_packets];values=[bits(p,20,96) for p in point_packets]
old=json.loads((R/'output/am-expanded-nine-point-certificate.json').read_text(encoding='utf-8'))
new=json.loads((R/'output/am-ninth-span-certificate.json').read_text(encoding='utf-8'))
cat=json.loads((R/'output/am-ninth-span-point-catalog.json').read_text(encoding='utf-8'))
assert len(branches)==84 and len(patches)==47 and len(routes)==1224 and len(packets)==1224
assert catalog==[tuple(p[:2]) for p in cat['point_catalog']]
assert len(catalog)==541 and len(cells)==241 and len(squares)==34 and len(spans)==28
SC=32768;KS=5*10**10*SC;DEN=10**10;SA=10**8
source_points={0:0}
for cell in old['captured_cells']:
 for a in cell['atoms']:
  for p,v in [(a[2],a[8]),(a[3],a[9])]:
   assert p not in source_points or source_points[p]==v
   source_points[p]=v
for p,v,*_ in old['point_catalog']:source_points[p]=v
assert sorted(source_points)==positions and [source_points[p] for p in positions]==values

def reflection(n):return n+241 if n<241 else n-241
def cell_bound(label,i,j,side):
 if label>=241:label,i,j=label-241,7-j,7-i
 slot=2*i if j==i+1 else 14+2*(i*(13-i)//2+j-i-2)
 return bits(cells[label][0],22*(slot+side),22)
def tight(label,i,j):
 return max(cell_bound(label,i,j,0),sum(cell_bound(label,k,k+1,0) for k in range(i,j))),min(cell_bound(label,i,j,1),sum(cell_bound(label,k,k+1,1) for k in range(i,j)))
def atom(label,i,j):
 if label>=241:label,i,j=label-241,7-j,7-i
 t=next(k for k,(a,b,w) in enumerate(terms) if (a,b)==(i,j))
 return bits(cells[label][1],67*t,67)
def enabled(word):
 kind,mix,p,r=[bits(word,0,2),bits(word,2,11),bits(word,13,11),bits(word,24,11)]
 return ([p] if kind==1 or kind==2 and mix>0 or kind==3 and mix<1024 else [])+([r] if kind==3 and mix>0 else [])
def anchor(i,j,p,v,lower,upper,right):
 V,dp0,dm0=[bits(v,k,32) for k in (0,32,64)]
 dm=dp0-2*10**9;dp=2*10**9-dm0
 l=min(lower,5*p);u=max(upper,5*p)
 return (i,j,10*(dp if right else dm),8+squares.index((i,j)),-1,-5*V*SC+50*(dm if right else dp)*p-10*((dm-dp)*u if right else (dp-dm)*l),False)
@functools.lru_cache(maxsize=None)
def frame(label,offset):
 rows=[]
 for i,j in spans:
  rows.extend([(i+offset,j+offset,1,0,0,5*cell_bound(label,i,j,1),True),(i+offset,j+offset,-1,0,0,-5*cell_bound(label,i,j,0),True)])
 for i,j,w in terms:
  word=atom(label,i,j);low,up=tight(label,i,j)
  rows.append((i+offset,j+offset,0,8+squares.index((i+offset,j+offset)),-1,-5*bits(word,35,32)*SC,False))
  for k in enabled(word):
   assert low<=positions[k]<=up
   rows.extend([anchor(i+offset,j+offset,positions[k],values[k],5*low,5*up,False),anchor(i+offset,j+offset,positions[k],values[k],5*low,5*up,True)])
 return rows

def close(matrix):
 d=[r.copy() for r in matrix]
 for k in range(9):
  for i in range(9):
   for j in range(9):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
 return d

@functools.lru_cache(maxsize=None)
def primitive_bounds(left,right):
 d=[[0]*9 for _ in range(9)]
 for i in range(9):
  for j in range(9):
   if i==j:continue
   v=[]
   if max(i,j)<=7:v.append(5*cell_bound(left,i,j,1) if i<j else -5*cell_bound(left,j,i,0))
   if min(i,j)>=1:v.append(5*cell_bound(right,i-1,j-1,1) if i<j else -5*cell_bound(right,j-1,i-1,0))
   if i==j+1:v.append(-4*SC)
   d[i][j]=min(v) if v else 10**30
 return d

@functools.lru_cache(maxsize=None)
def original_closure(left,right):
 return close(primitive_bounds(left,right))

def path_cost(word,matrix,first,last):
 length=bits(word,0,4)
 assert 1<=length<=9
 vertices=[bits(word,4+4*k,4) for k in range(length)]
 assert all(v<9 for v in vertices) and vertices[0]==first and vertices[-1]==last
 assert word>>(4+4*length)==0
 return sum(matrix[i][j] for i,j in zip(vertices,vertices[1:]))
for label,cell in enumerate(old['captured_cells']):
 assert [cell_bound(label,i,j,s) for i,j in spans for s in (0,1)]==cell['gap_bounds']+cell['span_bounds']

branch_lowers=[];tangent_sources={'direct-region':0,'old-enabled':0};tangent_points=set();direct_points=set();old_points=set();index=0
for patch_id,patch_json in enumerate(new['replacements']):
 left,right=patch_json['left'],patch_json['right'];orig=original_closure(left,right);used=[]
 for branch_json in patch_json['branches']:
  bleft,bright,low,up,bounds,descriptors,dual,paths=branches[index]
  assert (bleft,bright)==(left,right) and [low,up]==branch_json['bounds_5sc']
  d=[r.copy() for r in orig];d[0][8]=min(d[0][8],up);d[8][0]=min(d[8][0],-low);d=close(d)
  assert bounds==[v for row in d for v in row] and all(d[i][i]==0 for i in range(9))
  base=[r.copy() for r in primitive_bounds(left,right)]
  base[0][8]=min(base[0][8],up);base[8][0]=min(base[8][0],-low)
  assert len(paths)==81
  assert all(path_cost(word,base,slot//9,slot%9)<=bounds[slot] for slot,word in enumerate(paths))
  rows=frame(left,0)+frame(right,1)
  assert len(rows)==branch_json['base_rows'] and len(descriptors)==len(branch_json['added_rows'])
  for a,public in zip(descriptors,branch_json['added_rows']):
   kind,i,j,direct,old_index,offset,lf,ll,weight,right_cut=a
   tag,pi,pj=public[:3]
   assert (i,j)==(pi,pj) and 0<=i<j<=8
   if kind in (0,1):
    assert tag==('closure-upper' if kind==0 else 'closure-lower')
    rows.append((i,j,1 if kind==0 else -1,0,0,d[i][j] if kind==0 else d[j][i],True))
   else:
    _,_,_,p,v,listid,guard,side=public
    assert right_cut==(side=='U') and (i,j) in squares
    tangent_sources[guard]+=1;tangent_points.add(p)
    if kind==2:
     assert guard=='direct-region' and catalog[direct]==(p,v)
     region=(p+SC//2)//SC;L=bits(cat['region'][0],20*region,20);U=bits(cat['region'][1],20*region,20)
     assert region<16 and 5*L<=min(-d[j][i],5*p) and max(d[i][j],5*p)<=5*U
     direct_points.add(p)
    else:
     assert kind==3 and guard=='old-enabled' and offset in (0,1) and (lf+offset,ll+offset)==(i,j)
     label=left if offset==0 else right
     assert (lf,ll,weight) in terms and old_index in enabled(atom(label,lf,ll))
     assert (positions[old_index],values[old_index])==(p,v)
     L,U=tight(label,lf,ll)
     assert 5*L<=-d[j][i] and d[i][j]<=5*U
     old_points.add(p)
    rows.append(anchor(i,j,p,v,-d[j][i],d[i][j],right_cut))
  expected_dual=[(r,int(Fraction(v)*DEN)) for r,v in branch_json['dual_sparse']]
  assert dual==expected_dual and all(n>0 and Fraction(v)*DEN==n for (r,v),(i,n) in zip(branch_json['dual_sparse'],dual))
  assert all(0<=i<len(rows) for i,n in dual)
  multipliers=[(rows[r],n*(10**10 if rows[r][-1] else 1)) for r,n in dual]
  val=-sum(row[5]*lam for row,lam in multipliers)
  gap_pressure=[28898,86170,132798,156484,156484,132798,86170,28898]
  for c in range(42):
   if c<8:objective=10**10*gap_pressure[c]
   else:
    span=squares[c-8]
    objective=4*SA if span==(0,8) else sum(w for o in (0,1) for i,j,w in terms if (i+o,j+o)==span)
   residual=DEN*objective+sum(lam*(row[2] if c<8 and row[0]<=c<row[1] else row[4] if c>=8 and c==row[3] else 0) for row,lam in multipliers)
   vlo=max(4*SC,-d[c+1][c]) if c<8 else 0;vhi=d[c][c+1] if c<8 else KS
   val+=residual*(vlo if residual>=0 else vhi)
  lower=Fraction(val,2*SA*KS*DEN)
  assert lower==Fraction(branch_json['lower']) and lower>=Fraction(805403,SA)
  branch_lowers.append(lower);used.append(index);index+=1
 used += [used[-1]]*(3-len(used))
 pleft,pright,b0,b1,b2,lower_path,upper_path=patches[patch_id]
 assert (pleft,pright,b0,b1,b2)==(left,right,*used)
 assert branches[used[0]][2]==-orig[8][0] and branches[used[2]][3]==orig[0][8]
 assert branches[used[1]][2]<=branches[used[0]][3] and branches[used[2]][2]<=branches[used[1]][3]
 assert path_cost(lower_path,primitive_bounds(left,right),8,0)<=-branches[used[0]][2]
 assert path_cost(upper_path,primitive_bounds(left,right),0,8)<=branches[used[2]][3]
assert index==84
pair_dict={(p['left'],p['right']):p for p in old['pairs']}
reps=[p for p in old['pairs'] if (p['left'],p['right'])<=(reflection(p['right']),reflection(p['left']))]
assert [(p['left'],p['right']) for p in reps]==[(p[0],p[1]) for p in packets]
patch_map={(p['left'],p['right']):i for i,p in enumerate(new['replacements'])}
expected_routes=[patch_map[(p['left'],p['right'])] if Fraction(p['lower'])<Fraction(805403,SA) else 47 for p in reps]
assert routes==expected_routes and sum(x<47 for x in routes)==25
old_catalog=literal(old_text,'catalog');lambda_chunks=literal(old_text,'lambdaChunks')
top_position=old_text.index('def topMultipliers ')
top_multipliers=decode(re.search(r'n64%\s*"([A-Za-z0-9+/]+)"',old_text[top_position:])[1])
assert len(old_catalog)==237

def old_dual(count,word):
 pairs=[]
 for _ in range(count):
  code=bits(word,0,6)
  if code<63:
   number=bits(top_multipliers,58*code,58);skip=6
  else:
   k=bits(word,6,14);number=bits(lambda_chunks[k//64],58*(k%64),58);skip=20
  pairs.append((bits(word,skip,9),number));word>>=skip+9
 assert word==0
 return pairs

old_exact_lowers=[];old_basic_lowers=[];old_residuals=[];old_base_values=[]
for packet,pair in zip(packets,reps):
 left,right,count,word,extra_count,extra_word=packet
 rows=frame(left,0)+frame(right,1)
 for k in range(extra_count):
  atom_word=bits(extra_word,15*k,15)
  offset,i,j,catalog_index=[bits(atom_word,0,1),bits(atom_word,1,3),bits(atom_word,4,3),bits(atom_word,7,8)]
  assert catalog_index<len(old_catalog)
  catalog_word=old_catalog[catalog_index];p=bits(catalog_word,0,20);v=bits(catalog_word,20,96)
  lo,hi=tight(left if offset==0 else right,i,j)
  rows.extend([anchor(i+offset,j+offset,p,v,5*min(lo,p),5*max(hi,p),side) for side in (False,True)])
 dual=old_dual(count,word)
 public_dual=[(r,int(Fraction(v)*10**9)) for r,v in pair['dual_sparse']]
 assert dual==public_dual and all(n>0 and Fraction(v)*10**9==n for (r,v),(i,n) in zip(pair['dual_sparse'],dual))
 assert all(0<=i<len(rows) for i,n in dual)
 multipliers=[(rows[r],n*(10**10 if rows[r][-1] else 1)) for r,n in dual]
 val=-sum(row[5]*lam for row,lam in multipliers)
 old_base_values.append(val);residual_vector=[]
 d=original_closure(left,right)
 assert all(d[i][i]==0 for i in range(9))
 for c in range(42):
  if c<8:objective=10**10*gap_pressure[c]
  else:
   span=squares[c-8]
   objective=4*SA if span==(0,8) else sum(w for o in (0,1) for i,j,w in terms if (i+o,j+o)==span)
  residual=10**9*objective+sum(lam*(row[2] if c<8 and row[0]<=c<row[1] else row[4] if c>=8 and c==row[3] else 0) for row,lam in multipliers)
  residual_vector.append(residual)
  vlo=max(4*SC,-d[c+1][c]) if c<8 else 0;vhi=d[c][c+1] if c<8 else KS
  val+=residual*(vlo if residual>=0 else vhi)
 lower=Fraction(val,2*SA*KS*10**9)
 assert lower==Fraction(pair['lower'])
 old_exact_lowers.append(lower)
 old_residuals.append(residual_vector)
 primitive=primitive_bounds(left,right)
 basic=old_base_values[-1]
 for c,residual in enumerate(residual_vector):
  vlo=max(4*SC,-primitive[c+1][c]) if c<8 else 0;vhi=primitive[c][c+1] if c<8 else KS
  basic+=residual*(vlo if residual>=0 else vhi)
 old_basic_lowers.append(Fraction(basic,2*SA*KS*10**9))
assert all(lower>=Fraction(805403,SA) for route,lower in zip(routes,old_exact_lowers) if route==47)
assert sum(lower<Fraction(805403,SA) for lower in old_exact_lowers)==25
strong_basic_failures={i for i,(route,lower) in enumerate(zip(routes,old_basic_lowers)) if route==47 and lower<Fraction(805403,SA)}
assert len(strong_basic_failures)==55
old_boxes=literal(new_text,'oldBoxes');old_box_routes=literal(new_text,'oldBoxRoutes')
assert len(old_boxes)==55 and len(old_box_routes)==1224
assert {index for index,bounds,paths in old_boxes}==strong_basic_failures
old_box_lowers={}
for box_id,(index,bounds,paths) in enumerate(old_boxes):
 assert old_box_routes[index]==box_id and len(bounds)==16 and len(paths)==16
 left,right=packets[index][:2];primitive=primitive_bounds(left,right);full=original_closure(left,right)
 for slot,(bound,word) in enumerate(zip(bounds,paths)):
  c=slot//2;first,last=(c,c+1) if slot%2==0 else (c+1,c)
  assert path_cost(word,primitive,first,last)<=bound
  assert bound==full[first][last]
 val=old_base_values[index]
 for c,residual in enumerate(old_residuals[index]):
  vlo=max(4*SC,-bounds[2*c+1]) if c<8 else 0;vhi=bounds[2*c] if c<8 else KS
  val+=residual*(vlo if residual>=0 else vhi)
 lower=Fraction(val,2*SA*KS*10**9)
 assert lower==old_exact_lowers[index] and lower>=Fraction(805403,SA)
 old_box_lowers[index]=lower
assert all((route==55 if i not in strong_basic_failures else route<55 and old_boxes[route][0]==i) for i,route in enumerate(old_box_routes))
label_chunks=chunks(old_text,'pairLabelAtChunks');rep_chunks=chunks(old_text,'representativeLabelChunks');orbit_chunks=chunks(old_text,'orbitIndexAtChunks')
labels=[bits(label_chunks[i//32],18*(i%32),18) for i in range(2399)]
rep_labels=[bits(rep_chunks[i//32],18*(i%32),18) for i in range(1224)]
orbits=[bits(orbit_chunks[i//32],12*(i%32),12) for i in range(2399)]
assert set((bits(k,0,9),bits(k,9,9)) for k in labels)==set(pair_dict)
assert rep_labels==[a+(b<<9) for a,b,*_ in packets]
public_mirror_lower_differences=0
formal_cover_lowers=[];kernel_checked_route_lowers=[]
for k,code in zip(labels,orbits):
 rep=code//2;assert rep<1224
 a,b=packets[rep][:2]
 expected=(a,b) if code%2==0 else (reflection(b),reflection(a))
 assert k==expected[0]+(expected[1]<<9)
 public_mirror_lower_differences+=Fraction(pair_dict[expected]['lower'])!=old_exact_lowers[rep]
 route=routes[rep]
 if route==47:
  formal_cover_lowers.append(old_exact_lowers[rep])
  kernel_checked_route_lowers.append(old_basic_lowers[rep] if old_basic_lowers[rep]>=Fraction(805403,SA) else old_box_lowers[rep])
 else:
  replaced=[branch_lowers[i] for i in set(patches[route][2:5])]
  formal_cover_lowers.extend(replaced);kernel_checked_route_lowers.extend(replaced)
assert min(formal_cover_lowers)>Fraction(805403,SA)
assert min(kernel_checked_route_lowers)>=Fraction(805403,SA)
unchanged_lowers=[Fraction(p['lower']) for p in old['pairs'] if (p['left'],p['right']) not in patch_map]
assert len(unchanged_lowers)==2352 and min(unchanged_lowers+branch_lowers)>Fraction(805403,SA)
full_minimum=min(unchanged_lowers+branch_lowers)
assert full_minimum==Fraction(263917374155379049835090394947,32768000000000000000000000000000)
assert hashes=={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in files}, 'Input source changed during audit; rerun on frozen files.'
result={'scope':'Read-only independent automated literal/data and mathematical bridge review; no independent human review or compiler claim.','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','sources_sha256':hashes,'canonical_lf_input_pins':pins,'counts':{'branches':84,'patches':47,'representatives':1224,'weak_representatives':25,'strong_representatives':1199,'covered_ordered_pairs':2399,'direct_tangent_rows':tangent_sources['direct-region'],'old_enabled_tangent_rows':tangent_sources['old-enabled'],'all_tangent_distinct_points':len(tangent_points),'direct_distinct_points':len(direct_points),'old_enabled_distinct_points':len(old_points),'old_enabled_points_outside_direct':len(old_points-direct_points)},'minimum_branch_lower':str(min(branch_lowers)),'minimum_full_cover_lower':str(full_minimum),'minimum_branch_lower_greater_than_target':min(branch_lowers)>Fraction(805403,SA),'all_closed_span_endpoint_coverages':True,'all84_integer_rows_and_positive_duals_match_public_payload':True,'all84_signed_box_exact_lowers_match_public_payload':True,'all2399_reflection_orbit_routes_match_actual_packed_lean_tables':True}
result.update({'review_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'all1224_old_packed_duals_match_public_rational_duals':True,'all1224_old_exact_signed_box_lowers_match_public_payload':True,'all1199_unpatched_old_actual_packed_duals_pass_new_threshold':True,'minimum_strong_representative_lower':str(min(lower for route,lower in zip(routes,old_exact_lowers) if route==47)),'minimum_lean_reflection_cover_lower':str(min(formal_cover_lowers)),'all2399_lean_reflection_cover_lowers_greater_than_target':True,'public_ordered_pair_lowers_differing_from_canonical_representative_lower':public_mirror_lower_differences})
result.update({'all6804_branch_paths_have_correct_endpoints_and_sound_upper_costs':True,'all94_patch_outer_paths_cover_the_original_real_domains':True,'all880_old_box_paths_bound_their_actual_primitive_edges':True,'all55_old_path_box_exact_lowers_match_original_full_lower':True,'all55_basic_failing_strong_representatives_exactly_match_old_box_routes':True,'strong_primitive_box_passes':1144,'minimum_current_kernel_checked_route_lower':str(min(kernel_checked_route_lowers))})
if args.output:
 args.output.parent.mkdir(parents=True,exist_ok=True)
 args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(result,indent=2))
