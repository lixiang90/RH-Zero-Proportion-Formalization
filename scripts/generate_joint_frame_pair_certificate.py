"""Additive c805448 finite Lean translation; stdlib only, no optimization.

The public mathematical snapshot retains 201 original YA witnesses. A separate
frozen base-row dual adapter pays the same 201 frame conclusions in Lean.
All row guards, paths and integer residual payments are ordinary kernel checks.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,hashlib,json,sys
SC,KS,DEN,SA=32768,5*10**10*32768,10**10,10**8
TARGET,ELL=805448,805094
PUBLIC_PIN='cd031c3b3e7daa85f47a52ac4fd3c2d6d8512105c809061b39dfd8fa968b77d7'
ADAPTER_PIN='6871cc80f90aea753ac9db95321f6f6099a4b50fbe2fd2494e475251eb8140ec'

def read(path,pin=None):
 raw=path.read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
 if pin:assert hashlib.sha256(raw).hexdigest()==pin
 return json.loads(raw)
def ll(xs):return '['+','.join(map(str,xs))+']'
def item(xs):return '⟨'+','.join(str(x).lower() for x in xs)+'⟩'

FRAME_MODEL=r'''
def frameBranch (index : Nat) : FrameBranch := (frameBranches[index]?).getD default
def framePatch (index : Nat) : FramePatch := (framePatches[index]?).getD default
def frameSpanLower (b : FrameBranch) (i j : Nat) : Int := -((b.bounds[8*j+i]?).getD 0)
def frameSpanUpper (b : FrameBranch) (i j : Nat) : Int := (b.bounds[8*i+j]?).getD 0
def framePrimitive (label i j : Nat) : Int :=
  if i = j then 0 else
    let d : Int := if i < j then 5*(cellUpper label i j:Int) else -5*(cellLower label j i:Int)
    if i = j+1 then min d (-4*32768) else d
def frameEdge (b : FrameBranch) (i j : Nat) : Int :=
  let d := framePrimitive b.label i j
  if i = b.splitFirst ∧ j = b.splitLast then min d b.upper
  else if i = b.splitLast ∧ j = b.splitFirst then min d (-b.lower) else d
def framePathCheck (b : FrameBranch) (slot : Nat) : Bool :=
  JointFramePairPaths.check (frameEdge b) (slot/8) (slot%8)
    ((b.bounds[slot]?).getD 0) ((b.paths[slot]?).getD 0)
def frameOriginalPathCheck (label first last : Nat) (bound : Int) (word : Nat) : Bool :=
  JointFramePairPaths.check (framePrimitive label) first last bound word
def frameAddedLabel (b : FrameBranch) (_a : Added) : Nat := b.label
def frameAddedCheck (b : FrameBranch) (a : Added) : Bool :=
  decide (a.first < a.last ∧ a.last ≤ 7) &&
  if a.kind = 0 ∨ a.kind = 1 then true else
    decide ((a.first,a.last,a.weight) ∈ terms ∨ (a.first,a.last) ∈ terms.map (fun t => (t.1,t.2.1))) &&
    if a.kind = 2 then
      JointFramePairPoints.directCheck (frameSpanLower b a.first a.last)
        (frameSpanUpper b a.first a.last) a.direct
    else decide (a.kind = 3 ∧ a.offset = 0 ∧
      a.first = a.localFirst ∧ a.last = a.localLast ∧
      (a.localFirst,a.localLast,a.weight) ∈ terms ∧
      a.oldIndex ∈ oldPointIndices (termAtom b.label a.localFirst a.localLast) ∧
      5*(tightLower b.label a.localFirst a.localLast:Int) ≤ frameSpanLower b a.first a.last ∧
      frameSpanUpper b a.first a.last ≤ 5*(tightUpper b.label a.localFirst a.localLast:Int))
def frameAddedRow (b : FrameBranch) (a : Added) : IntegerRow :=
  if a.kind = 0 then ⟨a.first,a.last,1,0,0,frameSpanUpper b a.first a.last,true⟩
  else if a.kind = 1 then ⟨a.first,a.last,-1,0,0,-frameSpanLower b a.first a.last,true⟩
  else
    let V : Int := AMW.Cert.PyrD.lo32 (addedValue a)
    let dm : Int := (AMW.Cert.PyrD.lo32 (AMW.Cert.PyrD.hi32 (addedValue a)):Int)-2000000000
    let dp : Int := 2000000000-(AMW.Cert.PyrD.hi32 (AMW.Cert.PyrD.hi32 (addedValue a)):Int)
    let p : Int := addedPoint a
    let l5 := min (frameSpanLower b a.first a.last) (5*p)
    let u5 := max (frameSpanUpper b a.first a.last) (5*p)
    if a.rightCut then
      ⟨a.first,a.last,10*dp,squareColumn a.first a.last,-1,
        -5*V*32768+50*dm*p-10*(dm-dp)*u5,false⟩
    else
      ⟨a.first,a.last,10*dm,squareColumn a.first a.last,-1,
        -5*V*32768+50*dp*p-10*(dp-dm)*l5,false⟩
def frameRowsFor (b : FrameBranch) : List IntegerRow :=
  frameRows b.label 0 ++ b.added.map (frameAddedRow b)
def frameMultipliers (b : FrameBranch) : List (IntegerRow × Int) :=
  b.dual.map fun p =>
    let row := (frameRowsFor b).getD p.1 default
    (row,(p.2:Int)*(if row.geometric then 10000000000 else 1))
def frameBoxLo (b : FrameBranch) (column : Nat) : Int :=
  if column < 7 then max (4*32768) (frameSpanLower b column (column+1)) else 0
def frameBoxHi (b : FrameBranch) (column : Nat) : Int :=
  if column < 7 then frameSpanUpper b column (column+1) else 5*10000000000*32768
def frameLower (b : FrameBranch) : Int :=
  RHWeilRecord.SparseDualSoundness.checkerL 33 (frameMultipliers b)
    (fun c => 10000000000*JointFramePairFrame.frameObjectiveCoeff c)
    (fun r c => JointFramePairFrame.frameCoeff r.1 c)
    (fun r => r.1.bound) (fun r => r.2) (frameBoxLo b) (frameBoxHi b)
def frameBaseShape (row : IntegerRow) : Bool :=
  decide (row.last ≤ 7 ∧ (row.zcoef = 0 ∨ 8 ≤ row.square ∧ row.square < 34))
def frameGuard (index : Nat) : Bool :=
  let b := frameBranch index
  decide (b.label < 241 ∧ b.splitFirst < b.splitLast ∧ b.splitLast ≤ 7 ∧
    b.lower ≤ b.upper ∧ b.bounds.size = 64 ∧ b.paths.size = 64) &&
    (List.range 64).all (framePathCheck b) && b.added.all (frameAddedCheck b) &&
    (frameRows b.label 0).all frameBaseShape
def frameNumeric (index : Nat) : Bool :=
  decide (805094*(5*10000000000*32768)*10000000000 ≤ frameLower (frameBranch index))
def framePatchShape (index : Nat) : Bool :=
  let p := framePatch index
  let b0 := frameBranch p.branch0
  let b1 := frameBranch p.branch1
  let b2 := frameBranch p.branch2
  let b3 := frameBranch p.branch3
  decide (p.label = index ∧ p.label < 241 ∧
    p.branch0 < 244 ∧ p.branch1 < 244 ∧ p.branch2 < 244 ∧ p.branch3 < 244 ∧
    b0.label = p.label ∧ b1.label = p.label ∧ b2.label = p.label ∧ b3.label = p.label ∧
    b0.splitFirst = p.splitFirst ∧ b1.splitFirst = p.splitFirst ∧ b2.splitFirst = p.splitFirst ∧ b3.splitFirst = p.splitFirst ∧
    b0.splitLast = p.splitLast ∧ b1.splitLast = p.splitLast ∧ b2.splitLast = p.splitLast ∧ b3.splitLast = p.splitLast ∧
    frameOriginalPathCheck p.label p.splitLast p.splitFirst (-b0.lower) p.lowerPath = true ∧
    frameOriginalPathCheck p.label p.splitFirst p.splitLast b3.upper p.upperPath = true ∧
    b1.lower ≤ b0.upper ∧ b2.lower ≤ b1.upper ∧ b3.lower ≤ b2.upper)
'''

def fwitness(cells,label,span=None,L=None,U=None,tight_only=False):
 def primitive(i,j):
  if i==j:return 0
  d=5*gn.cb(cells,label,i,j,1) if i<j else -5*gn.cb(cells,label,j,i,0)
  return d
 initial=[[primitive(i,j) for j in range(8)] for i in range(8)]
 if span is not None:
  i,j=span;initial[i][j]=min(initial[i][j],U);initial[j][i]=min(initial[j][i],-L)
 d=[r[:] for r in initial];paths=[[[i] if i==j else [i,j] for j in range(8)] for i in range(8)]
 if tight_only:
  for i in range(8):
   for j in range(8):
    if i<j:
     lo,hi=gn.tight(cells,label,i,j);d[i][j]=5*hi;d[j][i]=-5*lo
     paths[i][j]=[i,j] if hi==gn.cb(cells,label,i,j,1) else list(range(i,j+1))
     paths[j][i]=[j,i] if lo==gn.cb(cells,label,i,j,0) else list(range(j,i-1,-1))
 else:
  for k in range(8):
   for i in range(8):
    for j in range(8):
     if d[i][k]+d[k][j]<d[i][j]:d[i][j]=d[i][k]+d[k][j];paths[i][j]=paths[i][k]+paths[k][j][1:]
 assert all(d[i][i]==0 for i in range(8))
 words=[]
 for i in range(8):
  for j in range(8):
   walk=[]
   for v in paths[i][j]:
    if v in walk:walk=walk[:walk.index(v)+1]
    else:walk.append(v)
   assert walk[0]==i and walk[-1]==j and 1<=len(walk)<=8
   assert sum(initial[a][b] for a,b in zip(walk,walk[1:]))<=d[i][j]
   words.append(len(walk)+sum(v<<(4+4*k) for k,v in enumerate(walk)))
 return d,words

def frame_lower(rows,dual,d):
 pairs=[(rows[r],int(Q(v)*DEN)*(10**10 if rows[r][-1] else 1)) for r,v in dual]
 value=-sum(l*r[5] for r,l in pairs)
 for c in range(33):
  emb=c if c<7 else c+1
  obj=10**10*[28898,57272,75526,80958,75526,57272,28898][c] if c<7 else gn.TERMS[c-7][2]
  res=DEN*obj+sum(l*gn.coeff(r,emb) for r,l in pairs)
  lo=max(4*SC,-d[c+1][c]) if c<7 else 0
  hi=d[c][c+1] if c<7 else KS
  value+=res*(lo if res>=0 else hi)
 return value

def main():
 if not __debug__:raise SystemExit('Assertions must remain enabled; do not use -O')
 global gn
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--check',action='store_true');ap.add_argument('--output',type=Path);args=ap.parse_args();root=args.root
 sys.path.insert(0,str(root/'scripts'));import generate_ninth_span_certificate as gn
 old=read(root/'output/am-expanded-nine-point-certificate.json',gn.OLDPIN)
 new=read(root/'output/am-joint-frame-pair-certificate.json',PUBLIC_PIN)
 prior=read(root/'output/am-ninth-span-certificate.json',gn.PIN)
 priorcat=read(root/'output/am-ninth-span-point-catalog.json',gn.CATPIN)
 adapter=read(root/'output/am-joint-frame-ya-adapter.json',ADAPTER_PIN)
 cells=old['captured_cells'];assert len(cells)==241
 original_values={0:0}
 for cell in cells:
  for a in cell['atoms']:
   for p,v in ((a[2],a[8]),(a[3],a[9])):assert p not in original_values or original_values[p]==v;original_values[p]=v
 for p,v,n in old['point_catalog']:original_values[p]=v
 oldidx={p:i for i,p in enumerate(sorted(original_values))};assert len(oldidx)==1089
 oldnew={p for p,v,n in priorcat['point_catalog']}
 catalogue=priorcat['point_catalog']+[[p,v,n] for p,v,n in new['point_catalog'] if p not in oldnew]
 directidx={p:i for i,(p,v,n) in enumerate(catalogue)};assert len(directidx)==721
 def descriptor(desc,a=None,b=None):
  if len(desc)==6:i,j,p,v,n,side=desc;guard='direct-region'
  else:
   tag,i,j=desc[:3]
   if tag.startswith('closure-'):return (0 if tag=='closure-upper' else 1,i,j,0,0,0,0,0,0,False)
   if len(desc)==7:_,i,j,p,v,n,side=desc;guard='direct-region'
   else:_,i,j,p,v,n,guard,side=desc
  if guard=='direct-region':
   t=directidx[p];assert catalogue[t]==[p,v,n];return (2,i,j,t,0,0,0,0,0,side=='U')
  found=None
  for label,off in ((a,0),(b,1)):
   for s,t,w in gn.TERMS:
    if (s+off,t+off)==(i,j) and (p,v) in gn.enabled(gn.atom(cells,label,s,t)):found=(off,s,t,w)
  assert found is not None;off,s,t,w=found
  return (3,i,j,0,oldidx[p],off,s,t,w,side=='U')
 def dual(record):
  out=[(r,int(Q(v)*DEN)) for r,v in record['dual_sparse']]
  assert all(Q(v)*DEN==n and n>0 for (r,v),(s,n) in zip(record['dual_sparse'],out))
  return out
 branchdata=[];patchdata=[]
 for rec in prior['replacements']+new['pair_patches']:
  a,b=rec['left'],rec['right'];orig,origpaths=gn.witnesses(cells,a,b);ids=[]
  for br in rec['branches']:
   assert not br['empty'];L,U=br['bounds_5sc'];d,paths=gn.witnesses(cells,a,b,L,U)
   rows=gn.frame(cells,a,0)+gn.frame(cells,b,1);assert len(rows)==br['base_rows'];ds=[]
   for desc in br['added_rows']:
    tag,i,j=desc[:3];ds.append(descriptor(desc,a,b))
    if tag.startswith('closure-'):rows.append((i,j,1 if tag=='closure-upper' else -1,0,0,d[i][j] if tag=='closure-upper' else d[j][i],True))
    else:
     _,i,j,p,v,n,guard,side=desc;rows.append(gn.anchor(i,j,p,v,-d[j][i],d[i][j],side=='U'))
   val=gn.lower(rows,br['dual_sparse'],d);assert Q(val,2*SA*KS*DEN)==Q(br['lower']) and val>=2*TARGET*KS*DEN
   ids.append(len(branchdata));branchdata.append((a,b,L,U,d,ds,dual(br),paths))
  assert 1<=len(ids)<=3;ids+= [ids[-1]]*(3-len(ids));patchdata.append((a,b,*ids,origpaths[72],origpaths[8]))
 assert len(branchdata)==104 and len(patchdata)==57
 replacements={(p[0],p[1]):i for i,p in enumerate(patchdata)}
 reps=[p for p in old['pairs'] if (p['left'],p['right'])<=(gn.reflected(p['right']),gn.reflected(p['left']))]
 assert len(reps)==1224
 routes=[replacements.get((p['left'],p['right']),57) if Q(p['lower'])<Q(TARGET,SA) else 57 for p in reps]
 oldboxes=[];oldroutes=[0]*1224
 for index,rec in enumerate(reps):
  if routes[index]<57:continue
  a,b=rec['left'],rec['right'];rows=gn.old_rows(cells,rec)
  primitive=[[gn.primitive(cells,a,b,i,j) for j in range(9)] for i in range(9)]
  if gn.lower(rows,rec['dual_sparse'],primitive)>=2*TARGET*KS*DEN:continue
  d,paths=gn.witnesses(cells,a,b);assert gn.lower(rows,rec['dual_sparse'],d)>=2*TARGET*KS*DEN
  bounds=[];words=[]
  for c in range(8):bounds.extend((d[c][c+1],d[c+1][c]));words.extend((paths[9*c+c+1],paths[9*(c+1)+c]))
  oldroutes[index]=len(oldboxes);oldboxes.append((index,bounds,words))
 nbox=len(oldboxes)
 for index,rec in enumerate(reps):
  if index not in {r[0] for r in oldboxes}:oldroutes[index]=nbox
 frames={r['label']:r for r in new['frame_patches']+adapter['records']};splits={r['label']:r for r in new['frame_split_patches']}
 assert set(frames).isdisjoint(splits) and set(frames)|set(splits)==set(range(241))
 fb=[];fp=[]
 for label in range(241):
  ids=[];span=splits[label]['span'] if label in splits else [0,1]
  original,op=fwitness(cells,label)
  records=splits[label]['branches'] if label in splits else [frames[label]]
  for rec in records:
   if label in splits:
    L,U=rec['bounds_5sc'];d,paths=fwitness(cells,label,span,L,U)
   else:
    L,U=5*gn.cb(cells,label,0,1,0),5*gn.cb(cells,label,0,1,1);d,paths=fwitness(cells,label,span,L,U,True)
   rows=gn.frame(cells,label,0);assert len(rows)==rec['base_rows'];ds=[]
   for desc in rec['added_rows']:
    ds.append(descriptor(desc))
    if len(desc)==6:
     i,j,p,v,n,side=desc;rows.append(gn.anchor(i,j,p,v,-d[j][i],d[i][j],side=='U'))
    else:
     tag,i,j=desc[:3]
     if tag.startswith('closure-'):rows.append((i,j,1 if tag=='closure-upper' else -1,0,0,d[i][j] if tag=='closure-upper' else d[j][i],True))
     else:_,i,j,p,v,n,side=desc;rows.append(gn.anchor(i,j,p,v,-d[j][i],d[i][j],side=='U'))
   val=frame_lower(rows,rec['dual_sparse'],d)
   expected=Q(rec['lower'] if label in splits else rec['lower_exact'])
   assert Q(val,SA*KS*DEN)==expected and val>=ELL*KS*DEN,(label,Q(val,SA*KS*DEN),expected)
   ids.append(len(fb));fb.append((label,*span,L,U,d,ds,dual(rec),paths))
  ids+=[ids[-1]]*(4-len(ids));fp.append((label,*span,*ids,op[8*span[1]+span[0]],op[8*span[0]+span[1]]))
 assert len(fb)==244 and len(fp)==241
 text=['import RecordProportion.FiniteCertificateData','import RecordProportion.JointFramePairPoints','import RecordProportion.SparseDualSoundness','import RecordProportion.FloydSoundness','import RecordProportion.NinthSpanPathSoundness','import RecordProportion.JointFramePairPathSoundness','import RecordProportion.JointFramePairFrame','import Lean.Elab.Command','',
  'namespace RHWeil.RecordSubmission.JointFramePairData','open RHWeil.RecordSubmission.FiniteCertificateData','noncomputable section','set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option stderrAsMessages false','set_option Elab.async false','-- Public mathematical snapshot: '+PUBLIC_PIN,'-- Separate base-only frame adapter: '+ADAPTER_PIN]
 text+= ['structure Added where',*[f'  {x} : Nat' for x in ['kind','first','last','direct','oldIndex','offset','localFirst','localLast','weight']],'  rightCut : Bool','deriving Inhabited','',
  'structure Branch where','  left : Nat','  right : Nat','  lower : Int','  upper : Int','  bounds : Array Int','  added : List Added','  dual : List (Nat × Nat)','  paths : Array Nat','deriving Inhabited','',
  'structure Patch where',*[f'  {x} : Nat' for x in ['left','right','branch0','branch1','branch2','lowerPath','upperPath']],'deriving Inhabited','',
  'structure OldBox where','  index : Nat','  bounds : Array Int','  paths : Array Nat','deriving Inhabited','',
  'structure FrameBranch where',*[f'  {x} : Nat' for x in ['label','splitFirst','splitLast']],'  lower : Int','  upper : Int','  bounds : Array Int','  added : List Added','  dual : List (Nat × Nat)','  paths : Array Nat','deriving Inhabited','',
  'structure FramePatch where',*[f'  {x} : Nat' for x in ['label','splitFirst','splitLast','branch0','branch1','branch2','branch3','lowerPath','upperPath']],'deriving Inhabited','',
  'def branches : Array Branch := #[']
 def rowdata(data,frame=False):
  rows=[]
  for values in data:
   *head,d,ds,du,paths=values
   rows.append('  '+item(head)[:-1]+',#'+ll([x for row in d for x in row])+','+ll([item(x) for x in ds])+','+ll([f'({a},{b})' for a,b in du])+',#'+ll(paths)+'⟩,')
  return rows
 text+=rowdata(branchdata)+[']','','def patches : Array Patch := #[']+[f'  {item(x)},' for x in patchdata]+[']','','def repRoutes : Array Nat := #'+ll(routes),'','def oldBoxes : Array OldBox := #[']
 text+=[f'  ⟨{i},#'+ll(bs)+',#'+ll(ps)+'⟩,' for i,bs,ps in oldboxes]+[']','','def oldBoxRoutes : Array Nat := #'+ll(oldroutes),'','def frameBranches : Array FrameBranch := #[']
 text+=rowdata(fb,True)+[']','','def framePatches : Array FramePatch := #[']+[f'  {item(x)},' for x in fp]+[']','']
 pairmodel=gn.DATA_MODEL.removeprefix('\n').replace('NinthSpanFiniteData','JointFramePairData').replace('NinthSpanPoints','JointFramePairPoints').replace('805403','805448').replace('84','104').replace('47','57').replace('55',str(nbox))
 pairmodel=pairmodel.replace('-- GENERATED_BATCH_CALLS',FRAME_MODEL+'\n-- GENERATED_BATCH_CALLS')
 pairmodel=pairmodel.replace('| "rep_route" => "repRouteCheck"', '| "rep_route" => "repRouteCheck"\n      | "frame_guard" => "frameGuard"\n      | "frame_numeric" => "frameNumeric"\n      | "frame_shape" => "framePatchShape"')
 batches=[]
 for name,n in [('branch_guard',104),('branch_numeric',104),('patch_shape',57),('rep_route',1224),('old_numeric',1224),('frame_guard',244),('frame_numeric',244),('frame_shape',241)]:
  for s in range(0,n,16):batches.append(f'prove_ninth_batch {name} {s} {min(s+16,n)}')
 pairmodel=pairmodel.replace('-- GENERATED_BATCH_CALLS','\n'.join(batches))
 pos='\nend\nend RHWeil.RecordSubmission.JointFramePairData'
 families='\ncombine_ninth_family frame_guard 244 frameGuard allFrameGuards\ncombine_ninth_family frame_numeric 244 frameNumeric allFrameNumeric\ncombine_ninth_family frame_shape 241 framePatchShape allFramePatchShapes\n'
 pairmodel=pairmodel.replace(pos,families+pos)
 text.append(pairmodel)
 text += ['#print axioms RHWeil.RecordSubmission.JointFramePairData.allFrameGuards',
          '#print axioms RHWeil.RecordSubmission.JointFramePairData.allFrameNumeric',
          '#print axioms RHWeil.RecordSubmission.JointFramePairData.allFramePatchShapes']
 out=args.output or root/'RecordProportion/JointFramePairFiniteData.lean';generated='\n'.join(text)
 if args.check:assert out.read_text(encoding='utf8').replace('\r\n','\n')==generated
 else:out.write_text(generated,encoding='utf8',newline='\n')
 print(json.dumps({'status':'exact translation PASS','source':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size,'pair_branches':104,'pair_patches':57,'routed_representatives':sum(v<57 for v in routes),'old_path_boxes':nbox,'frame_branches':244,'frame_patches':241,'new_point_entries':180}))
if __name__=='__main__':main()
