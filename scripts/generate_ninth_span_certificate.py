"""Additive, lossless translation of the frozen c403 branch certificate to Lean.

This script performs exact rational consistency checks, never optimization.
The generated Lean proof separately checks geometry, admitted row guards, and
integer inequalities through ordinary kernel reduction.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

PIN = '9fc7f9d8a00ebbc3e2f8ff236b247af5ac3173c3942ec72b9180c4473a65cf96'
CATPIN = 'cda8ce5fce3d0a639975f54e57b1991c7d5a2a2cb112df4e3dd13237a954fb27'
OLDPIN = '3a3c8b24015162a4835f5c1d8633a4f9f8bdace26d711631dd6374c689bce04f'
SC, KS, DEN, SA = 32768, 5*10**10*32768, 10**10, 10**8
TERMS = [(0,1,13630830),(0,3,19565904),(0,4,20317441),(0,5,45030671),
 (0,6,100000000),(0,7,200000000),(1,2,29997996),(1,3,30621878),
 (1,4,47766489),(1,5,79682558),(1,6,109938656),(1,7,100000000),
 (2,3,37356140),(2,4,69378121),(2,5,65335210),(2,6,79682558),
 (2,7,45030671),(3,4,38030065),(3,5,69378121),(3,6,47766489),
 (3,7,20317441),(4,5,37356140),(4,6,30621878),(4,7,19565904),
 (5,6,29997996),(6,7,13630830)]
CELLSPANS=[(i,i+1) for i in range(7)]+[(i,j) for i in range(7) for j in range(i+2,8)]
SQUARES=list(dict.fromkeys((i+o,j+o) for o in (0,1) for i,j,a in TERMS))+[(0,8)]
assert len(CELLSPANS)==28 and len(SQUARES)==34

def canonical(raw):return raw.replace(b'\r\n',b'\n').replace(b'\r',b'\n')
def read(path,pin):
 raw=canonical(path.read_bytes());assert hashlib.sha256(raw).hexdigest()==pin
 return json.loads(raw)
def reflected(n):return n+241 if n<241 else n-241
def fields(v):return v&((1<<32)-1),(v>>32)&((1<<32)-1),(v>>64)&((1<<32)-1)
def cb(cells,label,i,j,side):
 if label>=241:label,i,j=label-241,7-j,7-i
 pos=2*i if j==i+1 else 14+2*(i*(13-i)//2+j-i-2)
 return (cells[label]['gap_bounds']+cells[label]['span_bounds'])[pos+side]
def tight(cells,label,i,j):
 return max(cb(cells,label,i,j,0),sum(cb(cells,label,k,k+1,0) for k in range(i,j))),min(cb(cells,label,i,j,1),sum(cb(cells,label,k,k+1,1) for k in range(i,j)))
def atom(cells,label,i,j):
 if label>=241:label,i,j=label-241,7-j,7-i
 return cells[label]['atoms'][next(k for k,(a,b,w) in enumerate(TERMS) if (a,b)==(i,j))]
def enabled(a):
 k,m,p,r,L,U,l0,lb,pp,rp=a
 return ([(p,pp)] if k==1 or k==2 and m>0 or k==3 and m<1024 else [])+([(r,rp)] if k==3 and m>0 else [])
def anchor(i,j,p,v,L5,U5,side):
 V,plus,minus=fields(v);dm=plus-2*10**9;dp=2*10**9-minus
 l,u=min(L5,5*p),max(U5,5*p)
 return (i,j,10*(dp if side else dm),8+SQUARES.index((i,j)),-1,
  -5*V*SC+50*(dm if side else dp)*p-10*((dm-dp)*u if side else (dp-dm)*l),False)
def frame(cells,label,offset):
 rows=[]
 for i,j in CELLSPANS:
  rows.extend([(i+offset,j+offset,1,0,0,5*cb(cells,label,i,j,1),True),(i+offset,j+offset,-1,0,0,-5*cb(cells,label,i,j,0),True)])
 for i,j,w in TERMS:
  a=atom(cells,label,i,j);L,U=tight(cells,label,i,j)
  rows.append((i+offset,j+offset,0,8+SQUARES.index((i+offset,j+offset)),-1,-5*a[7]*SC,False))
  for p,v in enabled(a):
   rows.extend([anchor(i+offset,j+offset,p,v,5*L,5*U,False),anchor(i+offset,j+offset,p,v,5*L,5*U,True)])
 return rows
def old_rows(cells,item):
 a,b=item['left'],item['right'];rows=frame(cells,a,0)+frame(cells,b,1)
 for ex in item['extra_points']:
  i,j=ex['span'];off=ex['offset'];label=a if off==0 else b
  L,U=tight(cells,label,i,j);p,v=ex['point'],ex['pack']
  rows.extend([anchor(i+off,j+off,p,v,5*min(L,p),5*max(U,p),False),anchor(i+off,j+off,p,v,5*min(L,p),5*max(U,p),True)])
 return rows
def primitive(cells,left,right,i,j):
 if i==j:return 0
 INF=10**30
 a=(5*cb(cells,left,i,j,1) if i<j else -5*cb(cells,left,j,i,0)) if max(i,j)<=7 else INF
 b=(5*cb(cells,right,i-1,j-1,1) if i<j else -5*cb(cells,right,j-1,i-1,0)) if min(i,j)>=1 else INF
 d=min(a,b)
 return min(d,-4*SC) if i==j+1 else d
def floyd(d):
 for k in range(9):d=[[min(d[i][j],d[i][k]+d[k][j]) for j in range(9)] for i in range(9)]
 return d
def closure(cells,a,b,lo=None,hi=None):
 d=floyd([[primitive(cells,a,b,i,j) for j in range(9)] for i in range(9)])
 if lo is not None:
  d[0][8]=min(d[0][8],hi);d[8][0]=min(d[8][0],-lo);d=floyd(d)
 assert all(d[i][i]==0 for i in range(9))
 return d
def witnesses(cells,a,b,lo=None,hi=None):
 d=[[primitive(cells,a,b,i,j) for j in range(9)] for i in range(9)]
 if lo is not None:
  d[0][8]=min(d[0][8],hi);d[8][0]=min(d[8][0],-lo)
 initial=[r[:] for r in d]
 paths=[[[i] if i==j else [i,j] for j in range(9)] for i in range(9)]
 for k in range(9):
  for i in range(9):
   for j in range(9):
    if d[i][k]+d[k][j]<d[i][j]:
     d[i][j]=d[i][k]+d[k][j];paths[i][j]=paths[i][k]+paths[k][j][1:]
 result=[]
 for i in range(9):
  for j in range(9):
   walk=[]
   for v in paths[i][j]:
    if v in walk:walk=walk[:walk.index(v)+1]
    else:walk.append(v)
   assert walk[0]==i and walk[-1]==j and 1<=len(walk)<=9
   assert sum(initial[u][v] for u,v in zip(walk,walk[1:]))<=d[i][j]
   result.append(len(walk)+sum(v<<(4+4*k) for k,v in enumerate(walk)))
 return d,result
def coeff(row,c):
 i,j,s,z,q,b,geo=row
 return s if c<8 and i<=c<j else q if c>=8 and c==z else 0
def objective(c):
 if c<8:return 10**10*[28898,86170,132798,156484,156484,132798,86170,28898][c]
 p=SQUARES[c-8]
 return 4*SA if p==(0,8) else sum(a for o in (0,1) for i,j,a in TERMS if (i+o,j+o)==p)
def lower(rows,dual,d):
 multi=[(rows[r],int(Q(v)*DEN)*(10**10 if rows[r][-1] else 1)) for r,v in dual]
 value=-sum(l*r[5] for r,l in multi)
 for c in range(42):
  res=DEN*objective(c)+sum(l*coeff(r,c) for r,l in multi)
  lo=max(4*SC,-d[c+1][c]) if c<8 else 0
  hi=d[c][c+1] if c<8 else KS
  value+=res*(lo if res>=0 else hi)
 return value
def lean_list(xs):return '['+','.join(map(str,xs))+']'
DATA_MODEL = r'''
def branch (index : Nat) : Branch := (branches[index]?).getD default
def patch (index : Nat) : Patch := (patches[index]?).getD default
def repRoute (index : Nat) : Nat := (repRoutes[index]?).getD 47
def oldBoxRoute (index : Nat) : Nat := (oldBoxRoutes[index]?).getD 55
def oldBox (index : Nat) : OldBox := (oldBoxes[oldBoxRoute index]?).getD default
def spanLower (b : Branch) (i j : Nat) : Int := -((b.bounds[9*j+i]?).getD 0)
def spanUpper (b : Branch) (i j : Nat) : Int := (b.bounds[9*i+j]?).getD 0

/-- Each witness uses only original primitive bounds and the two real full-span
branch inequalities. No recursively unfolded Floyd equality is trusted. -/
def branchEdge (b : Branch) (i j : Nat) : Int :=
  let d := primitiveBound b.left b.right i j
  if i = 0 ∧ j = 8 then min d b.upper
  else if i = 8 ∧ j = 0 then min d (-b.lower) else d
def branchPathCheck (b : Branch) (slot : Nat) : Bool :=
  NinthSpanPaths.check (branchEdge b) (slot/9) (slot%9)
    ((b.bounds[slot]?).getD 0) ((b.paths[slot]?).getD 0)
def originalPathCheck (left right first last : Nat) (bound : Int) (word : Nat) : Bool :=
  NinthSpanPaths.check (primitiveBound left right) first last bound word

def spanInitial (left right : Nat) (lower upper : Int) : Array Int :=
  ((List.range 81).map fun slot =>
    let d := ((pairClosure left right)[slot]?).getD 0
    if slot = 8 then min d upper else if slot = 72 then min d (-lower) else d).toArray

def addedPoint (a : Added) : Nat :=
  if a.kind = 2 then NinthSpanPoints.catalogPoint a.direct else pointPosition a.oldIndex
def addedValue (a : Added) : Nat :=
  if a.kind = 2 then NinthSpanPoints.catalogValue a.direct else pointValue a.oldIndex
def addedLabel (b : Branch) (a : Added) : Nat := if a.offset = 0 then b.left else b.right

def addedCheck (b : Branch) (a : Added) : Bool :=
  decide (a.first < a.last ∧ a.last ≤ 8) &&
  if a.kind = 0 ∨ a.kind = 1 then true else
    decide ((a.first,a.last) ∈ squareSpans) &&
    if a.kind = 2 then
      NinthSpanPoints.directCheck (spanLower b a.first a.last)
        (spanUpper b a.first a.last) a.direct
    else decide (a.kind = 3 ∧ a.offset ≤ 1 ∧
      a.first = a.localFirst+a.offset ∧ a.last = a.localLast+a.offset ∧
      (a.localFirst,a.localLast,a.weight) ∈ terms ∧
      a.oldIndex ∈ oldPointIndices (termAtom (addedLabel b a) a.localFirst a.localLast) ∧
      5*(tightLower (addedLabel b a) a.localFirst a.localLast:Int) ≤ spanLower b a.first a.last ∧
      spanUpper b a.first a.last ≤ 5*(tightUpper (addedLabel b a) a.localFirst a.localLast:Int))

def addedRow (b : Branch) (a : Added) : IntegerRow :=
  if a.kind = 0 then ⟨a.first,a.last,1,0,0,spanUpper b a.first a.last,true⟩
  else if a.kind = 1 then ⟨a.first,a.last,-1,0,0,-spanLower b a.first a.last,true⟩
  else
    let V : Int := AMW.Cert.PyrD.lo32 (addedValue a)
    let dm : Int := (AMW.Cert.PyrD.lo32 (AMW.Cert.PyrD.hi32 (addedValue a)):Int)-2000000000
    let dp : Int := 2000000000-(AMW.Cert.PyrD.hi32 (AMW.Cert.PyrD.hi32 (addedValue a)):Int)
    let p : Int := addedPoint a
    let l5 := min (spanLower b a.first a.last) (5*p)
    let u5 := max (spanUpper b a.first a.last) (5*p)
    if a.rightCut then
      ⟨a.first,a.last,10*dp,squareColumn a.first a.last,-1,
        -5*V*32768+50*dm*p-10*(dm-dp)*u5,false⟩
    else
      ⟨a.first,a.last,10*dm,squareColumn a.first a.last,-1,
        -5*V*32768+50*dp*p-10*(dp-dm)*l5,false⟩

def branchRows (b : Branch) : List IntegerRow :=
  frameRows b.left 0 ++ frameRows b.right 1 ++ b.added.map (addedRow b)
def branchMultipliers (b : Branch) : List (IntegerRow × Int) :=
  b.dual.map fun p =>
    let row := (branchRows b).getD p.1 default
    (row,(p.2:Int)*(if row.geometric then 10000000000 else 1))
def boxLo (b : Branch) (column : Nat) : Int :=
  if column < 8 then max (4*32768) (spanLower b column (column+1)) else 0
def boxHi (b : Branch) (column : Nat) : Int :=
  if column < 8 then spanUpper b column (column+1) else 5*10000000000*32768
def branchLower (b : Branch) : Int :=
  RHWeilRecord.SparseDualSoundness.checkerL 42 (branchMultipliers b)
    (fun c => 10000000000*objectiveCoeff c) (fun r c => r.1.coeff c)
    (fun r => r.1.bound) (fun r => r.2) (boxLo b) (boxHi b)
def newIntegerTarget : Int := 2*805403*(5*10000000000*32768)*10000000000
def branchGuard (index : Nat) : Bool :=
  let b := branch index
  decide (b.left < 482 ∧ b.right < 482 ∧ b.lower ≤ b.upper ∧ b.bounds.size = 81 ∧
    b.paths.size = 81) &&
    ((List.range 81).all (branchPathCheck b) && b.added.all (addedCheck b))
def branchNumeric (index : Nat) : Bool := decide (newIntegerTarget ≤ branchLower (branch index))

def patchShape (index : Nat) : Bool :=
  let p := patch index
  let b0 := branch p.branch0
  let b1 := branch p.branch1
  let b2 := branch p.branch2
  decide (p.left < 482 ∧ p.right < 482 ∧
    p.branch0 < 84 ∧ p.branch1 < 84 ∧ p.branch2 < 84 ∧
    b0.left = p.left ∧ b0.right = p.right ∧
    b1.left = p.left ∧ b1.right = p.right ∧
    b2.left = p.left ∧ b2.right = p.right ∧
    originalPathCheck p.left p.right 8 0 (-b0.lower) p.lowerPath = true ∧
    originalPathCheck p.left p.right 0 8 b2.upper p.upperPath = true ∧
    b1.lower ≤ b0.upper ∧ b2.lower ≤ b1.upper)

def repRouteCheck (index : Nat) : Bool :=
  let p := patch (repRoute index)
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  decide (repRoute index = 47 ∨
    repRoute index < 47 ∧ p.left = packet.1 ∧ p.right = packet.2.1)
def strongIntegerCheck (index : Nat) : Bool :=
  decide (2*805403*(5*10000000000*32768)*1000000000 ≤ integerCertificateLower index)
def strongBasicCheck (index : Nat) : Bool :=
  decide (2*805403*(5*10000000000*32768)*1000000000 ≤ basicIntegerCertificateLower index)
def oldPathSlotCheck (index slot : Nat) : Bool :=
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let c := slot/2
  let first := if slot%2=0 then c else c+1
  let last := if slot%2=0 then c+1 else c
  NinthSpanPaths.check (primitiveBound packet.1 packet.2.1) first last
    (((oldBox index).bounds[slot]?).getD 0) (((oldBox index).paths[slot]?).getD 0)
def oldPathCheck (index : Nat) : Bool :=
  decide (oldBoxRoute index < 55 ∧ (oldBox index).index = index ∧
    (oldBox index).bounds.size = 16 ∧ (oldBox index).paths.size = 16) &&
    (List.range 16).all (oldPathSlotCheck index)
def oldPathLo (index c : Nat) : Int :=
  if c < 8 then max (4*32768) (-(((oldBox index).bounds[2*c+1]?).getD 0)) else 0
def oldPathHi (index c : Nat) : Int :=
  if c < 8 then (((oldBox index).bounds[2*c]?).getD 0) else 5*10000000000*32768
def oldRows (index : Nat) : List IntegerRow :=
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  frameRows packet.1 0 ++ frameRows packet.2.1 1 ++
    extraRows packet.1 packet.2.1 packet.2.2.2.2.1 packet.2.2.2.2.2
def oldMultipliers (index : Nat) : List (IntegerRow × Int) :=
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  (decodeMultipliers packet.2.2.1 packet.2.2.2.1).map fun p =>
    let row := (oldRows index).getD p.1 default
    (row,(p.2:Int)*(if row.geometric then 10000000000 else 1))
def oldPathLower (index : Nat) : Int :=
  RHWeilRecord.SparseDualSoundness.checkerL 42 (oldMultipliers index)
    (fun c => 1000000000*objectiveCoeff c) (fun r c => r.1.coeff c)
    (fun r => r.1.bound) (fun r => r.2) (oldPathLo index) (oldPathHi index)
def strongPathCheck (index : Nat) : Bool := oldPathCheck index &&
  decide (2*805403*(5*10000000000*32768)*1000000000 ≤ oldPathLower index)
def oldOrPatch (index : Nat) : Bool :=
  decide (repRoute index < 47) || strongBasicCheck index || strongPathCheck index

theorem strongCheck_of_basic {index : Nat} (h : strongBasicCheck index = true) :
    strongIntegerCheck index = true := by
  apply decide_eq_true
  exact (of_decide_eq_true h).trans (basicIntegerCertificateLower_le index)
theorem oldOrPatch_of_basic {index : Nat} (h : strongBasicCheck index = true) :
    oldOrPatch index = true := by simp [oldOrPatch,h]
theorem oldOrPatch_of_path {index : Nat} (h : strongPathCheck index = true) :
    oldOrPatch index = true := by simp [oldOrPatch,h]

elab "prove_ninth_batch" kind:ident first:num last:num : command => do
  Lean.Elab.withEnableInfoTree false do
    let kind := kind.getId.toString
    let fn := match kind with
      | "branch_guard" => "branchGuard"
      | "branch_numeric" => "branchNumeric"
      | "patch_shape" => "patchShape"
      | "rep_route" => "repRouteCheck"
      | _ => "oldOrPatch"
    for offset in List.range (last.getNat-first.getNat) do
      let index := first.getNat+offset
      let proof := if kind = "old_numeric" then
          "by\n  first\n  | have hp : repRoute " ++ toString index ++ " < 47 := by decide +kernel\n    simp [oldOrPatch,hp]\n  | exact oldOrPatch_of_basic (by decide +kernel)\n  | exact oldOrPatch_of_path (by decide +kernel)"
        else "by decide +kernel"
      let command := "theorem " ++ kind ++ "_" ++ toString index ++ " : " ++ fn ++
        " " ++ toString index ++ " = true := " ++ proof
      if index % 32 = 0 then
        Lean.Elab.Command.liftIO <| IO.eprintln s!"Kernel-checking ninth-span {kind} {index}"
      let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv)
          (Lean.Name.mkSimple "command") command with
        | .ok stx => pure stx
        | .error msg => Lean.throwError msg
      Lean.Elab.Command.elabCommand stx
      if (← get).messages.hasErrors then Lean.throwError "Ninth-span closed theorem failed"
      let name := Lean.Name.str (← Lean.getCurrNamespace) (kind ++ "_" ++ toString index)
      match ← Lean.getConstInfo name with
        | .thmInfo info =>
          if info.value.hasSorry || info.type.hasSorry then
            Lean.throwError "Ninth-span theorem contains a recovery placeholder"
        | _ => Lean.throwError "Ninth-span closed theorem was not installed"
      if index % 32 = 0 then
        Lean.Elab.Command.liftIO <| IO.eprintln s!"Kernel-checked ninth-span {kind} {index}"

elab "combine_ninth_family" kind:ident count:num fn:ident result:ident : command => do
  Lean.Elab.withEnableInfoTree false do
    let cases := (List.range count.getNat).map fun i =>
      "  | " ++ toString i ++ " => exact " ++ kind.getId.toString ++ "_" ++ toString i
    let command := "theorem " ++ result.getId.toString ++ " (index : Nat) (hi : index < " ++
      toString count.getNat ++ ") : " ++ fn.getId.toString ++ " index = true := by\n  match index with\n" ++
      String.intercalate "\n" cases ++ "\n  | n + " ++ toString count.getNat ++ " => omega"
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) (Lean.Name.mkSimple "command") command with
      | .ok stx => pure stx
      | .error msg => Lean.throwError msg
    Lean.Elab.Command.elabCommand stx
    if (← get).messages.hasErrors then Lean.throwError "Ninth-span family failed"
    let name := Lean.Name.str (← Lean.getCurrNamespace) result.getId.toString
    match ← Lean.getConstInfo name with
      | .thmInfo info =>
          if info.value.hasSorry || info.type.hasSorry then Lean.throwError "Family contains placeholder"
      | _ => Lean.throwError "Ninth-span family was not installed"

-- GENERATED_BATCH_CALLS
combine_ninth_family branch_guard 84 branchGuard allBranchGuards
combine_ninth_family branch_numeric 84 branchNumeric allBranchNumeric
combine_ninth_family patch_shape 47 patchShape allPatchShapes
combine_ninth_family rep_route 1224 repRouteCheck allRepRoutes
combine_ninth_family old_numeric 1224 oldOrPatch allOldOrPatch

end
end RHWeil.RecordSubmission.NinthSpanFiniteData
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allBranchGuards
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allBranchNumeric
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allPatchShapes
#print axioms RHWeil.RecordSubmission.NinthSpanFiniteData.allOldOrPatch
'''

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1])
 ap.add_argument('--output',type=Path)
 ap.add_argument('--template',type=Path,default=None)
 ap.add_argument('--check',action='store_true',help='compare generated LF source with existing output')
 args=ap.parse_args();root=args.root
 old=read(root/'output/am-expanded-nine-point-certificate.json',OLDPIN)
 new=read(root/'output/am-ninth-span-certificate.json',PIN)
 cat=read(root/'output/am-ninth-span-point-catalog.json',CATPIN)
 cells=old['captured_cells'];assert len(cells)==241
 pvalues={0:0}
 for cell in cells:
  for a in cell['atoms']:
   for p,v in [(a[2],a[8]),(a[3],a[9])]:
    assert p not in pvalues or pvalues[p]==v;pvalues[p]=v
 for p,v,l in old['point_catalog']:pvalues[p]=v
 oldidx={p:i for i,p in enumerate(sorted(pvalues))};assert len(oldidx)==1089
 newidx={p:i for i,(p,v,l) in enumerate(cat['point_catalog'])}
 # The new point module uses the catalog's exact published order.
 branchdata=[];patchdata=[]
 for patch in new['replacements']:
  a,b=patch['left'],patch['right'];ids=[]
  orig,orig_paths=witnesses(cells,a,b)
  for br in patch['branches']:
   assert not br['empty'];L,U=br['bounds_5sc'];d=closure(cells,a,b,L,U)
   path_d,paths=witnesses(cells,a,b,L,U);assert path_d==d
   rows=frame(cells,a,0)+frame(cells,b,1);assert len(rows)==br['base_rows']
   descriptors=[]
   for desc in br['added_rows']:
    tag,i,j=desc[:3]
    if tag.startswith('closure-'):
     k=0 if tag=='closure-upper' else 1
     descriptors.append((k,i,j,0,0,0,0,0,0,False))
     rows.append((i,j,1 if k==0 else -1,0,0,d[i][j] if k==0 else d[j][i],True))
    else:
     _,i,j,p,v,listid,guard,side=desc
     if guard=='direct-region':
      t=newidx[p];assert cat['point_catalog'][t]==[p,v,listid]
      descriptors.append((2,i,j,t,0,0,0,0,0,side=='U'))
     else:
      found=None
      for label,off in [(a,0),(b,1)]:
       for s,t,w in TERMS:
        if (s+off,t+off)==(i,j) and (p,v) in enabled(atom(cells,label,s,t)):
         l,u=tight(cells,label,s,t)
         if 5*l<=-d[j][i] and d[i][j]<=5*u:found=(off,s,t,w)
      assert found is not None
      off,s,t,w=found
      descriptors.append((3,i,j,0,oldidx[p],off,s,t,w,side=='U'))
     rows.append(anchor(i,j,p,v,-d[j][i],d[i][j],side=='U'))
   vl=lower(rows,br['dual_sparse'],d)
   assert Q(vl,2*SA*KS*DEN)==Q(br['lower']) and vl>=2*805403*KS*DEN
   dual=[(r,int(Q(v)*DEN)) for r,v in br['dual_sparse']]
   assert all(Q(v)*DEN==n and n>0 for (r,v),(s,n) in zip(br['dual_sparse'],dual))
   ids.append(len(branchdata));branchdata.append((a,b,L,U,d,descriptors,dual,paths))
  assert 1<=len(ids)<=3
  assert branchdata[ids[0]][2]==-orig[8][0] and branchdata[ids[-1]][3]==orig[0][8]
  ids=ids+[ids[-1]]*(3-len(ids));patchdata.append((a,b,*ids,orig_paths[72],orig_paths[8]))
 assert len(branchdata)==84 and len(patchdata)==47
 ps={(p['left'],p['right']):p for p in old['pairs']}
 reps=[p for k,p in ps.items() if k<=(reflected(k[1]),reflected(k[0]))]
 patches={(p['left'],p['right']):i for i,p in enumerate(new['replacements'])}
 routes=[patches.get((p['left'],p['right']),47) if Q(p['lower'])<Q(805403,SA) else 47 for p in reps]
 assert len(reps)==1224 and sum(x<47 for x in routes)==25
 oldboxes=[];oldboxroutes=[55]*1224
 for index,item in enumerate(reps):
  if routes[index]<47:continue
  a,b=item['left'],item['right'];rows=old_rows(cells,item)
  primitive_d=[[primitive(cells,a,b,i,j) for j in range(9)] for i in range(9)]
  if lower(rows,item['dual_sparse'],primitive_d)>=2*805403*KS*DEN:continue
  d,paths=witnesses(cells,a,b)
  assert Q(lower(rows,item['dual_sparse'],d),2*SA*KS*DEN)==Q(item['lower'])
  assert lower(rows,item['dual_sparse'],d)>=2*805403*KS*DEN
  bounds=[];words=[]
  for c in range(8):
   bounds.extend([d[c][c+1],d[c+1][c]])
   words.extend([paths[9*c+c+1],paths[9*(c+1)+c]])
  oldboxroutes[index]=len(oldboxes);oldboxes.append((index,bounds,words))
 assert len(oldboxes)==55
 text=['import RecordProportion.FiniteCertificateData','import RecordProportion.NinthSpanPoints',
 'import RecordProportion.SparseDualSoundness','import RecordProportion.FloydSoundness','import RecordProportion.NinthSpanPathSoundness',
 'import Lean.Elab.Command','','namespace RHWeil.RecordSubmission.NinthSpanFiniteData',
 'open RHWeil.RecordSubmission.FiniteCertificateData','noncomputable section',
 'set_option maxRecDepth 100000','set_option maxHeartbeats 0','set_option Elab.async false',
 '-- Frozen public certificate canonical LF SHA256: '+PIN,
 '-- Point catalog canonical LF SHA256: '+CATPIN,
 'structure Added where',*[f'  {x} : Nat' for x in ['kind','first','last','direct','oldIndex','offset','localFirst','localLast','weight']],
 '  rightCut : Bool','deriving Inhabited','',
 'structure Branch where','  left : Nat','  right : Nat','  lower : Int','  upper : Int','  bounds : Array Int',
 '  added : List Added','  dual : List (Nat × Nat)','  paths : Array Nat','deriving Inhabited','',
 'structure Patch where',*[f'  {x} : Nat' for x in ['left','right','branch0','branch1','branch2','lowerPath','upperPath']],'deriving Inhabited','',
 'structure OldBox where','  index : Nat','  bounds : Array Int','  paths : Array Nat','deriving Inhabited','',
 'def branches : Array Branch := #[']
 for a,b,L,U,d,ds,dual,paths in branchdata:
  dsL='['+','.join('⟨'+','.join(str(y).lower() for y in x)+'⟩' for x in ds)+']'
  duL='['+','.join(f'({r},{n})' for r,n in dual)+']'
  text.append(f'  ⟨{a},{b},{L},{U},#'+lean_list([x for r in d for x in r])+f',{dsL},{duL},#'+lean_list(paths)+'⟩,')
 text+= [']','','def patches : Array Patch := #[']
 text+= ['  ⟨'+','.join(map(str,x))+'⟩,' for x in patchdata]
 text+= [']','','def repRoutes : Array Nat := #'+lean_list(routes),'']
 text+= ['def oldBoxes : Array OldBox := #[']
 text+= [f'  ⟨{index},#'+lean_list(bounds)+',#'+lean_list(words)+'⟩,' for index,bounds,words in oldboxes]
 text+= [']','','def oldBoxRoutes : Array Nat := #'+lean_list(oldboxroutes),'']
 model=args.template.read_text(encoding='utf8') if args.template else DATA_MODEL.removeprefix('\n')
 batches=[]
 for name,n in [('branch_guard',84),('branch_numeric',84),('patch_shape',47),('rep_route',1224),('old_numeric',1224)]:
  for start in range(0,n,16):batches.append(f'prove_ninth_batch {name} {start} {min(start+16,n)}')
 model=model.replace('-- GENERATED_BATCH_CALLS','\n'.join(batches))
 text.append(model)
 out=args.output or root/'RecordProportion/NinthSpanFiniteData.lean'
 generated='\n'.join(text)
 if args.check:assert canonical(out.read_bytes()).decode('utf8')==generated
 else:out.write_text(generated,encoding='utf8',newline='\n')
 print(json.dumps({'output':str(out),'branches':84,'patches':47,'weak_representatives':25,
  'bytes':out.stat().st_size,'sha256':hashlib.sha256(out.read_bytes()).hexdigest()}))
if __name__=='__main__':main()
