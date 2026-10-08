"""Lossless transparent-Nat packing of the fixed c260 certificate.

This generator never optimizes a multiplier, changes the target, or establishes
the continuous theorem. The Lean checker must prove properties of decoded data.
"""
import argparse
import ast
import re
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "output/am-expanded-nine-point-certificate.json"
OUTPUT = ROOT / "RecordProportion/FiniteCertificateData.lean"
INPUT_SHA = "3a3c8b24015162a4835f5c1d8633a4f9f8bdace26d711631dd6374c689bce04f"


def canonical(raw):
    return raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n")


def pack(values, width):
    assert all(type(x) is int and 0 <= x < 1 << width for x in values)
    return sum(x << (width * i) for i, x in enumerate(values))


def unpack(word, count, width):
    return [(word >> (width * i)) & ((1 << width) - 1) for i in range(count)]


ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"


def literal(word):
    assert word >= 0
    chars = []
    value = word
    while value:
        chars.append(ALPHABET[value & 63])
        value >>= 6
    text = "".join(reversed(chars)) or "A"
    recovered = 0
    for c in text:
        recovered = recovered * 64 + ALPHABET.index(c)
    assert recovered == word
    return f'(n64% "{text}")'


def reflected(index):
    assert 0 <= index < 482
    return index + 241 if index < 241 else index - 241


def lookup(values, start=0):
    """Balanced transparent lookup; no huge Array literal is normalized per get."""
    assert values
    if len(values) == 1:
        return str(values[0])
    middle = len(values) // 2
    left = lookup(values[:middle], start)
    right = lookup(values[middle:], start + middle)
    return f"(if index < {start + middle} then {left} else {right})"


def packed_lookup(name, values, width):
    chunks = [literal(pack(values[i:i+32], width)) for i in range(0, len(values), 32)]
    return [f"def {name}Chunks (index : Nat) : Nat :=", "  " + lookup(chunks), "",
            f"def {name} (index : Nat) : Nat :=",
            f"  bits ({name}Chunks (index / 32)) ((index % 32) * {width}) {width}", ""]


NUMERIC_CODE = r'''
structure IntegerRow where
  first : Nat
  last : Nat
  slope : Int
  square : Nat
  zcoef : Int
  bound : Int
  geometric : Bool
deriving Inhabited

def IntegerRow.coeff (row : IntegerRow) (column : Nat) : Int :=
  if column < 8 then
    if row.first ≤ column ∧ column < row.last then row.slope else 0
  else if column = row.square then row.zcoef else 0

def terms : List (Nat × Nat × Nat) :=
  [(0,1,13630830),(0,3,19565904),(0,4,20317441),(0,5,45030671),
   (0,6,100000000),(0,7,200000000),(1,2,29997996),(1,3,30621878),
   (1,4,47766489),(1,5,79682558),(1,6,109938656),(1,7,100000000),
   (2,3,37356140),(2,4,69378121),(2,5,65335210),(2,6,79682558),
   (2,7,45030671),(3,4,38030065),(3,5,69378121),(3,6,47766489),
   (3,7,20317441),(4,5,37356140),(4,6,30621878),(4,7,19565904),
   (5,6,29997996),(6,7,13630830)]

def longSpans : List (Nat × Nat) :=
  [(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,5),(1,6),
   (1,7),(2,4),(2,5),(2,6),(2,7),(3,5),(3,6),(3,7),(4,6),(4,7),(5,7)]

def cellSpans : List (Nat × Nat) :=
  (List.range 7).map (fun i => (i,i+1)) ++ longSpans

def squareSpans : List (Nat × Nat) :=
  __GENERATED_COLUMN_SPANS__

def squareColumn (i j : Nat) : Nat :=
  8 + squareSpans.findIdx (fun p => p == (i,j))

def cellPacket (label : Nat) : Nat × Nat :=
  (cells[if label < 241 then label else label - 241]?).getD (0,0)

def geometrySlot (i j : Nat) : Nat :=
  if j = i + 1 then 2 * i
  else 14 + 2 * (i * (13-i) / 2 + (j-i-2))

def cellBound (label i j side : Nat) : Nat :=
  let pos := if label < 241 then geometrySlot i j else geometrySlot (7-j) (7-i)
  bits (cellPacket label).1 (22 * (pos + side)) 22

def cellLower (label i j : Nat) : Nat := cellBound label i j 0
def cellUpper (label i j : Nat) : Nat := cellBound label i j 1

def tightLower (label i j : Nat) : Nat :=
  max (cellLower label i j)
    (((List.range (j-i)).map fun k => cellLower label (i+k) (i+k+1)).sum)

def tightUpper (label i j : Nat) : Nat :=
  min (cellUpper label i j)
    (((List.range (j-i)).map fun k => cellUpper label (i+k) (i+k+1)).sum)

def termAtom (label i j : Nat) : Nat :=
  let span := if label < 241 then (i,j) else (7-j,7-i)
  let index := terms.findIdx (fun t => (t.1,t.2.1) == span)
  bits (cellPacket label).2 (67 * index) 67

def oldPointIndices (atom : Nat) : List Nat :=
  let kind := bits atom 0 2
  let mix := bits atom 2 11
  let p := bits atom 13 11
  let r := bits atom 24 11
  if kind = 1 then [p]
  else if kind = 2 then if 0 < mix then [p] else []
  else if kind = 3 then
    (if mix < 1024 then [p] else []) ++ (if 0 < mix then [r] else [])
  else []

def anchorRows (offset i j point value L U : Nat) : List IntegerRow :=
  let V : Int := bits value 0 32
  let dm : Int := (bits value 32 32 : Int) - 2000000000
  let dp : Int := 2000000000 - (bits value 64 32 : Int)
  let lo : Int := L
  let hi : Int := U
  let p : Int := point
  [⟨i+offset,j+offset,10*dm,squareColumn (i+offset) (j+offset),-1,
      -5*V*32768+50*dp*p-50*(dp-dm)*lo,false⟩,
   ⟨i+offset,j+offset,10*dp,squareColumn (i+offset) (j+offset),-1,
      -5*V*32768+50*dm*p-50*(dm-dp)*hi,false⟩]

def frameRows (label offset : Nat) : List IntegerRow :=
  let geometry := cellSpans.flatMap fun p =>
    [⟨p.1+offset,p.2+offset,1,0,0,5*(cellUpper label p.1 p.2 : Int),true⟩,
     ⟨p.1+offset,p.2+offset,-1,0,0,-5*(cellLower label p.1 p.2 : Int),true⟩]
  let forms := terms.flatMap fun t =>
    let i := t.1
    let j := t.2.1
    let atom := termAtom label i j
    let constant : IntegerRow :=
      ⟨i+offset,j+offset,0,squareColumn (i+offset) (j+offset),-1,
        -5*(bits atom 35 32 : Int)*32768,false⟩
    constant :: (oldPointIndices atom).flatMap fun p =>
      anchorRows offset i j (pointPosition p) (pointValue p)
        (tightLower label i j) (tightUpper label i j)
  geometry ++ forms

def extraRows (left right count word : Nat) : List IntegerRow :=
  (List.range count).flatMap fun k =>
    let atom := bits word (15*k) 15
    let offset := bits atom 0 1
    let i := bits atom 1 3
    let j := bits atom 4 3
    let packet := (catalog[bits atom 7 8]?).getD 0
    let p := bits packet 0 20
    let value := bits packet 20 96
    let label := if offset = 0 then left else right
    anchorRows offset i j p value (min (tightLower label i j) p)
      (max (tightUpper label i j) p)

def objectiveCoeff (column : Nat) : Int :=
  if column < 8 then
    10000000000 * (([28898,86170,132798,156484,156484,132798,86170,28898]
      : List Nat).getD column 0 : Int)
  else
    let p := squareSpans.getD (column-8) (0,0)
    if p = (0,8) then 400000000
    else ((terms.filter fun t => (t.1,t.2.1) = p).map fun t => (t.2.2 : Int)).sum +
      ((terms.filter fun t => (t.1+1,t.2.1+1) = p).map fun t => (t.2.2 : Int)).sum

def primitiveBound (left right i j : Nat) : Int :=
  if i = j then 0 else
  let infinity : Int := 1000000000000000000000000000000
  let first := if i ≤ 7 ∧ j ≤ 7 then
      if i < j then 5*(cellUpper left i j : Int)
      else -5*(cellLower left j i : Int)
    else infinity
  let second := if 1 ≤ i ∧ 1 ≤ j then
      if i < j then 5*(cellUpper right (i-1) (j-1) : Int)
      else -5*(cellLower right (j-1) (i-1) : Int)
    else infinity
  let bound := min first second
  if i = j+1 then min bound (-4*32768) else bound

def floydStep (d : Array Int) (k : Nat) : Array Int :=
  ((List.range 81).map fun slot =>
    let i := slot / 9
    let j := slot % 9
    min ((d[slot]?).getD 0)
      (((d[9*i+k]?).getD 0) + ((d[9*k+j]?).getD 0))).toArray

def pairClosure (left right : Nat) : Array Int :=
  (List.range 9).foldl floydStep
    (((List.range 81).map fun slot => primitiveBound left right (slot/9) (slot%9)).toArray)

def integerCertificateLower (index : Nat) : Int :=
  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)
  let left := packet.1
  let right := packet.2.1
  let count := packet.2.2.1
  let word := packet.2.2.2.1
  let extraCount := packet.2.2.2.2.1
  let extraWord := packet.2.2.2.2.2
  let rows := frameRows left 0 ++ frameRows right 1 ++ extraRows left right extraCount extraWord
  let multipliers := (decodeMultipliers count word).map fun p =>
    let row := rows.getD p.1 default
    let lambda : Int := p.2 * (if row.geometric then 10000000000 else 1)
    (row,lambda)
  let d := pairClosure left right
  let value := multipliers.foldl (fun total p =>
    total - p.2 * p.1.bound) 0
  value + ((List.range 42).map fun column =>
    let residual := multipliers.foldl (fun total p =>
      total + p.2 * p.1.coeff column) (1000000000*objectiveCoeff column)
    let lo := if column < 8 then max (4*32768) (-((d[9*(column+1)+column]?).getD 0)) else 0
    let hi := if column < 8 then (d[9*column+column+1]?).getD 0
      else 5*10000000000*32768
    residual * (if 0 ≤ residual then lo else hi)).sum

def integerCertificateCheck (index : Nat) : Bool :=
  decide (2*805260*(5*10000000000*32768)*1000000000 ≤ integerCertificateLower index)

/- The command emits ordinary theorem declarations. Every emitted proof
is checked by the kernel; the command contributes no mathematical premise. -/
elab "prove_integer_batch " first:num " " last:num : command => do
  Lean.Elab.withEnableInfoTree false do
    for offset in List.range (last.getNat-first.getNat) do
      let index := first.getNat+offset
      let command := "theorem integer_representative_" ++ toString index ++
        " : integerCertificateCheck " ++ toString index ++
        " = true := by decide +kernel"
      let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv)
          (Lean.Name.mkSimple "command") command with
        | .ok stx => pure stx
        | .error message => Lean.throwError message
      Lean.Elab.Command.elabCommand stx
      if (← get).messages.hasErrors then
        Lean.throwError "Generated integer theorem reported an elaboration error"
      let name := Lean.Name.str (← Lean.getCurrNamespace)
        ("integer_representative_" ++ toString index)
      match ← Lean.getConstInfo name with
        | .thmInfo info =>
          if info.value.hasSorry || info.type.hasSorry then
            Lean.throwError "Generated integer theorem failed; refusing a recovery placeholder"
        | _ => Lean.throwError "Generated integer theorem was not installed"
      if index % 64 = 0 then
        Lean.Elab.Command.liftIO <| IO.eprintln s!"Kernel-checked integer representative {index}/1224"

elab "combine_integer_representatives" : command => do
  Lean.Elab.withEnableInfoTree false do
    let cases := (List.range 1224).map fun index =>
      "  | " ++ toString index ++ " => exact integer_representative_" ++ toString index
    let command := "theorem all_integer_representatives (index : Nat) (hi : index < 1224) :\n" ++
      "    integerCertificateCheck index = true := by\n  match index with\n" ++
      String.intercalate "\n" cases ++ "\n  | n + 1224 => omega"
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv)
        (Lean.Name.mkSimple "command") command with
      | .ok stx => pure stx
      | .error message => Lean.throwError message
    Lean.Elab.Command.elabCommand stx
    if (← get).messages.hasErrors then
      Lean.throwError "Combined integer theorem reported an elaboration error"
    let name := Lean.Name.str (← Lean.getCurrNamespace) "all_integer_representatives"
    match ← Lean.getConstInfo name with
      | .thmInfo info =>
        if info.value.hasSorry || info.type.hasSorry then
          Lean.throwError "Combined integer theorem failed; refusing a recovery placeholder"
      | _ => Lean.throwError "Combined integer theorem was not installed"
    Lean.Elab.Command.liftIO <| IO.eprintln "Kernel-checked all 1224 integer representatives"

__GENERATED_BATCH_CALLS__
combine_integer_representatives
'''



ORIGINAL_TERMS = ast.literal_eval(re.search(r"def terms.*?:=\s*(\[.*?\])", NUMERIC_CODE, re.S).group(1))
COLUMN_SPANS = list(dict.fromkeys((i+offset,j+offset)
    for offset in (0,1) for i,j,_ in ORIGINAL_TERMS)) + [(0,8)]
assert len(COLUMN_SPANS) == 34 and len(set(COLUMN_SPANS)) == 34
assert COLUMN_SPANS[26:] == [(1,8),(2,8),(3,8),(4,8),(5,7),(5,8),(7,8),(0,8)]
assert set(COLUMN_SPANS) == ({(i,j) for i,j,_ in ORIGINAL_TERMS} |
    {(i+1,j+1) for i,j,_ in ORIGINAL_TERMS} | {(0,8)})
NUMERIC_CODE = NUMERIC_CODE.replace("__GENERATED_COLUMN_SPANS__",
    "[" + ",".join(f"({i},{j})" for i,j in COLUMN_SPANS) + "]")
NUMERIC_CODE = NUMERIC_CODE.replace("__GENERATED_BATCH_CALLS__", "\n".join(
    f"prove_integer_batch {first} {min(first+16,1224)}" for first in range(0,1224,16)))



def verify_integer_reconstruction(representatives, records, cells, point_words, catalogs, top, dictionary):
    """Check every reconstructed integer row/column against the frozen lower.

    This is a finite diagnostic, not a replacement for kernel soundness.
    It independently evaluates the exact transparent Lean arithmetic shapes.
    """
    spans = [(i,i+1) for i in range(7)] + ast.literal_eval(
        re.search(r"def longSpans.*?:=\s*(\[.*?\])", NUMERIC_CODE, re.S).group(1))
    index = {span:8+i for i,span in enumerate(COLUMN_SPANS)}
    terms_index = {(i,j):n for n,(i,j,_) in enumerate(ORIGINAL_TERMS)}
    scale = 5*10**10*32768
    def bits(x,p,w): return (x>>p)&((1<<w)-1)
    def bound(label,i,j,side):
        if label>=241:i,j=7-j,7-i
        slot=2*i if j==i+1 else 14+2*(i*(13-i)//2+j-i-2)
        return bits(cells[label%241][0],22*(slot+side),22)
    def atom(label,i,j):
        if label>=241:i,j=7-j,7-i
        return bits(cells[label%241][1],67*terms_index[i,j],67)
    def tight(label,i,j):
        return (max(bound(label,i,j,0),sum(bound(label,t,t+1,0) for t in range(i,j))),
                min(bound(label,i,j,1),sum(bound(label,t,t+1,1) for t in range(i,j))))
    def anchor(offset,i,j,p,value,L,U):
        V=bits(value,0,32);dm=bits(value,32,32)-2*10**9;dp=2*10**9-bits(value,64,32)
        return [(i+offset,j+offset,10*dm,index[i+offset,j+offset],-1,
                 -5*V*32768+50*dp*p-50*(dp-dm)*L,False),
                (i+offset,j+offset,10*dp,index[i+offset,j+offset],-1,
                 -5*V*32768+50*dm*p-50*(dm-dp)*U,False)]
    def frame(label,offset):
        rows=[]
        for i,j in spans:
            rows.extend([(i+offset,j+offset,1,0,0,5*bound(label,i,j,1),True),
                         (i+offset,j+offset,-1,0,0,-5*bound(label,i,j,0),True)])
        for i,j,_ in ORIGINAL_TERMS:
            a=atom(label,i,j);kind=bits(a,0,2);mix=bits(a,2,11)
            p,r=bits(a,13,11),bits(a,24,11)
            pts=([p] if kind==1 else [p] if kind==2 and mix>0 else
                 ([p] if mix<1024 else [])+([r] if mix>0 else []) if kind==3 else [])
            rows.append((i+offset,j+offset,0,index[i+offset,j+offset],-1,
                         -5*bits(a,35,32)*32768,False))
            L,U=tight(label,i,j)
            for point in pts:
                packet=point_words[point]
                rows.extend(anchor(offset,i,j,bits(packet,0,20),bits(packet,20,96),L,U))
        return rows
    frames={(label,offset):frame(label,offset) for label in range(482) for offset in (0,1)}
    weights={span:0 for span in COLUMN_SPANS}
    for off in (0,1):
        for i,j,a in ORIGINAL_TERMS:weights[i+off,j+off]+=a
    weights[0,8]=4*10**8
    objective=[10**10*x for x in [28898,86170,132798,156484,156484,132798,86170,28898]]
    objective += [weights[span] for span in COLUMN_SPANS]
    assert len(objective)==42 and all(x>0 for x in objective)
    for item,rec in zip(representatives,records):
        left,right,count,word,extra_count,extra_word=rec
        rows=frames[left,0]+frames[right,1]
        for k in range(extra_count):
            a=bits(extra_word,15*k,15);off=bits(a,0,1);i,j=bits(a,1,3),bits(a,4,3)
            packet=catalogs[bits(a,7,8)];point,value=bits(packet,0,20),bits(packet,20,96)
            L,U=tight(left if off==0 else right,i,j)
            rows += anchor(off,i,j,point,value,min(L,point),max(U,point))
        for i,j,slope,col,z,b,geom in rows:
            assert 0<=i<j<=8 and (z==0 or 8<=col<42)
        inf=10**30
        d=[[0 if i==j else min(
            (5*bound(left,i,j,1) if i<j else -5*bound(left,j,i,0)) if i<=7 and j<=7 else inf,
            (5*bound(right,i-1,j-1,1) if i<j else -5*bound(right,j-1,i-1,0)) if i>=1 and j>=1 else inf)
            for j in range(9)] for i in range(9)]
        for i in range(1,9):d[i][i-1]=min(d[i][i-1],-4*32768)
        for k in range(9):d=[[min(d[i][j],d[i][k]+d[k][j]) for j in range(9)] for i in range(9)]
        lo=[max(4*32768,-d[i+1][i]) for i in range(8)]+[0]*34
        hi=[d[i][i+1] for i in range(8)]+[scale]*34
        assert all(a<=b for a,b in zip(lo,hi))
        res=[10**9*x for x in objective];value=0
        for _ in range(count):
            code=word&63;word>>=6
            if code<63:lam=top[code]
            else:lam=dictionary[word&16383];word>>=14
            row=word&511;word>>=9
            assert row<len(rows)
            i,j,slope,col,z,b,geom=rows[row]
            lam*=10**10 if geom else 1
            value-=lam*b
            for c in range(i,j):res[c]+=lam*slope
            if z:res[col]+=lam*z
        assert word==0
        value+=sum(r*(a if r>=0 else b) for r,a,b in zip(res,lo,hi))
        lower=Fraction(value,2*10**8*scale*10**9)
        assert lower==Fraction(item['lower'])>=Fraction(805260,10**8), (left,right,lower,item['lower'])
    return {'integer_representatives_exactly_match_frozen_lower':len(records),
            'all_rows_have_valid_columns':True,'column_spans':COLUMN_SPANS}


def generate():
    raw = canonical(INPUT.read_bytes())
    assert hashlib.sha256(raw).hexdigest() == INPUT_SHA
    data = json.loads(raw)
    assert data["target_numerator"] == 805260 and len(data["pairs"]) == 2399
    bypair = {(p["left"], p["right"]): p for p in data["pairs"]}
    assert len(bypair) == 2399
    representatives = []
    fixed = 0
    for pair, item in bypair.items():
        mirror = (reflected(pair[1]), reflected(pair[0]))
        assert mirror in bypair
        assert (reflected(mirror[1]), reflected(mirror[0])) == pair
        assert Fraction(item["lower"]) >= Fraction(805260, 10**8)
        assert Fraction(bypair[mirror]["lower"]) >= Fraction(805260, 10**8)
        if pair <= mirror:
            representatives.append(item)
        fixed += pair == mirror
    assert len(representatives) == 1224 and fixed == 49
    representative_index = {
        (p["left"], p["right"]): i for i, p in enumerate(representatives)}
    orbits = []
    for pair in bypair:
        mirror = (reflected(pair[1]), reflected(pair[0]))
        key = min(pair, mirror)
        orbits.append(2 * representative_index[key] + int(pair != key))
    numerators = []
    for item in representatives:
        for row, value in item["dual_sparse"]:
            number = Fraction(value) * 10**9
            assert number.denominator == 1 and number > 0 and 0 <= row < 512
            numerators.append(number.numerator)
    dictionary = sorted(set(numerators))
    assert len(dictionary) < 16384 and max(dictionary) < 1 << 58
    indices = {x: i for i, x in enumerate(dictionary)}
    top = [x for x, _ in Counter(numerators).most_common(63)]
    top_index = {x: i for i, x in enumerate(top)}
    chunks = [pack(dictionary[i:i+64], 58) for i in range(0, len(dictionary), 64)]
    catalog = data["point_catalog"]
    point_index = {p: i for i, (p, _, _) in enumerate(catalog)}
    assert len(catalog) == len(point_index) == 237
    catalogs = [p + (pack_value << 20) + (list_id << 116)
                for p, pack_value, list_id in catalog]
    assert all(0 <= p < 1 << 20 and 0 <= v < 1 << 96 and 0 <= j < 512
               for p, v, j in catalog)
    points = {0: 0}
    for cell in data["captured_cells"]:
        for atom in cell["atoms"]:
            for point, value in [(atom[2], atom[8]), (atom[3], atom[9])]:
                assert point not in points or points[point] == value
                points[point] = value
    for point, value, _ in catalog:
        assert point not in points or points[point] == value
        points[point] = value
    point_values = sorted(points)
    point_indices = {p: i for i, p in enumerate(point_values)}
    assert len(points) == 1089 and len(points) < 2048
    point_words = [p + (points[p] << 20) for p in point_values]
    point_chunks = [pack(point_words[i:i+64], 116)
                    for i in range(0, len(point_words), 64)]
    cells = []
    for cell in data["captured_cells"]:
        geometry = cell["gap_bounds"] + cell["span_bounds"]
        geometry_word = pack(geometry, 22)
        assert unpack(geometry_word, 56, 22) == geometry
        atom_words = []
        for k, m, p, r, L, U, l0, lb, pp, rp in cell["atoms"]:
            assert 0 <= k < 4 and 0 <= m < 2048 and 0 <= p < 1 << 20
            assert 0 <= r < 1 << 20 and 0 <= lb < 1 << 32
            atom_words.append(k + (m << 2) + (point_indices[p] << 13)
                              + (point_indices[r] << 24) + (lb << 35))
        cells.append((geometry_word, pack(atom_words, 67)))
    records = []
    for item in representatives:
        stream, shift, decoded = 0, 0, []
        for row, value in item["dual_sparse"]:
            number = int(Fraction(value) * 10**9)
            code = top_index.get(number, 63)
            stream |= code << shift
            shift += 6
            if code == 63:
                stream |= indices[number] << shift
                shift += 14
            stream |= row << shift
            shift += 9
        remaining = stream
        for _ in item["dual_sparse"]:
            code, remaining = remaining & 63, remaining >> 6
            if code == 63:
                index, remaining = remaining & 16383, remaining >> 14
                number = dictionary[index]
            else:
                number = top[code]
            row, remaining = remaining & 511, remaining >> 9
            decoded.append([row, Fraction(number, 10**9)])
        assert remaining == 0 and decoded == [
            [row, Fraction(value)] for row, value in item["dual_sparse"]]
        extras = []
        for e in item["extra_points"]:
            i, j = e["span"]
            extras.append(e["offset"] + (i << 1) + (j << 4)
                          + (point_index[e["point"]] << 7))
            assert e["offset"] in (0, 1) and 0 <= i < 8 and 0 <= j < 8
        extra_word = pack(extras, 15)
        assert unpack(extra_word, len(extras), 15) == extras
        records.append((item["left"], item["right"], len(decoded), stream,
                        len(extras), extra_word))
    numeric_contract = verify_integer_reconstruction(
        representatives,records,cells,point_words,catalogs,top,dictionary)
    lines = [
        "import Lean", "", "/- Generated losslessly from the fixed c260 JSON.",
        f"Input canonical LF SHA256: {INPUT_SHA}",
        "No computational fact or continuous assertion is imported as an axiom. -/",
        "", "namespace RHWeil.RecordSubmission.FiniteCertificateData", "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0", "set_option stderrAsMessages false", "set_option Elab.async false", "",
        "def digit64 (c : Char) : Nat :=",
        "  let n := c.toNat",
        "  if 65 ≤ n ∧ n ≤ 90 then n - 65",
        "  else if 97 ≤ n ∧ n ≤ 122 then n - 71",
        "  else if 48 ≤ n ∧ n ≤ 57 then n + 4",
        "  else if n = 43 then 62 else if n = 47 then 63 else 0",
        "", "def decode64 (s : String) : Nat :=",
        "  s.toList.foldl (fun n c => n * 64 + digit64 c) 0", "",
        "/- This notation produces only an ordinary Nat numeral syntax node.",
        "Soundness uses checks of that numeral, not trust in this decoder. -/",
        "macro \"n64% \" s:str : term => do",
        "  let n := decode64 s.getString",
        "  return Lean.Syntax.mkNumLit (toString n)", "",
        "def geometryWidth : Nat := 22", "",
        "def bits (word offset width : Nat) : Nat :=",
        "  (word >>> offset) &&& ((1 <<< width) - 1)", "",
        "def lambdaChunks : Array Nat := #["]
    lines += [f"  {literal(x)}," for x in chunks]
    lines += ["]", "", "def pointChunks : Array Nat := #["]
    lines += [f"  {literal(x)}," for x in point_chunks]
    lines += ["]", "", "def pointPacket (index : Nat) : Nat :=",
        "  bits ((pointChunks[index / 64]?).getD 0) ((index % 64) * 116) 116",
        "", "def pointPosition (index : Nat) : Nat := bits (pointPacket index) 0 20",
        "def pointValue (index : Nat) : Nat := bits (pointPacket index) 20 96",
        "", f"def topMultipliers : Nat := {literal(pack(top, 58))}", "",
        "def multiplier (index : Nat) : Nat :=",
        "  bits ((lambdaChunks[index / 64]?).getD 0) ((index % 64) * 58) 58",
        "", "def catalog : Array Nat := #["]
    lines += [f"  {literal(x)}," for x in catalogs]
    lines += ["]", "", "def cells : Array (Nat × Nat) := #["]
    lines += [f"  ({literal(g)}, {literal(a)})," for g, a in cells]
    lines += ["]", "", "def pairPacks : Array (Nat × Nat × Nat × Nat × Nat × Nat) := #["]
    lines += [f"  ({a}, {b}, {n}, {literal(s)}, {k}, {literal(e)}),"
              for a, b, n, s, k, e in records]
    lines += ["]", ""]
    lines += packed_lookup("representativeLabel", [a + (b << 9) for a, b, *_ in records], 18)
    labels = [a + (b << 9) for a, b in bypair]
    lines += packed_lookup("pairLabelAt", labels, 18)
    lines += packed_lookup("orbitIndexAt", orbits, 12)
    lines += ["", "def reflectionLabel (i : Nat) : Nat :=",
        "  if i < 241 then i + 241 else i - 241", "",
        "theorem reflectionLabel_involution {i : Nat} (hi : i < 482) :",
        "    reflectionLabel (reflectionLabel i) = i := by",
        "  unfold reflectionLabel",
        "  split <;> split <;> omega", "",
        "def pairLabel (left right : Nat) : Nat := left + (right <<< 9)", "",
        "def reflectedPair (label : Nat) : Nat :=",
        "  pairLabel (reflectionLabel (bits label 9 9))",
        "    (reflectionLabel (bits label 0 9))", "",
        "def orbitCheck (index : Nat) : Bool :=",
        "  let code := orbitIndexAt index",
        "  let base := representativeLabel (code / 2)",
        "  let actual := pairLabelAt index",
        "  decide (code / 2 < 1224) &&",
        "    (actual == if code % 2 = 0 then base else reflectedPair base)", "",
        "def fixedRepresentativeCheck (index : Nat) : Bool :=",
        "  representativeLabel index == reflectedPair (representativeLabel index)", "",
        "def orbitBlockCheck (block : Nat) : Bool :=",
        "  (List.range 32).all fun offset =>",
        "    let index := 32 * block + offset",
        "    if index < 2399 then orbitCheck index else true", ""]
    for block in range(75):
        lines += [f"theorem orbit_block_{block} : orbitBlockCheck {block} = true := by",
                  "  decide +kernel", ""]
    lines += ["theorem orbit_block_checked (block : Nat) (hb : block < 75) :",
        "    orbitBlockCheck block = true := by", "  match block with"]
    lines += [f"  | {block} => exact orbit_block_{block}" for block in range(75)]
    lines += ["  | n + 75 => omega", "",
        "theorem orbit_coverage (index : Nat) (hi : index < 2399) :",
        "    orbitCheck index = true := by",
        "  have hb : index / 32 < 75 := by omega",
        "  have hp := orbit_block_checked (index / 32) hb",
        "  have hm : index % 32 ∈ List.range 32 :=",
        "    List.mem_range.mpr (Nat.mod_lt _ (by decide))",
        "  have ht := (List.all_eq_true.mp hp) (index % 32) hm",
        "  have he : 32 * (index / 32) + index % 32 = index := by omega",
        "  simpa only [he, if_pos hi] using ht", "",
        "def fixedBlockCount (block : Nat) : Nat :=",
        "  ((List.range 32).filter fun offset =>",
        "    let index := 32 * block + offset",
        "    index < 1224 && fixedRepresentativeCheck index).length", ""]
    block_counts = []
    for block in range(39):
        count = sum((reflected(records[i][1]), reflected(records[i][0])) == records[i][:2]
                    for i in range(32 * block, min(32 * (block + 1), 1224)))
        block_counts.append(count)
        lines += [f"theorem fixed_block_{block} : fixedBlockCount {block} = {count} := by",
                  "  decide +kernel", ""]
    assert sum(block_counts) == 49
    lines += ["def fixedRepresentativesCount : Nat :=",
        "  " + " + ".join(f"fixedBlockCount {block}" for block in range(39)), "",
        "theorem fixed_representatives_count : fixedRepresentativesCount = 49 := by",
        "  unfold fixedRepresentativesCount",
        "  rw [" + ", ".join(f"fixed_block_{block}" for block in range(39)) + "]",
        "",
        "def decodeMultipliers : Nat → Nat → List (Nat × Nat)",
        "  | 0, _ => []",
        "  | n + 1, word =>",
        "      let code := bits word 0 6",
        "      let number := if code < 63 then bits topMultipliers (code * 58) 58",
        "        else multiplier (bits word 6 14)",
        "      let skip := if code < 63 then 6 else 20",
        "      let row := bits word skip 9",
        "      (row, number) :: decodeMultipliers n (word >>> (skip + 9))", "",
        "theorem cells_size : cells.size = 241 := by decide +kernel",
        "theorem catalog_size : catalog.size = 237 := by decide +kernel",
        "theorem representative_size : pairPacks.size = 1224 := by decide +kernel",
        ""]
    lines += [
        "noncomputable def representativePacketCheck (index : Nat) : Bool :=",
        "  let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)",
        "  decide (packet.1 < 482 ∧ packet.2.1 < 482 ∧",
        "    representativeLabel index = pairLabel packet.1 packet.2.1)", "",
        "noncomputable def representativePacketBlock (block : Nat) : Bool :=",
        "  (List.range 32).all fun offset =>",
        "    let index := 32*block+offset",
        "    if index < 1224 then representativePacketCheck index else true", ""]
    for block in range(39):
        lines += [f"theorem representative_packet_block_{block} :",
                  f"    representativePacketBlock {block} = true := by decide +kernel", ""]
    lines += ["theorem representative_packet_block_checked (block : Nat) (hb : block < 39) :",
        "    representativePacketBlock block = true := by", "  match block with"]
    lines += [f"  | {b} => exact representative_packet_block_{b}" for b in range(39)]
    lines += ["  | n + 39 => omega", "",
        "theorem representative_packet_checked (index : Nat) (hi : index < 1224) :",
        "    representativePacketCheck index = true := by",
        "  have hp := representative_packet_block_checked (index/32) (by omega)",
        "  have hm : index%32 ∈ List.range 32 := List.mem_range.mpr (Nat.mod_lt _ (by decide))",
        "  have ht := (List.all_eq_true.mp hp) (index%32) hm",
        "  have he : 32*(index/32)+index%32=index := by omega",
        "  simpa only [he,if_pos hi] using ht", "",
        "theorem representative_packet_shape (index : Nat) (hi : index < 1224) :",
        "    let packet := (pairPacks[index]?).getD (0,0,0,0,0,0)",
        "    packet.1 < 482 ∧ packet.2.1 < 482 ∧",
        "      representativeLabel index = pairLabel packet.1 packet.2.1 := by",
        "  exact of_decide_eq_true (representative_packet_checked index hi)", ""]
    lines += NUMERIC_CODE.strip().splitlines()
    lines += ["", "end RHWeil.RecordSubmission.FiniteCertificateData", ""]
    # Kernel reduction still uses transparent bodies. Pure data/checker code
    # has no runtime role; avoid retaining unnecessary compiled table artifacts.
    lines = [re.sub(r"^def (?!digit64\b|decode64\b)", "noncomputable def ", line)
             for line in lines]
    result = "\n".join(lines).encode("utf-8")
    return result, {"bytes": len(result), "lines": len(lines)-1,
        "sha256": hashlib.sha256(result).hexdigest(),
        "multipliers": len(numerators), "dictionary": len(dictionary),
        "catalog": len(catalog), "cells": len(cells),
        "representatives": len(records), "all_pairs": len(labels),
        "fixed_orbits": fixed, "numeric_contract":numeric_contract}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content, report = generate()
    if args.write:
        OUTPUT.write_bytes(content)
    else:
        assert canonical(OUTPUT.read_bytes()) == content
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
