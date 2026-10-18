"""Fixed new-record source unpacking and structural parser (Stage A only).

No kernel evaluation, threshold change, leaf traversal, solver, or Lean.
Packed numeral expansion follows ZeroForgePackedNat.decode64 exactly and
requires the canonical inverse. All certificate literals come from SOURCE.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import ast
import itertools
import json
import os
import re
import sys
import time
import traceback

sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE = ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_SHA = 'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
ORIGINAL_CN = 893616123055294719
ALPHABET = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+_'


def encode64(n):
    if n == 0:
        return 'A'
    out = []
    while n:
        out.append(ALPHABET[n & 63]); n >>= 6
    return ''.join(reversed(out))


def decode_all(text):
    records = []
    def replace(m):
        bits, payload = int(m[1]), m[2]
        assert bits <= 65536
        assert payload and payload.isascii() and all(c in ALPHABET for c in payload)
        if bits == 0:
            assert payload == 'A'; value = 0
        else:
            assert len(payload) == (bits+5)//6
            leading = (bits-1)%6+1
            assert 1 << (leading-1) <= ALPHABET.index(payload[0]) < 1 << leading
            value = 0
            for c in payload:
                value = (value << 6)+ALPHABET.index(c)
        assert value.bit_length() == bits and encode64(value) == payload
        line = text.count('\n', 0, m.start())+1
        context = text[text.rfind('\n',0,m.start())+1:m.start()]
        name = re.search(r'def\s+(\w+)\b', context)
        records.append({'index':len(records),'line':line,
                        'definition':name[1] if name else None,
                        'bits':bits,'payload_length':len(payload),
                        'payload_sha256':sha256(payload.encode('ascii')).hexdigest(),
                        'decoded_hex_sha256':sha256(hex(value).encode('ascii')).hexdigest()})
        return hex(value)
    normalized = re.sub(r'zfNat64\s+(\d+)\s+"([A-Za-z0-9+_]*)"', replace, text)
    assert len(records) == 137, ('packing_count',len(records))
    assert len(re.findall(r'\bzfNat64\s+\d+', normalized)) == 0
    return normalized, records


def lean_expr(expr):
    tokens = re.findall(r'[()]|[^\s()]+', expr)
    pos = 0
    def parse():
        nonlocal pos
        token = tokens[pos]; pos += 1
        if token != '(':
            return token
        items = []
        while tokens[pos] != ')': items.append(parse())
        pos += 1
        assert items
        return items[0] if len(items)==1 else items
    result = parse()
    assert pos == len(tokens), ('expression_unparsed',tokens[pos:])
    return result


def dispatch_tree(expr, definitions):
    tree = lean_expr(expr)
    def evaluate(t,j):
        if isinstance(t,str):
            if t == 'j': return j
            if t.isdigit() or t.startswith('0x'): return int(t,0) if t.startswith('0x') else int(t)
            assert t in definitions, ('unknown_dispatch_atom',t)
            value = definitions[t]
            return evaluate(value,j) if isinstance(value,(str,list)) else value
        head,*args=t
        if head == 'dpk':
            assert len(args)==3
            a,b,c=[evaluate(x,j) for x in args]
            return c if a==b else 0
        if head == 'dsel':
            assert len(args)==4
            return evaluate(args[2] if evaluate(args[0],j)<evaluate(args[1],j) else args[3],j)
        assert len(args)==1 and args[0]=='j' and head in definitions, ('dispatch_call',t)
        return evaluate(definitions[head],j)
    return lambda j:evaluate(tree,j)


def point_tree(expr, definitions):
    leaves=[]
    def replace(m):
        entries=ast.literal_eval(m[2]); block=int(m[1])
        assert all(0<=a<1024 and b>=0 for a,b in entries)
        name='LEAF'+str(len(leaves)); leaves.append(('lf',block,entries));return name
    expr=re.sub(r'\.lf\s+(\d+)\s+(\[[^\]]*\])',replace,expr)
    toks=re.findall(r'\.nd|LEAF\d+|PTT_\d+|\d+|[()]',expr)
    pos=0
    def parse():
        nonlocal pos
        t=toks[pos];pos+=1
        if t=='(':
            obj=parse();assert toks[pos]==')';pos+=1;return obj
        if t.startswith('LEAF'):return leaves[int(t[4:])]
        if t.startswith('PTT_'):return definitions[t]
        assert t=='.nd', ('point_tree_token',t)
        k=int(toks[pos]);pos+=1
        return ('nd',k,parse(),parse())
    obj=parse();assert pos==len(toks)
    return obj


def point_lookup(tree,x):
    while tree[0]=='nd':tree=tree[2] if x//1024<tree[1] else tree[3]
    _,j,entries=tree
    if x//1024!=j:return 0
    return next((v for k,v in entries if k==x%1024),0)


def load_model():
    raw=SOURCE.read_bytes();assert sha256(raw).hexdigest()==SOURCE_SHA
    original=raw.decode('utf-8')
    text,packing=decode_all(original)
    start=text.index('namespace AMW.Cert.PC9QB6M\n')
    end=text.index('end AMW.Cert.PC9QB6MData',start)
    cert=text[start:end]
    def literal(name):
        found=re.findall(r'\bdef '+name+r'\s*:[^\n]*:= (\[[^\n]*\])',cert)
        assert len(found)==1,(name,len(found));return ast.literal_eval(found[0])
    def number(name):
        found=re.findall(r'\bdef '+name+r'\s*:[^\n]*:= (0x[\da-f]+|\d+)\s*$',cert,re.M)
        assert len(found)==1,(name,len(found));return int(found[0],0) if found[0].startswith('0x') else int(found[0])
    BS,TS,PR,BND=[literal(n) for n in ['BS','TS','PR','BND']]
    CN,SIG,TOP,TOPD,SA=[number(n) for n in ['cN','SIG','TOP','TOPD','SA']]
    assert CN==ORIGINAL_CN and SA==10**20
    assert len(BS)==8 and len(PR)==28 and len(TS)==34
    assert all(0<=i<j<=8 and a>0 for i,j,a,_ in TS)
    BK={int(j):int(v,16) for j,v in re.findall(r'\bdef BK_(\d+)[^\n]*:= (0x[\da-f]+)',cert)}
    BKD={int(j):int(v,16) for j,v in re.findall(r'\bdef BKD_(\d+)[^\n]*:= (0x[\da-f]+)',cert)}
    WL={}
    for r,k,v in re.findall(r'\bdef WL(\d+)_(\d+)[^\n]*:= (0x[\da-f]+|\d+)\s*$',cert,re.M):
        WL.setdefault(int(r),{})[int(k)]=int(v,0) if v.startswith('0x') else int(v)
    assert set(WL)==set(range(48))
    wd={int(a):int(b) for a,b in re.findall(r'\bdef WD(\d+) : ℕ → ℕ := rdw WL(\d+)\s*$',cert,re.M)}
    assert wd=={i:i for i in range(48)}
    # Validate all balanced dispatch functions against literal maps.
    dispatch_defs={}
    for name,value in re.findall(r'\bdef ((?:BKD?|WL\d+)(?:_\d+)?)\s*:[^\n]*:= (0x[\da-f]+|\d+)\s*$',cert,re.M):
        dispatch_defs[name]=int(value,0) if value.startswith('0x') else int(value)
    for name,expr in re.findall(r'\bdef ((?:BKD?|WL\d+)[A-Za-z0-9_]*) \(j : ℕ\) : ℕ := ([^\n]+)',cert):
        dispatch_defs[name]=lean_expr(expr)
    dispatch_checks=0
    for name,table,lim in [('BK',BK,512),('BKD',BKD,512)]+[(f'WL{r}',WL[r],max(WL[r])+2) for r in range(48)]:
        assert name in dispatch_defs,name
        fn=dispatch_tree(name,dispatch_defs)
        for j in range(lim+1):
            assert fn(j)==table.get(j,0),(name,j)
            dispatch_checks+=1
    PTraw={};duplicates=0
    for block,entries in re.findall(r'\.lf (\d+) (\[[^\]]*\])',cert):
        for off,value in ast.literal_eval(entries):
            x=1024*int(block)+off;duplicates+=x in PTraw;PTraw[x]=value
    assert duplicates==0 and PTraw
    pointdefs={}
    for name,expr in re.findall(r'\bdef (PTT(?:_\d+)?) : PTrD := ([^\n]+)',cert):
        pointdefs[name]=point_tree(expr,pointdefs)
    assert 'PTT' in pointdefs
    assert all(point_lookup(pointdefs['PTT'],x)==v for x,v in PTraw.items())
    assert 'ptGetD PTT x' in re.search(r'\bdef PT \(x : ℕ\)[^\n]+',cert)[0]
    covtxt=re.search(r'\bdef COV[^\n]*:= (\[[\s\S]*?)\nnoncomputable def SMAX',cert)[1]
    COV=ast.literal_eval(covtxt.replace('true','True').replace('false','False'))
    SMAX=ast.literal_eval(re.search(r'\bdef SMAX[^\n]*:= (\[[^\]]*\])',cert)[1])
    BAD=[[(a,b) for a,b,t in row if not t] for row in COV]
    rcM=int(re.search(r'\bdef RC[^\n]*:= rootCl 8 28 (\d+) COV',cert)[1])
    roots={}
    rootpat=(r'theorem ready(\d+)_parent_cursor : U \(walkCutR TOP BK TOPD BKD PT REG WD(\d+) '
             r'ready\d+_cuts(\d+) (\d+) (\d+)\) \(ofCl \(RC ([\d ]+)\) (\d+)\) = (\d+)')
    for a,b,cut,fuel,pos,idx,M,expected in re.findall(rootpat,cert):
        assert a==b and int(M)==0 and int(pos)==1
        roots[int(a)]={'indices':tuple(map(int,idx.split())),'cuts':int(cut),'fuel':int(fuel),'pos':int(pos),'expected':int(expected)}
    assert set(roots)==set(range(48))
    assert sorted(r['indices'] for r in roots.values())==sorted(itertools.product(*(range(len(row)) for row in BAD)))
    states={name:tuple(map(int,values.split(', '))) for name,values in
            re.findall(r'\bdef (ready\d+_\d+_state) : St := ⟨([\d, ]+)⟩',cert)}
    assert all(len(v)==73 for v in states.values())
    cursors=[]
    cursorpat=(r'theorem (ready(\d+)_(\d+))_cursor : U \(walkCut TOP BK TOPD BKD PT REG WD(\d+) '
               r'(ready\d+_cuts\d+) (\d+) (\d+)\) (ready\d+_\d+_state) = (\d+)')
    for name,r,j,wd,cuts,fuel,pos,state,endpos in re.findall(cursorpat,cert):
        assert r==wd and state==name+'_state' and state in states
        cursors.append({'name':name,'root':int(r),'index':int(j),'cuts':cuts,'fuel':int(fuel),'pos':int(pos),'state':state,'expected':int(endpos)})
    assert set(states)=={c['state'] for c in cursors}
    cutlists={}
    for r in range(48):
        assert re.search(r'\bdef ready'+str(r)+r'_cuts0 : List[^\n]*:= \[\]',cert)
        cutlists[f'ready{r}_cuts0']=[]
    for name,pos,state,endpos,prev in re.findall(r'\bdef (ready\d+_cuts\d+) : List[^\n]*:= \((\d+), (ready\d+_\d+_state), (\d+)\) :: (ready\d+_cuts\d+)',cert):
        assert prev in cutlists and state in states
        cutlists[name]=[(int(pos),state,int(endpos))]+cutlists[prev]
    for r,rec in roots.items():assert f'ready{r}_cuts{rec["cuts"]}' in cutlists
    # Capture runtime definitions for semantic review without importing old data.
    definitions={}
    for name in ['tm','splitAx','bcut','gpt','dec4F','ydec','mcheckP','mokI','pwD','coverChk','rdw','walkCut','walkCutR','cutAt']:
        pat=r'(?m)^(?:noncomputable )?def '+re.escape(name)+r'\b[\s\S]*?(?=^(?:noncomputable )?def |^theorem |^end |^namespace |\Z)'
        matches=re.findall(pat,text,re.M)
        assert len(matches)==1,(name,len(matches))
        definitions[name]=sha256(matches[0].encode('utf-8')).hexdigest()
    assert sha256(SOURCE.read_bytes()).hexdigest()==SOURCE_SHA
    return locals()


def summary(m):
    return {'source_sha256':SOURCE_SHA,'normalized_source_sha256':sha256(m['text'].encode('utf-8')).hexdigest(),
            'packing':m['packing'],'packing_count':len(m['packing']),
            'certificate_constants':{k:m[k] for k in ['CN','SIG','SA','rcM']},
            'literal_counts':{k:len(m[k]) for k in ['BS','TS','PR','BND','BK','BKD','PTraw','WL','roots','states','cursors','cutlists']},
            'dispatch_identity_checks':m['dispatch_checks'],
            'WD_identity_count':len(m['wd']),'root_records':m['roots'],
            'ready_cursors':m['cursors'],'runtime_definition_sha256':m['definitions'],
            'all_point_tree_entries_match_literal_map':True,
            'all_48_bad_interval_roots_present_once':True,
            'packing_bitlength_and_inverse_all_passed':True,
            'mathematical_leaf_checks_performed':False}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    out=HERE/'packing-parser.json';failure=HERE/'packing-parser-failure.json'
    if args.write_receipt:assert not out.exists() and not failure.exists()
    started=time.monotonic();record={'pid':os.getpid(),'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
                                    'source_sha256_start':sha256(SOURCE.read_bytes()).hexdigest(),'stage':'packing_parser_started'}
    print(json.dumps(record),flush=True)
    try:
        m=load_model();record.update(summary(m),passed=True,stage='packing_parser_complete',seconds=time.monotonic()-started)
        record['source_sha256_end']=sha256(SOURCE.read_bytes()).hexdigest()
        assert record['source_sha256_start']==record['source_sha256_end']==SOURCE_SHA
        if args.write_receipt:out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({k:record[k] for k in ['pid','passed','stage','packing_count','literal_counts','seconds']}),flush=True)
    except BaseException as exc:
        record.update(stage='packing_parser_failed',passed=False,error=repr(exc),traceback=traceback.format_exc(),seconds=time.monotonic()-started)
        if args.write_receipt:failure.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
        print(json.dumps(record),flush=True);raise


if __name__=='__main__':main()
