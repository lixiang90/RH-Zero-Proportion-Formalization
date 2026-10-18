"""Read fixed Lean text and compare interfaces; never elaborate or decode leaves."""
from pathlib import Path
from fractions import Fraction as F
import ast, hashlib, json, re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SOURCE=HERE/'snapshot/Solution.lean'
OLD=ROOT/'GramDefect20261015/Core.lean'

def sha(b):return hashlib.sha256(b).hexdigest()

def comments_masked(text):
    out=list(text);i=depth=0;string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):out[i:i+2]='  ';depth+=1;i+=2;continue
            if text.startswith('-/',i):out[i:i+2]='  ';depth-=1;i+=2;continue
            if text[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if text[i]=='\\':i+=2;continue
            if text[i]=='"':string=False
            i+=1;continue
        if text[i]=='"':string=True;i+=1;continue
        if text.startswith('/-',i):out[i:i+2]='  ';depth=1;i+=2;continue
        if text.startswith('--',i):
            while i<len(text)and text[i]!='\n':out[i]=' ';i+=1
            continue
        i+=1
    assert not depth and not string
    return ''.join(out)

DECL=re.compile(r'^(?:(?:noncomputable|private|protected|partial|unsafe|meta)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive)\s+([\w\u0080-\uffff.\']+)',re.M)
BOUND=re.compile(r'^(?:(?:noncomputable|private|protected|partial|unsafe|meta)\s+)*(?:def|abbrev|theorem|lemma|structure|inductive|namespace|end|section|noncomputable section|open|set_option|#print)\b',re.M)

def decl(text,name,after=0):
    masked=comments_masked(text)
    hits=[m for m in DECL.finditer(masked)if m.group(1)==name and m.start()>=after]
    assert hits,name
    m=hits[0];n=BOUND.search(masked,m.end());end=n.start()if n else len(text)
    raw=text[m.start():end].rstrip()
    norm=re.sub(r'\bnoncomputable\s+(?=def\b)','',comments_masked(raw))
    norm=re.sub(r'\s+','',norm)
    return {'name':name,'line':text.count('\n',0,m.start())+1,
            'bytes':len(raw.encode()),'text_sha256':sha(raw.encode()),
            'normalized_sha256':sha(norm.encode())},raw

def list_literal(text,name):
    m=re.search(r'^(?:noncomputable\s+)?def '+re.escape(name)+r'\s*:[^\n]*:=\s*(\[[^\n]*\])',text,re.M)
    assert m,name
    return ast.literal_eval(m.group(1))

def main():
    raw=SOURCE.read_bytes();text=raw.decode('utf-8');old=OLD.read_text(encoding='utf-8')
    assert sha(raw)=='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
    cm=comments_masked(text)
    coeff_text=decl(text,'cAMn')[1]
    coeff={int(j):int(v)for j,v in re.findall(r'\| (\d+) => (-?\d+)',coeff_text)}
    assert list(coeff)==list(range(13))
    oldcoeff={int(j):int(v)for j,v in re.findall(r'\| (\d+) => (-?\d+)',decl(old,'cAMn')[1])}
    cN=int(re.search(r'def cN\s*:\s*ℕ\s*:=\s*(\d+)',text).group(1))
    SA=int(re.search(r'def SA\s*:\s*ℕ\s*:=\s*(\d+)',text).group(1))
    bs=list_literal(text,'BS');ts=list_literal(text,'TS');pr=list_literal(text,'PR')
    H=F(6721290091768038344368273523390880473594,10**40)
    B=F(sum(bs),SA);c=F(cN,SA)
    R=F(3337839448633819172184136761695440236797,
        4955319193847235264050000000000000000000)
    assert (H-B)/(1-c)==R and len(bs)==8 and len(pr)==28 and len(ts)==34
    atext=decl(text,'aW9')[1]
    a={}
    for i,j,v,den in re.findall(r'\| (\d+), (\d+) => \((\d+) : ℝ\) / (\d+)',atext):
        a[int(i),int(j)]=F(int(v),int(den))
    assert len(a)==36
    weights={(i,j):F(v,SA)for i,j,v,_ in ts}
    assert all(a[i,j]==weights.get((i,j),0)for i,j in a)
    assert all(a[i,j]==a[8-j,8-i]for i,j in a)
    assert bs==bs[::-1]

    interfaces=[]
    for name in ['Cl','InCell','CovBy','Fg','Pg','MulOKg','mcheckGX','mcheckGX_sound',
                 'TVal','mtermTI','cuB','rootCl','cert_of']:
        nd,nraw=decl(text,name);od,oraw=decl(old,name)
        interfaces.append({'name':name,'new':nd,'old':od,
            'same_syntax_after_comments_whitespace_and_def_noncomputable_removed':
            nd['normalized_sha256']==od['normalized_sha256']})
    names=['cAMn','cAM','ωAM','vAM','KfunAM','kfunAM','wfunAM','HW','HW_ge',
           'mleafP','mleafP_ok','walk','walkCut','walkCutR','CutsOk',
           'covered_of_walk','covered_of_walkCutR','ready_cover_cursor','cert',
           'PC9QB6M_G_rev','PC9QB6M_cert_full','aW9','bW9','W9','W9_B','W9_adm',
           'Fw_W9','cert_AM','matching_defect_bound_n']
    selected=[]
    for name in names:
        row,_=decl(text,name);selected.append(row)
    pack_calls=re.findall(r'\bzfNat64\s+(\d+)\s+"([A-Za-z0-9+_]*)"',cm)
    # This counts source literals only. Payload values and tree nodes are not decoded.
    assert all(int(n)<=65536 for n,_ in pack_calls)
    wd=re.findall(r'^(?:noncomputable\s+)?def WD(\d+)\b',cm,re.M)
    root_cursors=re.findall(r'^theorem ready(\d+)_parent_cursor\b',cm,re.M)
    chunk_cursors=re.findall(r'^theorem ready\d+_\d+_cursor\b',cm,re.M)
    inventory={
      'scope':'Static text/constant/interface extraction; no Lean, kernel, optimizer or leaf decoding.',
      'source':{'path':SOURCE.relative_to(ROOT).as_posix(),'bytes':len(raw),'sha256':sha(raw),
                'lines':len(text.splitlines()),'website_2MB_headroom_bytes':2_000_000-len(raw)},
      'profile':{'name_from_attribution':'s1R','coefficient_denominator':10**9,
                 'cAMn':coeff,'omega0':'sqrt(2)','omega_j_positive':'2*pi*j',
                 'terms':13,'normalization':'KfunAM(0)',
                 'actual_kernel':'(integral[-1/2,1/2] vAM(t)*cos(2*pi*x*t)dt / KfunAM(0))^2',
                 'same_as_old_Core_profile':coeff==oldcoeff},
      'exact_constants':{'H_certified_lower':str(H),'B':str(B),'c9':str(c),'cN':cN,'SA':SA,
                         'record_R':str(R),'identity':'R=(H-B)/(1-c9)'},
      'ledger':{'points':9,'gaps':8,'BS_numerators':bs,'denominator':SA,
                'positive_TS':ts,'a_upper':[[i,j,str(a[i,j])]for i,j in sorted(a)],
                'positive_edges':len(ts),'pressure_reflection_exact':True,
                'pair_reflection_exact':True,'PR':pr},
      'finite_source_inventory':{'WD_definitions':len(wd),'WD_ids':list(map(int,wd)),
        'parent_cursor_theorems':len(root_cursors),'nested_cursor_theorems':len(chunk_cursors),
        'packed_numeral_source_occurrences':len(pack_calls),
        'declared_packed_bit_sum':sum(int(n)for n,_ in pack_calls),
        'payload_ascii_characters':sum(len(s)for _,s in pack_calls),
        'reported_leaf_count':13046,'leaf_count_locally_confirmed':False,
        'leaf_count_status':'Reported by task/site; no literal 13046 in source and payload decoding prohibited.'},
      'interfaces':interfaces,'selected_declarations':selected,
      'forbidden_code_token_scan':{n:len(re.findall(r'\b'+n+r'\b',cm))for n in ['sorry','axiom','native_decide','unsafe']},
      'raw_source_preserved':True,'Lean_invocations':0,'local_replay_passed':False,
      'leaf_payload_decoded':False,'new_floor_or_proportion_proven':False,
      'old_Core':{'path':OLD.relative_to(ROOT).as_posix(),'sha256':sha(OLD.read_bytes())},
      'extractor_sha256':sha(Path(__file__).read_bytes()),
    }
    out=HERE/'static-inventory.json'
    with out.open('x',encoding='utf-8',newline='\n')as f:
        json.dump(inventory,f,ensure_ascii=False,indent=2);f.write('\n')
    print(json.dumps({'path':out.relative_to(ROOT).as_posix(),'sha256':sha(out.read_bytes()),
                      'exact_constants':inventory['exact_constants'],
                      'finite_source_inventory':inventory['finite_source_inventory'],
                      'interface_same':{x['name']:x['same_syntax_after_comments_whitespace_and_def_noncomputable_removed']for x in interfaces}},ensure_ascii=False))

if __name__=='__main__':main()
