"""Read the frozen full W10 tree once; retain only actual witness semantics.

No search, optimization, mathematical thinning, Lean compilation, or writes
to an existing checkpoint are performed. The output cache is not a proof.
"""
from pathlib import Path
import collections, hashlib, json, re, struct, time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OLD=ROOT/'research-20261016-w10-cert'
PAIR=[(i,i+1) for i in range(9)]+[(i,j)for i in range(10)for j in range(i+2,10)]
SLOT={p:i for i,p in enumerate(PAIR)}
BB=1<<42
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def load_inputs():
    raw=(OLD/'ordered-proof-input.json').read_bytes()
    assert sha(raw)=='6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e'
    text=raw.decode(); dec=json.JSONDecoder()
    def field(name):
        m=re.search(r'"'+name+r'"\s*:\s*',text)
        return dec.raw_decode(text,m.end())[0]
    root=field('root'); branches={r['path']:r for r in field('branches')}
    terms=field('terms')
    del raw,text
    packed=(OLD/'ordered-compact.json').read_bytes()
    assert sha(packed)=='5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463'
    leaves={r['path']:r for r in json.loads(packed)['leaves']}
    return root,branches,leaves,terms

def child(state,axis,cut,upper):
    lo,hi=state;i,j=PAIR[axis]
    a,b,w=(i,j,cut)if upper else(j,i,-cut)
    def edge(x,y):return 0 if x==y else hi[SLOT[x,y]]if x<y else-lo[SLOT[y,x]]
    col=[max(0,BB+edge(x,a))for x in range(10)]
    row=[max(0,BB+w+edge(b,x))for x in range(10)]
    return ([max(v,max(0,2*BB-col[j]-row[i]))for v,(i,j)in zip(lo,PAIR)],
            [min(v,max(0,col[i]+row[j]-2*BB))for v,(i,j)in zip(hi,PAIR)])

def normal(state):
    if state[1][0]<=state[1][8]and state[0][0]<=state[0][8]:return state
    for _ in range(2):
        state=child(state,0,state[1][8],True)
        state=child(state,8,state[0][0],False)
    return state

def relative_decode(support,state,terms):
    mask=support&((1<<39)-1); tail=support>>39
    def take(n):
        nonlocal tail
        value=tail&((1<<n)-1);tail>>=n;return value
    def point(t):
        i,j,_=terms[t]; z=SLOT[i,j]
        lo=max(state[0][z],sum(state[0][i:j]));hi=min(state[1][z],sum(state[1][i:j]))
        base=(lo+31)//32;bits=max(0,hi//32-base).bit_length()
        return 32*(base+take(bits))
    result=[]
    for t in range(39):
        if not(mask>>t&1):result.append((0,0,0,0));continue
        if take(1)==0:result.append((1,0,point(t),0));continue
        kind=2+take(1);m=take(10);p=point(t);r=0
        if kind==3:
            tag=take(2);r=[max(0,p-32),p+32,max(0,p-256)][tag]if tag<3 else point(t)
        result.append((kind,m,p,r))
    assert tail==0
    return result

def canonical_record(h,path,kind,values):
    # Fixed separators and length delimiters bind every original evidence field.
    b=json.dumps([path,kind,*values],separators=(',',':')).encode()
    h.update(len(b).to_bytes(4,'little'));h.update(b)

def main():
    started=time.monotonic();root,branches,leaves,terms=load_inputs()
    assert len(branches)==95778 and len(leaves)==95779 and len(terms)==39
    canonical=hashlib.sha256();states=hashlib.sha256();kinds=collections.Counter()
    canonical_record(canonical,'r','root',[root])
    count=numeric=0; support_bits=0; max_point=0; active=collections.Counter()
    selected={};nodes=HERE/'nodes.bin';fsfile=HERE/'fs.bin';codes=HERE/'treecodes.bin'
    with nodes.open('wb')as no,fsfile.open('wb')as fo,codes.open('wb')as co:
        stack=[('r',root)]
        while stack:
            path,state=stack.pop();state=normal(state);count+=1
            states.update(struct.pack('<90I',*(state[0]+state[1])))
            if path in branches:
                r=branches[path];axis,cut=r['axis'],r['cut']
                no.write(struct.pack('<BBI',1,axis,cut))
                canonical_record(canonical,path,'branch',[axis,cut])
                if path=='r001100':selected={'path':path,'normalized_cell':state,'axis':axis,'cut':cut}
                stack.append((path+'1',child(state,axis,cut,False)))
                stack.append((path+'0',child(state,axis,cut,True)))
            else:
                r=leaves[path];kind=r['kind'];kinds[kind]+=1
                if kind=='numeric':
                    word=int(r['support_hex'],16);code=r['tree_code']
                    fs=relative_decode(word,state,terms)
                    no.write(b'\x00');co.write(struct.pack('<I',code))
                    for k,m,p,q in fs:
                        assert p%32==q%32==0
                        fo.write(struct.pack('<BHHH',k,m,p//32,q//32))
                        active[k]+=1;max_point=max(max_point,p,q)
                    canonical_record(canonical,path,'numeric',[hex(word),code])
                    support_bits+=word.bit_length();numeric+=1
                    if path in ['r0011000','r0011001']:
                        selected.setdefault('children',[]).append({'path':path,'FS':fs,'tree_code':code,
                          'normalized_cell':state,'support_hex':hex(word)})
                    if numeric%10000==0:print(json.dumps({'numeric':numeric,'seconds':time.monotonic()-started}),flush=True)
                elif kind=='reflection':
                    no.write(b'\x03');canonical_record(canonical,path,kind,[])
                else:
                    assert kind=='empty';axis=r['violation_axis']
                    no.write(bytes([2,axis]));canonical_record(canonical,path,kind,[axis])
    assert count==191557 and numeric==95615
    out={'scope':__doc__,'tree_sha256':'6f2bc79db4613b4130659c9e65e0a24ee07cc50fb0686878d01a8e3f73839c3e',
         'compact_sha256':'5fbb16de9f2b74d1816d7e251efb16c07c4f318a1aedf1a390f18ef6fe499463',
         'script_sha256':sha(Path(__file__).read_bytes()),'root':root,'terms':terms,
         'branches':len(branches),'leaves':len(leaves),'leaf_types':dict(kinds),
         'numeric':numeric,'nodes':count,'canonical_evidence_sha256':canonical.hexdigest(),
         'normalized_states_sha256':states.hexdigest(),'term_kind_counts':dict(active),
         'old_support_bits_sum':support_bits,'max_point':max_point,
         'cache_files':[{'path':p.name,'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())}for p in [nodes,fsfile,codes]],
         'seconds':time.monotonic()-started,'Lean_verified':False,'new_exclusions':0}
    (HERE/'semantics.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    (HERE/'selected-parent.json').write_text(json.dumps(selected,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:out[k]for k in ['nodes','numeric','leaf_types','term_kind_counts','seconds']}),flush=True)

if __name__=='__main__':main()
