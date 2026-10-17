"""Lossless semantic delta streams with shared canonical Huffman dictionaries.

This changes no mathematical witness. The exact printable Lean data bytes
are counted separately from the unchanged analytic base and the reserved
future decoder/checkpoint expander. No Lean proof is asserted.
"""
from pathlib import Path
import collections, hashlib, heapq, json, struct, time

HERE=Path(__file__).resolve().parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
ABC=''.join(chr(i)for i in range(33,127)if i not in(34,92))

def b92(n):
    out=[]
    while n:n,r=divmod(n,92);out.append(ABC[r])
    return ''.join(reversed(out))or'!'

def huffman(values,alphabet):
    counts=collections.Counter(values);heap=[];serial=0
    for symbol,count in sorted(counts.items()):
        assert 0<=symbol<alphabet
        heapq.heappush(heap,(count,serial,symbol));serial+=1
    lengths=[0]*alphabet
    if not heap:return bytes(lengths),b'',0
    if len(heap)==1:lengths[heap[0][2]]=1
    else:
        while len(heap)>1:
            a=heapq.heappop(heap);b=heapq.heappop(heap)
            heapq.heappush(heap,(a[0]+b[0],serial,(a[2],b[2])));serial+=1
        def visit(node,depth):
            if isinstance(node,int):lengths[node]=depth
            else:visit(node[0],depth+1);visit(node[1],depth+1)
        visit(heap[0][2],0)
    assert max(lengths)<256
    code=prev=0;codes={}
    for length,symbol in sorted((length,symbol)for symbol,length in enumerate(lengths)if length):
        code<<=length-prev;codes[symbol]=(code,length);code+=1;prev=length
    out=bytearray();word=bits=total=0
    for symbol in values:
        code,length=codes[symbol];word=(word<<length)|code;bits+=length;total+=length
        while bits>=8:
            bits-=8;out.append((word>>bits)&255)
        word&=(1<<bits)-1
    if bits:out.append(word<<(8-bits))
    return bytes(lengths),bytes(out),total

def main():
    started=time.monotonic();meta=json.loads((HERE/'semantics.json').read_bytes())
    for r in meta['cache_files']:assert sha((HERE/r['path']).read_bytes())==r['sha256']
    for delta in [False,True]:
        channels=collections.OrderedDict()
        def channel(name,alphabet):channels[name]={'alphabet':alphabet,'values':[]}
        channel('node_kind',4);channel('axis',45)
        for n in range(4):channel('cut'+str(n),256)
        for t in range(39):channel('term'+str(t),5 if delta else 4)
        channel('mix',2047 if delta else 1024)
        for prefix in ['point','second']:
            for n in range(3):channel(prefix+str(n),256)
        for n in range(8):channel('tree'+str(n),10)
        def put(name,x):channels[name]['values'].append(x)
        def varint(prefix,value):
            n=0
            while value>=128:
                put(prefix+str(n),(value&127)|128);value>>=7;n+=1
            put(prefix+str(n),value)
        def signed(prefix,value):varint(prefix,2*value if value>=0 else -2*value-1)
        oldcut=[0]*45;oldfs=[(0,0,0,0)]*39;lastpoint=[0]*39;oldtree=[0]*8
        unchanged=active=0;nodes=(HERE/'nodes.bin').read_bytes();pos=0
        with (HERE/'fs.bin').open('rb')as f,(HERE/'treecodes.bin').open('rb')as tree:
            while pos<len(nodes):
                kind=nodes[pos];pos+=1;put('node_kind',kind)
                if kind==1:
                    axis,cut=struct.unpack_from('<BI',nodes,pos);pos+=5
                    put('axis',axis);signed('cut',cut-oldcut[axis]);oldcut[axis]=cut
                elif kind==2:put('axis',nodes[pos]);pos+=1
                elif kind==0:
                    for t in range(39):
                        k,m,p,r=struct.unpack('<BHHH',f.read(7));old=oldfs[t]
                        same=(k,m,p,r)==old;unchanged+=same
                        put('term'+str(t),0 if delta and same else k+1 if delta else k)
                        oldfs[t]=(k,m,p,r)
                        if (delta and same)or k==0:continue
                        active+=1
                        if k>=2:
                            md=m-old[1]if delta else m
                            put('mix',2*md if md>=0 else -2*md-1)if delta else put('mix',m)
                        signed('point',p-lastpoint[t]);lastpoint[t]=p
                        if k==3:signed('second',r-p)
                    code=struct.unpack('<I',tree.read(4))[0]
                    for n in range(8):
                        digit=code//(10**n)%10
                        put('tree'+str(n),(digit-oldtree[n])%10 if delta else digit)
                        oldtree[n]=digit
            assert not f.read()and not tree.read()
        binary=bytearray(b'W10H\x01'+bytes([int(delta),len(channels)]));stats=[]
        for name,ch in channels.items():
            lengths,packed,bits=huffman(ch['values'],ch['alphabet'])
            binary.extend(struct.pack('<HII',ch['alphabet'],len(ch['values']),len(packed)))
            binary.extend(lengths);binary.extend(packed)
            stats.append({'name':name,'alphabet':ch['alphabet'],'tokens':len(ch['values']),
                          'model_bytes':len(lengths),'coded_bits':bits,'coded_bytes':len(packed)})
        stem='delta-huffman'if delta else'field-huffman';binary=bytes(binary)
        (HERE/(stem+'.bin')).write_bytes(binary)
        chunks=[b92(int.from_bytes(binary[i:i+256],'little'))for i in range(0,len(binary),256)]
        source='''/- Data-size audit only: no decoder or coverage theorem is asserted. -/
namespace W10SizeAudit
def byteCount : Nat := '''+str(len(binary))+'''
def chunks : Array String := #[
'''+',\n'.join('"'+c+'"'for c in chunks)+']\nend W10SizeAudit\n'
        sr=source.encode('utf8');(HERE/(stem+'-data.lean')).write_bytes(sr)
        out={'scope':__doc__,'codec':stem,'script_sha256':sha(Path(__file__).read_bytes()),
             'semantics_sha256':sha((HERE/'semantics.json').read_bytes()),
             'numeric_leaves':95615,'all_nodes':191557,'channels':stats,'delta':delta,
             'unchanged_full_term_rows':unchanged,'encoded_active_rows':active,
             'binary_bytes':len(binary),'binary_sha256':sha(binary),'data_source_bytes':len(sr),
             'data_source_sha256':sha(sr),'source_literal_chunks':len(chunks),
             'field_alphabet_tables_are_shared':True,'roundtrip_verified':False,
             'Lean_decoder_implemented':False,'Lean_verified':False,
             'seconds':time.monotonic()-started}
        (HERE/(stem+'.json')).write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
        print(json.dumps({k:out[k]for k in ['codec','binary_bytes','data_source_bytes','unchanged_full_term_rows','encoded_active_rows','seconds']}),flush=True)

if __name__=='__main__':main()
