"""Independent read-only field-Huffman decoder and full mathematical replay.

Parse the printable Lean literals, reject malformed Huffman/varint streams,
recover all semantic cache bytes, rebuild the complete ordered geometry,
derive every Pruefer dual from actual PT slopes and run every integer leaf
inequality.  No encoder/extractor import, optimizer, Lean, or new search.
Default read-only; --write-receipt writes an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction
import argparse,collections,hashlib,importlib.util,json,re,struct,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
OUT=HERE/'independent-codec-replay.json';SC=32768;BB=1<<42;MASK=(1<<32)-1
PAIR=[(i,i+1) for i in range(9)]+[(i,j) for i in range(10) for j in range(i+2,10)]
SLOT={p:k for k,p in enumerate(PAIR)}
ALPHABET=''.join(chr(c) for c in range(33,127) if c not in [34,92]);INDEX92={c:k for k,c in enumerate(ALPHABET)}
SCALE=3355443200000000000000000000;TARGET=433*(SCALE//50000)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def sub(a,b):return max(0,a-b)
def literal_bytes(path):
    text=path.read_text(encoding='utf8');count=int(re.search(r'def byteCount : Nat := (\d+)',text)[1])
    body=text.split('def chunks : Array String := #[',1)[1].split(']',1)[0]
    chunks=re.findall(r'"([^"\\]*)"',body);out=bytearray()
    # Do not split on an interior ']' inside a literal.  Find the final array
    # delimiter before end namespace, then parse the entire literal region.
    body=text.split('def chunks : Array String := #[',1)[1].rsplit(']\nend ',1)[0]
    chunks=re.findall(r'"([^"\\]*)"',body)
    for chunk in chunks:
        value=0
        for c in chunk:value=92*value+INDEX92[c]
        length=min(256,count-len(out));assert 0<length<=256 and value<256**length
        out.extend(value.to_bytes(length,'little'))
    assert len(out)==count
    return bytes(out),len(chunks)
def huffman(lengths,packed,count,coded_bits):
    assert len(packed)==(coded_bits+7)//8
    if count==0:
        assert not packed and coded_bits==0 and not any(lengths)
        return []
    table={};code=previous=0
    for length,symbol in sorted((length,symbol) for symbol,length in enumerate(lengths) if length):
        assert 1<=length<=255;code<<=length-previous;assert code<1<<length
        table[length,code]=symbol;code+=1;previous=length
    assert table
    maxlength=max(k[0] for k in table);values=[];position=0
    for _ in range(count):
        word=0;found=False
        for length in range(1,maxlength+1):
            assert position<coded_bits,'Huffman symbol truncated'
            word=2*word+((packed[position//8]>>(7-position%8))&1);position+=1
            if (length,word) in table:values.append(table[length,word]);found=True;break
        assert found,'No Huffman codeword'
    assert position==coded_bits,'Unused/noncanonical coded bits'
    if coded_bits%8:assert packed[-1]&((1<<(8-coded_bits%8))-1)==0,'Nonzero pad bits'
    return values
def channels_from(raw,metadata):
    assert raw[:5]==b'W10H\x01' and raw[5]==0 and raw[6]==60
    names=['node_kind','axis']+['cut'+str(i) for i in range(4)]+['term'+str(i) for i in range(39)]+['mix']
    names+=['point'+str(i) for i in range(3)]+['second'+str(i) for i in range(3)]+['tree'+str(i) for i in range(8)]
    assert [r['name'] for r in metadata['channels']]==names
    pos=7;channels={}
    for name,record in zip(names,metadata['channels']):
        assert pos+10<=len(raw);alphabet,count,length=struct.unpack_from('<HII',raw,pos);pos+=10
        assert alphabet==record['alphabet'] and count==record['tokens'] and length==record['coded_bytes']
        assert pos+alphabet+length<=len(raw);lengths=raw[pos:pos+alphabet];pos+=alphabet;packed=raw[pos:pos+length];pos+=length
        channels[name]=huffman(lengths,packed,count,record['coded_bits'])
    assert pos==len(raw),'Trailing bytes beyond channel framing'
    return channels
def edge(state,base,i,j):
    if i<j:return base+state[1][SLOT[i,j]]
    if i==j:return base
    return sub(base,state[0][SLOT[j,i]])
def child(state,axis,cut,upper):
    i,j=PAIR[axis];a,b=(i,j) if upper else (j,i);base=BB+cut if upper else sub(BB,cut)
    col=[edge(state,BB,x,a) for x in range(10)];row=[edge(state,base,b,x) for x in range(10)]
    return [[max(v,sub(2*BB,col[j]+row[i])) for v,(i,j) in zip(state[0],PAIR)],
        [min(v,sub(col[i]+row[j],2*BB)) for v,(i,j) in zip(state[1],PAIR)]]
def normal(state):
    if state[1][0]<=state[1][8] and state[0][0]<=state[0][8]:return state
    for _ in range(2):state=child(state,0,state[1][8],True);state=child(state,8,state[0][0],False)
    return state
def root_of(bs):
    sep=27852;budget=86600000*SC-sep*sum(bs);up=[sep+(budget+b-1)//b for b in bs]
    return [[(j-i)*sep for i,j in PAIR],
        [min(sum(up[i:j]),(j-i)*sep+(budget+min(bs[i:j])-1)//min(bs[i:j])) for i,j in PAIR]]
def slopes_and_moves(fs,code,terms,bs,points):
    coefficients=[1024000000000*b for b in bs]
    for (i,j,a),(kind,m,p,r) in zip(terms,fs):
        w1,w2=([0,0] if kind==0 else [1024,0] if kind==1 else [m,0] if kind==2 else [1024-m,m])
        slope=0
        for weight,anchor in [(w1,p),(w2,r)]:
            if weight:slope+=weight*(((points.get(anchor,(0,0,0))[0]>>32)&MASK)-2000000000)
        for z in range(i,j):coefficients[z]+=a*slope
    divergence=[-coefficients[0]]+[coefficients[r-1]-coefficients[r] for r in range(1,9)]+[coefficients[8]]
    assert sum(divergence)==0 and 0<=code<10**8
    seq=[code//10**r%10 for r in range(8)];vertices=list(range(10));remaining=divergence.copy();moves=[];rebuilt=[0]*10
    for step in range(9):
        if step<8:
            rest=seq[step:];leaf=next(v for v in vertices if v not in rest);parent=rest[0]
        else:leaf,parent=vertices
        signed=remaining[leaf];i,j=min(leaf,parent),max(leaf,parent)
        rebuilt[leaf]+=signed;rebuilt[parent]-=signed
        if i+1<j and signed:
            upper=(leaf<parent and signed>=0) or (parent<leaf and signed<0)
            moves.append((i,j,upper,abs(signed)))
        remaining[leaf]=0;remaining[parent]+=signed;vertices.remove(leaf)
    assert not any(remaining) and rebuilt==divergence
    return moves
def numeric_check(path,state,fs,code,terms,bs,points,lower):
    positive=[0]*9;negative=[0]*9;cp=cm=0
    moves=slopes_and_moves(fs,code,terms,bs,points)
    for i,j,upper,amount in moves:
        assert amount>=0 and 0<=i<j<=9 and i+1<j
        z=SLOT[i,j];base=sum(state[0][i:j])
        for k in range(i,j):(negative if upper else positive)[k]+=amount
        if upper:cp+=amount*sub(state[1][z],base);cm+=amount*sub(base,state[1][z])
        else:cp+=amount*sub(base,state[0][z]);cm+=amount*sub(state[0][z],base)
    value=loss=gain=0;slopes=[0]*9;mass=[0]*9
    for (i,j,a),(kind,m,p,r) in zip(terms,fs):
        assert kind in range(4) and 0<=m<=1024 and p>=0 and r>=0
        w1,w2=([0,0] if kind==0 else [1024,0] if kind==1 else [m,0] if kind==2 else [1024-m,m])
        z=SLOT[i,j];left=max(state[0][z],sum(state[0][i:j]));right=min(state[1][z],sum(state[1][i:j]));base=sum(state[0][i:j])
        total=(1024-w1-w2)*lower(left,max(left+1,right));derivative=0
        for weight,anchor in [(w1,p),(w2,r)]:
            word,valid_l,valid_u=points.get(anchor,(0,0,0))
            if weight:assert valid_u>0 and valid_l<=left<=anchor<=right<=valid_u,('Invalid PT domain',path,i,j,kind,m,p,r)
            total+=weight*(word&MASK);derivative+=weight*((word>>32)&MASK);d=word>>64
            loss+=a*weight*sub(2000000000,d)*sub(anchor,base);gain+=a*weight*sub(d,2000000000)*sub(anchor,base)
        value+=a*total
        for k in range(i,j):slopes[k]+=a*derivative;mass[k]+=a*(w1+w2)
    penalty=sum(sub(state[1][k],state[0][k])*sub(2000000000*mass[k]+positive[k],1024000000000*bs[k]+slopes[k]+negative[k]) for k in range(9))
    numerator=10240000000000*sum(bs[k]*state[0][k] for k in range(9))+SC*value+10*(gain+cm)-10*(loss+cp+penalty)
    assert numerator>=TARGET,('mcheckGX inequality failed',path,numerator-TARGET)
    return numerator,len(moves)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-receipt',action='store_true');args=parser.parse_args();began=time.monotonic()
    if args.write_receipt:assert not OUT.exists()
    paths=[Path(__file__),HERE/'field-huffman.bin',HERE/'field-huffman.json',HERE/'field-huffman-data.lean',HERE/'semantics.json',
        ROOT/'research-20261016/spectral-w10-refined-rational.json',ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean',
        ROOT/'research-20261016-w10-cert/independent_integer_audit.py',ROOT/'StructuralW10Cert20261016/FastPruefer.lean',
        ROOT/'StructuralW10Cert20261016/LocalChecker.lean',ROOT/'StructuralW10Cert20261016/AdaptiveCoverage.lean',
        ROOT/'StructuralGoal20261016/LeanCoverBase.lean']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths};meta=json.loads(paths[2].read_bytes());semantics=json.loads(paths[4].read_bytes());params=json.loads(paths[5].read_bytes())
    assert sha(paths[1])==meta['binary_sha256']=='9d0b93eed206e14eff3b0d25dc639cb75f5515ea855e6a7c36100ef87a3c5ba3'
    assert sha(paths[3])==meta['data_source_sha256'] and sha(paths[4])==meta['semantics_sha256']
    packed,chunks=literal_bytes(paths[3]);assert packed==paths[1].read_bytes()
    channels=channels_from(packed,meta);cursors={name:0 for name in channels}
    def read(name):
        pos=cursors[name];assert pos<len(channels[name]),('Channel exhausted',name,pos)
        value=channels[name][pos];cursors[name]+=1;return value
    def varint(prefix,maxbytes):
        result=0
        for index in range(maxbytes):
            value=read(prefix+str(index));result|=(value&127)<<(7*index)
            if value<128:
                assert index==0 or value!=0,'Nonminimal ULEB'
                return result
        raise AssertionError('Unterminated varint')
    def signed(prefix,maxbytes):
        value=varint(prefix,maxbytes);return value//2 if value%2==0 else -(value//2)-1
    spec=importlib.util.spec_from_file_location('frozen_independent_PT_reader',paths[7]);old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
    assert sha(paths[5])=='ad117819d63588c55d89bd59ae7f0ad11072faaf33ffc53bf08d7eef54010e03' and sha(paths[6])=='153e1ebfa23b5ef307dc39e36ee712d6f14d840b3b1fa5ff70b82e9dbc8dd244'
    points,lower=old.load_analytic_library();terms=[tuple(t) for t in params['a_upper'] if t[2]];bs=params['b_numerators']
    assert len(terms)==39 and list(map(list,terms))==semantics['terms'] and root_of(bs)==semantics['root']
    hashes={name:hashlib.sha256() for name in ['nodes.bin','fs.bin','treecodes.bin']};states=hashlib.sha256();evidence=hashlib.sha256()
    counters=collections.Counter();kindcounts=collections.Counter();oldcut=[0]*45;lastpoint=[0]*39;stack=[('r',semantics['root'])]
    minimum=None;minimum_path=None;maxmoves=0
    while stack:
        path,rawstate=stack.pop();state=normal(rawstate);states.update(struct.pack('<90I',*(state[0]+state[1])))
        kind=read('node_kind');assert kind in range(4);counters['nodes']+=1;record=[path,kind]
        if kind==1:
            axis=read('axis');assert 0<=axis<45
            cut=oldcut[axis]+signed('cut',4);oldcut[axis]=cut
            assert state[0][axis]<cut<state[1][axis] and cut<1<<32
            hashes['nodes.bin'].update(struct.pack('<BBI',1,axis,cut));counters['branches']+=1;record.extend([axis,cut])
            stack.append((path+'1',child(state,axis,cut,False)));stack.append((path+'0',child(state,axis,cut,True)))
        elif kind==2:
            axis=read('axis');assert 0<=axis<45 and state[1][axis]<state[0][axis],('Invalid empty',path,axis)
            hashes['nodes.bin'].update(bytes([2,axis]));counters['empty']+=1;record.append(axis)
        elif kind==3:
            assert state[1][8]<state[0][0],('Invalid reflection',path)
            hashes['nodes.bin'].update(bytes([3]));counters['reflection']+=1
        else:
            hashes['nodes.bin'].update(bytes([0]));fs=[]
            for t in range(39):
                k=read('term'+str(t));assert 0<=k<=3
                if k==0:m=p=r=0
                else:
                    m=read('mix') if k>=2 else 0
                    point=lastpoint[t]+signed('point',3);assert 0<=point<1<<16;lastpoint[t]=point;p=32*point
                    r=32*(point+signed('second',3)) if k==3 else 0
                assert p%32==r%32==0 and 0<=r//32<1<<16
                hashes['fs.bin'].update(struct.pack('<BHHH',k,m,p//32,r//32));fs.append((k,m,p,r));kindcounts[k]+=1
            code=sum(read('tree'+str(i))*10**i for i in range(8));assert 0<=code<10**8
            hashes['treecodes.bin'].update(struct.pack('<I',code));numerator,moves=numeric_check(path,state,fs,code,terms,bs,points,lower)
            counters['numeric']+=1;maxmoves=max(maxmoves,moves);record.extend([fs,code,str(numerator)])
            if minimum is None or numerator<minimum:minimum=numerator;minimum_path=path
            if counters['numeric']%10000==0:print(json.dumps({'numeric_checked':counters['numeric'],'seconds':time.monotonic()-began}),flush=True)
        encoded=json.dumps(record,separators=(',',':')).encode();evidence.update(len(encoded).to_bytes(4,'little'));evidence.update(encoded)
    assert counters=={'nodes':191557,'branches':95778,'numeric':95615,'empty':163,'reflection':1}
    assert all(cursors[name]==len(values) for name,values in channels.items()),'Unused channel symbols'
    for expected in semantics['cache_files']:assert hashes[expected['path']].hexdigest()==expected['sha256']
    assert states.hexdigest()==semantics['normalized_states_sha256']
    assert dict(kindcounts)=={int(k):v for k,v in semantics['term_kind_counts'].items()}
    assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    out={'scope':__doc__,'status':'field_huffman_full_semantic_roundtrip_and_all_integer_leaf_checks_passed',
        'source_sha256_start':initial,'source_sha256_end':final,'all_sources_unchanged':True,
        'literal_chunks_checked':chunks,'Huffman_channels':len(channels),'all_symbols_consumed':True,'all_padding_checked_zero':True,
        'strict_framing_and_varints_checked':True,'cache_reconstruction_sha256':{name:h.hexdigest() for name,h in hashes.items()},
        'normalized_states_sha256':states.hexdigest(),'independent_full_mathematical_evidence_sha256':evidence.hexdigest(),
        'counts':dict(counters),'term_kind_counts':dict(kindcounts),'max_nonadjacent_dual_moves':maxmoves,
        'minimum_integer_leaf_numerator':str(minimum),'minimum_integer_leaf_path':minimum_path,'target_numerator':str(TARGET),
        'minimum_exact_margin':str(minimum-TARGET),'pure_stdlib_replay':True,'optimizer_calls':0,'Lean_invocations':0,
        'new_Huffman_Lean_decoder_or_expander_implemented':False,'new_complete_Lean_Huffman_cover_checked':False,
        'data_source_bytes':(HERE/'field-huffman-data.lean').stat().st_size,'data_source_alone_under_2000000':False,
        'two_MB_complete_source_achieved':False,'new_exclusions':0,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['status','counts','minimum_exact_margin','data_source_bytes','elapsed_milliseconds']}),flush=True)


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
