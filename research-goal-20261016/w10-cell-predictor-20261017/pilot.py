"""Fixed cell-to-witness predictors on the first1000 frozen W10 numeric leaves.

Read-only frozen caches. No optimizer, new cover, Lean or predictor tuning.
Explicit exceptions reconstruct every original FS byte; original Pruefer
codes are retained. Every domain and integer leaf inequality is rechecked.
"""
from pathlib import Path
import bisect, collections, gzip, hashlib, heapq, importlib.util, json, math, struct, sys, time

HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
CACHE=HERE.parent/'w10-size-audit-20261017'


def digest(p):
    h=hashlib.sha256()
    with p.open('rb')as f:
        for b in iter(lambda:f.read(1<<20),b''):h.update(b)
    return h.hexdigest()


def module(name,p):
    s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def huffbits(values):
    q=list(collections.Counter(values).values());heapq.heapify(q)
    if len(q)<2:return sum(q)
    total=0
    while len(q)>1:
        x=heapq.heappop(q)+heapq.heappop(q);total+=x;heapq.heappush(q,x)
    return total


def signed_bytes(value):
    value=2*value if value>=0 else -2*value-1;out=[]
    while value>=128:out.append((value&127)|128);value>>=7
    return out+[value]


def read_signed(raw,pos):
    x=0
    for j in range(3):
        v=raw[pos];pos+=1;x|=(v&127)<<(7*j)
        if v<128:return (x//2 if x%2==0 else -(x//2)-1),pos
    raise AssertionError('nonterminating point varint')


def numeral(state,fs,code,terms,bs,points,lower,replay):
    # Same integer arithmetic as independent_codec_replay, without its final
    # target assertion, so negative candidates are reported as negative.
    lo,hi=state;positive=[0]*9;negative=[0]*9;cp=cm=0
    for i,j,upper,amount in replay.slopes_and_moves(fs,code,terms,bs,points):
        z=replay.SLOT[i,j];base=sum(lo[i:j])
        for k in range(i,j):(negative if upper else positive)[k]+=amount
        if upper:cp+=amount*max(0,hi[z]-base);cm+=amount*max(0,base-hi[z])
        else:cp+=amount*max(0,base-lo[z]);cm+=amount*max(0,lo[z]-base)
    value=loss=gain=0;slopes=[0]*9;mass=[0]*9
    for (i,j,a),(kind,m,p,r)in zip(terms,fs):
        w1,w2=([0,0]if kind==0 else[1024,0]if kind==1 else[m,0]if kind==2 else[1024-m,m])
        z=replay.SLOT[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]));base=sum(lo[i:j])
        total=(1024-w1-w2)*lower(left,max(left+1,right));derivative=0
        for weight,anchor in [(w1,p),(w2,r)]:
            word,vl,vu=points.get(anchor,(0,0,0))
            if weight:assert vu>0 and vl<=left<=anchor<=right<=vu
            total+=weight*(word&replay.MASK);derivative+=weight*((word>>32)&replay.MASK);d=word>>64
            loss+=a*weight*max(0,2000000000-d)*max(0,anchor-base)
            gain+=a*weight*max(0,d-2000000000)*max(0,anchor-base)
        value+=a*total
        for k in range(i,j):slopes[k]+=a*derivative;mass[k]+=a*(w1+w2)
    penalty=sum(max(0,hi[k]-lo[k])*max(0,2000000000*mass[k]+positive[k]-1024000000000*bs[k]-slopes[k]-negative[k])for k in range(9))
    return 10240000000000*sum(bs[k]*lo[k]for k in range(9))+32768*value+10*(gain+cm)-10*(loss+cp+penalty)


def predictions(state,terms,points,anchors,slot):
    result=[[],[],[]];available=[]
    for i,j,_ in terms:
        z=slot[i,j];left=max(state[0][z],sum(state[0][i:j]));right=min(state[1][z],sum(state[1][i:j]))
        legal=[p for p in anchors[bisect.bisect_left(anchors,left):bisect.bisect_right(anchors,right)]
          if points[p][2]>0 and points[p][1]<=left and right<=points[p][2]]
        available.append(len(legal))
        choices=[min(legal,key=lambda p:(abs(2*p-left-right),p)),legal[0],legal[-1]]if legal else[None]*3
        for out,p in zip(result,choices):out.append((1,0,p,0)if p is not None else(0,0,0,0))
    return result,available


def main():
    started=time.monotonic();out=HERE/'result.json';assert not out.exists()
    protocol=json.loads((HERE/'protocol.json').read_bytes());assert protocol['limit']==1000
    inputs=[Path(__file__),HERE/'protocol.json',CACHE/'semantics.json',CACHE/'field-huffman.json',
      CACHE/'source-size-accounting.json',CACHE/'independent_codec_replay.py',
      ROOT/'research-20261016-w10-cert/independent_integer_audit.py',
      ROOT/'research-20261016-w10-cert/tree_flow.py',ROOT/'research-20261016/spectral-w10-refined-rational.json',
      ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean']+[CACHE/n for n in ['nodes.bin','fs.bin','treecodes.bin']]
    guards={p.relative_to(ROOT).as_posix():digest(p)for p in inputs}
    meta=json.loads((CACHE/'semantics.json').read_bytes())
    for row in meta['cache_files']:assert digest(CACHE/row['path'])==row['sha256']
    replay=module('frozen_geometry_integer',CACHE/'independent_codec_replay.py')
    analytic=module('frozen_analytic',ROOT/'research-20261016-w10-cert/independent_integer_audit.py')
    params=json.loads((ROOT/'research-20261016/spectral-w10-refined-rational.json').read_bytes())
    points,lower=analytic.load_analytic_library();anchors=sorted(p for p in points if p%32==0);terms=[tuple(t)for t in meta['terms']];bs=params['b_numerators']
    assert replay.root_of(bs)==meta['root'];samples=[];stack=[('r',meta['root'])];geometry=hashlib.sha256();consumed=0
    with(CACHE/'nodes.bin').open('rb')as nodes,(CACHE/'fs.bin').open('rb')as f,(CACHE/'treecodes.bin').open('rb')as trees:
        while len(samples)<1000:
            path,state=stack.pop();state=replay.normal(state);kind=nodes.read(1)[0];consumed+=1
            geometry.update(struct.pack('<90I',*(state[0]+state[1])))
            if kind==1:
                axis,cut=struct.unpack('<BI',nodes.read(5));assert state[0][axis]<cut<state[1][axis]
                stack.extend([(path+'1',replay.child(state,axis,cut,False)),(path+'0',replay.child(state,axis,cut,True))])
            elif kind==2:
                axis=nodes.read(1)[0];assert state[1][axis]<state[0][axis]
            elif kind==3:assert state[1][8]<state[0][0]
            else:
                assert kind==0;fs=[tuple([k,m,32*p,32*r])for k,m,p,r in[struct.unpack('<BHHH',f.read(7))for _ in range(39)]]
                code=struct.unpack('<I',trees.read(4))[0]
                original,_=replay.numeric_check(path,state,fs,code,terms,bs,points,lower)
                assert numeral(state,fs,code,terms,bs,points,lower,replay)==original
                pred,available=predictions(state,terms,points,anchors,replay.SLOT)
                samples.append((path,state,fs,code,original,pred,available))
    stats=[]
    for rule in range(3):
        raw=bytearray(b'W10P\x01'+bytes([rule])+struct.pack('<H',len(samples)));counts=collections.Counter();channels={n:[]for n in ['kind','mix']+[f'mask{i}'for i in range(5)]+[f'{s}{i}'for s in ['p','r']for i in range(3)]}
        pred_pass=original_point_match=0;minimum_pred=None
        for path,state,fs,code,original,pred,available in samples:
            guess=pred[rule];mask=sum(int(a!=b)<<t for t,(a,b)in enumerate(zip(fs,guess)));raw.extend(mask.to_bytes(5,'little'))
            for i in range(5):channels[f'mask{i}'].append((mask>>(8*i))&255)
            for t,(old,new)in enumerate(zip(fs,guess)):
                counts['terms']+=1;counts['exact_row_matches']+=old==new;counts['kind_matches']+=old[0]==new[0];counts['PT_available']+=available[t]>0
                if old[0]:counts['original_active']+=1;counts['active_first_point_matches']+=old[2]==new[2]
                if old==new:continue
                k,m,p,r=old;raw.append(k);channels['kind'].append(k);counts['exception_rows']+=1
                if k>=2:raw.extend(struct.pack('<H',m));channels['mix'].append(m)
                if k:
                    b=signed_bytes((p-new[2])//32);raw.extend(b)
                    for i,x in enumerate(b):channels[f'p{i}'].append(x)
                if k==3:
                    b=signed_bytes((r-p)//32);raw.extend(b)
                    for i,x in enumerate(b):channels[f'r{i}'].append(x)
            raw.extend(struct.pack('<I',code))
            val=numeral(state,guess,code,terms,bs,points,lower,replay);pred_pass+=val>=replay.TARGET
            minimum_pred=val-replay.TARGET if minimum_pred is None else min(minimum_pred,val-replay.TARGET)
        # A separate read of the emitted bytes reconstructs all original rows.
        pos=8;assert raw[:5]==b'W10P\x01' and raw[5]==rule and struct.unpack_from('<H',raw,6)[0]==1000
        for path,state,fs,code,original,pred,_ in samples:
            mask=int.from_bytes(raw[pos:pos+5],'little');pos+=5;assert mask<1<<39;decoded=[]
            for t,new in enumerate(pred[rule]):
                if not(mask>>t)&1:decoded.append(new);continue
                k=raw[pos];pos+=1;m=p=r=0;assert k<4
                if k>=2:m=struct.unpack_from('<H',raw,pos)[0];pos+=2
                if k:delta,pos=read_signed(raw,pos);p=new[2]+32*delta
                if k==3:delta,pos=read_signed(raw,pos);r=p+32*delta
                decoded.append((k,m,p,r))
            saved=struct.unpack_from('<I',raw,pos)[0];pos+=4
            assert decoded==fs and saved==code
            assert replay.numeric_check(path,state,decoded,saved,terms,bs,points,lower)[0]==original
        assert pos==len(raw)
        p=HERE/f'rule{rule}-exceptions.bin';assert not p.exists();p.write_bytes(raw)
        gzp=p.with_suffix('.bin.gz');assert not gzp.exists();gzp.write_bytes(gzip.compress(raw,mtime=0))
        bits={name:huffbits(values)for name,values in channels.items()}
        stats.append({'rule':protocol['rules'][rule],'counts':dict(counts),'predicted_FS_with_old_tree_pass':pred_pass,
          'minimum_predicted_margin':str(minimum_pred),'lossless_exception_bytes_with_original_tree_codes':len(raw),
          'gzip_bytes_not_a_Lean_decoder_claim':gzp.stat().st_size,'raw_sha256':digest(p),'gzip_sha256':digest(gzp),
          'all_1000_original_FS_exactly_reconstructed_and_integer_checked':True,'exception_Huffman_payload_bits':bits,
          'exception_Huffman_payload_bits_total':sum(bits.values()),'shared_model_bytes':5*256+4+1024+6*256})
    fixed=[]
    for code,name in zip(protocol['fixed_tree_codes'],protocol['fixed_tree_names']):
        margins=[numeral(s,fs,code,terms,bs,points,lower,replay)-replay.TARGET for _,s,fs,_,_,_,_ in samples]
        fixed.append({'name':name,'code':code,'exact_original_code_matches':sum(code==x[3]for x in samples),
          'original_FS_domain_valid_and_integer_check_passes':sum(v>=0 for v in margins),'minimum_margin':str(min(margins))})
    portfolio=sum(any(numeral(s,fs,c,terms,bs,points,lower,replay)>=replay.TARGET for c in protocol['fixed_tree_codes'])for _,s,fs,_,_,_,_ in samples)
    globalmeta=json.loads((CACHE/'field-huffman.json').read_bytes());categories=collections.Counter()
    for ch in globalmeta['channels']:
        name=ch['name'];cat='geometry'if name in ['node_kind','axis']or name.startswith('cut')else'tree'if name.startswith('tree')else'FS'
        categories[cat]+=10+ch['model_bytes']+ch['coded_bytes']
    retained=json.loads((CACHE/'source-size-accounting.json').read_bytes())['exact_retained_base_wrapper_license_bytes']
    for r in stats:
        projected_binary=7+categories['geometry']+categories['tree']+math.ceil(r['exception_Huffman_payload_bits_total']*95615/8000)+r['shared_model_bytes']+130
        r['nonrigorous_prefix_distribution_extrapolation']={'binary_bytes':projected_binary,
          'source_bytes_with_1p25_literal_factor_542851_retained_and_128000_decoder_reserve':math.ceil(projected_binary*1.25)+retained+128000+1024,
          'assumption':'First1000 nonrandom preorder leaves have identical residual distributions to all95615 leaves; not a bound or full-source artifact.'}
    assert all(digest(ROOT/n)==v for n,v in guards.items())
    result={'scope':__doc__,'source_and_input_sha256':guards,'protocol_sha256':digest(HERE/'protocol.json'),
      'sample_numeric_leaves':1000,'preorder_nodes_consumed':consumed,'first_path':samples[0][0],'last_path':samples[-1][0],
      'sample_normalized_geometry_sha256':geometry.hexdigest(),'rules':stats,'fixed_tree_results':fixed,
      'fixed_tree_portfolio_integer_check_passes':portfolio,'global_original_Huffman_category_bytes':dict(categories),
      'retained_source_bytes':retained,'decoder_expander_reserved_bytes':128000,
      'tree_recompute_static_review':'tree_flow.recompute calls nx.network_simplex on all directed arcs with DBM costs and divergence demands; not simple greedy. It then completes its flow forest by ordered adjacent zero-flow edges. No call was executed.',
      'optimizer_calls':0,'Lean_invocations':0,'new_cover_search':False,'full95615_predictor_run':False,
      'complete_Lean_decoder_or_cover_proven':False,'two_MB_complete_source_achieved':False,'new_zero_proportion_proven':False,
      'seconds':time.monotonic()-started}
    out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'sample':1000,'rules':[{k:r[k]for k in ['rule','counts','predicted_FS_with_old_tree_pass','lossless_exception_bytes_with_original_tree_codes','exception_Huffman_payload_bits_total','nonrigorous_prefix_distribution_extrapolation']}for r in stats],'fixed_trees':fixed,'portfolio':portfolio,'seconds':result['seconds']}),flush=True)


if __name__=='__main__':
    assert __debug__
    main()
