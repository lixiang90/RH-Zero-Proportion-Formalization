"""Independent stdlib whole-tree W10 support-domain opportunity replay.

No producer import, integer energy/floor check, oracle, solver, new codec,
curve certificate or Lean. Reconstruct geometry, component guards, graphic
rank, fixed five antichains and attributed original-stream engineering costs.
Default read-only; --write-receipt creates an absent receipt once.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,ast,collections,functools,gzip,hashlib,json,re,struct,sys,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
SRC=ROOT/'research-goal-20261017-w10-slice-opportunity';OLD=ROOT/'research-goal-20261016/w10-size-audit-20261017'
OUT=HERE/'independent-replay.json';REPORT_SHA='41b036ab5a82d247105f989b15ff0648fa2cc411cbcdaf5eaf5bd9d0b046cf84'
BB=1<<42;PAIRS=[(i,i+1)for i in range(9)]+[(i,j)for i in range(10)for j in range(i+2,10)];INDEX={e:k for k,e in enumerate(PAIRS)}
HEAD=struct.Struct('<IIIIIIQQ');CAND=struct.Struct('<I10sQBBBHQL');REC=HEAD.size+2*CAND.size
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
    b=p.read_bytes();return json.loads(gzip.decompress(b)if p.suffix=='.gz'else b)
def restrict(state,axis,cut,is_upper):
    lo,hi=state;i,j=PAIRS[axis];a,b,w=(i,j,cut)if is_upper else(j,i,-cut)
    def d(x,y):return 0 if x==y else hi[INDEX[x,y]]if x<y else-lo[INDEX[y,x]]
    col=[max(0,BB+d(x,a))for x in range(10)];row=[max(0,BB+w+d(b,x))for x in range(10)]
    return [[max(v,max(0,2*BB-col[y]-row[x]))for v,(x,y)in zip(lo,PAIRS)],
            [min(v,max(0,col[x]+row[y]-2*BB))for v,(x,y)in zip(hi,PAIRS)]]
def normalize(state):
    if state[1][0]<=state[1][8]and state[0][0]<=state[0][8]:return state
    for _ in range(2):state=restrict(state,0,state[1][8],True);state=restrict(state,8,state[0][0],False)
    return state
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();reportpath=SRC/'opportunities.json';assert sha(reportpath)==REPORT_SHA
    p=read(reportpath);assert p['all_inputs_unchanged']and p['source_sha256_start']==p['source_sha256_end']
    pins={**p['source_sha256_start'],reportpath.relative_to(ROOT).as_posix():REPORT_SHA,Path(__file__).relative_to(ROOT).as_posix():sha(Path(__file__))}
    for rec in[p['parent_records']]+p['prefix_files']:pins[rec['path']]=rec['sha256'];assert(ROOT/rec['path']).stat().st_size==rec['bytes']
    for n,h in pins.items():assert sha(ROOT/n)==h
    meta=read(OLD/'semantics.json');terms=list(map(tuple,meta['terms']));nodes=(OLD/'nodes.bin').read_bytes();fb=(OLD/'fs.bin').read_bytes();codes=(OLD/'treecodes.bin').read_bytes()
    for r in meta['cache_files']:assert len((OLD/r['path']).read_bytes())==r['bytes']and sha(OLD/r['path'])==r['sha256']
    assert len(terms)==39 and len({(i,j)for i,j,a in terms})==39 and all(a>0 for i,j,a in terms)
    rawrecords=gzip.decompress((ROOT/p['parent_records']['path']).read_bytes());assert len(rawrecords)==p['parent_records']['uncompressed_bytes']and hashlib.sha256(rawrecords).hexdigest()==p['parent_records']['uncompressed_sha256']
    assert rawrecords[:6]==b'W10OP\x01'and struct.unpack_from('<IH',rawrecords,6)==(95778,118)and REC==118
    text=(ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean').read_text(encoding='utf8');text=text.split('namespace AMW.Cert.PC9QB6M\n',1)[1];points={}
    for block,table in re.findall(r'\.lf (\d+) (\[[^\]]*\])',text):
        for offset,word in ast.literal_eval(table):
            anchor=1024*int(block)+offset;assert anchor not in points
            points[anchor]=(max(0,anchor-((word>>96)&((1<<20)-1))),anchor+(word>>116))
    del text
    hm=read(OLD/'field-huffman.json');binary=(OLD/'field-huffman.bin').read_bytes();assert binary[:7]==b'W10H\x01\x00'+bytes([len(hm['channels'])])
    lengths={};pos=7
    for r in hm['channels']:
        alphabet,count,size=struct.unpack_from('<HII',binary,pos);pos+=10;assert(alphabet,count,size)==(r['alphabet'],r['tokens'],r['coded_bytes'])
        lengths[r['name']]=binary[pos:pos+alphabet];pos+=alphabet+size
    assert pos==len(binary)and sha(OLD/'field-huffman.bin')==hm['binary_sha256']
    literal=(OLD/'field-huffman-data.lean').read_bytes();chunks=re.findall(r'"([^"\\]*)"',literal.decode().split('def chunks : Array String := #[',1)[1]);nchars=sum(map(len,chunks));overhead=len(literal)-nchars
    token_counts=collections.Counter();token_bits=collections.Counter()
    def token(name,value):
        assert 0<=value<len(lengths[name]);bits=lengths[name][value];assert bits>0
        token_counts[name]+=1;token_bits[name]+=bits;return bits
    def signed(prefix,value):
        z=2*value if value>=0 else-2*value-1;bits=0;j=0
        while True:
            byte=z&127;z>>=7;bits+=token(prefix+str(j),byte+(128 if z else 0));j+=1
            if not z:return bits
    @functools.lru_cache(maxsize=4096)
    def fs(n):return tuple(struct.iter_unpack('<BHHH',fb[273*n:273*(n+1)]))
    @functools.lru_cache(maxsize=8192)
    def graphic_rank(mask):
        # The invertible gap-to-position incidence transformation maps
        # 1_[i,j) to edge e_j-e_i. Rank=10-number_of_graph_components.
        parent=list(range(10));rank=0
        def find(v):
            while parent[v]!=v:parent[v]=parent[parent[v]];v=parent[v]
            return v
        for t,(i,j,a)in enumerate(terms):
            if mask>>t&1:
                x,y=find(i),find(j)
                if x!=y:parent[x]=y;rank+=1
        return rank
    def components(rep,state):
        lo,hi=state;cm=sm=nc=mass=weighted=0
        for t,((i,j,a),(kind,m,p0,p1))in enumerate(zip(terms,fs(rep))):
            assert kind in range(4)and 0<=m<=1024
            masses=[0,0]if kind==0 else[1024,0]if kind==1 else[m,0]if kind==2 else[1024-m,m]
            assert 0<=1024-sum(masses)<=1024
            left=max(lo[INDEX[i,j]],sum(lo[i:j]));right=min(hi[INDEX[i,j]],sum(hi[i:j]))
            for slot,(w,p0)in enumerate(zip(masses,[p0,p1])):
                if not w:continue
                anchor=32*p0;vl,vu=points.get(anchor,(0,0))
                if not(vu>0 and vl<=left<=anchor<=right<=vu):cm|=1<<(2*t+slot);sm|=1<<t;nc+=1;mass+=w;weighted+=a*w
        return cm,sm,nc,sm.bit_count(),graphic_rank(sm),mass,weighted
    oldcuts=[0]*45;lastpoint=[0]*39
    def numbits(n):
        bits=token('node_kind',0)
        for t,(kind,m,p0,p1)in enumerate(fs(n)):
            bits+=token('term'+str(t),kind)
            if kind:
                if kind>=2:bits+=token('mix',m)
                bits+=signed('point',p0-lastpoint[t]);lastpoint[t]=p0
                if kind==3:bits+=signed('second',p1-p0)
        code=struct.unpack_from('<I',codes,4*n)[0];assert code<10**8
        for j in range(8):bits+=token('tree'+str(j),code//10**j%10)
        return bits
    offset=numeric=ordinal=recordpos=0;counts=collections.Counter();states=hashlib.sha256();repbits=[];parents=[];hist=collections.Counter();joint=collections.Counter();phist=collections.Counter()
    sys.setrecursionlimit(10000)
    def walk(path,raw):
        nonlocal offset,numeric,ordinal,recordpos
        state=normalize(raw);nid=ordinal;ordinal+=1;states.update(struct.pack('<90I',*(state[0]+state[1])))
        kind=nodes[offset];offset+=1;counts['nodes']+=1;first=numeric
        if kind==0:
            n=numeric;numeric+=1;counts['numeric']+=1;bits=numbits(n);repbits.append(bits);assert components(n,state)[2]==0
            return n,1,1,0,bits
        own=token('node_kind',kind)
        if kind==2:
            own+=token('axis',nodes[offset]);offset+=1;counts['empty']+=1;return None,0,1,0,own
        if kind==3:counts['reflection']+=1;return None,0,1,0,own
        assert kind==1;axis,cut=struct.unpack_from('<BI',nodes,offset);offset+=5;assert 0<=axis<45 and state[0][axis]<cut<state[1][axis]
        counts['branches']+=1;own+=token('axis',axis)+signed('cut',cut-oldcuts[axis]);oldcuts[axis]=cut
        left=walk(path+'0',restrict(state,axis,cut,True));right=walk(path+'1',restrict(state,axis,cut,False));candidates=[]
        for rep in[left[0],right[0]]:
            if rep is None:candidates.append(None)
            else:
                d=components(rep,state);candidates.append((rep,*d,repbits[rep]));hist[d[2]]+=1;joint[d[2],d[3],d[4]]+=1
        valid=[v for v in candidates if v is not None and v[3]>0]
        phist['min_nonempty_distinct',min(v[4]for v in valid)if valid else-1]+=1;phist['min_nonempty_rank',min(v[5]for v in valid)if valid else-1]+=1
        nnum=left[1]+right[1];nnodes=left[2]+right[2]+1;nbranch=left[3]+right[3]+1;bits=left[4]+right[4]+own
        head=(nid,ordinal,first,nnum,nnodes,nbranch,own,bits)
        expect=bytearray(HEAD.pack(*head))
        for candidate in candidates:
            if candidate is None:expect.extend(CAND.pack(2**32-1,b'\0'*10,0,0,0,0,0,0,0))
            else:
                rep,cm,sm,nc,nd,nr,mass,weighted,rb=candidate;expect.extend(CAND.pack(rep,cm.to_bytes(10,'little'),sm,nc,nd,nr,mass,weighted,rb))
        start=12+recordpos*REC;assert rawrecords[start:start+REC]==expect,('parent record mismatch',path,recordpos);recordpos+=1
        parents.append((*head,path,*candidates))
        if recordpos%25000==0:print(json.dumps({'phase':'whole_tree_component_guard_replay','parents':recordpos}),flush=True)
        return left[0]if left[0]is not None else right[0],nnum,nnodes,nbranch,bits
    top=walk('r',meta['root'])
    assert offset==len(nodes)and numeric==95615 and ordinal==191557 and recordpos==95778 and 12+recordpos*REC==len(rawrecords)
    assert counts==p['counts']=={'nodes':191557,'branches':95778,'numeric':95615,'empty':163,'reflection':1}
    assert states.hexdigest()==p['normalized_states_sha256']==meta['normalized_states_sha256']
    assert hist[0]==p['J0_candidate_count_not_a_slice_opportunity']==5737 and sum(hist.values())==p['candidate_count']==191392
    assert {str(k):v for k,v in sorted(hist.items())}==p['invalid_component_histogram']
    assert[[a,b,c,n]for(a,b,c),n in sorted(joint.items())]==p['joint_component_distinct_rank_histogram']and[[a,b,n]for(a,b),n in sorted(phist.items())]==p['parent_min_nonempty_dimension_histogram']
    for r in hm['channels']:assert token_counts[r['name']]==r['tokens']and token_bits[r['name']]==r['coded_bits']
    totalbits=sum(token_bits.values());assert totalbits==top[4]==p['original_all_codeword_bits']and overhead==p['fixed_literal_syntax_overhead_bytes']
    size=read(OLD/'source-size-accounting.json');base=size['exact_retained_base_wrapper_license_bytes'];assert base==542851
    def equiv(remove,rb=0):
        n=hm['binary_bytes']*8-remove+rb;assert 0<=n<=hm['binary_bytes']*8
        return overhead+(nchars*n+hm['binary_bytes']*8-1)//(hm['binary_bytes']*8)
    family_results=[]
    for spec,row in zip([('distinct1',4,1),('distinct2',4,2),('rank1',5,1),('rank2',5,2),('all_nonempty',4,39)],p['prefix_results']):
        family,metric,threshold=spec;assert row['family']==family
        stop=-1;chosen=[];covered=removed=nn=nb=rb=0
        for record in sorted(parents,key=lambda r:r[0]):
            nid,end,first,nnum,nnodes,nbranch,own,bits,path,left,right=record
            if nid<stop:continue
            possible=[v for v in[left,right]if v is not None and v[3]>0 and v[metric]<=threshold]
            if not possible:continue
            candidate=possible[0];rep,cm,sm,nc,nd,nr,mass,weighted,representativebits=candidate;stop=end
            chosen.append({'path':path,'preorder_node_id':nid,'subtree_end_id_exclusive':end,'original_numeric_first':first,'original_numeric_covered':nnum,'original_nodes':nnodes,'original_branches':nbranch,'representative_original_numeric_index':rep,'invalid_component_mask':hex(cm),'invalid_distinct_span_mask':hex(sm),'invalid_component_count':nc,'distinct_span_count':nd,'span_indicator_Qrank':nr,'invalid_mass_sum':mass,'invalid_ledger_mass_numerator_over1024':weighted,'original_subtree_attributed_codeword_bits':bits,'original_representative_attributed_codeword_bits':representativebits})
            covered+=nnum;removed+=bits;nn+=nnodes;nb+=nbranch;rb+=representativebits
        packet=read(ROOT/row['selection_packet']['path']);assert packet['family']==family and packet['dimension_threshold']==threshold and packet['selected_prefixes']==chosen
        assert all(a['subtree_end_id_exclusive']<=b['preorder_node_id']and a['original_numeric_first']+a['original_numeric_covered']<=b['original_numeric_first']for a,b in zip(chosen,chosen[1:]))
        assert all(not b['path'].startswith(a['path'])for a,b in zip(chosen,chosen[1:]))
        ideal=equiv(removed);budget=equiv(removed,rb);headroom=2000000-base-128000-budget
        expected={'prefix_free_replacements_assumed_provable':len(chosen),'original_numeric_covered_without_overlap':covered,'hypothetical_remaining_numeric_including_new_curve_leaves':95615-covered+len(chosen),'hypothetical_numeric_reduction':covered-len(chosen),'original_nodes_removed':nn,'original_branches_removed':nb,'original_nodes_retained':191557-nn,'original_branch_records_retained':95778-nb,'attributed_original_codeword_bits_removed':removed,'attributed_original_codeword_bits_retained':totalbits-removed,'old_representative_attributed_bit_budget':rb,'retained_base_source_bytes':542851,'new_consumer_source_reserve_bytes':128000,'ideal_zero_new_payload_literal_equivalent_bytes':ideal,'ideal_source_equivalent_total_bytes':base+128000+ideal,'representative_payload_budget_literal_equivalent_bytes':budget,'budgeted_source_equivalent_before_curve_proofs':base+128000+budget,'additional_curve_proof_payload_budget_total_bytes':headroom,'additional_curve_proof_payload_budget_mean_bytes':str(F(headroom,len(chosen)))if chosen else None}
        for k,v in expected.items():assert row[k]==v,(family,k)
        assert not row['new_decodable_stream_or_source_feasibility_proven']and not row['actual_curve_proof_payload_known']
        family_results.append({'family':family,**expected})
    assert len(family_results)==5 and not p['complete_source_proven_feasible']and p['mathematical_merges_proven']==0
    for n,h in pins.items():assert sha(ROOT/n)==h
    result={'scope':__doc__,'passed':True,'source_sha256_start':pins,'source_sha256_end':pins,'all_inputs_unchanged':True,'whole_tree_nodes':191557,'normal_parent_records_checked':95778,'numeric_leaf_support_guards_checked':95615,'candidate_parent_supports_checked':191392,'J0_candidates_not_eligible':5737,
        'all_118_byte_postorder_records_exactly_match':True,'mixed_masses_1024_preserved_componentwise':True,'graph_incidence_rank_independently_matches_Q_rank':True,'normalized_states_sha256':states.hexdigest(),'all_original_Huffman_token_counts_and_bits_match':True,'new_encoding_generated':False,'family_results':family_results,
        'all_five_prefix_families_checked':True,'no_sixth_rank3_selection_generated':True,'root_partition_preserved_conditionally_on_replacement_proofs':True,'engineering_costs_not_new_source_sizes':True,'actual_curve_certificates_proven':0,'failure_scope':'Fixed original leftmost representatives and attributed original-stream cost model only; no impossibility for other low-dimensional methods is asserted.',
        'producer_imports':0,'solver_calls':0,'oracle_calls':0,'integer_floor_checks':0,'new_witnesses':0,'codec_generation_calls':0,'Lean_invocations':0,'global_cover_Lean_completed':False,'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'parents':95778,'candidates':191392,'families':[{k:r[k]for k in['family','hypothetical_numeric_reduction','ideal_source_equivalent_total_bytes','budgeted_source_equivalent_before_curve_proofs']}for r in family_results],'seconds':result['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
