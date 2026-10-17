"""One read-only whole-W10 support-domain opportunity audit.

No integer floor/oracle, new witness, curve, solver, codec or Lean check.
Original leftmost-child representatives and all original masses are fixed.
Prefix potentials assume the selected nonempty curve family can be proved;
the attributed original-stream source burden is an engineering estimate,
not a new decodable stream or mathematical merge.
"""
from pathlib import Path
from fractions import Fraction as F
import ast,collections,ctypes,functools,gzip,hashlib,json,math,re,struct,sys,time,traceback
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
OLD=ROOT/'research-goal-20261016/w10-size-audit-20261017'
OUT=HERE/'opportunities.json';RECORDS=HERE/'opportunity-records.bin.gz'
LIMIT=1536*1024**2;FILELIMIT=40*1024**2;BB=1<<42
PAIRS=[(i,i+1) for i in range(9)]+[(i,j) for i in range(10) for j in range(i+2,10)]
SLOT={p:i for i,p in enumerate(PAIRS)};NO_REP=2**32-1
BASE=struct.Struct('<IIIIIIQQ');CAND=struct.Struct('<I10sQBBBHQL');RSIZE=BASE.size+2*CAND.size
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def memory():
    from ctypes import wintypes as W
    class PMC(ctypes.Structure):
        _fields_=[('cb',W.DWORD),('PageFaultCount',W.DWORD)]+[(s,ctypes.c_size_t) for s in
            ['PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage']]
    k=ctypes.WinDLL('kernel32');k.GetCurrentProcess.restype=W.HANDLE;p=ctypes.WinDLL('psapi');p.GetProcessMemoryInfo.argtypes=[W.HANDLE,ctypes.POINTER(PMC),W.DWORD]
    m=PMC();m.cb=ctypes.sizeof(m);assert p.GetProcessMemoryInfo(k.GetCurrentProcess(),ctypes.byref(m),m.cb)
    return {'working_set_bytes':m.WorkingSetSize,'peak_working_set_bytes':m.PeakWorkingSetSize,'private_commit_bytes':m.PagefileUsage}
def child(state,axis,cut,upper):
    lo,hi=state;i,j=PAIRS[axis];a,b,w=(i,j,cut) if upper else (j,i,-cut)
    def edge(x,y):return 0 if x==y else hi[SLOT[x,y]] if x<y else -lo[SLOT[y,x]]
    col=[max(0,BB+edge(x,a)) for x in range(10)];row=[max(0,BB+w+edge(b,x)) for x in range(10)]
    return ([max(v,max(0,2*BB-col[j]-row[i])) for v,(i,j) in zip(lo,PAIRS)],
        [min(v,max(0,col[i]+row[j]-2*BB)) for v,(i,j) in zip(hi,PAIRS)])
def normal(state):
    if state[1][0]<=state[1][8] and state[0][0]<=state[0][8]:return state
    for _ in range(2):state=child(state,0,state[1][8],True);state=child(state,8,state[0][0],False)
    return state
def main():
    assert not OUT.exists() and not RECORDS.exists();began=time.monotonic();sys.setrecursionlimit(10000)
    paths=[Path(__file__),HERE/'run_once.py',OLD/'semantics.json',OLD/'nodes.bin',OLD/'fs.bin',OLD/'treecodes.bin',
        OLD/'field-huffman.bin',OLD/'field-huffman.json',OLD/'field-huffman-data.lean',OLD/'source-size-accounting.json',
        ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean',
        ROOT/'research-goal-20261016/w10-size-merge-20261017/merged-summary.json']
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    report={'scope':__doc__,'phase':'loading_frozen_sources','source_sha256_start':initial,'memory_snapshots':[],
        'solver_calls':0,'oracle_calls':0,'integer_floor_checks':0,'actual_kernel_evaluations':0,'new_witnesses':0,
        'new_partitions':0,'codec_generation_calls':0,'Lean_invocations':0,'mathematical_merges_proven':0,
        'complete_source_proven_feasible':False,'new_unconditional_zero_proportion_proven':False}
    def save(phase):
        m=memory();m.update({'phase':phase,'elapsed_milliseconds':int((time.monotonic()-began)*1000)});report['memory_snapshots'].append(m)
        final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
        report.update({'phase':phase,'source_sha256_end':final,'all_inputs_unchanged':True,'elapsed_milliseconds':m['elapsed_milliseconds']})
        temp=OUT.with_suffix('.partial');temp.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8');temp.replace(OUT)
        if m['peak_working_set_bytes']>LIMIT:raise MemoryError('whole-tree opportunity1.5GiB RSS guard')
    save('loading_frozen_sources')
    try:
        meta=json.loads(paths[2].read_bytes());terms=[tuple(t) for t in meta['terms']];nodes=paths[3].read_bytes();fsbytes=paths[4].read_bytes();codes=paths[5].read_bytes()
        for r in meta['cache_files']:assert sha(OLD/r['path'])==r['sha256']
        assert len(terms)==39 and len(set((i,j) for i,j,a in terms))==39 and all(a>0 for i,j,a in terms)
        prior=json.loads(paths[11].read_bytes());assert prior['successful_parent_checks']==0 and prior['parents_tested']==95778
        # Parse only actual PT support validity endpoints; no wfun or lower
        # table lookup is evaluated, and no DualMove amount is decoded.
        text=paths[10].read_text(encoding='utf8');text=text[text.index('namespace AMW.Cert.PC9QB6M\n'):];pt={}
        for j,table in re.findall(r'\.lf (\d+) (\[[^\]]*\])',text):
            for k,v in ast.literal_eval(table):
                p=1024*int(j)+k;assert p not in pt;pt[p]=(max(0,p-((v>>96)&(2**20-1))),p+(v>>116))
        del text
        # Read existing canonical Huffman lengths. Reproduce only old token
        # accounting; this never emits a modified binary/codebook/decoder.
        hm=json.loads(paths[7].read_bytes());binary=paths[6].read_bytes();assert binary[:7]==b'W10H\x01\x00'+bytes([len(hm['channels'])])
        hp=7;lengths={};seen_tokens=collections.Counter();seen_bits=collections.Counter()
        for ch in hm['channels']:
            alphabet,count,packed=struct.unpack_from('<HII',binary,hp);hp+=10
            assert (alphabet,count,packed)==(ch['alphabet'],ch['tokens'],ch['coded_bytes'])
            lengths[ch['name']]=binary[hp:hp+alphabet];hp+=alphabet+packed
        assert hp==len(binary) and sha(paths[6])==hm['binary_sha256']
        lean=paths[8].read_bytes();literal_text=lean.decode().split('def chunks : Array String := #[',1)[1]
        literal_chars=sum(len(s) for s in re.findall(r'"([^"\\]*)"',literal_text));literal_overhead=len(lean)-literal_chars
        assert len(lean)==hm['data_source_bytes'] and literal_chars>0
        del binary,lean,literal_text
        def token(name,value):
            lens=lengths[name];assert 0<=value<len(lens) and lens[value]>0
            seen_tokens[name]+=1;seen_bits[name]+=lens[value];return lens[value]
        def signed(prefix,value):
            z=2*value if value>=0 else -2*value-1;k=0;bits=0
            while z>=128:bits+=token(prefix+str(k),(z&127)|128);z>>=7;k+=1
            return bits+token(prefix+str(k),z)
        oldcut=[0]*45;lastpoint=[0]*39
        @functools.lru_cache(maxsize=4096)
        def fs(index):
            start=index*273;return tuple(struct.iter_unpack('<BHHH',fsbytes[start:start+273]))
        vectors=[tuple(int(i<=k<j) for k in range(9)) for i,j,a in terms]
        @functools.lru_cache(maxsize=8192)
        def rank(mask):
            if mask.bit_count()<=2:return mask.bit_count()
            basis={}
            for t in range(39):
                if not (mask>>t)&1:continue
                row=list(vectors[t])
                for pivot,b in sorted(basis.items()):
                    a=row[pivot]
                    if a:
                        row=[b[pivot]*x-a*y for x,y in zip(row,b)];g=math.gcd(*row)
                        if g:row=[x//g for x in row]
                pivot=next((k for k,v in enumerate(row) if v),None)
                if pivot is not None:
                    if row[pivot]<0:row=[-v for v in row]
                    basis[pivot]=row
                    if len(basis)==9:return 9
            return len(basis)
        def invalid(index,state):
            lo,hi=state;componentmask=spanmask=count=masssum=weighted=0
            for t,((i,j,a),(kind,m,p,r)) in enumerate(zip(terms,fs(index))):
                assert 0<=kind<=3 and 0<=m<=1024
                masses=(0,0) if kind==0 else (1024,0) if kind==1 else (m,0) if kind==2 else (1024-m,m)
                const=1024-sum(masses);assert const>=0 and sum(masses)+const==1024
                z=SLOT[i,j];left=max(lo[z],sum(lo[i:j]));right=min(hi[z],sum(hi[i:j]))
                for slot,(mass,anchor) in enumerate(zip(masses,(32*p,32*r))):
                    if not mass:continue
                    vl,vu=pt.get(anchor,(0,0))
                    if not (vu>0 and vl<=left<=anchor<=right<=vu):
                        componentmask|=1<<(2*t+slot);spanmask|=1<<t;count+=1;masssum+=mass;weighted+=a*mass
            assert count==componentmask.bit_count() and masssum<=39936 and weighted<2**64
            return componentmask,spanmask,count,spanmask.bit_count(),rank(spanmask),masssum,weighted
        def numeric_bits(index):
            bits=token('node_kind',0)
            for t,(kind,m,p,r) in enumerate(fs(index)):
                bits+=token('term'+str(t),kind)
                if kind==0:continue
                if kind>=2:bits+=token('mix',m)
                bits+=signed('point',p-lastpoint[t]);lastpoint[t]=p
                if kind==3:bits+=signed('second',r-p)
            code=struct.unpack_from('<I',codes,4*index)[0];assert code<10**8
            for j in range(8):bits+=token('tree'+str(j),code//(10**j)%10)
            return bits
        position=numeric=ordinal=0;parents=[];counts=collections.Counter();states=hashlib.sha256();candidate_hist=collections.Counter();joint_hist=collections.Counter();parent_hist=collections.Counter();repbits=[]
        def visit(path,state):
            nonlocal position,numeric,ordinal
            state=normal(state);nodeid=ordinal;ordinal+=1;states.update(struct.pack('<90I',*(state[0]+state[1])))
            kind=nodes[position];position+=1;counts['nodes']+=1;firstnumeric=numeric
            if kind==0:
                idx=numeric;numeric+=1;counts['numeric']+=1;own=numeric_bits(idx);repbits.append(own)
                assert invalid(idx,state)[2]==0,('original leaf guard invalid',path)
                return idx,1,1,0,own
            own=token('node_kind',kind)
            if kind==2:
                axis=nodes[position];position+=1;own+=token('axis',axis);counts['empty']+=1
                return None,0,1,0,own
            if kind==3:
                counts['reflection']+=1;return None,0,1,0,own
            assert kind==1;axis,cut=struct.unpack_from('<BI',nodes,position);position+=5;counts['branches']+=1
            own+=token('axis',axis)+signed('cut',cut-oldcut[axis]);oldcut[axis]=cut
            left=visit(path+'0',child(state,axis,cut,True));right=visit(path+'1',child(state,axis,cut,False))
            cand=[]
            for rep in [left[0],right[0]]:
                if rep is None:cand.append(None);continue
                data=invalid(rep,state);cand.append((rep,*data,repbits[rep]))
                candidate_hist[data[2]]+=1;joint_hist[(data[2],data[3],data[4])]+=1
            nonempty=[v for v in cand if v is not None and v[3]>0]
            parent_hist[('min_nonempty_distinct',min(v[4] for v in nonempty) if nonempty else -1)]+=1
            parent_hist[('min_nonempty_rank',min(v[5] for v in nonempty) if nonempty else -1)]+=1
            nnum=left[1]+right[1];nnodes=left[2]+right[2]+1;nbranch=left[3]+right[3]+1;bits=left[4]+right[4]+own
            parents.append((nodeid,ordinal,firstnumeric,nnum,nnodes,nbranch,own,bits,path,cand[0],cand[1]))
            if len(parents)%10000==0:report['parents_completed']=len(parents);save('whole_parent_supports_'+str(len(parents)))
            return left[0] if left[0] is not None else right[0],nnum,nnodes,nbranch,bits
        top=visit('r',meta['root'])
        assert position==len(nodes) and numeric==95615 and ordinal==191557 and len(parents)==95778
        assert counts=={'nodes':191557,'branches':95778,'numeric':95615,'empty':163,'reflection':1}
        assert states.hexdigest()==meta['normalized_states_sha256']
        for ch in hm['channels']:assert seen_tokens[ch['name']]==ch['tokens'] and seen_bits[ch['name']]==ch['coded_bits']
        assert sum(seen_bits.values())==top[4];totalbits=top[4]
        raw=bytearray(b'W10OP\x01'+struct.pack('<IH',len(parents),RSIZE))
        for nid,end,first,nnum,nnodes,nbranch,own,bits,path,left,right in parents:
            raw.extend(BASE.pack(nid,end,first,nnum,nnodes,nbranch,own,bits))
            for c in [left,right]:
                if c is None:raw.extend(CAND.pack(NO_REP,b'\x00'*10,0,0,0,0,0,0,0))
                else:
                    rep,cm,sm,nc,nd,nr,mass,weighted,rb=c;raw.extend(CAND.pack(rep,cm.to_bytes(10,'little'),sm,nc,nd,nr,mass,weighted,rb))
        assert len(raw)==12+RSIZE*95778 and len(raw)<FILELIMIT
        packed=gzip.compress(raw,compresslevel=9,mtime=0);RECORDS.write_bytes(packed)
        report['parent_records']={'path':RECORDS.relative_to(ROOT).as_posix(),'bytes':len(packed),'sha256':sha(RECORDS),
            'uncompressed_bytes':len(raw),'uncompressed_sha256':hashlib.sha256(raw).hexdigest(),'record_size':RSIZE,
            'schema':'header6=W10OP byte1; uint32records,uint16recordSize. Postorder parents: <IIIIIIQQ nodeID,endID_exclusive,firstNumeric,numericCount,subtreeNodes,subtreeBranches,ownAttributedBits,subtreeAttributedBits; two candidates <I10sQBBBHQL repID,invalidComponentMask78bitLE,invalidSpanMask39bit,componentCount,distinctCount,Qrank,massSum,ledgerWeightedMassNumerator,repAttributedBits; 0xffffffff rep absent.'}
        del raw
        size=json.loads(paths[9].read_bytes());base=size['exact_retained_base_wrapper_license_bytes'];reserve=128000;cap=2000000
        assert base==542851 and size['website_limit_bytes']==cap
        def equiv(removed,repbudget=0):
            # Original-stream proportional literal burden only. Keep all
            # old header/model/padding bits and all literal syntax overhead.
            binarybits=hm['binary_bytes']*8-removed+repbudget;assert 0<=binarybits<=hm['binary_bytes']*8
            return literal_overhead+(literal_chars*binarybits+hm['binary_bytes']*8-1)//(hm['binary_bytes']*8)
        rows=[];ordered=sorted(parents,key=lambda r:r[0]);prefixfiles=[]
        for family,metric,threshold in [('distinct1',4,1),('distinct2',4,2),('rank1',5,1),('rank2',5,2),('all_nonempty',4,39)]:
            skip=-1;chosen=[];covered=removedbits=removednodes=removedbranches=repbudget=0
            for row in ordered:
                nid,end,first,nnum,nnodes,nbranch,own,bits,path,left,right=row
                if nid<skip:continue
                eligible=[v for v in [left,right] if v is not None and v[3]>0 and v[metric]<=threshold]
                if not eligible:continue
                c=eligible[0];rep,cm,sm,nc,nd,nr,mass,weighted,rb=c;skip=end
                chosen.append({'path':path,'preorder_node_id':nid,'subtree_end_id_exclusive':end,'original_numeric_first':first,
                    'original_numeric_covered':nnum,'original_nodes':nnodes,'original_branches':nbranch,
                    'representative_original_numeric_index':rep,'invalid_component_mask':hex(cm),'invalid_distinct_span_mask':hex(sm),
                    'invalid_component_count':nc,'distinct_span_count':nd,'span_indicator_Qrank':nr,'invalid_mass_sum':mass,
                    'invalid_ledger_mass_numerator_over1024':weighted,'original_subtree_attributed_codeword_bits':bits,
                    'original_representative_attributed_codeword_bits':rb})
                covered+=nnum;removedbits+=bits;removednodes+=nnodes;removedbranches+=nbranch;repbudget+=rb
            assert covered<=95615 and removednodes<=191557 and removedbits<=totalbits
            assert all(a['subtree_end_id_exclusive']<=b['preorder_node_id'] for a,b in zip(chosen,chosen[1:]))
            ideal=equiv(removedbits);budget=equiv(removedbits,repbudget);headroom=cap-base-reserve-budget
            payload={'scope':'Conditional prefix-free replacement potential only. Every selected nonempty slice must still be proved; no new leaf is a mathematical certificate.',
                'family':family,'dimension_metric':'distinct spans' if metric==4 else 'exact rational rank of gap-span indicators',
                'dimension_threshold':threshold,'root_partition_coverage_conditional_on_each_replacement':True,'selected_prefixes':chosen}
            encoded=json.dumps(payload,separators=(',',':')).encode();assert len(encoded)<FILELIMIT
            path=HERE/('prefix-'+family+'.json.gz');assert not path.exists();path.write_bytes(gzip.compress(encoded,compresslevel=9,mtime=0))
            pf={'path':path.relative_to(ROOT).as_posix(),'bytes':path.stat().st_size,'sha256':sha(path),'uncompressed_bytes':len(encoded)};prefixfiles.append(pf)
            rows.append({'family':family,'prefix_free_replacements_assumed_provable':len(chosen),'original_numeric_covered_without_overlap':covered,
                'hypothetical_remaining_numeric_including_new_curve_leaves':95615-covered+len(chosen),
                'hypothetical_numeric_reduction':covered-len(chosen),'original_nodes_removed':removednodes,'original_branches_removed':removedbranches,
                'original_nodes_retained':191557-removednodes,'original_branch_records_retained':95778-removedbranches,
                'attributed_original_codeword_bits_removed':removedbits,'attributed_original_codeword_bits_retained':totalbits-removedbits,
                'old_representative_attributed_bit_budget':repbudget,'retained_base_source_bytes':base,'new_consumer_source_reserve_bytes':reserve,
                'ideal_zero_new_payload_literal_equivalent_bytes':ideal,'ideal_source_equivalent_total_bytes':base+reserve+ideal,
                'representative_payload_budget_literal_equivalent_bytes':budget,'budgeted_source_equivalent_before_curve_proofs':base+reserve+budget,
                'additional_curve_proof_payload_budget_total_bytes':headroom,
                'additional_curve_proof_payload_budget_mean_bytes':str(F(headroom,len(chosen))) if chosen else None,
                'curve_proof_payload_assumed_zero_only_in_explicit_ideal_scenario':True,'actual_curve_proof_payload_known':False,
                'new_decodable_stream_or_source_feasibility_proven':False,'selection_packet':pf})
        report.update({'complete_one_geometry_and_support_pass':True,'counts':dict(counts),'normalized_states_sha256':states.hexdigest(),
            'candidate_count':sum(candidate_hist.values()),'invalid_component_histogram':dict(sorted(candidate_hist.items())),
            'joint_component_distinct_rank_histogram':[[a,b,c,n] for (a,b,c),n in sorted(joint_hist.items())],
            'parent_min_nonempty_dimension_histogram':[[kind,d,n] for (kind,d),n in sorted(parent_hist.items())],
            'J0_candidate_count_not_a_slice_opportunity':candidate_hist[0],
            'representative_rule':'Each child original-subtree leftmost numeric; at most one per side. No hypothetical success is propagated to choose a new representative. Per-family eligible parent chooses left before right.',
            'mass_rule':'k0 const1024; k1 p1024; k2 p*m+const*(1024-m); k3 p*(1024-m)+r*m. Only positive support masses are checked individually.',
            'dimension_rule':'Distinct actual spans and exact rational rank are separate. Same-span invalid components retain their individual masses; rank is not a separable-curve proof.',
            'candidate_guard_rule':'vu>0 and vl<=max(parent_lo_span,sum adjacent lo)<=anchor<=min(parent_hi_span,sum adjacent hi)<=vu',
            'prefix_results':rows,'prefix_files':prefixfiles,'original_all_codeword_bits':totalbits,
            'original_all_field_literal_source_bytes':hm['data_source_bytes'],'fixed_literal_syntax_overhead_bytes':literal_overhead,
            'literal_accounting_formula':'syntaxOverhead+ceil(originalLiteralChars*(originalBinaryBits-removedAttributedBits+oldRepBitBudget)/originalBinaryBits). This is fixed-original-stream proportional engineering burden, not a new encoding.',
            'source_accounting_caveat':'point and cut deltas cross records; removing a subtree or moving a representative changes later symbols/varints and may require absent Huffman codes. No resynchronization, decoder, curve payload or valid new source is supplied.',
            'future_slice_obligations':['Keep original FS-decoded DualMove AMOUNTS fixed; tree_code alone cannot preserve them after changing FS slopes.',
                'Recompute whole-parent runDual/CpCm and coordinate residual; none computed here.',
                'Use actual safe affine V+dminus*(s-L0)-dplus*(p-L0), with mcp/mcn offsets; do not replace by V+dminus*(s-p).',
                'Preserve all component masses/1024 and old actual kernel identity; future curve and partial consumer soundness remain unproved.'],
            'rank_cache':list(rank.cache_info()),'raw_file_limit_bytes':FILELIMIT})
        assert not any(n.split('.')[0] in ['numpy','scipy','scs'] for n in sys.modules)
        save('one_read_only_whole_W10_opportunity_pass_complete_no_new_certificates')
        print(json.dumps({'phase':report['phase'],'elapsed_milliseconds':report['elapsed_milliseconds'],'candidate_count':report['candidate_count'],
            'J0_count':report['J0_candidate_count_not_a_slice_opportunity'],'prefix_results':[{k:r[k] for k in ['family','prefix_free_replacements_assumed_provable',
                'original_numeric_covered_without_overlap','hypothetical_numeric_reduction','budgeted_source_equivalent_before_curve_proofs','additional_curve_proof_payload_budget_total_bytes']} for r in rows]}),flush=True)
    except BaseException as exc:
        report.update({'exception':repr(exc),'traceback':traceback.format_exc()});save('opportunity_pass_stopped_without_retry');raise
if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
