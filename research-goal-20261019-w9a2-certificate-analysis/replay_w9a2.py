"""W9A2 deterministic replay of all 48 original finite certificate trees.

Checks packed decoding, tree topology, active tangent interval containment,
branch boxes, reflection leaves, numeric inequalities and agreement with
the new printed mcheckP AST. No ready/cut contracts exist in the new source.
True-WZ analytic/root inequalities remain source proof dependencies.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
from fractions import Fraction
import gzip
import json
import os
import re
import sys
import time
import traceback

import packing_parser_w9a2 as parser
import record_math_w9a2 as math

sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'baseline-replay.json'
FAIL=HERE/'baseline-math-failure.json'
START=HERE/'baseline-math-started.json'
TRACE=HERE/'baseline-events.jsonl.gz'
PROGRESS=HERE/'baseline-progress.json'
SOURCE=parser.SOURCE
SOURCE_SHA=parser.SOURCE_SHA


def pin(path):return sha256(path.read_bytes()).hexdigest()
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode('ascii')
def state_flat(state):return tuple(v for pair in zip(state[0],state[1]) for v in pair)+(0,)
def state_hash(state):return sha256(canonical(state_flat(state))).hexdigest()


def rss():
    if os.name!='nt':return None
    import ctypes
    class PMC(ctypes.Structure):
        _fields_=[('cb',ctypes.c_ulong),('PageFaultCount',ctypes.c_ulong),('PeakWorkingSetSize',ctypes.c_size_t),
                  ('WorkingSetSize',ctypes.c_size_t),('QuotaPeakPagedPoolUsage',ctypes.c_size_t),('QuotaPagedPoolUsage',ctypes.c_size_t),
                  ('QuotaPeakNonPagedPoolUsage',ctypes.c_size_t),('QuotaNonPagedPoolUsage',ctypes.c_size_t),
                  ('PagefileUsage',ctypes.c_size_t),('PeakPagefileUsage',ctypes.c_size_t)]
    pm=PMC();pm.cb=ctypes.sizeof(pm)
    ctypes.windll.kernel32.GetCurrentProcess.restype=ctypes.c_void_p
    h=ctypes.windll.kernel32.GetCurrentProcess()
    assert ctypes.windll.psapi.GetProcessMemoryInfo(ctypes.c_void_p(h),ctypes.byref(pm),pm.cb)
    return {'current_bytes':pm.WorkingSetSize,'peak_bytes':pm.PeakWorkingSetSize}


def ycheck(word,offset,state,stats):
    scan=offset
    for _ in range(42):
        if not ((word>>scan)&1):break
        tag=(word>>(scan+1))&31
        assert tag<28,('ydec_tag',tag,scan)
        scan+=21;stats['valid_ydec_entries']+=1


class FullWalker:
    def __init__(self,r,model,stream,digest,progress):
        self.r=r;self.model=model;self.blocks=model['WL'][r]
        self.stream=stream;self.digest=digest;self.progress=progress
        self.count=Counter();self.nodes={};self.minmargin=None;self.minpos=None
        self.last=None

    def bits(self,pos):return (self.blocks.get(pos//32768,0)>>(pos%32768))&((1<<480)-1)

    def emit(self,event):
        raw=canonical(event);self.stream.write(raw);self.digest.update(raw);self.count['trace_events']+=1

    def numeric(self,state,word,pos):
        lo,hi=state
        assert all(l<=u for l,u in zip(lo[:8],hi[:8])),('numeric_box',self.r,pos)
        offset=0
        for i,j,_a,_slot in self.model['TS']:
            L,U=math.term_bounds(state,i,j);assert L<=U
            (kind,lam,p,q),offset=math.dec(word,offset,L,U)
            assert kind in range(4) and 0<=lam<=1024
            self.count['term_decode_checks']+=1
            for amount,point in zip(math.weights(kind,lam),(p,q)):
                if amount==0:continue
                assert point in self.model['PTraw'],('point_absent',self.r,pos,point)
                packed=self.model['PTraw'][point]
                vl=max(0,point-((packed>>96)&((1<<20)-1)))
                vu=point+(packed>>116)
                assert 1<=vu and vl<=L<=point<=U<=vu,('mokI',self.r,pos,i,j,amount,point,vl,L,U,vu)
                self.count['active_mokI_checks']+=1
                self.count['active_tangent_mass']+=amount
        ycheck(word,offset,state,self.count)
        compact,consumed=math.calc(state,word)
        direct=math.direct_mcheck_margin(state,word)
        assert compact==direct,('mcheckP_AST_mismatch',self.r,pos,compact,direct)
        assert compact>=0,('original_floor_failed',self.r,pos,compact)
        self.count['numeric_leaves']+=1;self.count['direct_AST_comparisons']+=1
        if self.minmargin is None or compact<self.minmargin:self.minmargin,self.minpos=compact,pos
        if self.count['numeric_leaves']%250==0:self.progress(self.r,pos,self.count)
        return consumed,compact

    def walk(self,state,pos=1,fuel=128):
        self.last={'root':self.r,'position':pos,'fuel':fuel,'state_sha256':state_hash(state)}
        assert fuel>0,('fuel',self.r,pos)
        assert pos not in self.nodes,('duplicate_node_position',self.r,pos)
        assert max(state[0]+state[1])<math.BB and min(state[0]+state[1])>=0
        entry={'state':state_flat(state),'fuel':fuel}
        self.nodes[pos]=entry;self.count['nodes']+=1
        w=self.bits(pos)
        if w&1:
            ax=(w>>1)&63;md=(w>>7)&1
            assert ax<len(math.ALL),('axis',self.r,pos,ax)
            i,j=math.ALL[ax];q=math.bcut(state[0][ax],state[1][ax]) if md else (state[0][ax]+state[1][ax])>>1
            assert 0<=q<math.BB
            left=math.split(state,i,j,q,True);right=math.split(state,i,j,q,False)
            self.count['split_nat_sub_preconditions']+=2
            endleft,heightleft=self.walk(left,pos+8,fuel-1)
            end,heightright=self.walk(right,endleft,fuel-1)
            height=1+max(heightleft,heightright);self.count['branches']+=1
            entry.update(kind='branch',axis=ax,mode=md,cut=q,left=pos+8,right=endleft,end=end,height=height)
            self.emit({'root':self.r,'pos':pos,'kind':'branch','axis':ax,'mode':md,'cut':q,'left':pos+8,'right':endleft,'end':end,'state_sha256':self.last_state_hash(entry)})
            return end,height
        self.count['terminal_leaves']+=1
        margin=None
        if state[1][7]<state[0][0]:
            kind='reflection';end=pos+1;self.count['reflection_leaves']+=1
        elif (w>>1)&1:
            kind='farkas';ycheck(w>>2,0,state,self.count)
            P,S,cp,cm,consumed=math.ydec(w>>2,0,state)
            value=cm-cp-sum(max(0,p-s)*max(0,u-l) for s,p,u,l in zip(S,P,state[1][:8],state[0][:8]))
            assert value>0,('farkas',self.r,pos,value)
            end=pos+2+consumed;self.count['farkas_leaves']+=1;margin=value
        else:
            kind='numeric';consumed,margin=self.numeric(state,w>>2,pos);end=pos+2+consumed
        entry.update(kind=kind,end=end,height=1,margin=margin)
        self.emit({'root':self.r,'pos':pos,'kind':kind,'end':end,'margin':margin,'state_sha256':self.last_state_hash(entry)})
        return end,1

    @staticmethod
    def last_state_hash(entry):return sha256(canonical(entry['state'])).hexdigest()

    def cutwalk(self,state,pos,fuel,cuts,stats):
        assert fuel>0,('ready_fuel',self.r,pos)
        assert pos in self.nodes,('ready_position_not_in_plain_tree',self.r,pos)
        node=self.nodes[pos]
        assert tuple(state)==node['state'],('ready_state_changed',self.r,pos)
        stats['cutwalk_state_equalities']+=1
        for p,name,end in cuts:
            if p==pos:
                assert tuple(state)==self.model['states'][name]
                assert end==node['end']
                stats['cut_hits']+=1
                return end
        if node['kind']=='branch':
            mid=self.cutwalk(self.nodes[node['left']]['state'],node['left'],fuel-1,cuts,stats)
            assert mid==node['right']
            return self.cutwalk(self.nodes[mid]['state'],mid,fuel-1,cuts,stats)
        return node['end']

    def ready_contracts(self):
        contracts=[];covered=set();stats=Counter()
        records=sorted((c for c in self.model['cursors'] if c['root']==self.r),key=lambda c:c['index'])
        assert [c['index'] for c in records]==list(range(len(records)))
        for rec in records:
            cuts=self.model['cutlists'][rec['cuts']]
            assert all(name in covered for _pos,name,_end in cuts),('cut_dependency_order',rec['name'])
            state=self.model['states'][rec['state']]
            actual=self.cutwalk(state,rec['pos'],rec['fuel'],cuts,stats)
            assert actual==rec['expected'],('ready_end',rec['name'],actual,rec['expected'])
            assert actual!=0 and state[-1]==0
            covered.add(rec['state'])
            contracts.append({**rec,'actual':actual,'state_sha256':sha256(canonical(state)).hexdigest(),'passed':True})
        rootrec=self.model['roots'][self.r]
        rootcuts=self.model['cutlists'][f'ready{self.r}_cuts{rootrec["cuts"]}']
        assert all(name in covered for _p,name,_e in rootcuts)
        actual=self.cutwalk(self.nodes[1]['state'],1,rootrec['fuel'],rootcuts,stats)
        assert actual==rootrec['expected']
        stats['parent_cursor_checks']+=1;stats['nested_cursor_checks']+=len(records)
        return contracts,stats


def root_guards_static(model):
    """Replay no-new-kernel root guards; mark printed WZ analytic/numeric gap.

    True COV WZ guards are retained as explicit source proof dependencies.
    This stage does not silently substitute the old12-mode cell_wz routine.
    """
    adjacency=[i for i,e in enumerate(model['TS']) if e[1]==e[0]+1]
    assert [model['TS'][i][:2] for i in adjacency]==[(r,r+1) for r in range(8)]
    rows=[]
    for r in range(8):
        pos=16384
        for lo,hi,truth in model['COV'][r]:
            assert lo==pos and lo<=hi<1048576
            rows.append({'kind':'cover','gap':r,'lo':lo,'hi':hi,'truth':truth,
                         'WZ_integer_check_replayed':False if truth else None,
                         'source_analytic_and_finite_WZ_contract_retained':bool(truth)})
            pos=hi
        assert pos==model['SMAX'][r]
        large=model['BS'][r]*model['SMAX'][r]//32768
        small=model['TS'][adjacency[r]][2]//4
        assert large>=model['CN'] and small>=model['CN']
        rows.extend([{'kind':'pressure_tail','gap':r,'value':large,'passed':True},
                     {'kind':'small_gap','gap':r,'value':small,'passed':True}])
    assert 8*1048576<=model['rcM']
    return {'rows':rows,'topology_and_tail_small_arithmetic_passed':True,
            'all_COV_true_WZ_integer_values_replayed':False,
            'scope':'Root outside true-WZ integer guards not independently recalculated here. Their explicit source coverChk proof remains a dependency. No old-kernel constants are used.'}


def main():
    start=time.monotonic();model=parser.load_model();math.configure(model)
    assert not OUT.exists(), 'immutable output already exists'
    tree=math.direct_mcheck_tree();assert tree[0]=='Nat.ble'
    rootguards=root_guards_static(model);totals=Counter();roots=[];leaves=[];trace_digest=sha256()
    def progress(r,pos,c):
        print(json.dumps({'root':r,'position':pos,'counts':dict(c),'seconds':time.monotonic()-start}),flush=True)
    with gzip.open(HERE/'walk-events.jsonl.gz','wb') as stream:
        for r in range(48):
            walker=FullWalker(r,model,stream,trace_digest,progress)
            end,height=walker.walk(math.root(model['roots'][r]['indices']))
            assert end==model['roots'][r]['expected'], (r,end,model['roots'][r]['expected'])
            roots.append({'root':r,'indices':model['roots'][r]['indices'],'end':end,'height':height,'counts':dict(walker.count),'minimum_margin':walker.minmargin,'minpos':walker.minpos})
            totals.update(walker.count)
            for pos,node in walker.nodes.items():
                if node['kind']=='numeric':
                    lo=node['state'][0:16:2];hi=node['state'][1:16:2]
                    leaves.append({'root':r,'pos':pos,'margin':node['margin'],'lo':lo,'hi':hi,'state':node['state'],'end':node['end']})
            print(json.dumps({'root_complete':r,'numeric':walker.count['numeric_leaves'],'seconds':time.monotonic()-start}),flush=True)
    leaves.sort(key=lambda x:(x['margin'],x['root'],x['pos']))
    with gzip.open(HERE/'numeric-leaves-sorted.jsonl.gz','wt',encoding='ascii') as f:
        for leaf in leaves:f.write(json.dumps(leaf,separators=(',',':'))+'\n')
    result={'passed':True,'source':SOURCE.relative_to(ROOT).as_posix(),'source_sha256':SOURCE_SHA,
      'seconds':time.monotonic()-start,'CN':model['CN'],'SA':model['SA'],'SLOPE':math.SLOPE,
      'counts':dict(totals),'roots':roots,'minimum20':leaves[:20],
      'rootguards':rootguards,'trace_canonical_sha256':trace_digest.hexdigest(),
      'dispatch_identity_checks':model['dispatch_checks'],'packing_count':len(model['packing']),
      'tangent_entries':len(model['PTraw']),'scope':'Integer arithmetic traversal/decoding, active tangent interval guards, Farkas guards and numeric mcheckP AST comparison only. Existing Lean soundness of LB/PT analytic bounds and true-WZ root intervals retained. No LP, floating evaluation, Lean or new kernel run.'}
    OUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'passed':True,'seconds':result['seconds'],'counts':dict(totals),'minima':[{k:x[k] for k in ['root','pos','margin','lo','hi']} for x in leaves[:4]]}),flush=True)
if __name__=='__main__':main()
