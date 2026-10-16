"""Generate a storage-only variant; frozen search and verifier stay untouched."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).parent

def change(source,old,new):
    assert source.count(old)==1,(source.count(old),old)
    return source.replace(old,new)

def main():
    original=HERE/'window_obbt_newton_cover.py';source=original.read_text(encoding='utf8')
    source=change(source,'import cover_sublevel_obbt_api as obbt','import cover_sublevel_obbt_api as obbt\nimport cover_compact_codec as codec')
    source=change(source,"default=HERE/'window-obbt-newton-cover.json'","default=HERE/'window-compact-obbt-cover.json'")
    source=change(source,"ROOT/'research-20261016-followup/global_periodic_upper_bound.py']","ROOT/'research-20261016-followup/global_periodic_upper_bound.py',\n      HERE/'cover_compact_codec.py',HERE/'cover_flow_basis.py',HERE/'cover_correlated_replay.py',HERE/'cover_contractor_verify.py']")
    source=change(source,"assert old['target']==args.floor and old['root']==[list(x) for x in w.root()]","assert old['target']==args.floor and old['root']==[list(x) for x in w.root()]\n        if old['format']=='RelevantBelow-KKT-OBBT-v1':old=codec.pack_document(old)\n        assert old['format']=='RelevantBelow-KKT-OBBT-compact-v2'")
    source=change(source,"'format':'RelevantBelow-KKT-OBBT-v1'","'format':'RelevantBelow-KKT-OBBT-compact-v2'")
    source=change(source,"sum(len(v['certificates']) for v in sublevel.values())","sum(len(v['b']) for v in sublevel.values())")
    source=change(source,"sublevel[path]={'old_cell':state,'new_cell':refined,'certificates':bounds}","sublevel[path]=codec.pack_obbt({'old_cell':state,'new_cell':refined,'certificates':bounds})")
    source=change(source,"contractions.setdefault(path,[]).extend(steps)","contractions.setdefault(path,[]).extend(codec.pack_newton(step) for step in steps)")
    source=change(source,"accepted.append({'path':path,'depth':depth,'kind':kind,'result':result})","accepted.append(codec.pack_leaf({'path':path,'depth':depth,'kind':kind,'result':result}))")
    source=source.replace('Complete-domain discovery with sublevel epigraph OBBT and KKT Newton contraction.','Complete-domain OBBT/Newton discovery with compact, lossless witnesses.')
    runner=HERE/'window_compact_obbt_cover.py';runner.write_text(source,encoding='utf8',newline='\n')
    original_replay=HERE/'window_obbt_newton_replay.py';source=original_replay.read_text(encoding='utf8')
    source=change(source,'import cover_sublevel_obbt_verify_api as obbt','import cover_sublevel_obbt_verify_api as obbt\nimport cover_compact_codec as codec')
    source=change(source,"data['format']=='RelevantBelow-KKT-OBBT-v1'","data['format']=='RelevantBelow-KKT-OBBT-compact-v2'")
    source=change(source,"usedsublevel.add(path);counts['sublevel_paths']+=1;counts['sublevel_bounds']+=len(sublevel[path]['certificates'])\n            state=obbt.verify_step(state,sublevel[path],g.TARGET)","usedsublevel.add(path);counts['sublevel_paths']+=1\n            decoded=codec.unpack_obbt(state,sublevel[path],g.TARGET,w)\n            counts['sublevel_bounds']+=len(decoded['certificates'])\n            state=obbt.verify_step(state,decoded,g.TARGET)")
    source=change(source,'for step in contractions[path]:\n                assert state is not None\n                state=newton.verify_step(state,step,w.P,table)',
      'for packed_step in contractions[path]:\n                assert state is not None\n                step=codec.unpack_newton(state,packed_step,w)\n                state=newton.verify_step(state,step,w.P,table)')
    source=change(source,"row=leaves[path];kind=row['kind']","row=codec.unpack_leaf(state,leaves[path],w);kind=row['kind']")
    source=change(source,"default=HERE/'window-obbt-newton-replay.json'","default=HERE/'window-compact-obbt-replay.json'")
    source=source.replace('Replay a full/partial KKT-minimizer tree with explicit contraction maps.','Decode and replay a compact partial/full KKT-minimizer partition.')
    replay=HERE/'window_compact_obbt_replay.py';replay.write_text(source,encoding='utf8',newline='\n')
    files=[original,original_replay,runner,replay,HERE/'cover_compact_codec.py']
    out={'scope':__doc__,'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
      'storage_only_change':True,'mathematical_search_order_changed':False,'complete_global_cover':False,'new_zero_proportion_proven':False}
    (HERE/'cover-compact-variant-generated.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out))
if __name__=='__main__':main()
