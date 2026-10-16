"""Project nineteen closed finite-move-cut regions to a compact ancestor archive."""
from pathlib import Path
import gzip,hashlib,json
import cover_compact_codec as c
import cover_global_cut_codec as cc
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    sources={};proofs={}
    for name in ['cover-global-cut-contractor','cover-global-cut-full-contractor','cover-global-cut-hypograph','cover-global-cut-intersection']:
        raw=(HERE/(name+'.json')).read_bytes();receipt=json.loads((HERE/(name+'-replay.json')).read_bytes())
        assert receipt['all_passed'] and receipt['input_sha256']==sha(raw);sources[name]=sha(raw);proofs[name]=json.loads(raw)
    oldraw=(HERE/'cover-sublevel-obbt.json').read_bytes();old=json.loads(oldraw);lookup={r['path']:r for r in old['contractions']}
    full=proofs['cover-global-cut-full-contractor'];fl={r['path']:r for r in full['contractions']}
    hypo=proofs['cover-global-cut-hypograph'];hl={r['path']:r for r in hypo['rows']};choices={}
    def add(path,row):
        if path not in choices or len(json.dumps(row,separators=(',',':')))<len(json.dumps(choices[path],separators=(',',':'))):choices[path]=row
    for name in ['cover-global-cut-contractor','cover-global-cut-full-contractor','cover-global-cut-hypograph']:
        doc=proofs[name]
        for r in doc['rows' if name.endswith('hypograph') else 'contractions']:
            if not r['result']:continue
            prior=fl[r['path']]['prior_newton_steps'] if name.endswith('hypograph') else r['prior_newton_steps']
            add(r['path'],{'kind':'single_chain','source_document':name,'source_row_sha256':c.digest(r),
              'prior_newton':[c.pack_newton(s) for s in prior],'cuts':[cc.pack_step(s) for s in r['steps']],
              'leaf':c.pack_leaf(r['result'])})
    for r in proofs['cover-global-cut-intersection']['rows']:
        if not r['result']:continue
        p=r['path'];f=fl[p];h=hl[p]
        add(p,{'kind':'intersection_chain','source_document':'cover-global-cut-intersection','source_row_sha256':c.digest(r),
          'prior_newton':[c.pack_newton(s) for s in f['prior_newton_steps']],
          'single_cuts':[cc.pack_step(s) for s in f['steps']],'mixed_cuts':[cc.pack_step(s) for s in h['steps']],
          'newton':[c.pack_newton(s) for s in r['Newton_steps']],'leaf':c.pack_leaf(r['result'])})
    paths=set(choices);assert len(paths)==19 and not any(p!=q and p.startswith(q) for p in paths for q in paths)
    prior_moves=set()
    for name in ['cover-integer-move-concave.json','cover-global-move-epigraph.json']:
        prior_moves.update(r['path'] for r in json.loads((HERE/name).read_bytes())['exclusions'])
    joint={r['path'] for r in json.loads((HERE/'cover-joint-after-obbt.json').read_bytes())['exclusions']}
    assert len(prior_moves)==24 and not any(p.startswith(q) or q.startswith(p) for p in paths for q in prior_moves|joint)
    prefixraw=gzip.decompress((HERE/'cover-correlated-direction.input.json.gz').read_bytes());prefix=json.loads(prefixraw);branches={r['path']:r for r in prefix['branches']}
    needed={p[:k] for p in paths for k in range(1,len(p)+1)};ancestors=[branches[p] for p in sorted(needed-paths)]
    descendants=[r for r in prefix['branches'] if any(r['path'].startswith(p) for p in paths)];cases=[]
    for p,row in sorted(choices.items()):
        original=lookup[p];assert original['result'] is None
        cases.append({'path':p,'obbt':c.pack_obbt({k:original[k] for k in ['old_cell','new_cell','certificates']}),**row})
    data={'scope':__doc__,'source_proofs':sources,'source_OBBT_sha256':sha(oldraw),'source_old_prefix_sha256':sha(prefixraw),
      'source_root':prefix['root'],'source_root_target':prefix['target'],'target_numerator':full['receipt']['target_numerator'],
      'ancestors':ancestors,'old_descendant_branches':descendants,'cases':cases,'prior_move_paths':sorted(prior_moves),'prior_joint_paths':sorted(joint),
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode();packed=gzip.compress(raw,compresslevel=9,mtime=0)
    dest=HERE/'cover-global-cut-union-evidence';dest.mkdir(exist_ok=True);(dest/'proof.json.gz').write_bytes(packed)
    pins=json.loads((HERE/'cover-obbt-archive/manifest.json').read_bytes())['sources']
    names=['cover_compact_codec.py','cover_flow_basis.py','cover_global_cut_codec.py','cover_global_cut_full_verify.py',
      'cover_global_cut_hypograph_verify.py','cover_integer_move_verify.py','cover_integer_move_concave_verify.py',
      'cover_global_move_epigraph_verify.py','cover_newwindow_gram_replay.py','cover_global_cut_archive_replay.py']
    for name in names:p=HERE/name;pins[str(p.relative_to(ROOT)).replace('\\','/')]=sha(p.read_bytes())
    for name,digest in pins.items():assert sha((ROOT/name).read_bytes())==digest,name
    out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'sources':pins,'file':'proof.json.gz','bytes':len(packed),
      'sha256':sha(packed),'uncompressed_bytes':len(raw),'uncompressed_sha256':sha(raw),'new_closed_regions':19,
      'new_old_branches_covered':len(descendants),'prior_moves':24,'combined_topmost_global_regions':43,'joint7_overlap':0,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False}
    (dest/'manifest.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in out.items() if k!='sources'}),flush=True)
if __name__=='__main__':main()
