"""Prepare a new, separate mixed-cover replay surface without running Lean/Nano."""
from pathlib import Path
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--subtree-module')
 ap.add_argument('--subtree-root')
 ap.add_argument('--graph-cover', action='store_true')
 ap.add_argument('--lifted-pilot', action='store_true')
 ap.add_argument('--record-ordinary', action='store_true')
 args=ap.parse_args()
 assert bool(args.subtree_module)==bool(args.subtree_root)
 prefix='StructuralGoal20261016.'
 module=prefix+'WindowMixedIndependentRoots'
 cover='WindowGraphCover' if args.graph_cover else 'WindowMixedCover'
 imports=[prefix+'WindowCurvatureLeavesAll',prefix+cover]
 roots=[prefix+'WindowCurvatureLeavesAll.exclude',prefix+cover+'.global_floor880']
 if args.subtree_module:
  assert args.subtree_module.startswith(prefix) and args.subtree_root.startswith(prefix)
  imports.append(args.subtree_module)
  roots.append(args.subtree_root)
 if args.lifted_pilot:
  imports.append(prefix+'WindowLiftedPilot')
  roots.append(prefix+'WindowLiftedPilot.exclude')
 known={r['module']:r for r in json.loads((HERE/'lean_verification.json').read_text())['modules']}
 for imported in imports:
  row=known[imported]
  assert row['passed'] and row['source_unchanged'], imported
  assert row['source_sha256']==hashlib.sha256((ROOT/(imported.replace('.','/')+'.lean')).read_bytes()).hexdigest(), imported
 source='/- SPDX-License-Identifier: Apache-2.0\n'
 source+='Partial mixed-cover milestone replay. No complete global tree is asserted.\n'
 source+='The global-floor transfer retains its explicit complete-tree Bool premise.\n-/\n'
 source+=''.join('import '+m+'\n' for m in dict.fromkeys(imports))
 source+='set_option Elab.async false\nset_option pp.fullNames true\n'
 source+=''.join('#print axioms '+n+'\n' for n in roots)
 target=ROOT/'StructuralGoal20261016/WindowMixedIndependentRoots.lean'
 target.write_text(source,encoding='utf8')
 manifest={'scope':'PARTIAL mixed-cover milestone: actual negative-curvature exclusions and a concrete global-floor transfer with its complete-tree Boolean premise still explicit. Local subtree/actual lifted-graph pilot roots are included only when requested after ordinary-kernel success. Self replay, not a website statement comparison.',
  'module':module,'roots':roots,'source_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),
  'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
  'subtree_root':args.subtree_root,'local_subtree_included':bool(args.subtree_root),
  'graph_cover_transfer_included':args.graph_cover,'actual_lifted_graph_pilot_included':args.lifted_pilot,
  'ordinary_compile_proven':False,'independent_nanoda_proven':False,'global_energy_floor_proven':False,
  'unconditional_counting_proven':False,'submission_ready':False,
  'old_22_root_archive_unchanged':True,'heavy_replay_started':False}
 if args.record_ordinary:
  row=known[module]
  assert row['passed'] and row['source_unchanged'] and row['source_sha256']==manifest['source_sha256']
  assert hashlib.sha256((HERE/row['log']).read_bytes()).hexdigest()==row['log_sha256']
  manifest['ordinary_compile_proven']=True
  manifest['ordinary_receipt']={k:row[k] for k in ['source_sha256','olean_sha256','log','log_sha256','whole_process_seconds']}
 (HERE/'window-mixed-independent-roots.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({'module':module,'roots':len(roots),'source_sha256':manifest['source_sha256'],'prepared_only':True}))

if __name__=='__main__':main()
