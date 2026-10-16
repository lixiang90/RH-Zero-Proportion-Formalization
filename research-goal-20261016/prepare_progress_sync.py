"""Stage a reproducible research checkpoint, excluding evolving/failed proofs."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def main():
    receipt=json.loads((HERE/'ordinary-verified-current.json').read_bytes())
    files=['.gitattributes','README.md','submission/goal-20261016/STATUS.zh.md']
    names=['README.md','ordinary-verified-current.json','seal_ordinary_progress.py','prepare_progress_sync.py',
      'window_interval_kernel.py','window_interval_kernel.json','window_jet_crosscheck.py','window_jet_crosscheck.json',
      'window_global_cover.py','window_lower_global_cover.py','window_make_lower_variant.py','window_make_lower_variant.json',
      'window_minimizer_cover.py','window_correlated_minimizer_cover.py','window_make_correlated_variant.py','window_make_correlated_variant.json',
      'window_cover_replay.py','window_direction_probe.py','window_snapshot.py',
      'cover_newjet.py','cover_newjet.json','cover_correlated_api.py','cover_correlated_direction.py',
      'cover_correlated_verify.py','cover_correlated_replay.py','cover_contractor_api.py','cover_contractor_verify.py',
      'cover_newton_contractor.py','cover_projection_archive.py','cover_archive_replay.py',
      'lean_generate.py','lean_verify.py',
      'ordinary-axiom-audit-dependencies.json',
      'window_normalized_interval.py','window_normalized_interval.json',
      'window_normalized_grid_audit.py','window_normalized_grid_audit.json',
      'window_lean_precision_probe.py','window_lean_precision_probe.json',
      'window_lean_precision_bridge_audit.py','window_lean_precision_bridge_audit.json',
      'cover_sublevel_contractor.py','cover_sublevel_verify.py','cover_sublevel_api.py','cover_sublevel_verify_api.py',
      'cover_sublevel_obbt.py','cover_sublevel_obbt_verify.py','cover_sublevel_obbt_api.py','cover_sublevel_obbt_verify_api.py',
      'cover-sublevel-obbt-replay.json','cover_obbt_archive.py','cover_obbt_archive_replay.py',
      'cover_obbt_prune.py','cover-obbt-pruned-replay.json','cover_obbt_note.md',
      'cover_flow_basis.py','cover-flow-basis-probe.json','cover_flow_basis_replay.py',
      'cover_flow_basis_archive_replay.py','cover_flow_basis_lean_pilot.py','cover_flow_basis_lean_pilot.json',
      'cover_newwindow_gram.py','cover_newwindow_gram_replay.py','cover-newwindow-gram.json','cover-newwindow-gram-replay.json',
      'cover_emit_window_gram.py','cover_emit_window_transfer.py','cover_gram_basin_api.py',
      'window_newton_gram_cover.py','window_newton_gram_cover_cached.py','window_newton_gram_replay.py',
      'cover_make_obbt_variant.py','window_obbt_newton_cover.py','window_obbt_newton_replay.py',
      'window_nine_point_search.py','window-nine-point-search.json','window-nine-point-search.npz',
      'window_nine_point_joint_search.py','window-nine-point-joint-search.json','window-nine-point-joint-search.npz',
      'window_nine_point_rationalize.py','window-nine-point-rational.json',
      'window_nine_point_cover.py','window-nine-point-convex.json','window_nine_point_replay.py','window_nine_point_snapshot.py',
      'window_generate_asymptotic.py','window_generate_counting_base.py','window_generate_discrete.py',
      'window_generate_matching.py','window_generate_separated.py','window_generate_uniform.py',
      'window_generate_jet_tables.py','window_generate_convexity_checks.py',
      'window_adjacent_localization_probe.py','window_adjacent_localization_probe.json',
      'window_local_range_probe.py','window_local_range_probe.json',
      'window_range_ledger_search.py','window-range-ledger-n10-r6.json','window-range-ledger-n10-r6.npz',
      'window_generate_fixed_kernel.py','window_fixed_kernel_modules.json',
      'window_generate_fixed_tables_all.py','window_generate_anchor_certificate.py','window_anchor_certificate_modules.json',
      'window_generate_anchor_all.py','window_generate_linear_convexity_checks.py','window_linear_convexity_modules.json',
      'window_linear_bernstein_audit.json','window_generate_bernstein_weights.py','window_bernstein_weight_modules.json',
      'window_generate_counting.py','window_generate_counting_geometry.py',
      'window_generate_independent_roots.py','window-independent-roots.json','window_independent_replay.py']
    files+=['research-goal-20261016/'+s for s in names]
    # This immutable manifest pins the reviewed compact-prefix recovery and
    # replay artifacts, without adding the live 148+ MB search checkpoint.
    compact_manifest=HERE/'cover-compact-progress-files.json'
    assert hashlib.sha256(compact_manifest.read_bytes()).hexdigest()=='bc63e6decdd5c286362c1a4f5bb6fee85bd099b2e3fa3516b239a9b4d47cbed2'
    compact=json.loads(compact_manifest.read_bytes())
    for path,row in compact['files'].items():
        p=HERE/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/cover-compact-progress-files.json')
    move_manifest=HERE/'cover-global-move-progress-files.json'
    assert hashlib.sha256(move_manifest.read_bytes()).hexdigest()=='c63e29e6cccd543fb710cd35d9c3ed8ab4094c750c6dccd0f52c301ec138ac38'
    moves=json.loads(move_manifest.read_bytes())
    for path,row in moves['files'].items():
        p=HERE/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/cover-global-move-progress-files.json')
    followup_manifest=HERE/'cover-global-move-epigraph-followup-files.json'
    assert hashlib.sha256(followup_manifest.read_bytes()).hexdigest()=='1b7793e17f5570219f9dcbc6218ae092933ed0ec9b8afed104e22dadb18d595a'
    followup=json.loads(followup_manifest.read_bytes())
    for path,row in followup['files'].items():
        p=HERE/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/cover-global-move-epigraph-followup-files.json')
    independent_folder=HERE/'window-independent-20261017'
    independent_manifest=independent_folder/'archive-manifest.json'
    assert hashlib.sha256(independent_manifest.read_bytes()).hexdigest()=='684b02c2bd1355cd89f1941f88b1d3c0c0494714df0ab1480b0b027deab87154'
    independent=json.loads(independent_manifest.read_bytes())
    assert independent['passed'] and independent['independent_nanoda_passed'] and independent['partial_roots_only']
    assert not independent['global_energy_floor_proven'] and not independent['website_statement_verified']
    for path,row in independent['files'].items():
        p=independent_folder/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append(str(independent_manifest.relative_to(ROOT)).replace('\\','/'))
    cut_manifest=HERE/'cover-global-cut-progress-files.json'
    assert hashlib.sha256(cut_manifest.read_bytes()).hexdigest()=='3e5215245a34103c570cf8b4513873bc59bbcd0df120ed9b2e17ee20ba36e01a'
    cuts=json.loads(cut_manifest.read_bytes())
    for path,row in cuts['files'].items():
        p=HERE/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/cover-global-cut-progress-files.json')
    compiled=receipt['modules']+receipt.get('compiled_without_printed_axiom_audit',[])
    for row in compiled:
        for key,sha_key in [('source','source_sha256'),('log','log_sha256')]:
            p=ROOT/row[key];assert hashlib.sha256(p.read_bytes()).hexdigest()==row[sha_key]
            files.append(row[key])
    files += [str(p.relative_to(ROOT)).replace('\\','/') for folder in ['cover-compact-archive','cover-obbt-archive','cover-flow-basis-pruned','nine-point-pilot','snapshots']
              for p in sorted((HERE/folder).glob('*')) if p.is_file()]
    # Keep the generation programs that reproduce the verified actual profile.
    files += ['research-goal-20261016/'+s for s in ['window_generate_energy.py','window_generate_energy_bound.py','window_generate_profile.py']]
    files=sorted(set(files));assert all((ROOT/p).is_file() for p in files)
    subprocess.run(['git','add','-f','--',*files],cwd=ROOT,check=True)
    subprocess.run(['git','add','--renormalize','-f','--',*files],cwd=ROOT,check=True)
    entries=[]
    for path in files:
        raw=git('show',':'+path);sha=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        actual=(ROOT/path).read_bytes()
        assert raw==actual or (path in ['README.md','.gitattributes'] and raw==actual.replace(b'\r\n',b'\n')),('Index differs from selected source',path)
        try:raw.decode('utf8');binary=b'\0' in raw
        except UnicodeDecodeError:binary=True
        entries.append({'path':path,'sha':sha,'bytes':len(raw),'binary':binary})
    out={'base_commit':git('rev-parse','HEAD').decode().strip(),'tree_sha':git('write-tree').decode().strip(),
         'files':entries,'file_count':len(entries),'bytes':sum(x['bytes'] for x in entries),
         'submission_ready':False,'new_unconditional_zero_proportion_proven':False}
    dest=ROOT/'tmp/goal-20261016/staged.json';dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:out[k] for k in ['base_commit','tree_sha','file_count','bytes']}))
if __name__=='__main__':main()
