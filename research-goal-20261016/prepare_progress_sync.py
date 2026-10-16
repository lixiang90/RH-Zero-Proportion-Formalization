"""Stage a reproducible research checkpoint, excluding evolving/failed proofs."""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def indexed_blobs(paths):
    index={}
    for row in git('ls-files','--stage','-z').split(b'\0'):
        if not row:continue
        head,path=row.split(b'\t',1);mode,sha,stage=head.split()
        assert stage==b'0','Unmerged index'
        index[path.decode('utf8')]=sha
    shas=[index[path]for path in paths]
    batch=subprocess.check_output(['git','cat-file','--batch'],
      input=b'\n'.join(shas)+b'\n',cwd=ROOT)
    offset=0
    for path,sha in zip(paths,shas):
        end=batch.index(b'\n',offset);actual,kind,size=batch[offset:end].split()
        assert actual==sha and kind==b'blob'
        offset=end+1;raw=batch[offset:offset+int(size)];offset+=int(size)
        assert batch[offset:offset+1]==b'\n';offset+=1
        yield path,raw
    assert offset==len(batch)
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
    cut_union_manifest=HERE/'cover-global-cut-union-files.json'
    assert hashlib.sha256(cut_union_manifest.read_bytes()).hexdigest()=='8b5d4d86bea3c638dd29db9a6436e44b4fa8016070674f6b652e5bb1ab221fbd'
    cut_union=json.loads(cut_union_manifest.read_bytes())
    assert cut_union['combined_topmost_global_regions']==43 and not cut_union['complete_global_cover']
    for path,row in cut_union['files'].items():
        p=HERE/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/cover-global-cut-union-files.json')
    curvature_manifest=HERE/'cover-targeted-curvature-files.json'
    assert hashlib.sha256(curvature_manifest.read_bytes()).hexdigest()=='f50faebb40cc501ceb4590c5f645dd78c713d108ab7d88d28310fe9f314ffef5'
    curvature=json.loads(curvature_manifest.read_bytes())
    for path,row in curvature['files'].items():
        p=HERE/path
        assert p.is_file() and len(p.read_bytes())==row['bytes']
        assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/cover-targeted-curvature-files.json')
    # New graph and curvature archives are immutable, independently replayed
    # local evidence. Their manifests retain their original verification
    # scope; the separate current Lean receipt records later formal passes.
    for name,digest in [
      ('cover-curvature-actual-feed-files.json','1a97c06e106a94d16db31fbc2900d1a44fd85b9845f188ea85db8fbb8a4c5712'),
      ('cover-lifted-graph8-files.json','9a185cddae2b0f02b3b32a7c87ac0437b8258816dbd7200e5d6389b924d509f3'),
      ('cover-lifted-graph64-files.json','372b623d5831e05603de9518604007329fa42c0679702b70060aa88aaad749d3'),
      ('cover-lifted-graph-discovery-input-files.json','78e2f828ce724e26db7399bfeadde6292e8065e63a4fb052b0c8c69a474fe04f'),
      ('cover-lifted-graph-replacement-files.json','b491d496783ffd205aa1498bc137519e5e91121c3690d1a92f07513f1c32f9fa'),
      ('cover-lifted-radial8-files.json','d00d183c4e9497589cea3d396490e58e5f2643469163f6e84726c70a594ae724'),
      ('cover-lifted-disjunction-files.json','0c6de43b1cb1e71c9cfce72a52e7c77f0d9c2d3590b7302fbb472c4e274e52a3'),
      ('cover-phase-psd-files.json','7e46cef3d672741ea1f83f976f2b469f2d38aa1d6ac627224f346243315b1a7f'),
      ('window-mixed-independent-progress-files.json','2ff3acfa47fe9c840d1ab94f6699f8ca4c0e007929a3de40cf7dd4ec016b798a'),
      ('window-phase-uniform-progress-files.json','f782555de142f67db56606f68fa43cb41c10a344266fbb98f056d9385dd78727'),
      ('cover-phase-kkt-files.json','b633781f75b493affa8164300afc300fa58e46b78390a8c29d141074a563e94b'),
      ('cover-gradient-mixture-files.json','bc83b24e89b6231a027aa8a450a659f78470762b030f2cb49b98aa639a69f015'),
      ('cover-cross-moment-two-files.json','f1a499f158445218def874cddf6d440c89725bb07290a62b3058f18f72fe7683'),
      ('moment-followup-auxiliary-files.json','93d553c98e6cfb4c5719078fe337968c513511908959d2d1b64843c139cd18a8'),
      ('cover-cross-moment-remaining-files.json','a43e79af34ab38caea36f8dc9a11aead391eb11a6033945cf3b85dd95624b08b'),
      ('moment-friendly-input-files.json','78385cf83b95aa7d0f82e8c2f94378332e7fa787159bfca9f98b178e14a9db29'),
      ('cover-cross-moment-factor-files.json','2ac9f7c06164fe2d80a183794bb1578cb5666d8c44e9946be319782ad401e63b'),
      ('window_moment_numeric_sync_files.json','6534d9a78342f55d406a4d54ec44c4db14aa2d5e9fa517d4bede48513197b2cb'),
      ('cover-cross-moment-global-box-files.json','d5a8a471f46fefa0de591a13ba62fbc6f6097e664f9c6656958266d0a8b57790'),
      ('cover-cross-moment-aggregate-files.json','209cc75f7af3f151fb238cf0d4f8e9b82dd3763e37fda1aa3bdc1de8cf6e0b05'),
      ('window_moment_actual_inputs_sync_files.json','292f094bd0ef5a1548f3a4e134fbd5a1041425824d73f5a7542ede2479129c83'),
      ('window-phase-lattice-rigidity-files.json','4b005ad8c405126bc22b7c2858ad42999ab8b806cfc6433d595acba1477a2351'),
      ('window-joint-cycle-projection-replay-files.json','137dccdf29cf46b6776571e2c020b47285cb42b31cd98ff3b101b740d0ac197e'),
      ('cover-main-recovery-files.json','7cdd09185db00e5920b5ea6e3ea36dab420ea156bb952bd7df07bccb11773754'),
      ('cover-span-slack-files.json','98160e9301d384be90a38b632968a9820afbf6f235e80526f6dfee373643ef0c'),
      ('window_moment_actual_exclusion_sync_files.json','2bd71aff6dc350328d6fd44c0bf8ba1e562d8f7922c7fed0cf57779dd2308268'),
      ('window-new-structural-cores-files.json','17d81b858aa1cb0f956dc89ed578a6b82981af55ee803336c1a684ffc6bcd74c'),
      ('window-post-sync14-static-research-files.json','96a9854573a63c5047c9782c5f9a305cc09063df34a4ca475d9f26c97cfea006'),
      ('cover-main-streaming-design-files.json','10e0091e0402e9c3405db49aa4e18707ded79dc96ebe054b81289a20b6275647'),
      ('cover-main-stopped-files.json','221fc5a87281f420b483c261187b0fd185beb495a31a694a1db5b4115c7766d8'),
      ('cover-sqlite-proof-store-files.json','303140b2d05eb21e0250a2b0f205e3ccfc22c4b523f2517656a56c4db3e51b13'),
      ('window-kkt-projection-variance-files.json','26c0d0254793324ddddf042fbc26d6787ac0db843d8c882031e428a0ea69d640'),
      ('lean_leaf_pilot_sync_files.json','42bbd464797d35b25c81b7ba69145af6d0ae83c16a6b0d5a889ed592d2226b9a'),
      ('window_bregman_core_sync_files.json','136c833c4bc76353ff6b092665f49da87644a4769eba7278ecf6edd32aa3ec9e'),
      ('cover-residual-psd-rational-files.json','5995d2ba510e40e31edbd17d3337a4f39c89acc62e209c016b0d584464714c6b'),
      ('lean_leaf_batch_sync_files.json','e814c478d4f9f8d35026a3f1b3fa69e57873b5d34c498464f0cf9f421c2a8b49'),
      ('lean_aux127_sync_files.json','73381a7c26f11a36b9749a8078adb9e35d7e2d4bcf3964bdf58be2cd74e8b606'),
      ('cover-sqlite-real-node-files.json','9098f8da0b31609d5ae352ceb165099c8f9e6606f6c4fbb011ff6dd61adaa4ec'),
      ('window-kernel-transfer-files.json','240f532c0b4752dd4a779e56a168ffed1b25369a21de9fe9b8d693aa3b120564'),
      ('window-embedded-old-ledger-files.json','e0709586f2b36241ce6a42482225bc281ccec254e440b3e59dbadc569d473334'),
      ('cover-sqlite-campaign133004-files.json','75db72c3932e479f75f6126cc5c76694492f339f6ad9f31dad7d1e0ee4e26c0e'),
      ('cover-dynamic-sector-files.json','7ae3208f705a7fec9ca0796ff47f7c23426356c7b140e6920933be8048e28922'),
      ('cover-joint-jet-hessian-files.sha256.json','a582d06fd30a88b9756711ec5f3e0ac4a9c150d1c258f304ad885917601b21e2'),
      ('window_scalar_sector_sync_files.json','ac8b344e559c5b3b7006787366019cb4aea05242cb014782205fc6bd89265017')]:
        manifest=HERE/name
        assert hashlib.sha256(manifest.read_bytes()).hexdigest()==digest
        pinned=json.loads(manifest.read_bytes())
        rows=pinned.get('files',pinned.get('package_files'))
        if rows is None and 'files_sha256' in pinned:
            rows=[{'path':path,'sha256':digest,'bytes':(ROOT/path).stat().st_size}
                  for path,digest in pinned['files_sha256'].items()]
            replay=json.loads((HERE/'cover-joint-jet-hessian-replay.json').read_bytes())
            assert replay['inputs_unchanged'] and replay['input_sha256_start']==replay['input_sha256_end']
            for path,digest in replay['input_sha256_end'].items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
                files.append(path)
        if isinstance(rows,dict):
            rows=[dict(row,path='research-goal-20261016/'+path) for path,row in rows.items()]
        rows=rows+pinned.get('frozen_input_files',[])+pinned.get('SCS_discovery_sources_unchanged',[])+pinned.get('dependencies',[])
        for path,digest in pinned.get('dependency_sha256',{}).items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
            files.append(path)
        for row in rows:
            p=ROOT/row['path'];raw=p.read_bytes()
            assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
            files.append(row['path'])
        files.append('research-goal-20261016/'+name)
    pilot_manifest=HERE/'window_lifted_pilot_formal_manifest.json'
    assert hashlib.sha256(pilot_manifest.read_bytes()).hexdigest()=='e596fdc941371d673dce842ca7592ca808a8d42fa79f32485e6001fd7708980f'
    pilot=json.loads(pilot_manifest.read_bytes())
    assert pilot['ordinary_Lean_complete'] and pilot['fully_actual_scalar_and_facet_premises_discharged']
    for row in pilot['modules']:
        for p,digest in [(ROOT/row['source'],row['source_sha256']),(HERE/row['log'],row['log_sha256'])]:
            assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
            files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    for name,digest in pilot['inputs'].items():
        p=HERE/name
        assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    files.append('research-goal-20261016/window_lifted_pilot_formal_manifest.json')
    for name,digest in [
      ('window_phase_hermitian_audit.txt','db6ac3c30d3bc991eee72475f40f2e16a25755ce61bfbfb0cdd47ff6df6abb90'),
      ('window_phase_hermitian_diagnostic.py','3828f10c08cc5c90a1872c502eb6f7476d488c167e30d728217b314fe75f5634'),
      ('window_phase_hermitian_diagnostic.json','babcf3204df816bde6c1edd838d72c66bed78b8af560a30346c0377f9023ae7a')]:
        p=HERE/name
        assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
        files.append(str(p.relative_to(ROOT)).replace('\\','/'))
    compiled=receipt['modules']+receipt.get('compiled_without_printed_axiom_audit',[])
    for row in compiled:
        for key,sha_key in [('source','source_sha256'),('log','log_sha256')]:
            p=ROOT/row[key];assert hashlib.sha256(p.read_bytes()).hexdigest()==row[sha_key]
            files.append(row[key])
    files += [str(p.relative_to(ROOT)).replace('\\','/') for folder in ['cover-compact-archive','cover-obbt-archive','cover-flow-basis-pruned','nine-point-pilot','snapshots']
              for p in sorted((HERE/folder).glob('*')) if p.is_file()]
    # Keep the generation programs that reproduce the verified actual profile.
    files += ['research-goal-20261016/'+s for s in ['window_generate_energy.py','window_generate_energy_bound.py','window_generate_profile.py']]
    files += ['research-goal-20261016/'+s for s in [
      'window_generate_root_cell.py','window_generate_root_cell.json','window_generate_lower_root_cell.json',
      'window_generate_convexity_all.py','window_generate_actual_basins.py','window_actual_basin_modules.json',
      'window_generate_raw_coefficients.py','window_generate_choice_grid.py','window_choice_grid.json',
      'window_generate_grid_checks.py','window_grid_check_modules.json',
      'window_generate_scalar_line_pilot.py','window_generate_scalar_line_pilot.json',
      'window_generate_rational_basins.py','window_rational_basin_audit.json','window_rational_basin_modules.json',
      'window_generate_rational_basin_groups.py','window_rational_basin_group_modules.json',
      'lean_new_actual_bridges_20261017.json', 'lean_window_closure_20261017.json',
      'window_generate_curvature_oracle.py','window_generate_curvature_grid.py',
      'window_curvature_grid_modules.json','window_curvature_scalar_audit.py',
      'window_curvature_scalar_audit.json','window_generate_curvature_leaves.py',
      'window_curvature_leaf_generation.json','window_curvature_leaf_modules.json',
      'window_generate_curvature_subtree.py','window_generate_curvature_obbt_groups.py',
      'window_generate_curvature_subtree_geometry.py','window_generate_curvature_subtree_proof.py',
      'window_curvature_subtree_generation.json','window_curvature_obbt_group_modules.json',
      'lean_local_mixed_snapshot.py','lean_local_mixed_20261017.json',
      'window_generate_mixed_independent_roots.py','window-mixed-independent-roots.json',
      'window_mixed_independent_replay.py','window_archive_mixed_replay.py']]
    files=sorted(set(files));assert all((ROOT/p).is_file() for p in files)
    # Keep the verified allowlist literal and avoid Windows' command-line
    # length limit as independent finite-check shards accumulate.
    pathspec=b'\0'.join(path.encode('utf8') for path in files)+b'\0'
    subprocess.run(['git','--literal-pathspecs','add','-f','--pathspec-from-file=-','--pathspec-file-nul'],
                   input=pathspec,cwd=ROOT,check=True)
    subprocess.run(['git','--literal-pathspecs','add','--renormalize','-f',
                    '--pathspec-from-file=-','--pathspec-file-nul'],input=pathspec,cwd=ROOT,check=True)
    entries=[]
    for path,raw in indexed_blobs(files):
        sha=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
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
