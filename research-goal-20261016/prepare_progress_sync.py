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
    files=['.gitattributes','AGENTS.md','README.md','submission/goal-20261016/STATUS.zh.md']
    names=['README.md','DIRECTION.zh.md','direction-state.json','macro-reviews/001-20261017.zh.md','macro-reviews/002-20261017.zh.md','macro-reviews/003-20261018.zh.md','macro-reviews/004-20261018.zh.md',
      'gates/stageB-20261018.json','gates/stageC-dbm-20261018.json',
      'gates/stageD-affine-point-20261018.json',
      'gates/stageE-margin-dbm-20261018.json',
      'gates/stageF-exact-lp-20261018.json',
      'gates/stageG-complete-classification-20261018.json',
      'gates/stageH-ordered-transport-20261018.json',
      'gates/stageI-fixed-original-affine-point-20261018.json',
      'gates/stageI-independent-original-affine-20261018.json',
      'gates/stageJ-fixed-basis-complete-20261018.json',
      'gates/stageJ-independent-complete-20261018.json',
      'gates/stageL-J-enhanced-fixed-cycle-20261018.json',
      'gates/stageL-independent-upgraded-cycle-20261018.json',
      'gates/stageM-component-envelope-fixed-20261018.json',
      'gates/stageM-independent-component-20261018.json',
      'gates/stageK-window-potential-cycle-20261018.json',
      'gates/stageK-independent-cycle-20261018.json',
      'ordinary-verified-current.json','seal_ordinary_progress.py','prepare_progress_sync.py',
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
      ('window_scalar_sector_sync_files.json','ac8b344e559c5b3b7006787366019cb4aea05242cb014782205fc6bd89265017'),
      ('cover-full-u-files.json','fef4caa3f4566b398d66a3d9e8b12e846e128fb5bf8188bca1e0284267db1e46'),
      ('cover-common-anchor-curvature-six-files.json','994e848cba046e35248ce4229ca6860cc75ad20d219dc935657e26014d4d26de'),
      ('window-large-embedding-files.json','0c9805d8f2a134b9c8df61d2c4cacffc03799e99d3a3f02f78e618d97e50ebc2'),
      ('cover-full-u-face-files.json','a5304f7603f971eee6bf1571411ae4da20765aa43470d314ef6bc93c67ce1dcf'),
      ('window-large-embedding-portable-files.json','bbb158e76d5817ccc5c0bce56a5048e55ff620a308e0b4400b36a569104c80bf'),
      ('research-goal-20261017-quartic/quartic-files.json','4a0681e23ea0810c9b7656ba120189c97911d41fa3ea958766aa660f61d189c1'),
      ('research-goal-20261017-quartic/quartic-positivity-correction-files.json','014479ce687c9b0d418ba214b3f19b5761aaa7d7670cf6acef5111e47ed440a0'),
      ('research-goal-20261017-quartic-split/split-files.json','8ec9a4e4314ae3071b59745c9730d2789c9329f1f31eb328cfa1cc78349dfedf'),
      ('lean_aux478_sync_files.json','bf665097729da8ca772e67481adc0c25a09141820000b874c5b89454872adc7f'),
      ('research-goal-20261017-multiwindow/multiwindow-files.json','1d67f1eabe6ce212bfea667635f238b8722a1b73e2e9401763947c67685b022f'),
      ('cover-sqlite-bounded143004-files.json','4e89d569ba203f02637b73f8e24590403233ac93e4350585e52d34d523bc764a'),
      ('research-goal-20261016/w10-size-audit-20261017/audit-files.json','0c5f9ea5b6970be10dab268f03a99d7057a911383aeef5a1a2ea4e09798d6a72'),
      ('research-goal-20261016/w10-size-audit-20261017/independent-codec-files.json','02a68ff5e65a7d9525a7d0e6e00b285760db7a2ee6e5dbf965c8a1a0a9912401'),
      ('research-goal-20261016/w10-size-merge-20261017/merge-files.json','d8de91c3dac67e581e68c5f93a778d0ffbfd01c929398f4c0072551197f77f34'),
      ('research-goal-20261017-global-competitor/swap-files.json','25a6e4998bdea29bde92794aabe8a8893ac10f9946f589d0707ca6d6016ce979'),
      ('w10-cell-predictor-files.json','19f68bd8b566d245e326beac61b0418f1c78659d5a9dea9de480f89bc46b69c4'),
      ('research-goal-20261017-adjacent-swap-family/swap-family-files.json','cb58c919806562b89e1af167ed66f2e6b15d2c09dffb22383e1a6ad52ff0084e'),
      ('window_global_competitor_sync_files.json','5250cb779cf5d696e1e4866ca30faa2c653e73887efb9c51b791a4b5ca4730f0'),
      ('research-goal-20261017-swap67-quartic/swap67-quartic-files.json','2aff4318c4f9f6945d0dde8ad79cfdd35fac24cfad5e9d00a65d50c9213dcf6f'),
      ('research-goal-20261017-swap67-audit/audit-files.json','26c1d38c21b3389355ab67172473cd2adb33169a43080ae40fb8e171f13e1a3c'),
      ('research-goal-20261017-swap67-formal-plan/formal-plan-files.json','698ed0ce1b239af5369dbd5b551fbc0befcb88b5b2289f42664aef4b4cfba639'),
      ('research-goal-20261017-swap-family-audit/audit-files.json','84c7564e8010896a795143bbf5b3823c20100ebf7d8ccd1bd8145ae8a3807fcd'),
      ('research-goal-20261017-swap-family-quartic/swap-family-files.json','c5801f1d784cbcbfb6e7b135490076340c004b19a067ce3ed7555431c0cab49d'),
      ('research-goal-20261017-swap-point-hessian/files.json','d170aad38757e1d6101d2a8cd8fb77bacf5388a033522a3d035e567142fc7fcd'),
      ('research-goal-20261017-quartic-hessian-localizer/hessian-localizer-files.json','bcf5a8d24a7c2a55adec85567c6aac727c55b524ed882edc47ac31bf64fe18ab'),
      ('research-goal-20261017-local-phase/local-phase-files.json','5bd98be403f6738c378a1e174dba45a321f09bc202226b8702f11d36e5f3cd4b'),
      ('research-goal-20261017-swap67-quadratic-localizer/q2-files.json','2683b0927c2dd60f70b9dc1e56fd69013b2b6e5c1e2ba79ca101c8c9b0c22b17'),
      ('research-goal-20261017-swap67-q2-audit/audit-files.json','91c9ad31dfd4f4612d71eb55cde7bcdd4320c0aca8e07a282afc151b341279bb'),
      ('research-goal-20261017-swap67-divided-difference/divided-files.json','f3a617be27477c26d12acb70850baf8df10194871a1998b658b7d0e1e192f802'),
      ('research-goal-20261017-swap67-divided-audit/audit-files.json','1211af4ba21b2dc44df2ae5c82dc4deefb953d7c531c4d9a801e1b58d3fbbf29'),
      ('research-goal-20261017-stationary-swap-audit/stationary-audit-files.json','2bee34739565a3027c108941ba97b45dae6ab0a4872f12be20acb58202f6d541'),
      ('research-goal-20261017-degree6-review/degree6-review-files.json','8d2d3bcbba63cb7e49efe9905d0528f64b8d023ebba521470b259e0ad82ba9a9'),
      ('research-goal-20261017-degree6-static/degree6-files.json','5087488b96c95d5f59adaf406ae8a208e9fdcbe26ca27178dd535ee41ff6c01f'),
      ('research-goal-20261017-degree6-audit/degree6-audit-files.json','83641d25a1a080db1750c0c30975f92f10e189812050752f519fb5286bbbb789'),
      ('research-goal-20261017-rankone-full8/files.json','11fefa4b3f1db11d68889ad2e03351fb5165a467d69088497550225c3d269bed'),
      ('research-goal-20261017-sextic-envelope-plan/plan-files.json','efe5a4dd640004086f10ae9c98b03f9b6fcd729a331f869339950a031f397326'),
      ('research-goal-20261017-period9-gate/files.json','e85f7d8998d32b3bc4496d70afce2db0d1f09ad5b84860c3ac98163c1194dde5'),
      ('research-goal-20261017-degree6-run-audit/audit-files.json','b909eef7ffee44a05fc771c3cbbe9333f09bfa4b69082e730c375763996c5548'),
      ('research-goal-20261017-degree6-cone/degree6-cone-files.json','6689194501b4e8613389da78ea95b04b7f2a7285215b82293a33cdbd8b844196'),
      ('research-goal-20261017-actual-sextic-static/actual-sextic-files.json','de6b1928b99a73db303f5c37994a1354ebe39ec1152342dac61ca9b475c8a5fb'),
      ('research-goal-20261017-actual-sextic-audit/sextic-audit-files.json','4a7782404601be29ea913fb45d7a580fe7e971c1940e3166b250edfc0050d300'),
      ('research-goal-20261017-clipped-coboundary/files.json','1adf2aec40b6e4854e75d404afacaeb6cd8a123bb5a496ace0ac16ba2dab32a7'),
      ('research-goal-20261017-ternary-coboundary/files.json','689cae3b63506e640b5c973aa3765682e9a3aa4b01c05913cbb9b44637f1c205'),
      ('research-goal-20261017-quadratic-coboundary-budget/files.json','7e819375590d5b66ef72f48c4a159ff82cf48b4a188300fa6c1fc9f5db97c8c0'),
      ('research-goal-20261017-actual-sextic-cone/actual-sextic-cone-files.json','4094f05bf934e083aebd99ed548836b1487681a963f53fe2fa95d930b8ecffd8'),
      ('research-goal-20261017-actual-sextic-cone-audit/preflight-files.json','885d7665637ea4aa71268376907042099c3cf01a2330646dbb95c99cabad299e'),
      ('research-goal-20261017-actual-sextic-cone-audit/worker-review-files.json','f1bd017848b3013e5d0ec24ecd689a4eb3155a96187b45a2f41d9e848697d68b'),
      ('research-goal-20261017-actual-sextic-run-audit/run-audit-files.json','3c0153cd799b769960b7fc092bcdf5510bbf475d5ec9f2f9f9439e17f5792d96'),
      ('research-goal-20261017-actual-sextic-exact-ray/exact-ray-files.json','c19797f38f2a7687817735b91163bf329d6f2ad7cb26e9989b3e76bb99f5ceae'),
      ('research-goal-20261017-exact-ray-audit/audit-files.json','1c481ad3f3055b175791a373d28eedb331913faa03e434b783d185f31db21cb8'),
      ('research-goal-20261017-actual-sextic-lean-plan/actual-lean-plan-files.json','f973491641f2014d96c787cbfd867ce132b1a3729ab822e2d243cf4b7ed591d0'),
      ('research-goal-20261017-transfer-budget-audit/audit-files.json','92be5868bc25e1367378583c1959516aa4c086e3e5af8af65a35dca6bfea4c9e'),
      ('research-goal-20261017-old-analytic-transfer-budget/transfer-budget-files.json','bdba0046a75ea098ffbe566de6951ca83058e2cedef96c631c162eb25476236e'),
      ('research-goal-20261017-fixed-gram-tail/fixed-tail-files.json','7811b31d9453ad344d47cebc016c980cfbac6a88e21230cb788dea7d93c935f0'),
      ('research-goal-20261017-fixed-gram-tail-audit/audit-files.json','41475b2345a6146ea97df8ce8101c69596677372f99a4404f8fa836f6f67135f'),
      ('research-goal-20261017-edge6-bernstein-transfer/edge6-transfer-files.json','4bf905c38868e07f64b91afb681ae9bf75b2f57bcc35fafa82bc40e46d1643ae'),
      ('research-goal-20261017-edge6-transfer-audit/audit-files.json','df2b75b49cf0f6a2632fef55f17e6262bcebc2984ab0ab08ef0f1e13daf4b4ee'),
      ('research-goal-20261017-edge6-payment-audit/audit-files.json','df1076f2a378507fc4bf6b61c7a3e084b9113e4c22475f11a19a2c30420b6e3d'),
      ('research-goal-20261017-global-relevance-audit/relevance-files.json','065d2cfe8b4dd8e11e3f47633d18a5dfbe72dc2e712df3a75cbb1b0890ba36f1'),
      ('research-goal-20261017-global-relevance-independent/audit-files.json','957a2523611f815ec94cab29f62e60f3ccf374faf3f9ce7c392dc7ff7eb0b86c'),
      ('research-goal-20261017-w10-slice-opportunity/opportunity-files.json','845a7956173a35b3e7f07a3ac1ec217e39b6724eee7c30259d64149faff97957'),
      ('research-goal-20261017-w10-slice-opportunity-audit/audit-files.json','8eef18b2b1988210861d8b48892dfc56b0308ed6c7111ab9ca1ff7abc3cd78f9'),
      ('research-goal-20261017-w10-generator-policy/policy-files.json','195fbd6987adc8e2515541aa3f2645afa6021454d9904a19adf4d4b76df381db'),
      ('research-goal-20261017-w10-generator-static-audit/audit-files.json','40ea66b6da4727b91a0481b6fa51cd386d30d2c9fe2be6966e66798cacd5ec52'),
      ('research-goal-20261017-w10-elaboration-generator-review/review-files.json','a8026c6d47d534c32677eb71f23a3f3b9e9b86f83797569ee13e6818e89f2f85'),
      ('research-goal-20261017-ninepoint-decomposition/decomposition-files.json','794508e11eb5becfcf4aad4785b72bc674a6639c6ea2b3ea1f811d260f1b555d'),
      ('research-goal-20261017-ninepoint-worker-audit/audit-files.json','dcda20afd7956c412fe2d445ca52814acbc21834ec0f3d4a997f19d3fe5e0cec'),
      ('research-goal-20261017-common-rounding/rounding-files.json','ee38c50b20cbe0f8cedfe22c01f78d65d9330dd826e86622fb14756825ada0d2'),
      ('research-goal-20261017-common-shift-rounding-audit/rounding-audit-files.json','eb0b85e624f2580cd7be593da61327e20be7e23fd16f8b71d94f12c63f63d445'),
      ('research-goal-20261017-new24-integer-floor-inventory/files.json','a70b84041c9ab0890707f9c921e3fa6aa182539689d6e17045013d6912bdaf3d'),
      ('research-goal-20261017-new24-integer-floor-inventory/addendum-files.json','43fc1e860df549dfa6228c195327e0f5bfafcc73217b50953c5c9523a8180caf'),
      ('research-goal-20261017-rounding-benefit/files.json','4da900e24183e2fd4b541cbe931c1368472498d305479ec523c77923c67b9d5e'),
      ('research-goal-20261017-integer-adjacent-floor-audit/audit-files.json','f143123dd9f302e0a77f745b0649a805afe91328815c857ee06f17f286387242'),
      ('research-goal-20261017-rounding-benefit-independent/audit-files.json','ef3d0fac3d33321e915e4d70e2d3e414e9c4e9ae985d50612d4436dc06f4ad66'),
      ('research-goal-20261017-fixed-best-point-identity/files.json','2851d5d85cf8d0ce30125ea207e6041ad93eb6fcf940ee3573f783d6e7a5a24e'),
      ('research-goal-20261017-pressure-budget/files.json','8f67f34cc7da5834008b9f89e1f77fe565093344eb0f1ced9f0096a80c65f12b'),
      ('research-goal-20261017-pressure-budget-independent/audit-files.json','397b118250fdb38fc12b397747f190b05ec474fc45891dc9ffdcb0bab0731276'),
      ('research-goal-20261017-pressure-budget-static-review/review-files.json','d3357cd81df489bbe77ba680e5616d846e5ebf9b66cfe695340b76054f475ffb'),
      ('research-goal-20261017-gluing-joint-infimum/joint-infimum-files.json','03f27afd41379548da4e0374905190b26cb3f625b4c3012f600f07b4623d3877'),
      ('research-goal-20261017-gluing-separated-review/review-files.json','bc5b29003f0ef9f4e5b4b898419873f2dc2541894c37cecb500a0046b47d89fd'),
      ('research-goal-20261017-gluing-exception-static-audit/files.json','0d1e6ad17c69b527238bcc4d563c91c76fe72e86123436728334ef1272eaff96'),
      ('research-goal-20261018-record-source-audit/source-audit-files.json','a4979eb961b87a14ba3dc7419066e102a2661f6289543d46d3728e6c15f731b8'),
      ('research-goal-20261018-target-arithmetic/files.json','4fd1475357692e67d8be4a5afc633e6e966ff2965593225b7127f11630972414'),
      ('research-goal-20261018-record-overlap-static/review-files.json','bedba14933f6c981fd27b9f42098b40549933ce26901d7e2407b69c8c9fde0ef'),
      ('research-goal-20261018-record-packing-independent/packing-files.json','ade046ca2398cc3825d81a74aec1afa955b8957bf56dea8cd9cb8fd1c38cabc6'),
      ('research-goal-20261018-record-wz-static-addendum/addendum-files.json','8ebc8493025eb7e63c4fe3419c4e929ca34033bafda434fa79905b95dfb17af6'),
      ('research-goal-20261018-record-baseline-replay/files.json','03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f'),
      ('research-goal-20261018-stageB-static-contract/contract-files.json','b9d9315cd76e9be9d4c860fe1368d06433e8ccabdeb5740b0109140ffa8c17f8'),
      ('research-goal-20261018-record-baseline-independent/audit-files.json','2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c'),
      ('research-goal-20261018-stageB-classification/files.json','3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad'),
      ('research-goal-20261018-product-consumer-static/review-files.json','3f8970a054ce7ebf894e913fd117837e4e7fb8c9fa6f2e12c54fe26f2ad9227b'),
      ('research-goal-20261018-dbm-gate-static/review-files.json','eea2ca9d0165364f8178cd0106de91aa4050a0c5d5fd9a00330174460d980a27'),
      ('research-goal-20261018-stageB-independent/audit-files.json','e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288'),
      ('research-goal-20261018-stageC-dbm/files.json','31e29433295f301c663fc2077d071bae4dfb89b1514eaa694e878fd9f5c8aae0'),
      ('research-goal-20261018-stageC-independent/audit-files.json','835389ce30ca1ffab2601105f1da51efc69e40b402fab64eedb1816bdb529a5b'),
      ('research-goal-20261018-joint-affine-static/review-files.json','51220d528c3c7e7f3673dda216a462117c6def29f9cacb44d19fab41d0500637'),
      ('research-goal-20261018-joint-affine-flow-proof/proof-files.json','e3d61af4a46aed20eaee334af3f2c3c9c95e8ceb1c06027a7e22e0de349064eb'),
      ('research-goal-20261018-joint-transshipment-static/review-files.json','714eea6eba4c8805b242a89fb1c6f20194b8289cf9e84ca89a151b67e48d24fc'),
      ('research-goal-20261018-fixed-joint-affine/files.json','683cbf5372fc5246d28a88fadab3dadf59bd758ed9e99458619f503cb30427c0'),
      ('research-goal-20261018-stageD-independent/audit-files.json','228105f6ff207a9f89f5bb4341af81f5b84568517063f5bd6d3bfb3f0afe5000'),
      ('research-goal-20261018-stageE-static-review/review-files.json','c04ea3c185d6d6e3ad05cbb99eeda8301f440a5651c12a6470bc9f261284697c'),
      ('research-goal-20261018-stageE-independent/plan-files.json','4a33d80c7fb6ace9e589c1e9fd1a945f7d6a91608fdadf2ed30bf23c99166b0f'),
      ('research-goal-20261018-stageE-floor-dbm/files.json','73b1cc1367b32cd769712370defef03288d625b4ab04c02df56ffe4b92b3b21a'),
      ('research-goal-20261018-stageE-independent/audit-files.json','37a3817aa099a951e362887d0022739f7560569495167b0d3a8908ab6ce1e32b'),
      ('research-goal-20261018-stageF-static-review/review-files.json','5647a5fc023dfe06a994f1de7464414b6c18918a161086bccf3ea2ec870c572d'),
      ('research-goal-20261018-stageF-exact-lp/files.json','ae64407781ef18022c7729523b645426bfa080fd44ad428d6b537ad4f8e0da24'),
      ('research-goal-20261018-stageF-independent/audit-files.json','6c0dab6de2295e46b5570c1166e8e7d8a205139c5ae86358e541d007271b636b'),
      ('research-goal-20261018-record-recheck/files.json','6e17996df45fa99f0370d29f5405931160c5f30358767e5cf1b3b277c53b8327'),
      ('research-goal-20261018-joint-size-opportunity/files.json','d6d1ec081a26a27faef2cee07b7ce4efa7c96ff3d731f68b151c18f9019f9916'),
      ('research-goal-20261018-global-delivery-static/contract-files.json','de2abe74665dfbf842f2c69f41ae87e8e0b268c7fd43a49d2b6843e9c940e021'),
      ('research-goal-20261018-stageG-complete-classification/files.json','93d7b1af5248aac7867e81bed3f1866b5d9c844c622f0a0ca01f28db2656972b'),
      ('research-goal-20261018-stageG-independent/audit-files.json','af09979447c2054f1daaa5a19e6abc59d04decee7752dfc53fe66c0643e30dc6'),
      ('research-goal-20261018-ordered-transport-static/files.json','0bfa1f2db8858f7520360212266cef2bff8e63899017782f1c977ce352f9a7fa'),
      ('research-goal-20261018-ordered-ray-fan-static/files.json','84a0089fa3c4b1e079ff17af22ae3ea43e0716872540689488030ff4f018f00b'),
      ('research-goal-20261018-stageH-ordered-transport/files.json','327562525e30d7b706777e71af003e51ca93a218ac7cfd9bfa0994abe56f8f8c'),
      ('research-goal-20261018-stageH-independent/audit-files.json','a0018aa4ce33e4cb6cea2019739e857fa3a1b58cc8b48f001e17d651e1dcbb3a'),
      ('research-goal-20261018-stageI-static-contract/files.json','f526477985915b2e26d9db1c81ecbcd246564ed7241a9724bc325fb7e0dfca76'),
      ('research-goal-20261018-stageI-original-affine-point/files.json','afaece4fee2e74d064258f689faff64d9732c53f8a412d0c71f6140d7653f482'),
      ('research-goal-20261018-stageI-independent/audit-files.json','2e0e18319ceabada6e2466ecfabc2d19b63d8c5282dc98099315a4131f4d538e'),
      ('research-goal-20261018-nonlinear-remainder-static/delivery-files.json','15418d3c8ef19489d26f15bd9ccb6e522e63e888498e01e430323b14dc226cdc'),
      ('research-goal-20261018-window-potential-static/delivery-files.json','610650840f9b6ec8cecdd90f23d6d329bc491ebd13124082b39e86e48b3a459b'),
      ('research-goal-20261018-window-potential-cycle/files.json','89fd14950a06a8e12c9feb7c09efd90bfdb6723f021fde14ddc39b2ca27c6916'),
      ('research-goal-20261018-window-potential-cycle-independent/audit-files.json','98983c69e3fb9070149afbd79e01f5877138a5983641b2e0b7523698bf6a635d'),
      ('research-goal-20261018-stageJ-fixed-basis-preparation/prepared-files.json','6fe73e334d4011ae3dbdb3cec601874fcdce4ab7f683d413f89715894c06fd62'),
      ('research-goal-20261018-stageJ-fixed-basis-preparation/files.json','90726f8987fd69820f70a63cc55c22f279a872263ced314fa41a452d4f1b09cd'),
      ('research-goal-20261018-stageJ-independent/audit-files.json','32de2e9381d1c103209c89b8f007d29815746a398c5c3d197f7762a727f55005'),
      ('research-goal-20261018-upgraded-cycle/files.json','38d82a7df7ec213cf478eb7f8e2144293767b6e236063a1a2caf5eb05d791bd5'),
      ('research-goal-20261018-upgraded-cycle-independent/audit-files.json','ca36c252e5a72c92e2066e8c195d3ef464ac9fc57e089ce74a74d24401afd055'),
      ('research-goal-20261018-stageM-component-envelope-preparation/prepared-files.json','b6cf0775e78fd7eb310a96393a43502584082b2824892244e15a9c13e2d04bbe'),
      ('research-goal-20261018-stageM-component-envelope-preparation/files.json','129c706dcab0aff47ef54a0f249e5d0a49e8f718476faaf453681e73858526d8'),
      ('research-goal-20261018-stageM-independent/prepared-files.json','23f0f7dd8bb9d28d3ca0352a2efd7c41a899cf3c752955c48c0b4a7b38c58a05'),
      ('research-goal-20261018-stageM-independent/audit-files.json','2887e7527180ca2b77d7779cd5c25ada853d040e82d0380a125f7f821c907be4'),
      ('research-goal-20261018-stageM-local-result/files.json','78355e0fdf0b12f4bc270e5a770bf0a74971a6c3931d88d4bed95fa9d165c949'),
      ('research-goal-20261018-stageM-actual-bridge-static/files.json','57ae12cffbdbf9ebba6a013698ac26ef5ae4e06e3006453cb63ea1af7a579597'),
      ('research-goal-20261018-component-flow-normalization-static/delivery-files.json','db80eb2822f2ed4aeb37e0b23c013f8e68d1a26802fc82018278d10395cbe7c4'),
      ('research-goal-20261018-component-flow-normalization-independent/audit-files.json','bcf78974d087ff0ba1d1d570261be9fa1fe41faed7a8fe7b414d480f3f208cbb'),
      ('research-goal-20261018-round2-delivery/files.json','50150cc8d2210011d9ea69ea1651371c3bcc81039e2da2e0ced1b2e33aa8bd6f'),
      ('research-goal-20261018-macro006-delivery/files.json','f40ccb7b98644bcbdeab167c3b78aed23ac507e8de77cdb14baa58a063bb4f7c')]:
        manifest=ROOT/name if '/' in name else HERE/name
        assert hashlib.sha256(manifest.read_bytes()).hexdigest()==digest
        pinned=json.loads(manifest.read_bytes())
        if 'external_read_only_runtime_identity' in pinned:
            runtime=pinned['external_read_only_runtime_identity']
            raw=Path(runtime['path']).read_bytes()
            assert len(raw)==runtime['bytes']
            assert hashlib.sha256(raw).hexdigest()==runtime['sha256_start']==runtime['sha256_end']
        if 'external_read_only_runtime' in pinned:
            runtime=pinned['external_read_only_runtime']
            runtime_path=runtime.get('path',runtime.get('executable'))
            assert runtime_path is not None
            raw=Path(runtime_path).read_bytes()
            assert len(raw)==runtime['bytes'] and hashlib.sha256(raw).hexdigest()==runtime['sha256']
            for extra in runtime.get('additional_files',[]):
                raw=Path(extra['path']).read_bytes()
                assert len(raw)==extra['bytes'] and hashlib.sha256(raw).hexdigest()==extra['sha256']
        if 'external_runtime_identity_file' in pinned:
            identity=pinned['external_runtime_identity_file']
            raw=(ROOT/identity['path']).read_bytes()
            assert len(raw)==identity['bytes'] and hashlib.sha256(raw).hexdigest()==identity['sha256']
            for runtime in json.loads(raw)['files']:
                external_raw=Path(runtime['path']).read_bytes()
                assert len(external_raw)==runtime['bytes'] and hashlib.sha256(external_raw).hexdigest()==runtime['sha256']
        for runtime in pinned.get('external_audit_runtime',[]):
            raw=Path(runtime['path']).read_bytes()
            assert len(raw)==runtime['bytes'] and hashlib.sha256(raw).hexdigest()==runtime['sha256']
        for runtime in (pinned.get('runtime_dependency_files',[])
                        +pinned.get('runtime_dependency_not_staged_wholesale',[])):
            # Bind the measured local runtime without publishing its
            # platform-specific temporary installation as research source.
            raw=(ROOT/runtime['path']).read_bytes()
            assert hashlib.sha256(raw).hexdigest()==runtime['sha256']
            if 'bytes' in runtime:assert len(raw)==runtime['bytes']
        for restored in pinned.get('reconstructed_dependency_files',[]):
            raw=(ROOT/restored['path']).read_bytes()
            assert hashlib.sha256(raw).hexdigest()==restored['sha256']
            if 'bytes' in restored:assert len(raw)==restored['bytes']
        rows=pinned.get('files',pinned.get('package_files'))
        if rows is None and 'files_sha256' in pinned:
            rows=[{'path':path,'sha256':digest,'bytes':(ROOT/path).stat().st_size}
                  for path,digest in pinned['files_sha256'].items()]
            if name=='cover-joint-jet-hessian-files.sha256.json':
                replay=json.loads((HERE/'cover-joint-jet-hessian-replay.json').read_bytes())
                assert replay['inputs_unchanged'] and replay['input_sha256_start']==replay['input_sha256_end']
                inputs=replay['input_sha256_end']
            elif name=='cover-common-anchor-curvature-six-files.json':
                inputs=json.loads((HERE/'cover-common-anchor-curvature-six.json').read_bytes())['input_sha256']
            else:raise AssertionError('Unreviewed files_sha256 schema: '+name)
            for path,digest in inputs.items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
                files.append(path)
        if isinstance(rows,dict):
            rows=[dict(row,path='research-goal-20261016/'+path) for path,row in rows.items()]
        rows=(rows+pinned.get('frozen_input_files',[])+pinned.get('SCS_discovery_sources_unchanged',[])
              +pinned.get('dependencies',[])+pinned.get('dependency_files',[])
              +pinned.get('frozen_dependencies',[]))
        if name=='research-goal-20261017-new24-integer-floor-inventory/files.json':
            rows+=pinned['reference_inputs']
        if name in ['research-goal-20261017-rounding-benefit-independent/audit-files.json',
                    'research-goal-20261017-pressure-budget-independent/audit-files.json']:
            rows+=pinned['pinned_inputs']
        if name=='research-goal-20261017-fixed-best-point-identity/files.json':
            rows+=pinned['read_only_reference_inputs']
        if name=='research-goal-20261017-gluing-exception-static-audit/files.json':
            rows+=pinned['read_only_references']
        if name=='research-goal-20261018-target-arithmetic/files.json':
            rows+=pinned['existing_read_only_input_references']
        if name=='research-goal-20261018-record-baseline-replay/files.json':
            rows+=pinned['read_only_existing_references']
        if name in ['research-goal-20261018-stageB-classification/files.json',
                    'research-goal-20261018-stageC-dbm/files.json',
                    'research-goal-20261018-fixed-joint-affine/files.json',
                    'research-goal-20261018-stageE-floor-dbm/files.json',
                    'research-goal-20261018-stageF-exact-lp/files.json',
                    'research-goal-20261018-joint-size-opportunity/files.json',
                    'research-goal-20261018-stageG-complete-classification/files.json',
                    'research-goal-20261018-ordered-transport-static/files.json',
                    'research-goal-20261018-ordered-ray-fan-static/files.json',
                    'research-goal-20261018-stageH-ordered-transport/files.json',
                    'research-goal-20261018-stageH-independent/audit-files.json',
                    'research-goal-20261018-stageI-static-contract/files.json',
                    'research-goal-20261018-stageI-original-affine-point/files.json',
                    'research-goal-20261018-stageI-independent/audit-files.json',
                    'research-goal-20261018-nonlinear-remainder-static/delivery-files.json',
                    'research-goal-20261018-window-potential-static/delivery-files.json',
                    'research-goal-20261018-window-potential-cycle/files.json',
                    'research-goal-20261018-window-potential-cycle-independent/audit-files.json',
                    'research-goal-20261018-stageJ-fixed-basis-preparation/prepared-files.json',
                    'research-goal-20261018-stageJ-fixed-basis-preparation/files.json',
                    'research-goal-20261018-stageJ-independent/audit-files.json',
                    'research-goal-20261018-upgraded-cycle/files.json',
                    'research-goal-20261018-upgraded-cycle-independent/audit-files.json',
                    'research-goal-20261018-stageM-component-envelope-preparation/prepared-files.json',
                    'research-goal-20261018-stageM-component-envelope-preparation/files.json',
                    'research-goal-20261018-stageM-independent/prepared-files.json',
                    'research-goal-20261018-stageM-independent/audit-files.json',
                    'research-goal-20261018-stageM-local-result/files.json',
                    'research-goal-20261018-stageM-actual-bridge-static/files.json',
                    'research-goal-20261018-component-flow-normalization-static/delivery-files.json',
                    'research-goal-20261018-component-flow-normalization-independent/audit-files.json']:
            rows+=pinned['read_only_dependencies']
        if name=='research-goal-20261018-stageE-independent/plan-files.json':
            rows+=pinned['dependency_manifests']
        if name=='research-goal-20261017-local-phase/local-phase-files.json':
            source_index=json.loads((ROOT/pinned['dependency_index']['path']).read_bytes())
            identity_rows=source_index['actual_identity_sources']+source_index['prior_work_reviewed']
            rows+=identity_rows
            rows += [row['ordinary_log'] for row in identity_rows if 'ordinary_log' in row]
        if name=='research-goal-20261017-degree6-review/degree6-review-files.json':
            embedding=json.loads((ROOT/pinned['external_model_source_index']['path']).read_bytes())
            api=json.loads((ROOT/pinned['actual_API_source_index']['path']).read_bytes())
            rows+=embedding['source_dependencies']+api['sources']
        if name=='research-goal-20261016/w10-size-merge-20261017/merge-files.json':
            # The published lossless pieces recreate these large audit inputs.
            # Verify their pins without also staging the duplicate raw caches.
            independent_merge=json.loads((ROOT/'research-goal-20261016/w10-size-merge-20261017/independent-merge-files.json').read_bytes())
            for row in independent_merge['dependency_files']:
                raw=(ROOT/row['path']).read_bytes()
                assert len(raw)==row['bytes'] and hashlib.sha256(raw).hexdigest()==row['sha256']
        if name=='w10-cell-predictor-files.json':
            for path,digest in pinned['source_and_input_sha256'].items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
        for path,digest in pinned.get('dependency_sha256',{}).items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest
            files.append(path)
        for row in rows:
            p=ROOT/row['path'];raw=p.read_bytes()
            # Some independent addons pin dependencies by SHA256 alone;
            # package rows additionally retain their explicit byte length.
            assert hashlib.sha256(raw).hexdigest()==row['sha256']
            if 'bytes' in row:assert len(raw)==row['bytes']
            if row['path'].startswith('tmp/goal-20261016/python-sdp/'):
                # Independent record audits may repeat runtime pins as
                # dependencies. Verify them, but keep the install local.
                continue
            if row['path']=='tmp/setup-20261015/packages/Comparator/Main.lean':
                # This pinned installed verifier source is reviewed runtime,
                # not candidate source; its official commit is in the report.
                continue
            if row['path'] in [
                  'research-goal-20261017-swap-family-quartic/swap-family-quartic.json.gz',
                  'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz',
                  'research-goal-20261017-actual-sextic-cone/new-rows-float.npz',
                  'research-goal-20261016/w10-size-audit-20261017/fs.bin',
                  'research-goal-20261016/w10-size-audit-20261017/nodes.bin',
                  'research-goal-20261016/w10-size-audit-20261017/treecodes.bin']:
                # These complete packets are reproduced from their published
                # hash-checked pieces; do not stage a second copy of the bytes.
                continue
            files.append(row['path'])
        files.append(str(manifest.relative_to(ROOT)).replace('\\','/'))
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
    assert not any(p.startswith('tmp/') for p in files),'Temporary runtime leaked into allowlist'
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
