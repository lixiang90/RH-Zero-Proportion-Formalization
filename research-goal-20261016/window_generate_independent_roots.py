"""Generate the explicitly partial new-window replay import/axiom surface."""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
imports = [
    'WindowAnchorAll', 'WindowLinearConvexityPilot', 'WindowRecordFromFloor',
    'WindowRecordDyadic', 'WindowPressureRoot', 'WindowKKTInstance',
    'WindowSecondVariation', 'WindowQuantizedSupport', 'DifferenceCell', 'FlowBasisPilot',
]
names = [
    'WindowFixedTablesAll.k_sound', 'WindowFixedTablesAll.w_sound',
    'WindowAnchorAll.valid', 'WindowLinearConvexityPilot.cell',
    'WindowPairCertificate.short_pair_floor', 'WindowGapEnergy.exists_ordered_global_min',
    'WindowPressureRoot.selected_span_upper', 'WindowPressureRoot.global_floor_of_checked',
    'WindowKKTInstance.of_relevantBelow', 'WindowSecondVariation.curvature_nonneg_of_relevant',
    'WindowQuantizedSupport.zero_extension', 'DifferenceCell.split_sound',
    'DifferenceCell.affine_flow_bound',
    *['FlowBasisPilot.bound'+str(i) for i in range(4)],
    'WindowRecordFromFloor.improvement', 'WindowRecordFromFloor.simple_cumulative',
    'WindowRecordFromFloor.distinct_cumulative', 'WindowRecordDyadic.simple_dyadic',
    'WindowRecordDyadic.distinct_dyadic',
]
prefix = 'StructuralGoal20261016.'
module = prefix+'WindowIndependentRoots'
roots = [prefix+n for n in names]
source = ('/- SPDX-License-Identifier: Apache-2.0\n'
          'Partial replay surface only. No global energy floor is asserted here.\n'
          'The counting roots retain their explicit Floor premise.\n-/\n')
source += ''.join('import '+prefix+n+'\n' for n in imports)
source += 'set_option Elab.async false\nset_option pp.fullNames true\n'
source += ''.join('#print axioms '+n+'\n' for n in roots)
target = ROOT/'StructuralGoal20261016/WindowIndependentRoots.lean'
target.write_text(source, encoding='utf8')
manifest = {
    'scope': 'PARTIAL: all actual integer jet centres and 1567 anchor certificates; '
             'one actual convexity subinterval; actual short-pair floor; '
             'coercivity/KKT/coupled-pressure and affine-flow soundness; '
             'conditional counting with its energy-Floor premise still present. '
             'Self replay, not a website statement comparison.',
    'module': module, 'roots': roots,
    'source_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
    'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'ordinary_compile_proven': False, 'independent_nanoda_proven': False,
    'unconditional_counting_proven': False, 'global_energy_floor_proven': False,
    'submission_ready': False,
}
(HERE/'window-independent-roots.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps({'module': module, 'roots': len(roots), 'source_sha256': manifest['source_sha256']}))
