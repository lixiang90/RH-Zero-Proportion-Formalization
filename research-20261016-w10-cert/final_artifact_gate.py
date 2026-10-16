"""Bind the final independent arithmetic audit to the emitted Lean data.

These checks are publication/reproduction gates, not mathematical premises.
The exact standalone upload still requires its own ordinary kernel replay.
"""
from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def finite_binding(manifest=None):
    if not __debug__:
        raise RuntimeError('Final artifact assertions must remain enabled')
    paths = {
        'tree': HERE/'ordered-proof-input.json',
        'compact': HERE/'ordered-compact.json',
        'audit': HERE/'independent-audit-complete.json',
        'audit_script': HERE/'independent_integer_audit.py',
        'emission': HERE/'emitted-tree.json',
        'emitter': HERE/'emit_tree.py',
        'certificate': ROOT/'StructuralW10Cert20261016/Certificate.lean',
        'parameter': ROOT/'research-20261016/spectral-w10-refined-rational.json',
        'analytic_source': ROOT/'formal/upstream/ajp88-reweighted-nine-point.lean',
    }
    hashes = {name: sha(path) for name, path in paths.items()}
    audit = json.loads(paths['audit'].read_bytes())
    emitted = json.loads(paths['emission'].read_bytes())
    for flag in ['passed', 'complete_finite_partition', 'required_complete',
                 'required_all_packed', 'ordered_normalization',
                 'root_reconstructed', 'all_partition_edges_replayed']:
        assert audit.get(flag) is True, ('Final integer audit flag required', flag)
    assert audit['unresolved_frontier'] == 0 and audit['empty_children'] == 0
    assert len(audit['inputs']) == len(audit['packed_inputs']) == 1
    assert audit['inputs'][0]['sha256'] == hashes['tree']
    assert audit['packed_inputs'][0]['sha256'] == hashes['compact']
    assert all(row.get('unchanged_after_audit') is True
               for row in audit['inputs']+audit['packed_inputs'])
    assert audit['script_sha256'] == hashes['audit_script']
    assert audit['parameter_sha256'] == hashes['parameter']
    assert audit['source_sha256'] == hashes['analytic_source']
    assert emitted['tree_input_sha256'] == hashes['tree']
    assert emitted['compact_input_sha256'] == hashes['compact']
    assert emitted['script_sha256'] == hashes['emitter']
    assert emitted['source_sha256'] == hashes['certificate']
    assert emitted['source_bytes'] == paths['certificate'].stat().st_size
    assert emitted['branches'] == audit['branches']
    assert emitted['numeric_leaves'] == audit['numeric_leaves'] == audit['independently_decoded_relative_leaves']
    empty = audit['normalized_empty_leaves']+audit['reflection_leaves']
    assert empty == audit['independently_checked_packed_empty_leaves']
    assert emitted['leaves'] == audit['numeric_leaves']+empty
    assert emitted['nodes'] == emitted['branches']+emitted['leaves'] == 2*emitted['branches']+1
    assert int(audit['minimum_integer_margin']) >= 0
    result = {'file_sha256': {str(path.relative_to(ROOT)).replace('\\', '/'): hashes[name]
                              for name, path in paths.items()},
              'tree_input_sha256': hashes['tree'], 'compact_input_sha256': hashes['compact'],
              'certificate_source_sha256': hashes['certificate'],
              'complete_audit_sha256': hashes['audit'],
              'emission_receipt_sha256': hashes['emission'],
              'branches': emitted['branches'], 'leaves': emitted['leaves'],
              'numeric_leaves': emitted['numeric_leaves'], 'nodes': emitted['nodes']}
    if manifest is not None:
        assert manifest['assembly_complete'] is True
        assert manifest['finite_certificate_binding'] == result
        modules = manifest['source_modules_sha256']
        assert modules['StructuralW10Cert20261016/Certificate.lean'] == hashes['certificate']
        for name, expected in modules.items():
            assert sha(ROOT/name) == expected, ('Bundled module changed', name)
    assert hashes == {name: sha(path) for name, path in paths.items()}, 'A final input changed during binding'
    return result
