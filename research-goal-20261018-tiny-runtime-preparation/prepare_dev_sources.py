"""Text-only namespace split; reuse the proved current s1R analytic prefix."""
import ast
import difflib
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def item(p):
    b = p.read_bytes()
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': len(b),
            'sha256': hashlib.sha256(b).hexdigest()}


def new_file(path, text):
    path.parent.mkdir(exist_ok=True, parents=True)
    with path.open('x', encoding='utf-8', newline='\n') as f:
        f.write(text)


ALIASES = r'''noncomputable section
namespace AMW.Cert.PC9TinyData
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC9Tiny
set_option maxRecDepth 100000

-- Exact aliases of the already-proved current-kernel LB/jet tables.
noncomputable def TOP : ℕ := AMW.Cert.PC9QB6MData.TOP
noncomputable def BK : ℕ → ℕ := AMW.Cert.PC9QB6MData.BK
theorem lbS : Pyr.LBSound TOP BK := AMW.Cert.PC9QB6MData.lbS
noncomputable def TOPD : ℕ := AMW.Cert.PC9QB6MData.TOPD
noncomputable def BKD : ℕ → ℕ := AMW.Cert.PC9QB6MData.BKD
theorem lbD : LBSoundD TOPD BKD := AMW.Cert.PC9QB6MData.lbD
noncomputable def REG : ℕ × ℕ × List (List ℕ) := AMW.Cert.PC9QB6MData.REG
theorem hR : rgOk REG = true := AMW.Cert.PC9QB6MData.hR
noncomputable def PT : ℕ → ℕ := AMW.Cert.PC9QB6MData.PT
theorem ptS : ∀ x, PVI x (PT x) := AMW.Cert.PC9QB6MData.ptS

'''

HEADER = r'''/-
SPDX-License-Identifier: Apache-2.0
PREPARATION ONLY, not compiled.
Versioned development split of frozen Tiny Core 9fbdf3f2...: the imported
CurrentPrefix is the already-proved actual current s1R prefix, including its
original attribution and modification notices. The new concrete PC9Tiny
namespace re-proves all strengthened TinyGoal walk/cut/leaf statements.
Only the existing LB/PT tables are aliases; no strengthened coverage is
imported from the old c9 Covered/CovK interface. The packed certificate
payloads/cursors and every numeric check are retained.

The inherited AMFinal/public candidate wrapper is archived separately. It
does not match this machine's trusted CandidateSpec and is not compiled.
No trusted constants are defined or changed here. Final deployment requires
the actual tiny rational and a newly trusted preparation/verification job.
All original third-party notices and full license texts are retained below
and in the imported prefix source; neither local proof counts nor this
split are a completed website submission.
-/
import StructuralS1RM20261018.CurrentPrefix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

'''


def main():
    canonical = ROOT/'StructuralS1RTiny20261018/Core.lean'
    prefix = ROOT/'StructuralS1RM20261018/CurrentPrefix.lean'
    counting = ROOT/'StructuralS1RTiny20261018/Counting.lean'
    assert item(canonical)['sha256'] == '9fbdf3f2dc62333b636d3b25dfb3bf2b15e3b8c628ece73d6ba1bc768fc5f1a6'
    assert item(prefix)['sha256'] == 'ea8e01118d19158ba8313504910645ad467ea86eb2ea65a897859ae98101df21'
    assert item(counting)['sha256'] == 'ddb73bed77f0c63f8e60e4549cfbf21eb8fb50f1e229bc647eb1393081bedb78'
    s = canonical.read_text(encoding='utf-8')
    p = prefix.read_text(encoding='utf-8')
    concrete_ns = s.index('namespace AMW.Cert.PC9QB6M\n')
    concrete_start = s.rfind('noncomputable section\n', 0, concrete_ns)
    concrete_end = s.index('end AMW.Cert.PC9QB6M\nend\n', concrete_ns) + len('end AMW.Cert.PC9QB6M\nend\n')
    data_ns = s.index('namespace AMW.Cert.PC9QB6MData\n')
    cov_start = s.index('noncomputable def COV :', data_ns)
    data_end = s.index('end AMW.Cert.PC9QB6MData\nend\n', cov_start) + len('end AMW.Cert.PC9QB6MData\nend\n')
    counting_end = s.index('end OpethN.Counting\nend\n', data_end) + len('end OpethN.Counting\nend\n')
    notices = s.index('/-\nADDITIONAL THIRD-PARTY NOTICES AND LICENSE TEXTS', counting_end)
    assert 'candidateKappa' not in s[data_end:counting_end]
    # The imported table block is byte-identical modulo closing blank lines.
    table_start = s.index('noncomputable def TOP :', data_ns)
    prefix_table_start = p.index('noncomputable def TOP :', p.index('namespace AMW.Cert.PC9QB6MData\n'))
    prefix_table_end = p.index('end AMW.Cert.PC9QB6MData\n', prefix_table_start)
    assert s[table_start:cov_start].strip() == p[prefix_table_start:prefix_table_end].strip()

    rename = lambda x: x.replace('PC9QB6M', 'PC9Tiny')
    concrete = rename(s[concrete_start:concrete_end])
    rest = rename(s[cov_start:data_end])
    tail = rename(s[data_end:counting_end])
    license_text = s[notices:]
    assert 'candidateKappa' not in concrete+rest+tail
    text = HEADER + concrete + '\n' + ALIASES + rest + tail + '\n' + license_text
    source = ROOT/'StructuralS1RTiny20261018/Dev/Core.lean'
    new_file(source, text)
    old_payloads = re.findall(r'zfNat64\s+\d+\s+"[^"\n]*"', s[cov_start:data_end])
    new_payloads = re.findall(r'zfNat64\s+\d+\s+"[^"\n]*"', rest)
    assert old_payloads == new_payloads and len(old_payloads) == 137
    assert 'namespace AMW.Cert.PC9QB6M\n' not in text
    assert 'namespace AMW.Cert.PC9QB6MData\n' not in text
    assert text.count('namespace AMW.Cert.PC9Tiny\n') == 1
    assert text.count('namespace AMW.Cert.PC9TinyData\n') == 1
    assert 'end OpethN.Counting\nend\n' in text
    assert not re.search(r'^(?:private )?theorem candidate_', text, re.M)
    assert 'sorry' not in text and 'native_decide' not in text

    archive = HERE/'inherited-tail.archive.lean.txt'
    new_file(archive, s[counting_end:notices])
    devcount = ROOT/'StructuralS1RTiny20261018/Dev/Counting.lean'
    ct = counting.read_text(encoding='utf-8')
    new_ct = ct.replace('import StructuralS1RTiny20261018.Core\n',
                        'import StructuralS1RTiny20261018.Dev.Core\n', 1)
    assert ct != new_ct and new_ct.replace('import StructuralS1RTiny20261018.Dev.Core\n',
                        'import StructuralS1RTiny20261018.Core\n', 1) == ct
    new_file(devcount, new_ct)
    diff = HERE/'DevCore.diff'
    new_file(diff, ''.join(difflib.unified_diff(s.splitlines(keepends=True), text.splitlines(keepends=True),
        fromfile='frozen/Core.lean', tofile='Dev/Core.lean')))
    countdiff = HERE/'DevCounting.diff'
    new_file(countdiff, ''.join(difflib.unified_diff(ct.splitlines(keepends=True), new_ct.splitlines(keepends=True),
        fromfile='frozen/Counting.lean', tofile='Dev/Counting.lean')))
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    manifest = {
        'schema':'tiny-current-prefix-reuse-dev-source-preparation-v1',
        'files':[item(x) for x in [source,devcount,archive,diff,countdiff,Path(__file__)]],
        'read_dependencies':[item(x) for x in [canonical,prefix,counting,
            ROOT/'research-goal-20261018-tiny-core-preparation/prepared-files.json',
            ROOT/'research-goal-20261018-tiny-counting-preparation/prepared-files.json']],
        'reused_olean_metadata_only':item(ROOT/'tmp/current-s1r-M-20261018/phaseA1b/lib/StructuralS1RM20261018/CurrentPrefix.olean'),
        'new_concrete_namespace':'AMW.Cert.PC9Tiny',
        'new_data_namespace':'AMW.Cert.PC9TinyData',
        'aliased_original_data':['TOP','BK','lbS','TOPD','BKD','lbD','REG','hR','PT','ptS'],
        'table_block_byte_identical_to_proved_prefix':True,
        'raw_packed_payloads_137_byte_identical':True,
        'all_new_TinyGoal_numeric_leaf_walk_and_cut_proofs_reelaborated':True,
        'reelaboration_claim_is_future_obligation_not_completed':True,
        'old_covered_or_CovK_not_used_as_new_E_proof':True,
        'retained_through':'end OpethN.Counting',
        'legacy_AMFinal_and_public_wrappers_compiled':False,
        'imported_prefix_bytes':len(p.encode('utf-8')),
        'new_concrete_bytes':len(concrete.encode('utf-8')),
        'new_data_alias_bytes':len(ALIASES.encode('utf-8')),
        'new_cov_and_walk_data_bytes':len(rest.encode('utf-8')),
        'actual_counting_tail_bytes':len(tail.encode('utf-8')),
        'license_trailer_bytes':len(license_text.encode('utf-8')),
        'devCore_bytes':len(text.encode('utf-8')),
        'devCounting_bytes':len(new_ct.encode('utf-8')),
        'uncropped_flatten_prefix_plus_devCore_plus_devCounting_bytes':len((p+text+new_ct).encode('utf-8')),
        'uncropped_remaining_2MB_before_Localization_and_final_wrapper':2000000-len((p+text+new_ct).encode('utf-8')),
        'Lean_runs':0,'new_math_evaluations':0,'future_gate_required':True}
    out=HERE/'dev-source-files.json'
    new_file(out,json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(item(out)))
    print(json.dumps({'DevCore':item(source),'DevCounting':item(devcount),
        'uncropped_total':manifest['uncropped_flatten_prefix_plus_devCore_plus_devCounting_bytes'],
        'uncropped_remaining':manifest['uncropped_remaining_2MB_before_Localization_and_final_wrapper']}))


if __name__=='__main__':
    main()
