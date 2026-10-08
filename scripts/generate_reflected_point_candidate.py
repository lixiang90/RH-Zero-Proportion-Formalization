"""Reproduce the kernel-checked reflected Point candidate in ignored tmp only.

This performs a deterministic source transformation, not a proof checker.
The ordinary module and serial independent Nano ledgers separately certify the
candidate. It never edits the frozen Point/Data sources or a public Solution.
"""
from __future__ import annotations
import argparse
import hashlib
from pathlib import Path

if not __debug__:
    raise SystemExit('Reflected Point generation requires assertions enabled')

ROOT = Path(__file__).resolve().parents[1]
PINS = {
    'RecordProportion/PointSoundness.lean': 'e0feca589d54ae049e8ff721dfd1bbe7ea9804f0fac0c42ba96ef0d5bd153764',
    'RecordProportion/FiniteCertificateData.lean': '0b12cba764e62ac55f1d7acdebc6c86cf1a26253ccb31939519b983f01b1bc59',
    'RecordProportion/FrameReflection.lean': '1ec117c627997eab4801023ccffb9e9a10e6ac006ed6470a8437a5dbd9d22be7',
}
CANDIDATE_SHA = 'f7d766f8e4b389a5bbb410df05bd718f4149fd3e5f8941bcf52ef0e0eb33b7ad'
PREFIX_SHA = '816a9f9f737461c519aee76a70961275bb5ca007dce483e20b4d7fbba2c3174f'
SUFFIX_SHA = '98d7800536e84ce824da43ad4a64072b267bed4fbcfd14cd54510a49c15f9bcf'
REOPEN = '\n\nnamespace RHWeil.RecordSubmission.PointSoundness\nopen FiniteCertificateData\nopen AMW.Cert.Pyr AMW.Cert.PyrD\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\nattribute [local irreducible] FiniteCertificateData.cells FiniteCertificateData.pairPacks\n  FiniteCertificateData.catalog FiniteCertificateData.pointPacket AMW.Cert.PC8CLData.PT\n\nprivate theorem allFrom_intro {a n : Nat} {f : Nat → Bool}\n    (h : ∀ i < n, f (a+i) = true) : allFrom a n f = true := by\n  revert h\n  induction n with\n  | zero => intro h; rfl\n  | succ n ih =>\n    intro h\n    change Bool.rec (motive := fun _ => Bool) false (f (Nat.add a n)) (allFrom a n f) = true\n    rw [ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))]\n    exact h n (Nat.lt_succ_self n)\n\n'
FRAME_ALL = 'private theorem frame_all : allFrom 0 482 frameCheck = true := by\n  apply allFrom_intro\n  intro index hi\n  simp only [Nat.zero_add]\n  by_cases ho : index < 241\n  · simpa only [Nat.zero_add] using allFrom_spec frame_original_all index ho\n  · have hs : index-241 < 241 := by omega\n    have he : index-241+241 = index := by omega\n    have hm := CheckpointFrameReflection.frameCheck_mirror hs\n    rw [he] at hm\n    rw [hm]\n    simpa only [Nat.zero_add] using allFrom_spec frame_original_all (index-241) hs\n\n'

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)

def pinned_inputs() -> dict[str, bytes]:
    data = {name: (ROOT/name).read_bytes() for name in PINS}
    for name, value in data.items():
        require(sha(value) == PINS[name], 'Frozen input changed: '+name)
        require(b'\r' not in value, 'Expected canonical UTF-8 LF: '+name)
        value.decode('utf-8')
    return data

def candidate(data: dict[str, bytes]) -> bytes:
    original = data['RecordProportion/PointSoundness.lean'].decode('utf-8')
    helper = data['RecordProportion/FrameReflection.lean'].decode('utf-8')
    marker = '/- Ordinary top-level closed blocks keep the frontend state bounded. -/\n'
    require(original.count(marker) == 1, 'Original numerical-block marker changed')
    prefix = original[:original.index(marker)]
    suffix = original[original.index('theorem frameChecks'):]
    require(sha(prefix.encode()) == PREFIX_SHA, 'Computational prefix changed')
    require(sha(suffix.encode()) == SUFFIX_SHA, 'Extra and semantic suffix changed')
    start = helper.index('noncomputable section')
    stop = helper.index('end CheckpointFrameReflection')+len('end CheckpointFrameReflection')
    body = helper[start:stop]
    require(body.count('#print axioms frameCheck_mirror\n') == 1, 'Helper audit marker changed')
    body = body.replace('#print axioms frameCheck_mirror\n', '')
    blocks = ''.join(f'private theorem frame_block_{i} : allFrom {16*i} {16 if i<15 else 1} frameCheck = true := by decide +kernel\n' for i in range(16))
    chain = 'private theorem frame_original_all : allFrom 0 241 frameCheck = true := by\n'
    chain += '  have h0 : allFrom 0 16 frameCheck = true := frame_block_0\n'
    for i in range(1,16):
        n = 16*(i+1) if i<15 else 241
        chain += f'  have h{i} : allFrom 0 {n} frameCheck = true := allFrom_add h{i-1} frame_block_{i}\n'
    chain += '  exact h15\n\n'
    text = prefix+'end RHWeil.RecordSubmission.PointSoundness\n\n'+body+REOPEN+blocks+chain+FRAME_ALL+suffix
    result = text.encode('utf-8')
    require(sha(result) == CANDIDATE_SHA, 'Candidate differs from the checked source')
    require('import RecordProportion.PointSoundness\n' not in text, 'Candidate must not import old Point proofs')
    require(text.startswith(prefix) and text.endswith(suffix), 'Unchanged source regions lost')
    return result

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    parser.add_argument('--output', type=Path, default=Path('tmp/checkpoint_optimization/PointReflected.lean'))
    args = parser.parse_args()
    require((ROOT/'tmp').resolve() == ROOT/'tmp', 'The ignored tmp root must not be a symlink or reparse redirect')
    output = (ROOT/args.output).resolve()
    require(output.is_relative_to((ROOT/'tmp').resolve()) and output.suffix == '.lean', 'Output must be a Lean file under ignored tmp/')
    before = pinned_inputs()
    result = candidate(before)
    if args.check:
        require(output.is_file() and output.read_bytes() == result, 'Existing scratch candidate differs')
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(result)
    require(pinned_inputs() == before, 'Frozen inputs changed during generation')
    print(f'PASS {"check" if args.check else "write"}: {output.relative_to(ROOT)}; {len(result)} bytes; SHA256 {sha(result)}')
    print('Scope: exact source reproduction only; no new Lean, Nano, whole-submission or site check.')

if __name__ == '__main__':
    main()
