"""Stable no-optimizer verifier API for a per-span OBBT refinement."""
from pathlib import Path
import hashlib
import cover_sublevel_obbt_verify as helper

def verify_step(state,step,target):
    assert step['old_cell']==[list(state[0]),list(state[1])]
    helper.verify({**step,'result':None},int(target),None)
    return step['new_cell']

def source_hashes():
    return {'obbt_verifier_api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'obbt_verifier_helper_sha256':hashlib.sha256(Path(helper.__file__).read_bytes()).hexdigest(),
      'minorant_checker_sha256':hashlib.sha256(Path(helper.shared.__file__).read_bytes()).hexdigest()}
