"""Stable KKT-only interval-Newton contraction API.

contract(state,max_rounds=8,oracle=None) returns
(new_state, contraction_step_certificates, correlated_exclusion_or_None).
new_state=None certifies that no original KKT point survives the contractions.
The certificates preserve KKT points, not all points in the original cell.
"""
from pathlib import Path
import hashlib
import cover_newton_contractor as core
import cover_correlated_api as direction

_default_oracle=None

def contract(state,max_rounds=8,oracle=None):
    global _default_oracle
    if oracle is None:
        if _default_oracle is None:_default_oracle=direction.make_correlated_oracle()
        oracle=_default_oracle
    certificates=[];excluded=None
    for _ in range(max_rounds):
        refined,rows=core.contract_once(state,oracle)
        if not rows:break
        certificates.append({'old_cell':state,'new_cell':refined,'certificates':rows})
        state=refined
        if state is None:break
        excluded=direction.correlated_exclusion(state,oracle)
        if excluded is not None:break
    return state,certificates,excluded

def api_sources(oracle):
    return {'contractor_api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'contractor_core_sha256':hashlib.sha256(Path(core.__file__).read_bytes()).hexdigest(),
      **direction.api_sources(oracle)}
