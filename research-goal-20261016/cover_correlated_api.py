"""Stable correlated directional-derivative discovery API.

make_correlated_oracle(path) builds the exact scalar Taylor/RMQ data.
correlated_exclusion(state, oracle=None) selects a direction by floating LP,
then accepts only after strict negative INTEGER min-cost-flow replay.
No floating value is used as an accepted certificate inequality.
Analytic jet/Taylor and KKT Lean bridges remain separate obligations.
"""
from pathlib import Path
import hashlib
import cover_correlated_direction as engine

HERE=Path(__file__).resolve().parent
DEFAULT_TABLE=HERE/'cover_newjet.json'
_default_oracle=None

def make_correlated_oracle(path=DEFAULT_TABLE):
    return engine.TaylorOracle(Path(path))

def api_sources(oracle):
    return {'api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'engine_sha256':hashlib.sha256(Path(engine.__file__).read_bytes()).hexdigest(),
      'parameter_sha256':hashlib.sha256(engine.w.PARAM.read_bytes()).hexdigest(),
      'derivative_table_sha256':oracle.sha,
      'profile_coefficient_numerators_1e9':oracle.receipt['coefficient_numerators_1e9'],
      'pressure_numerators':list(engine.g.BS),
      'pair_numerators':[list(row) for row in engine.g.TERMS],
      'weight_denominator':engine.g.D,'coordinate_scale':engine.g.SC,
      'separation':'123/128','taylor_order':24,'scalar_recipe':'correlated-v1'}

def correlated_exclusion(state,oracle=None):
    global _default_oracle
    if oracle is None:
        if _default_oracle is None:_default_oracle=make_correlated_oracle()
        oracle=_default_oracle
    result=engine.exclusion(state,oracle)
    if result is not None:
        assert int(result['upper_numerator'])<0
        result={**result,'kind':'correlated_direction','scalar_recipe':'correlated-v1'}
    return result
