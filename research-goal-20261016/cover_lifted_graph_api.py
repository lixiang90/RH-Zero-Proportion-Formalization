"""Frozen-fork interface for the independently replayed lifted graph predicate.

This module does not modify or resume any runner.  A future independent
runner can call exclusion on an original closed cell before OBBT/Newton,
store a new graph leaf, and send that leaf to the separate graph verifier.
"""
from pathlib import Path
import hashlib
import cover_lifted_graph_probe as engine
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;DEFAULT_TABLE=HERE/'cover_newjet.json'
_default=None


def make_graph_oracle(taylor=None,path=DEFAULT_TABLE):
    """Reuse an existing first-order Taylor oracle, or build it once."""
    path=Path(path);taylor=taylor or engine.context.curvature.first.TaylorOracle(path)
    graph=engine.GraphOracle(path);assert taylor.sha==graph.sha
    return {'taylor':taylor,'graph':graph,'table_path':path}


def source_hashes(oracle):
    files=[Path(__file__),Path(engine.__file__),Path(engine.context.__file__),
      Path(engine.context.curvature.__file__),Path(engine.context.curvature.first.__file__),
      Path(engine.context.w.__file__),Path(engine.g.__file__),engine.context.w.PARAM,oracle['table_path']]
    return {p.resolve().relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def probe(state,oracle=None):
    """Return (strict certificate or None, diagnostic statistics)."""
    global _default
    if oracle is None:
        if _default is None:_default=make_graph_oracle()
        oracle=_default
    result,statistics,_=engine.solve((list(state[0]),list(state[1])),oracle['taylor'],oracle['graph'],True)
    if result is not None:assert int(result['strict_margin'])>0
    return result,statistics


def exclusion(state,oracle=None):
    """Accept only an exact residual-paid integer Farkas/flow contradiction."""
    return probe(state,oracle)[0]
