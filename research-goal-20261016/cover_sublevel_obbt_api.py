"""Stable epigraph OBBT API with an explicit floor and private window instance.

make_engine(window_module) binds the frozen, exact-flow discovery code to
the chosen high/low window's own tangent hint cache without modifying the
original module or its live processes. contract returns a sublevel-only
refinement and independently replayable per-span mixture/flow certificates.
"""
from pathlib import Path
import hashlib,importlib.util

HERE=Path(__file__).parent

def make_engine(window_module):
    path=HERE/'cover_sublevel_obbt.py'
    spec=importlib.util.spec_from_file_location('_private_obbt_'+str(id(window_module)),path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    assert module.g.BS==window_module.g.BS and module.g.TERMS==window_module.g.TERMS
    assert module.g.DEN==window_module.g.DEN and module.g.SC==window_module.g.SC
    module.w=window_module;module.g=window_module.g
    return module

def contract(state,target,axes=None,engine=None):
    if engine is None:
        import window_global_cover as window_module
        engine=make_engine(window_module)
    return engine.contract(state,int(target),axes)

def source_hashes():
    return {'obbt_api_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'obbt_core_sha256':hashlib.sha256((HERE/'cover_sublevel_obbt.py').read_bytes()).hexdigest(),
      'sublevel_prototype_sha256':hashlib.sha256((HERE/'cover_sublevel_contractor.py').read_bytes()).hexdigest()}
