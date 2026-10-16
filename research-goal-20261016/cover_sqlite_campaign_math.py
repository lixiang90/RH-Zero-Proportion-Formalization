"""Frozen-call-order adapter for the capped SQLite1000-node campaign.

No algorithm, threshold, scalar oracle, cache policy or mathematical source
is altered. A single candidate is returned without mutating storage.
"""
import os
import window_sqlite_node_pilot as inherited

w = inherited.low
g = w.g


def current_rss_bytes():
    if os.name != 'nt':
        from pathlib import Path
        return int(Path('/proc/self/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
    import ctypes
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_ = [('cb', wintypes.DWORD), ('PageFaultCount', wintypes.DWORD)]+[
          (n, ctypes.c_size_t) for n in ['PeakWorkingSetSize', 'WorkingSetSize', 'QuotaPeakPagedPoolUsage',
          'QuotaPagedPoolUsage', 'QuotaPeakNonPagedPoolUsage', 'QuotaNonPagedPoolUsage', 'PagefileUsage', 'PeakPagefileUsage']]
    c = Counters();c.cb = ctypes.sizeof(c);kernel = ctypes.WinDLL('kernel32')
    kernel.GetCurrentProcess.restype = wintypes.HANDLE;psapi = ctypes.WinDLL('psapi')
    psapi.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.POINTER(Counters), wintypes.DWORD]
    assert psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(), ctypes.byref(c), c.cb)
    return c.WorkingSetSize


def discover(incoming, oracle, registry, engine, known_supports, epoch_digest):
    state = (incoming['state'][0], incoming['state'][1]);path = incoming['path'];depth = incoming['depth']
    codec = inherited.codec;direction = inherited.direction
    def cheap(state):
        basin = inherited.gram.gram_basin(state, '11/1250', registry)
        if basin:
            return 'Gram', basin
        ex = direction.exclusion(state, True)
        if ex is None:
            ex = inherited.correlated.correlated_exclusion(state, oracle)
        if ex:
            ex['derivative_grid_sha256'] = oracle.sha;return 'stationary', ex
        return None, None
    packed_obbt = None;packed_newton = [];rec = None
    if state[1][8] < state[0][0]:
        resolution = {'kind': 'leaf', 'leaf': {'path': path, 'depth': depth, 'kind': 'reflection'}}
    else:
        kind, result = cheap(state)
        if kind is None:
            rec = w.certify(state)
            if int(rec.get('floor_numerator', '-1')) >= g.TARGET:
                kind, result = 'value', rec
        if kind is None:
            assert rec is not None;axis, _ = g.cut(state, rec);axes = sorted(set(list(range(9))+[axis]))
            refined, bounds = inherited.obbt.contract(state, g.TARGET, axes, engine)
            if bounds:
                packed_obbt = codec.pack_obbt({'old_cell': state, 'new_cell': refined, 'certificates': bounds});state = refined
                if state is None:
                    kind, result = 'sublevel_empty', {'reason': 'No F<target point survives epigraph OBBT'}
                else:
                    kind, result = cheap(state)
                    if kind is None:
                        rec = w.certify(state)
                        if int(rec.get('floor_numerator', '-1')) >= g.TARGET:
                            kind, result = 'value', rec
        if kind is None:
            refined, steps, ex = inherited.newton.contract(state, 8, oracle)
            if steps:
                packed_newton = [codec.pack_newton(step) for step in steps];state = refined
                if state is None:
                    kind, result = 'stationary_empty', {'reason': 'KKT-only contraction closure is empty'}
                else:
                    basin = inherited.gram.gram_basin(state, '11/1250', registry)
                    if basin:
                        kind, result = 'Gram', basin
                    elif ex:
                        ex['derivative_grid_sha256'] = oracle.sha;kind, result = 'stationary', ex
                    else:
                        kind, result = cheap(state)
                        if kind is None:
                            rec = w.certify(state)
                            if int(rec.get('floor_numerator', '-1')) >= g.TARGET:
                                kind, result = 'value', rec
        if kind is not None:
            resolution = {'kind': 'leaf', 'leaf': codec.pack_leaf({'path': path, 'depth': depth, 'kind': kind, 'result': result})}
        else:
            assert state is not None and rec is not None
            ax, cut = g.cut(state, rec);assert state[0][ax] < cut < state[1][ax];children = []
            for bit, upper in [('1', False), ('0', True)]:
                child = g.split(state, ax, cut, upper)
                if child is not None:
                    children.append({'path': path+bit, 'depth': depth+1, 'state': child})
            resolution = {'kind': 'branch', 'branch': {'path': path, 'axis': ax, 'cut': cut}, 'children': children}
    supports = [[p, *w.original_support(p)] for p in sorted(w.USED_SUPPORTS) if p not in known_supports]
    return {'path': path, 'depth': depth, 'epoch_sha256': epoch_digest,
      'incoming_cell_sha256': inherited.sha(inherited.store.canonical(incoming['state'])),
      'supports': supports, 'OBBT': packed_obbt, 'Newton': packed_newton, 'resolution': resolution}
