"""Read-only cache/source provenance checks; no compiler or Lake execution.

The borrowed SDK hash APIs below only hash caller-owned constant byte/string
objects. They do not initialize an environment, import a module, run Lean main,
or check any user proof. Exact SDK archive verification must precede use.
"""
from pathlib import Path
import ctypes
import hashlib
import json
import os
import re
import struct
import subprocess

MASK = 2**64 - 1
M = 0xc6a4a7935bd1e995
CACHE_ROOTS = {'Mathlib', 'Batteries', 'BatteriesRecycling', 'Aesop', 'Cli', 'ImportGraph',
              'LeanSearchClient', 'Plausible', 'Qq', 'ProofWidgets', 'Archive', 'Counterexamples',
              'MathlibTest', 'Requests', 'OpenAIClient', 'Reap', 'Canonical', 'Duper', 'Auto',
              'PremiseSelection', 'Hammer'}


def mix(h, k):
    k = k * M & MASK
    k ^= k >> 47
    k ^= M
    return (h ^ k) * M & MASK


def hash_list(values):
    h = 7
    for value in values:
        h = mix(h, value)
    return h


class SDKHash:
    def __init__(self, sdk):
        assert os.name == 'nt' and ctypes.sizeof(ctypes.c_void_p) == 8
        self.directory = os.add_dll_directory(str(Path(sdk) / 'bin'))
        self.dll = ctypes.CDLL(str(Path(sdk) / 'bin/libleanshared.dll'))
        self.dll.lean_byte_array_hash.argtypes = [ctypes.c_void_p]
        self.dll.lean_byte_array_hash.restype = ctypes.c_uint64
        self.dll.lean_string_hash.argtypes = [ctypes.c_void_p]
        self.dll.lean_string_hash.restype = ctypes.c_uint64
        kernel = ctypes.WinDLL('kernel32', use_last_error=True)
        kernel.GetModuleFileNameW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p, ctypes.c_ulong]
        kernel.GetModuleFileNameW.restype = ctypes.c_ulong
        path = ctypes.create_unicode_buffer(32768)
        length = kernel.GetModuleFileNameW(self.dll._handle, path, len(path))
        assert 0 < length < len(path)
        self.loaded_path = Path(path.value)
        assert self.loaded_path.resolve() == (Path(sdk) / 'bin/libleanshared.dll').resolve()

    def bytes(self, raw):
        # lean.h: lean_object (8B), size_t size/capacity, scalar data.
        # Persistent refcount=0; borrowed hashing never consumes this object.
        buf = ctypes.create_string_buffer(24 + len(raw))
        struct.pack_into('<iHBBQQ', buf, 0, 0, 0, 1, 248, len(raw), len(raw))
        ctypes.memmove(ctypes.addressof(buf) + 24, raw, len(raw))
        return int(self.dll.lean_byte_array_hash(ctypes.addressof(buf)))

    def string(self, text):
        raw = text.encode('utf-8')
        buf = ctypes.create_string_buffer(32 + len(raw) + 1)
        struct.pack_into('<iHBBQQQ', buf, 0, 0, 0, 0, 249, len(raw) + 1,
                         len(raw) + 1, len(text))
        ctypes.memmove(ctypes.addressof(buf) + 32, raw, len(raw))
        return int(self.dll.lean_string_hash(ctypes.addressof(buf)))

    def lake_bytes(self, raw):
        return f'{mix(1723, self.bytes(raw)):016x}'

    def lake_text(self, raw):
        text = raw.decode('utf-8').replace('\r\n', '\n')
        return f'{mix(1723, self.string(text)):016x}'


def strip_comments(text):
    out, pos, depth = [], 0, 0
    while pos < len(text):
        if text.startswith('/-', pos):
            out.append(' ')
            depth += 1
            pos += 2
        elif depth and text.startswith('-/', pos):
            depth -= 1
            pos += 2
        elif depth:
            if text[pos] == '\n':
                out.append('\n')
            pos += 1
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        else:
            out.append(text[pos])
            pos += 1
    assert depth == 0
    return ''.join(out)


def imports(raw):
    return header(raw)[1]


def header(raw):
    """Exact supported prefix of ParseImportsFast; fail on escaped identifiers.

    Multiline imports work. Import order and duplicates are retained. Doc
    comments terminate the header just as ParseImportsFast.whitespace does.
    Only ASCII module names are admitted in this fixed source closure.
    """
    text = raw.decode('utf-8'); pos = 0
    def ws():
        nonlocal pos
        while pos < len(text):
            if text[pos].isspace():
                assert text[pos] != '\t', 'Tab in import header'
                pos += 1
            elif text.startswith('--', pos):
                end = text.find('\n', pos); pos = len(text) if end < 0 else end
            elif text.startswith('/-', pos) and not text.startswith(('/--', '/-!'), pos):
                depth = 1; pos += 2
                while depth:
                    assert pos < len(text), 'Unterminated header comment'
                    if text.startswith('/-', pos): depth += 1; pos += 2
                    elif text.startswith('-/', pos): depth -= 1; pos += 2
                    else: pos += 1
            else: return
    def kw(word):
        nonlocal pos
        if text.startswith(word, pos) and (pos + len(word) == len(text) or
             not (text[pos+len(word)].isalnum() or text[pos+len(word)] in "_'")):
            pos += len(word); ws(); return True
        return False
    ws(); is_module = kw('module'); prelude = kw('prelude'); result = []
    while True:
        start = pos; public = kw('public'); meta = kw('meta')
        if not kw('import'):
            # Atomic import parser rolls back before a legal body command,
            # e.g. `public section` or `public meta section`.
            pos = start; break
        all_import = kw('all')
        assert is_module or not (public or meta or all_import)
        match = re.match(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', text[pos:])
        assert match, 'Unsupported module identifier'
        result.append(match.group()); pos += len(match.group())
        assert pos == len(text) or text[pos].isspace() or text.startswith(('--', '/-'), pos), 'Unsupported module identifier tail'
        ws()
    return is_module, result, prelude


def git_tree(package, expected):
    env = dict(os.environ, GIT_NO_LAZY_FETCH='1', GIT_OPTIONAL_LOCKS='0')
    prefix = ['git', '-c', 'safe.directory=' + str(package), '-C', str(package)]
    actual = subprocess.check_output(prefix + ['rev-parse', 'HEAD'], env=env, text=True).strip()
    assert actual == expected
    rows = subprocess.check_output(prefix + ['ls-tree', '-rz', 'HEAD'], env=env)
    result = {}
    for row in rows.split(b'\0'):
        if row:
            meta, name = row.split(b'\t', 1)
            mode, kind, oid = meta.decode().split()
            result[name.decode()] = (mode, kind, oid)
    return result


def canonical_git_blob(path, relative, tree):
    mode, kind, oid = tree[relative]
    assert mode in ['100644', '100755'] and kind == 'blob'
    raw = Path(path).read_bytes()
    for value in [raw, raw.replace(b'\r\n', b'\n')]:
        digest = hashlib.sha1(b'blob ' + str(len(value)).encode() + b'\0' + value).hexdigest()
        if digest == oid:
            return value
    raise AssertionError('Source differs from pinned Git blob: ' + str(path))


def flatten_values(value):
    if isinstance(value, dict):
        for x in value.values():
            yield from flatten_values(x)
    elif isinstance(value, list):
        for x in value:
            yield from flatten_values(x)
    elif isinstance(value, str):
        yield value


def trace_bind(source, base, sdk_hash, pin):
    """Source/SDK/output checks. Assembler separately checks complete inputs."""
    trace_path = base.with_suffix('.trace')
    trace = json.loads(trace_path.read_text(encoding='utf-8'))
    values = list(flatten_values(trace.get('inputs', [])))
    expected_source = sdk_hash.lake_text(source.read_bytes())
    pairs = {}
    def visit(x):
        if isinstance(x, list):
            if len(x) == 2 and isinstance(x[0], str) and isinstance(x[1], str):
                pairs[x[0]] = x[1]
            for y in x:
                visit(y)
    visit(trace.get('inputs', []))
    source_entries = [(k, v) for k, v in pairs.items() if k.lower().endswith('.lean')]
    assert any(Path(k).name.casefold() == source.name.casefold() and v == expected_source
               for k, v in source_entries), str(source)
    assert any('d8b18978322de05a8f3dba51ef03cf5461676c17' in v for v in values)
    return verify_outputs(trace, base, sdk_hash, pin)


def verify_outputs(trace, base, sdk_hash, pin):
    pin(base.with_suffix('.trace'), 'source-bound-Lake-trace')
    outputs = trace['outputs']
    assert isinstance(outputs, dict) and outputs.get('o')
    data = []
    for suffix in ['olean', 'olean.server', 'olean.private', 'ir', 'ir.sig']:
        path = base.with_suffix('.' + suffix)
        if not path.exists():
            continue
        raw = path.read_bytes()
        lake = sdk_hash.lake_bytes(raw)
        assert lake + '.' + suffix in list(flatten_values(outputs)), str(path)
        stored_hash = Path(str(path) + '.hash')
        assert stored_hash.read_text().strip() == lake, str(path)
        pin(path, 'source-bound-cached-data')
        pin(stored_hash, 'verified-Lake-output-hash')
        data.append(path)
    assert base.with_suffix('.olean') in data
    expected = outputs['o'] + ([outputs['r']] if outputs.get('r') else []) + ([outputs['rs']] if outputs.get('rs') else [])
    assert len(data) == len(expected), str(base)
    return data


class CacheSourceHash:
    def __init__(self, sdk_hash, mathlib, find_source, canonical_source):
        self.sdk = sdk_hash
        self.find = find_source
        self.canonical = canonical_source
        self.memo = {}
        self.active = set()
        self.root_hash = hash_list([5] + [self.sdk.string((mathlib / n).read_bytes().decode('utf-8').replace('\r\n', '\n'))
                                        for n in ['lakefile.lean', 'lean-toolchain', 'lake-manifest.json']])

    def module(self, module):
        if module in self.memo:
            return self.memo[module]
        assert module not in self.active
        self.active.add(module)
        path, owner = self.find(module)
        assert owner != 'SDK'
        raw = self.canonical(path, owner)
        deps = [m for m in imports(raw) if m.split('.')[0] in CACHE_ROOTS]
        import_hashes = [self.module(m) for m in deps]
        parts = module.split('.')
        parts[-1] += '.lean'
        path_hash = hash_list([self.sdk.string(s) for s in parts])
        file_hash = self.sdk.string(raw.decode('utf-8').replace('\r\n', '\n'))
        value = hash_list([self.root_hash, path_hash, file_hash, *import_hashes])
        self.memo[module] = value
        self.active.remove(module)
        return value
