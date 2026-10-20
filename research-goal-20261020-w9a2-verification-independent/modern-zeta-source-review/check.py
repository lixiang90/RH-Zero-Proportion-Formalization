"""Independent read-only Lake trace arithmetic; no SDK load/API/proof.

Reconstruct all four transitive import hashes from source header flags and
existing literal output .hash files, then compare every existing Zeta trace.
This deliberately does not establish actual output bytes' Lake hashes.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PKGS = [p for p in (ROOT / '.lake/packages').iterdir() if p.is_dir()]
SDK = Path('C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2')
MASK = (1 << 64) - 1
M = 0xc6a4a7935bd1e995
pins = {}
nodes = {}


def read(p):
    b = p.read_bytes()
    row = dict(path=str(p), bytes=len(b), sha256=hashlib.sha256(b).hexdigest())
    key = str(p).casefold()
    assert key not in pins or pins[key] == row
    pins[key] = row
    return b


def mix(h, k):
    k = (k * M) & MASK
    k ^= k >> 47
    k ^= M
    return ((h ^ k) * M) & MASK


def fold(values):
    h = 1723
    for x in values:
        h = mix(h, x)
    return h


def header(raw):
    text = raw.decode('utf-8')
    at = 0

    def space():
        nonlocal at
        while at < len(text):
            if text[at].isspace():
                assert text[at] != '\t'
                at += 1
            elif text.startswith('--', at):
                stop = text.find('\n', at)
                at = len(text) if stop == -1 else stop
            elif text.startswith('/-', at) and not text.startswith(('/--', '/-!'), at):
                depth = 1
                at += 2
                while depth:
                    assert at < len(text)
                    if text.startswith('/-', at):
                        depth += 1
                        at += 2
                    elif text.startswith('-/', at):
                        depth -= 1
                        at += 2
                    else:
                        at += 1
            else:
                break

    def token(word):
        nonlocal at
        stop = at + len(word)
        if text.startswith(word, at) and (stop == len(text) or not (text[stop].isalnum() or text[stop] in "_'")):
            at = stop
            space()
            return True
        return False

    space()
    modern = token('module')
    prelude = token('prelude')
    imports = []
    while True:
        saved = at
        public = token('public')
        meta = token('meta')
        if not token('import'):
            at = saved
            break
        all_ = token('all')
        assert modern or not (public or meta or all_)
        mat = re.match(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', text[at:])
        assert mat
        name = mat.group()
        at += len(name)
        assert at == len(text) or text[at].isspace() or text.startswith(('--', '/-'), at)
        imports.append(dict(name=name, public=public or not modern, meta=meta, all=all_))
        space()
    # SDK Init imports are absent from Lake.findModules; record their exact
    # parser defaults only in the report, never add them to package trace folds.
    return modern, prelude, imports


def source(name):
    rel = Path(*name.split('.')).with_suffix('.lean')
    found = [(p / rel, p) for p in PKGS if (p / rel).is_file()]
    if not found:
        assert any((r / rel).is_file() for r in [SDK / 'src/lean', SDK / 'src/lean/lake']), name
        return None
    assert len(found) == 1, name
    return found[0]


def visit(name):
    if name in nodes:
        return nodes[name]
    found = source(name)
    if found is None:
        return None
    source_path, pkg = found
    modern, prelude, imports = header(read(source_path))
    base = pkg / '.lake/build/lib/lean' / Path(*name.split('.'))
    # Reserve before recursion, then reject cyclic dependency if encountered.
    nodes[name] = None
    imps = []
    for imp in imports:
        child = visit(imp['name'])
        assert imp['name'] not in nodes or child is not None, name
        if child is not None:
            imps.append((imp, child))
    kinds = {'public': ['olean'], 'meta': ['olean', 'ir.sig', 'ir'],
             'all': ['olean', 'olean.server', 'olean.private', 'ir.sig', 'ir']}
    if not modern:
        kinds = {k: ['olean'] for k in kinds}
    artifact = {}
    for mode, suffixes in kinds.items():
        vals = []
        for suffix in suffixes:
            path = Path(str(base) + '.' + suffix + '.hash')
            literal = read(path).decode('ascii').strip()
            assert re.fullmatch('[0-9a-f]{16}', literal), str(path)
            vals.append(int(literal, 16))
        artifact[mode] = fold(vals)
    trans = {k: 1723 for k in ['public', 'meta', 'all', 'legacy']}
    expected = []
    for imp, child in imps:
        mode = 'all' if imp['all'] else 'meta' if imp['meta'] else 'public'
        selected = 'legacy' if not modern else mode
        arts = 'all' if not modern else mode
        expected += [[imp['name'] + ' transitive imports (' + selected + ')', f"{child['trans'][selected]:016x}"],
                     [imp['name'] + (':importAllArts' if arts == 'all' else ':importArts (meta)' if arts == 'meta' else ':importArts'), f"{child['artifact'][arts]:016x}"]]
        trans['legacy'] = mix(mix(trans['legacy'], child['trans']['legacy']), child['artifact']['all'])
        trans['all'] = mix(mix(trans['all'], child['trans'][mode]), child['artifact'][mode])
        trans['meta'] = mix(mix(trans['meta'], child['trans']['meta']), child['artifact']['meta'])
        if imp['public']:
            mode = 'meta' if imp['meta'] else 'public'
            trans['public'] = mix(mix(trans['public'], child['trans'][mode]), child['artifact'][mode])
    node = dict(source=str(source_path), base=str(base), modern=modern, prelude=prelude,
                imports=imports, artifact=artifact, trans=trans, expected_imports=expected)
    nodes[name] = node
    return node


def treehash(item):
    assert isinstance(item, list) and len(item) == 2 and isinstance(item[0], str)
    return int(item[1], 16) if isinstance(item[1], str) else fold(map(treehash, item[1]))


def main():
    trace_paths = sorted((ROOT / '.lake/packages/Zeta23/.lake/build/lib/lean/Zeta23').rglob('*.trace'))
    rows = []
    for p in trace_paths:
        module = '.'.join(p.relative_to(ROOT / '.lake/packages/Zeta23/.lake/build/lib/lean').with_suffix('').parts)
        n = visit(module)
        trace = json.loads(read(p))
        inputs = trace['inputs']
        assert len(inputs) == 9
        assert inputs[0][0] == 'deps'
        assert inputs[0][1][1] == ['imports', n['expected_imports']], module
        assert inputs[5] == ['isModule: ' + str(n['modern']).lower(), f"{mix(1723, 11 if n['modern'] else 13):016x}"], module
        actual = f"{fold(map(treehash, inputs)):016x}"
        assert trace['depHash'] == actual, module
        rows.append(dict(module=module, modern=n['modern'], imports_match=True,
                         depHash=actual, complete_trace_tree_hash_matches=True))
    euler = nodes['Zeta23.FromPNTPlus.EulerMaclaurin']
    assert euler['expected_imports'] == [
        ['Mathlib.NumberTheory.AbelSummation transitive imports (public)', '96f70e16101598b7'],
        ['Mathlib.NumberTheory.AbelSummation:importArts', 'baf83acae4c1bb2c']]
    after = []
    for r in pins.values():
        raw = Path(r['path']).read_bytes()
        assert len(raw) == r['bytes'] and hashlib.sha256(raw).hexdigest() == r['sha256']
        after.append(r)
    result = dict(scope='Read-only source-header flags plus existing .hash literal trace arithmetic; actual artifact-byte Lake hashes and fixed Git/SDK provenance are NOT checked here.',
                  SDK_loads=0, SDK_hash_API_calls=0, compiler_runs=0, proof_runs=0,
                  package_nodes=len(nodes), zeta_trace_count=len(rows),
                  modern_zeta=[r['module'] for r in rows if r['modern']],
                  modern_expected_imports=euler['expected_imports'],
                  implicit_Init_flags=dict(ordinary=dict(public=False,meta=False,all=False),meta=dict(public=False,meta=True,all=False)),
                  all_input_bytes_unchanged=True, zeta_traces=rows, input_files=after)
    with (HERE / 'evidence.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
        f.write('\n')
    print(json.dumps({k: result[k] for k in ['package_nodes', 'zeta_trace_count', 'modern_zeta', 'all_input_bytes_unchanged']}))


if __name__ == '__main__':
    main()
