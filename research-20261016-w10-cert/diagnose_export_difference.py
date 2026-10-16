"""Small independent NDJSON expression diagnostic, not a proof checker."""
from pathlib import Path
from array import array
import json, re, sys, hashlib


class Export:
    def __init__(self, path, limit):
        self.path = Path(path)
        self.stream = self.path.open('rb')
        self.offsets = array('Q', [0])
        self.names = {0: ''}
        self.levels = {}
        self.proof_declarations = {}
        offset = 0
        for line in self.stream:
            if line.startswith(b'{"in":'):
                data = json.loads(line)
                if 'str' in data:
                    v = data['str']; n = v['str']
                else:
                    v = data['num']; n = str(v['i'])
                pre = self.names[v['pre']]
                self.names[data['in']] = pre + '.' + n if pre else n
            elif b'"il":' in line:
                data = json.loads(line)
                self.levels[data['il']] = data
            elif line.startswith((b'{"thm":', b'{"def":')):
                data = json.loads(line)
                kind = next(iter(data))
                decl = data[kind]
                name = self.names[decl['name']]
                if any(name == prefix + suffix for prefix in [
                    'StructuralW10Cert20261016.FinalConditional.SeparatedFloor.', 'Pantera.sep.']
                    for suffix in ['_proof_1', '_proof_2']):
                    self.proof_declarations[name] = {'kind': kind, 'record': decl}
            match = re.search(rb'"ie":(\d+)', line)
            if match:
                index = int(match[1])
                while len(self.offsets) <= index:
                    self.offsets.append(0)
                self.offsets[index] = offset
                if index >= limit:
                    break
            offset += len(line)
        self.cache = {}

    def get(self, index):
        if index not in self.cache:
            self.stream.seek(self.offsets[index])
            self.cache[index] = json.loads(self.stream.readline())
        return self.cache[index]

    def tree(self, index):
        data = self.get(index)
        kind = next(k for k in data if k != 'ie')
        v = data[kind]
        if kind == 'const':
            return [kind, self.names[v['name']], v['us']]
        if kind in ['forallE', 'lam']:
            return [kind, self.names[v['name']], v['binderInfo'], self.tree(v['type']), self.tree(v['body'])]
        if kind == 'app':
            return [kind, self.tree(v['fn']), self.tree(v['arg'])]
        if kind == 'bvar':
            return [kind, v]
        if kind in ['lit', 'sort', 'natVal', 'strVal']:
            return [kind, v]
        if kind == 'letE':
            return [kind, self.names[v['name']], self.tree(v['type']), self.tree(v['value']), self.tree(v['body'])]
        if kind == 'proj':
            return [kind, self.names[v['typeName']], v['idx'], self.tree(v['struct'])]
        raise ValueError(data)


def main():
    work = Path('/var/tmp/rh-zero-20261015/w10-conditional-replay')
    result = {}
    proof_declarations = {}
    for label in ['modular', 'single']:
        export = Export(work/(label+'-export.ndjson'), 2916763)
        tree = export.tree(2916763)
        result[label] = tree
        proof_declarations[label] = {
            name: {**d, 'type_expression': export.tree(d['record']['type']),
                   'value_expression': export.tree(d['record']['value'])}
            for name, d in export.proof_declarations.items()}
    print('same_tree', result['modular'] == result['single'])
    def differences(a, b, path=()):
        if a == b: return []
        if isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
            return [d for i, (x,y) in enumerate(zip(a,b)) for d in differences(x,y,path+(i,))]
        return [{'path': list(path), 'modular': a, 'single': b}]
    diagnostic = {
        'scope': 'DIAGNOSTIC_ONLY', 'proof_checked_by_this_script': False,
        'pinned_comparator_passed': False,
        'same_tree': result['modular'] == result['single'],
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'export_sha256': {k: hashlib.sha256((work/(k+'-export.ndjson')).read_bytes()).hexdigest()
                          for k in ['modular', 'single']},
        'differences': differences(result['modular'], result['single']),
        'proof_types_description': ['Nat.AtLeastTwo (16 + 1)', 'Nat.AtLeastTwo (19 + 1)'],
        'individual_proof_axiom_closure_computed': False,
        'permitted_global_axioms': ['propext','Quot.sound','Classical.choice'],
        'whole_export_nanoda_observed_axioms': {
            label: re.findall(r'^axiom ([^\s.{]+(?:\.[^\s.{]+)*)',
                (work/'logs'/(('modular' if label=='modular' else 'single')+'-nanoda.log')).read_text(), re.M)
            for label in ['modular','single']},
        'proof_declarations': proof_declarations,
        'expression_trees': result}
    pairs=[]
    for i in [1,2]:
        left=proof_declarations['modular']['StructuralW10Cert20261016.FinalConditional.SeparatedFloor._proof_'+str(i)]
        right=proof_declarations['single']['Pantera.sep._proof_'+str(i)]
        pairs.append({'index':i, 'same_type_expression':left['type_expression']==right['type_expression'],
                      'same_value_expression':left['value_expression']==right['value_expression']})
    diagnostic['proof_pair_structural_comparison']=pairs
    print(json.dumps({k: diagnostic[k] for k in ['differences','proof_types_description',
                      'proof_pair_structural_comparison','whole_export_nanoda_observed_axioms']}))
    target=work/'separated-floor-expression-diagnostic.json'
    target.write_text(json.dumps(diagnostic, indent=2))
    repo=Path(__file__).resolve().parents[1]/'verification/w10-20261016/conditional'
    (repo/target.name).write_bytes(target.read_bytes())


if __name__ == '__main__':
    main()
