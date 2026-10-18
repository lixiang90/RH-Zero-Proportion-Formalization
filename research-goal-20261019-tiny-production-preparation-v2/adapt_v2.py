"""Static adaptation to pinned preinstalled native tools and official serial Nano.

Writes a new version only. Does not execute the cold runner or generator.
"""
import ast
import difflib
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
OLD = ROOT / 'research-goal-20261019-tiny-production-preparation-v1'

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    oldmanifest = OLD / 'prepared-files.json'
    assert sha(oldmanifest.read_bytes()) == '68fe3090b406a84ac30d88ebd8e75b104e1d30ddea50e81fd83ca2a09cc1f4b3'
    for row in json.loads(oldmanifest.read_text(encoding='utf-8'))['files']:
        assert sha((ROOT / row['path']).read_bytes()) == row['sha256']
    s = (OLD / 'run_production.py').read_text(encoding='utf-8')
    s = s.replace('/var/tmp/rh-zero-20261015/tiny-production-v1', '/var/tmp/rh-zero-20261015/tiny-production-v2')
    s = s.replace('tmp/current-s1r-tiny-20261018/production-v1', 'tmp/current-s1r-tiny-20261018/production-v2')
    s = s.replace("'schema': 'tiny-cold-production-result-v2'", "'schema': 'tiny-cold-production-result-v3'")
    marker = '        self.active = None\n        self.setup_done = False'
    assert s.count(marker) == 1
    s = s.replace(marker, marker + '\n        self.native_resolutions = {}\n        self.native_binaries = {}')
    marker = '    def immutable(self):\n'
    assert s.count(marker) == 1
    s = s.replace(marker, marker + "        for original, resolved in self.native_resolutions.items():\n            assert str(Path(original).resolve()) == resolved, 'A native runtime symlink changed'\n")
    s = s.replace("'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}", "'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8',\n                'LEAN_SYSROOT': str(Path(self.lean).parent.parent)}")
    method = (HERE / 'native_binding_method.py.txt').read_text(encoding='utf-8')
    marker = '    def source(self, folder, relative, data):'
    assert s.count(marker) == 1
    s = s.replace(marker, method + '\n' + marker)
    s = s.replace("self.receipt['local_nanoda_threads'] = 4", "self.receipt['local_nanoda_threads'] = 0")
    marker = "        self.bind(config['Windows_Python_DLL_Linux_path'], config['Windows_Python_DLL_sha256'])"
    assert s.count(marker) == 1
    s = s.replace(marker, marker + '\n        self.bind_native_tools(gate, config)')
    a = s.index("        tools = self.work / 'tools'")
    b = s.index('        exports = {}', a)
    s = s[:a] + "        toolpaths = paths  # Native tools need no trusted-tool/user olean overlay.\n        self.immutable()\n" + s[b:]
    old = """            exports[label] = self.run(label + '-export', self.lean_command('--run',
                tools / 'source/ExporterMain.lean', module, '--', *ROOTS, *PRIMITIVES),
                env=self.environment(toolpaths), output=target)"""
    new = """            exports[label] = self.run(label + '-export',
                [self.native_binaries['lean4export'], module, '--', *ROOTS, *PRIMITIVES],
                env=self.environment(toolpaths), output=target)"""
    assert s.count(old) == 1
    s = s.replace(old, new)
    old = """        self.run('comparator-default-kernel', self.lean_command('--run', tools / 'source/CoreAudit.lean',
            self.work / 'challenge.ndjson', self.work / 'solution.ndjson', *ROOTS), env=self.environment(toolpaths))"""
    new = """        self.run('comparator-default-kernel',
            [self.native_binaries['coreaudit'], str(self.work / 'challenge.ndjson'),
             str(self.work / 'solution.ndjson'), *ROOTS], env=self.environment(toolpaths))"""
    assert s.count(old) == 1
    s = s.replace(old, new)
    assert s.count("'num_threads': 4") == 1
    s = s.replace("'num_threads': 4", "'num_threads': 0")
    assert '--run' not in s
    assert 'tomllib' not in s
    helper = (OLD / 'windows_generate.py').read_text(encoding='utf-8').replace(
        'tmp/current-s1r-tiny-20261018/production-v1', 'tmp/current-s1r-tiny-20261018/production-v2')
    freezer = (OLD / 'freeze_static.py').read_text(encoding='utf-8')
    freezer = freezer.replace("'schema': 'tiny-production-configuration-v2'", "'schema': 'tiny-production-configuration-v3'")
    freezer = freezer.replace("'schema': 'tiny-cold-production-prepared-v2'", "'schema': 'tiny-cold-production-prepared-v3'")
    freezer = freezer.replace("'local_nanoda_threads': 4", "'local_nanoda_threads': 0")
    marker = "    depnames = {"
    freezer = freezer.replace(marker, marker + "\n        'research-goal-20261019-tiny-production-preparation-v1/prepared-files.json',\n        'research-goal-20261019-tiny-production-preparation-v1/run_production.py',\n        'research-goal-20261019-native-tools-preparation/prepared-files.json',\n        'research-goal-20261019-native-tools-preparation/lakefile.toml.in',\n        'research-goal-20261019-native-verifier-source-audit/files.json',\n        'research-goal-20261019-native-verifier-source-audit/install-verifier-tools.sh',")
    marker = "        'local_nanoda_threads': 0,"
    freezer = freezer.replace(marker, marker + "\n        'native_lakefile_template': 'research-goal-20261019-native-tools-preparation/lakefile.toml.in',\n        'native_installation_and_setup_prepared_supplied_by_gate': True,\n        'preinstalled_trusted_native_tools_required': True,\n        'trusted_tools_recompiled_in_proof_attempt': False,")
    outputs = {'run_production.py': s, 'windows_generate.py': helper, 'freeze_static.py': freezer}
    for name, text in outputs.items():
        ast.parse(text, filename=name)
        assert not (HERE / name).exists()
    for name, text in outputs.items():
        with (HERE / name).open('x', encoding='utf-8', newline='\n') as f:
            f.write(text)
    diff = ''.join(''.join(difflib.unified_diff((OLD / name).read_text(encoding='utf-8').splitlines(keepends=True),
        text.splitlines(keepends=True), fromfile='interpreted-v1/' + name, tofile='native-v2/' + name))
        for name, text in outputs.items())
    with (HERE / 'v1-to-v2.diff').open('x', encoding='utf-8', newline='\n') as f:
        f.write(diff)
    with (HERE / 'version-delta.json').open('x', encoding='utf-8', newline='\n') as f:
        json.dump({'schema': 'native-serial-fullcold-v2-static-adaptation',
            'old_prepared_sha256': sha(oldmanifest.read_bytes()),
            'new_linux_directory': '/var/tmp/rh-zero-20261015/tiny-production-v2',
            'native_installation_path_and_sha_are_gate_parameters': True,
            'native_source_and_binary_runtime_closure_checked_under_proof_t0': True,
            'nanoda_num_threads': 0, 'trusted_tools_recompiled': False,
            'candidate_generation_or_verification_executions': 0,
            'full_checking_scope_and_allowed_axioms_unchanged': True,
            'old_files_modified': False}, f, indent=2); f.write('\n')
    print(json.dumps({'native_fullcold_statically_adapted': True, 'proof_executions': 0}))

if __name__ == '__main__':
    main()
