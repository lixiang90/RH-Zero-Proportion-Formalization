"""Read SDK text and write metadata only. No compiler/linker/tool executable run."""
from pathlib import Path
import json

SDK = Path('/var/tmp/rh-zero-20261015/lean-4.33.0-rc2-linux')
OUT = Path('/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization/research-goal-20261019-native-tools-preparation/sdk-details.json')
assert not OUT.exists()
found = []
for p in (SDK / 'src').rglob('*.lean'):
    if any(k in p.as_posix() for k in ['/Lake/Config/LeanExe', '/Lake/Build/Executable',
                                      '/Lake/Build/Common', '/Lean/Util/Path.lean']):
        found.append(p)
excerpts = {}
for p in found:
    lines = p.read_text(encoding='utf-8').splitlines()
    hits = [i for i, l in enumerate(lines) if any(t in l for t in [
        'supportInterpreter', 'findSysroot', 'LEAN_SYSROOT', 'whole-archive',
        'exportDynamic', 'linkArgs', 'moreLinkArgs', 'leancArgs'])]
    selected = sorted({j for i in hits for j in range(max(0, i-4), min(len(lines), i+13))})
    excerpts[str(p.relative_to(SDK))] = [{'line': i+1, 'text': lines[i]} for i in selected]
libraries = [{'path': str(p), 'bytes': p.stat().st_size} for p in sorted((SDK/'lib').rglob('*'))
             if p.is_file() and ('.so' in p.name or p.suffix == '.a')]
obj = {'scope': 'Read-only SDK/source/library metadata; no tool execution',
       'source_files_found': list(excerpts), 'excerpts': excerpts,
       'native_libraries': libraries,
       'sdk_executables': [{'path': str(SDK/'bin'/n), 'exists': (SDK/'bin'/n).exists()}
                           for n in ['lean','lake','leanc','clang','ld.lld','llvm-ar']]}
with OUT.open('x', encoding='utf-8') as f:
    json.dump(obj, f, ensure_ascii=False, indent=2); f.write('\n')
print(json.dumps({'read_only_metadata_written': True, 'source_files': len(excerpts),
                  'libraries': len(libraries)}))
