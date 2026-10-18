"""Read-only SDK/native-artifact inventory. Does not run any compiler or tool."""
from pathlib import Path
import json

ROOT = Path('/var/tmp/rh-zero-20261015/lean-4.33.0-rc2-linux')
NAMES = ['bin/lean', 'bin/lake', 'bin/leanc', 'bin/clang', 'bin/ld.lld',
         'include/lean/lean.h', 'lib/lean/libLean.a', 'lib/lean/libInit.a',
         'lib/lean/libStd.a', 'lib/lean/libleanrt.a', 'lib/lean/libleanshared.so',
         'lib/lean/libLake.a', 'src/lean/Lake/Config/LeanExeConfig.lean',
         'src/lean/Lean/Environment.lean']
result = {'scope': 'Read-only file inventory; no compiler, linker, ldd or verification command run',
          'sdk': [{'path': str(ROOT/n), 'exists': (ROOT/n).exists(),
                   'bytes': (ROOT/n).stat().st_size if (ROOT/n).exists() else None} for n in NAMES]}
result['cc_candidates'] = [{'path': n, 'exists': Path(n).exists(), 'resolved': str(Path(n).resolve())}
    for n in ['/usr/bin/cc', '/usr/bin/gcc', '/usr/bin/clang', '/usr/bin/ld', '/usr/bin/ar', '/usr/bin/ldd']]
result['existing_tool_ir'] = [{'package': name, 'files': [str(p.relative_to(Path('/var/tmp/rh-zero-20261015/.lake/packages')/name))
    for p in (Path('/var/tmp/rh-zero-20261015/.lake/packages')/name/'.lake/build').rglob('*')
    if p.is_file() and p.suffix in {'.c', '.o', '.a', '.so'}][:50]} for name in ['lean4export', 'Comparator']]
sources = {}
for rel in ['src/lean/Lake/Config/LeanExeConfig.lean', 'src/lean/Lean/Environment.lean',
            'src/lean/Lake/Build/Executable.lean', 'src/lean/Lake/Build/Common.lean']:
    p = ROOT / rel
    if not p.exists():
        continue
    lines = p.read_text(encoding='utf-8').splitlines()
    hits = [i for i, line in enumerate(lines) if any(t in line for t in [
        'supportInterpreter', 'importModules', 'loadDynlib', 'whole-archive', 'linkFlags', 'exportDynamic'])]
    selected = sorted({j for i in hits for j in range(max(0, i-3), min(len(lines), i+8))})
    sources[rel] = [{'line': j+1, 'text': lines[j]} for j in selected]
result['source_excerpts'] = sources
print(json.dumps(result, ensure_ascii=False, indent=2))
