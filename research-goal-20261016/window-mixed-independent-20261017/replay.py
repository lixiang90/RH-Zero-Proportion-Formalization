"""Serial, pinned two-kernel replay of selected mixed-cover milestone roots.

Run under WSL only after the ordinary Lean queue has stopped. This checks a
partial mathematical interface, not the website contract or a global floor.
The exporter, Comparator self-audit and Nano are the existing pinned tools.
"""
from pathlib import Path
import argparse, json, os, re, shutil, sys, time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'scripts'))
import verify_single_solution as base
import verify_record_20261015 as legacy


def main():
    assert __debug__ and os.name != 'nt', 'Run under the pinned WSL Python, without -O'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('module')
    ap.add_argument('--root', action='append', default=[])
    ap.add_argument('--root-manifest', type=Path)
    ap.add_argument('--work-dir', type=Path, required=True)
    ap.add_argument('--scope')
    ap.add_argument('--timeout', type=int, default=14400)
    args = ap.parse_args()
    if args.root_manifest:
        selection = json.loads(args.root_manifest.read_bytes())
        assert selection['module'] == args.module
        assert selection['ordinary_compile_proven'], 'Freeze a current ordinary-kernel receipt first'
        args.root += selection['roots']
        args.scope = args.scope or selection['scope']
    assert args.root and args.scope, 'Provide roots and their explicitly partial scope'
    identifier = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+')
    assert all(identifier.fullmatch(n) for n in [args.module, *args.root])
    work = args.work_dir.resolve()
    assert work.is_relative_to(Path('/var/tmp/rh-zero-20261015'))
    assert not work.exists() or not any(work.iterdir()), 'Use a fresh replay directory'
    (work/'logs').mkdir(parents=True, exist_ok=True)
    output = HERE/'window-mixed-independent-replay.json'
    setup = ROOT/'tmp/setup-20261015'
    args.runtime_manifest = setup/'runtime.json'
    args.sources_manifest = setup/'sources.json'
    args.dependencies_manifest = setup/'dependencies.json'
    args.package_manifest = ROOT/'lake-manifest.json'
    args.nanoda_provenance = setup/'nanoda-build.json'
    args.nanoda_bin = Path('/var/tmp/rh-zero-20261015/nanoda-target/release/nanoda_bin')
    args.nanoda_sha256 = None
    args.distribution = 'Ubuntu'
    args.prepare_only = False
    record = {
        'scope': args.scope, 'module': args.module, 'roots': list(dict.fromkeys(args.root)),
        'passed': False, 'stage': 'preflight', 'partial_roots_only': True,
        'website_statement_verified': False, 'unconditional_counting_proven': False,
        'global_energy_floor_proven': False,
        'all_partition_checked': False, 'submission_ready': False, 'submitted': False,
        'official_website_acceptance': False, 'single_heavy_process_required': True,
    }
    bound = {}
    started = time.time()

    def bind(path):
        path = path.resolve()
        digest = base.sha(path)
        assert str(path) not in bound or bound[str(path)] == digest
        bound[str(path)] = digest
        return digest

    def checkpoint(stage):
        record['stage'] = stage
        record['elapsed_seconds'] = time.time()-started
        record['bound_input_sha256'] = bound
        base.write_json(work/'verification.json', record)
        base.write_json(output, record)
        print(json.dumps({'stage': stage, 'passed': record['passed']}), flush=True)

    def command(paths, *extra):
        return ['/usr/bin/prlimit', '--stack=268435456:268435456', '--', 'env',
                'PATH='+lean.rsplit('/', 1)[0]+':/usr/bin:/bin',
                'LEAN_PATH='+':'.join(map(str, paths)), lean, '-j1', '-M13500',
                '--tstack=262144', '-DrelaxedAutoImplicit=false', *extra]

    def run(label, argv, *, binary=False, stdin=None):
        resources = work/'logs'/f'{label}-resources.log'
        result = base.run_logged(args,
            ['/usr/bin/time', '-v', '-o', str(resources), *argv],
            work/'logs'/f'{label}.log', stdin=stdin,
            binary_output=work/f'{label}.ndjson' if binary else None)
        bind(resources)
        bind(Path(result['log']))
        return result

    try:
        # Refuse a concurrent Lean/exporter/Nano process. The caller owns the
        # ordinary queue and must reach an actual process boundary first.
        import subprocess
        for name in ['lean', 'nanoda_bin']:
            p = subprocess.run(['/usr/bin/pgrep', '-x', name], capture_output=True)
            assert p.returncode == 1, ('A heavy verifier is still running', name, p.stdout)
        bind(Path(__file__))
        if args.root_manifest:
            record['root_manifest_sha256'] = bind(args.root_manifest)
        for p in [Path(base.__file__), Path(legacy.__file__), args.runtime_manifest,
                  args.sources_manifest, args.dependencies_manifest, args.package_manifest,
                  args.nanoda_provenance, ROOT/'tools/ComparatorCoreAudit.lean']:
            bind(p)
        lean, packages, info = legacy.runtime(args)
        record['runtime'] = {k: v for k, v in info.items() if k != 'dependency_compiled_modules'}
        record['pins'] = base.PINS
        libraries = [Path('/var/tmp/rh-zero-20261015/w10-cert/lib'),
                     Path('/var/tmp/rh-zero-20261015/research-20261016/lib'),
                     Path('/var/tmp/rh-zero-20261015/record-verification/modular/lib')]
        ordinary = json.loads((HERE/'lean_verification.json').read_bytes())
        known = {row['module']: row for row in ordinary['modules']}
        modules, pending = {}, [args.module]
        while pending:
            name = pending.pop()
            if name in modules:
                continue
            relative = Path(*name.split('.'))
            source = ROOT/relative.with_suffix('.lean')
            if not source.exists():
                continue  # External packages are validated by the pinned runtime.
            olean = next(p/relative.with_suffix('.olean') for p in libraries
                         if (p/relative.with_suffix('.olean')).is_file())
            source_hash, olean_hash = bind(source), bind(olean)
            if name == args.module and args.root_manifest:
                assert source_hash == selection['source_sha256']
            if name.startswith('StructuralGoal20261016.'):
                row = known[name]
                assert row['passed'] and row['source_unchanged']
                assert row['source_sha256'] == source_hash and row['olean_sha256'] == olean_hash
                log = HERE/row['log']
                assert bind(log) == row['log_sha256']
            modules[name] = {'source_sha256': source_hash, 'olean_sha256': olean_hash}
            pending += re.findall(r'^import\s+(\S+)', source.read_text(), re.M)
        record['bound_local_modules'] = modules
        checkpoint('pinned-tool-preparation')
        tools, provenance = legacy.copy_tools(args, work)
        record['tool_provenance'] = provenance
        for p in (tools/'source').rglob('*.lean'):
            bind(p)
        bind(args.nanoda_bin)
        tool_paths = [str(tools/'lib'), *packages]
        record['tool_compilation'] = [base.compile_one(args, lean, tool_paths, tools, m)
                                      for m in base.topological_modules(tools)]
        for p in (tools/'lib').rglob('*'):
            if p.is_file():
                bind(p)
        paths = [tools/'lib', *libraries, *packages]
        roots = record['roots']
        checkpoint('export')
        export_roots = list(dict.fromkeys([*roots, *base.PRIMITIVES]))
        record['export'] = run('export', command(paths, '--run',
            str(tools/'source/ExporterMain.lean'), args.module, '--', *export_roots), binary=True)
        export = work/'export.ndjson'
        record['export_sha256'], record['export_bytes'] = bind(export), export.stat().st_size
        checkpoint('default-kernel-self-replay')
        record['default_kernel'] = run('default-kernel', command(tool_paths, '--run',
            str(tools/'source/CoreAudit.lean'), str(export), str(export), *roots))
        text = Path(record['default_kernel']['log']).read_text(errors='replace')
        for phrase in ['Pinned Comparator statement, dependency and primitive comparison passed',
                       'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
            assert phrase in text
        record['default_kernel_passed'] = True
        record['comparison_scope'] = 'Self-replay of selected roots; NOT a website statement comparison'
        checkpoint('independent-nanoda')
        config = work/'nanoda-config.json'
        base.write_json(config, {'use_stdin': True, 'permitted_axioms': base.ALLOWED,
            'unpermitted_axiom_hard_error': True, 'nat_extension': True, 'string_extension': True,
            'num_threads': 2, 'unsafe_permit_all_axioms': False, 'print_success_message': True,
            'print_axioms': True, 'pp_to_stdout': True})
        bind(config)
        record['nanoda'] = run('nanoda', [str(args.nanoda_bin), str(config)], stdin=export)
        text = Path(record['nanoda']['log']).read_text(errors='replace')
        count = re.search(r'Checked (\d+) declarations with no errors', text)
        assert count
        axioms = [n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', text, re.M)]
        assert set(axioms) <= set(base.ALLOWED)
        record['nanoda'].update(checked_declarations=int(count[1]), observed_axioms=axioms)
        assert bound == {n: base.sha(Path(n)) for n in bound}, 'A bound input changed'
        record.update(passed=True, inputs_unchanged=True, independent_nanoda_passed=True)
        checkpoint('complete')
    except Exception as error:
        record.update(passed=False, error_type=type(error).__name__, error=str(error))
        checkpoint('failed')
        raise
    finally:
        checkpoint(record['stage'])


if __name__ == '__main__':
    main()
