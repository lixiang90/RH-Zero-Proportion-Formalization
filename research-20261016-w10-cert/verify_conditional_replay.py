"""CONDITIONAL_ONLY: compare and replay the explicit-premise W10 theorems.

This deliberately does not target the website's three unconditional roots.
It reuses the sealed base's already successful ordinary Lean compilation.
The complete concrete finite certificate is not asserted or evaluated here.
Run under the pinned WSL Python runtime; no website upload is performed.
"""
from pathlib import Path
import argparse, json, os, re, shutil, sys, time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'scripts'))
import verify_single_solution as base
import verify_record_20261015 as legacy

FINAL = 'StructuralW10Cert20261016.FinalConditional.'
FINITE = 'StructuralW10Cert20261016.FiniteConditional.'
FINAL_ROOTS = [FINAL+n for n in ['exact_formula', 'strict_improvement', 'simple_dyadic',
                                'simple_cumulative', 'distinct_dyadic', 'distinct_cumulative']]
FINITE_ROOTS = [FINITE+n for n in ['local_floor', 'strict_improvement', 'simple_dyadic',
                                  'simple_cumulative', 'distinct_dyadic', 'distinct_cumulative']]
SINGLE_MODULE = '«research-20261016-w10-cert».BundlePreflight'
SINGLE_SHA = 'c82f5d7e3e07f563722f62fdd3087e00fb7ce490e9c1b2fe4c0b61404b734dae'


def main():
    if not __debug__:
        raise RuntimeError('Conditional verification assertions must remain enabled')
    assert os.name != 'nt', 'Run this script under WSL'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work-dir', type=Path, default=Path('/var/tmp/rh-zero-20261015/w10-conditional-replay'))
    ap.add_argument('--receipt-dir', type=Path, default=ROOT/'verification/w10-20261016/conditional')
    ap.add_argument('--timeout', type=int, default=14400)
    args = ap.parse_args()
    work = args.work_dir.resolve()
    assert work.is_relative_to(Path('/var/tmp/rh-zero-20261015'))
    assert not work.exists() or not any(work.iterdir()), 'Use a fresh conditional replay directory'
    for sub in ['lib', 'logs']:
        (work/sub).mkdir(parents=True, exist_ok=True)
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
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
    receipt = {'scope': 'CONDITIONAL_ONLY', 'passed': False,
               'website_statement_verified': False, 'higher_kappa': False,
               'higher_kappa_proven': False, 'all_partition_checked': False,
               'submission_ready': False, 'submitted': False,
               'official_website_acceptance': False,
               'final_conditional_roots': FINAL_ROOTS, 'finite_conditional_roots': FINITE_ROOTS,
               'stage': 'runtime-validation'}
    bound = {}

    def bind(path):
        path = path.resolve()
        value = base.sha(path)
        if str(path) in bound:
            assert bound[str(path)] == value
        bound[str(path)] = value
        return value

    def checkpoint(stage):
        receipt['stage'] = stage
        base.write_json(work/'verification.json', receipt)
        print(stage, flush=True)

    def run(label, command, *, binary=False):
        resources = work/'logs'/f'{label}-resources.log'
        command = ['/usr/bin/time', '-v', '-o', str(resources), *command]
        result = base.run_logged(args, command, work/'logs'/f'{label}.log',
                                 binary_output=work/f'{label}.ndjson' if binary else None)
        result['resources_sha256'] = base.sha(resources)
        return result

    try:
        bind(Path(__file__))
        for path in [Path(base.__file__), Path(legacy.__file__), args.runtime_manifest,
                     args.sources_manifest, args.dependencies_manifest, args.package_manifest,
                     args.nanoda_provenance, ROOT/'tools/ComparatorCoreAudit.lean']:
            bind(path)
        lean, package_paths, info = legacy.runtime(args)
        receipt['runtime'] = {k: v for k, v in info.items() if k != 'dependency_compiled_modules'}
        receipt['pins'] = base.PINS
        sealed = ROOT/'submission/w10-20261016/proof/ConditionalBase.lean'
        compile_receipt = HERE/'compressed-preflight.json'
        provenance = json.loads(compile_receipt.read_bytes())
        assert provenance['passed'] and provenance['exit_code'] == 0 and provenance['source_unchanged']
        assert provenance['source_sha256'] == bind(sealed) == SINGLE_SHA
        bind(compile_receipt)
        original = Path('/var/tmp/rh-zero-20261015/w10-base-preflight/Compressed.olean')
        single_olean = work/'lib/research-20261016-w10-cert/BundlePreflight.olean'
        single_olean.parent.mkdir(parents=True, exist_ok=True)
        original_sha = bind(original)
        shutil.copyfile(original, single_olean)
        assert bind(single_olean) == original_sha
        receipt['sealed_base'] = {'source_sha256': SINGLE_SHA, 'source_bytes': sealed.stat().st_size,
                                  'compile_receipt_sha256': base.sha(compile_receipt),
                                  'compiled_olean_sha256': original_sha,
                                  'actual_module_name': 'research-20261016-w10-cert.BundlePreflight',
                                  'ordinary_compilation_reused': True}
        local_libraries = [Path('/var/tmp/rh-zero-20261015/w10-cert/lib'),
                           Path('/var/tmp/rh-zero-20261015/record-verification/modular/lib')]
        local_modules = set()
        pending = ['StructuralW10Cert20261016.FiniteConditional']
        while pending:
            name = pending.pop()
            if name in local_modules:
                continue
            local_modules.add(name)
            path = ROOT/Path(*name.split('.')).with_suffix('.lean')
            bind(path)
            top = name.split('.')[0]
            library = next(lib for lib in local_libraries if (lib/top).is_dir())
            bind(library/Path(*name.split('.')).with_suffix('.olean'))
            imports = re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
            pending += [m for m in imports if m.startswith(('GramDefect20261015.',
                        'StructuralResearch20261016.', 'StructuralW10Cert20261016.'))]
        receipt['bound_local_modules'] = sorted(local_modules)
        checkpoint('pinned-tool-preparation')
        tools, tool_provenance = legacy.copy_tools(args, work)
        receipt['tool_provenance'] = tool_provenance
        for path in (tools/'source').rglob('*.lean'):
            bind(path)
        bind(args.nanoda_bin)
        tool_paths = [str(tools/'lib'), *package_paths]
        receipt['tool_compiled_modules'] = []
        for module in base.topological_modules(tools):
            receipt['tool_compiled_modules'].append(base.compile_one(args, lean, tool_paths, tools, module))
        for path in (tools/'lib').rglob('*'):
            if path.is_file():
                bind(path)
        exporter = str(tools/'source/ExporterMain.lean')
        audit = str(tools/'source/CoreAudit.lean')
        all_roots = FINAL_ROOTS+FINITE_ROOTS
        export_roots = list(dict.fromkeys([*all_roots, *base.PRIMITIVES]))
        modular_paths = [str(tools/'lib'), str(work/'lib'), *map(str, local_libraries), *package_paths]
        single_paths = [str(tools/'lib'), str(work/'lib'), *package_paths]
        checkpoint('modular-conditional-export')
        modular = run('modular-export', base.lean_command(args, lean, modular_paths,
                      '--run', exporter, 'StructuralW10Cert20261016.FiniteConditional', '--', *export_roots), binary=True)
        receipt['modular_export'] = modular
        bind(work/'modular-export.ndjson')
        checkpoint('modular-conditional-default-kernel')
        mod_audit = run('modular-default-kernel', base.lean_command(args, lean, tool_paths,
                        '--run', audit, str(work/'modular-export.ndjson'), str(work/'modular-export.ndjson'), *all_roots))
        transcript = Path(mod_audit['log']).read_text(errors='replace')
        for required in ['Pinned Comparator statement, dependency and primitive comparison passed',
                         'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
            assert required in transcript
        receipt.update(modular_default_kernel_passed=True, modular_transitive_axioms_checked=True)
        receipt['modular_comparator_default_kernel'] = mod_audit

        def nanoda(label, export_file):
            config = {'use_stdin': True, 'permitted_axioms': base.ALLOWED,
                      'unpermitted_axiom_hard_error': True, 'nat_extension': True,
                      'string_extension': True, 'num_threads': 2,
                      'unsafe_permit_all_axioms': False, 'print_success_message': True,
                      'print_axioms': True, 'pp_to_stdout': True}
            config_path = work/f'{label}-config.json'
            base.write_json(config_path, config)
            bind(config_path)
            resources = work/'logs'/f'{label}-resources.log'
            result = base.run_logged(args, ['/usr/bin/time', '-v', '-o', str(resources),
                                     str(args.nanoda_bin), str(config_path)], work/'logs'/f'{label}.log',
                                     stdin=export_file)
            text = Path(result['log']).read_text(errors='replace')
            count = re.search(r'Checked (\d+) declarations with no errors', text)
            assert count
            observed = [n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', text, re.M)]
            assert set(observed) <= set(base.ALLOWED)
            result.update(checked_declarations=int(count[1]), observed_axioms=observed,
                          resources_sha256=base.sha(resources))
            return result

        checkpoint('modular-conditional-nanoda')
        receipt['modular_nanoda'] = nanoda('modular-nanoda', work/'modular-export.ndjson')
        receipt['modular_independent_nanoda_passed'] = True
        checkpoint('sealed-single-conditional-export')
        single_ok = False
        try:
            single = run('single-export', base.lean_command(args, lean, single_paths,
                         '--run', exporter, SINGLE_MODULE, '--',
                         *list(dict.fromkeys([*FINAL_ROOTS, *base.PRIMITIVES]))), binary=True)
            receipt['single_export'] = single
            bind(work/'single-export.ndjson')
            single_ok = True
        except Exception as error:
            receipt['standalone_export_fallback'] = {'error_type': type(error).__name__, 'error': str(error)}
        if single_ok:
            checkpoint('standalone-modular-conditional-comparison-and-default-kernel')
            comparison = run('single-default-kernel', base.lean_command(args, lean, tool_paths,
                             '--run', audit, str(work/'modular-export.ndjson'), str(work/'single-export.ndjson'), *FINAL_ROOTS))
            text = Path(comparison['log']).read_text(errors='replace')
            for required in ['Pinned Comparator statement, dependency and primitive comparison passed',
                             'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
                assert required in text
            receipt.update(standalone_modular_statement_comparison_passed=True,
                           standalone_transitive_axioms_checked=True, standalone_default_kernel_passed=True)
            receipt['standalone_comparator_default_kernel'] = comparison
            checkpoint('sealed-single-conditional-nanoda')
            receipt['single_nanoda'] = nanoda('single-nanoda', work/'single-export.ndjson')
            receipt['standalone_independent_nanoda_passed'] = True
        else:
            receipt['standalone_modular_statement_comparison_passed'] = False
        assert bound == {name: base.sha(Path(name)) for name in bound}, 'A proof, tool, input or export changed'
        receipt.update(passed=True, inputs_unchanged=True, stage='complete',
                       result_kind='conditional_single_and_modular' if single_ok else 'conditional_modular_only_fallback')
        print(json.dumps({k: receipt[k] for k in ['scope', 'passed', 'result_kind',
                         'website_statement_verified', 'higher_kappa_proven']}), flush=True)
    except Exception as error:
        receipt.update(passed=False, error_type=type(error).__name__, error=str(error))
        raise
    finally:
        receipt['bound_input_sha256'] = bound
        base.write_json(work/'verification.json', receipt)
        for folder in ['', 'logs', 'tools/logs']:
            for path in (work/folder).glob('*'):
                if path.is_file() and path.suffix in ['.json', '.log']:
                    target = args.receipt_dir/folder/path.name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, target)


if __name__ == '__main__':
    main()
