"""Finish separately scoped self-replays after the recorded comparison failure.

CONDITIONAL_ONLY.  Does not claim standalone/modular statement equivalence.
Preserves the failed comparison receipt and never re-runs a completed export.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse, copy, json, os, re, shutil, sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import verify_single_solution as base


def main():
    assert __debug__ and os.name != 'nt'
    work = Path('/var/tmp/rh-zero-20261015/w10-conditional-replay')
    out = ROOT / 'verification/w10-20261016/conditional'
    receipt_path = work / 'verification.json'
    receipt = json.loads(receipt_path.read_bytes())
    assert receipt['scope'] == 'CONDITIONAL_ONLY' and not receipt['passed']
    assert receipt['modular_default_kernel_passed']
    assert receipt['modular_independent_nanoda_passed']
    failed_log = work / 'logs/single-default-kernel.log'
    message = failed_log.read_text()
    assert "Const does not match between challenge and target 'StructuralW10Cert20261016.FinalConditional.SeparatedFloor'" in message
    failure_file = work / 'verification-failed-comparison.json'
    assert not failure_file.exists()
    shutil.copyfile(receipt_path, failure_file)
    bound = copy.deepcopy(receipt['bound_input_sha256'])
    assert all(base.sha(Path(n)) == h for n, h in bound.items())
    bound[str(Path(__file__).resolve())] = base.sha(Path(__file__))
    bound[str(failure_file)] = base.sha(failure_file)
    bound[str(failed_log)] = base.sha(failed_log)
    receipt['comparison_failure'] = {
        'receipt_sha256': base.sha(failure_file),
        'log_sha256': base.sha(failed_log),
        'message': message.strip(),
        'original_error_type': receipt.pop('error_type'),
        'original_error': receipt.pop('error'),
    }
    receipt['standalone_modular_statement_comparison_passed'] = False
    receipt['stage'] = 'standalone-separate-self-replays'
    base.write_json(receipt_path, receipt)
    args = argparse.Namespace(distribution='Ubuntu', timeout=14400)
    roots = receipt['final_conditional_roots']
    export = work / 'single-export.ndjson'
    template = receipt['modular_comparator_default_kernel']['command']
    run_pos = template.index('--run')
    command = template[:run_pos+2] + [str(export), str(export), *roots]
    command[command.index('-o')+1] = str(work/'logs/standalone-self-default-kernel-resources.log')
    config = work / 'single-nanoda-config.json'
    base.write_json(config, {'use_stdin': True, 'permitted_axioms': base.ALLOWED,
        'unpermitted_axiom_hard_error': True, 'nat_extension': True,
        'string_extension': True, 'num_threads': 2,
        'unsafe_permit_all_axioms': False, 'print_success_message': True,
        'print_axioms': True, 'pp_to_stdout': True})
    bound[str(config)] = base.sha(config)
    nanoda = Path('/var/tmp/rh-zero-20261015/nanoda-target/release/nanoda_bin')

    def default_kernel():
        print('standalone-self-default-kernel', flush=True)
        result = base.run_logged(args, command, work/'logs/standalone-self-default-kernel.log')
        text = Path(result['log']).read_text()
        for expected in ['Pinned Comparator statement, dependency and primitive comparison passed',
                         'Pinned Comparator transitive axiom check passed', 'Lean default kernel replay passed']:
            assert expected in text
        result['resources_sha256'] = base.sha(work/'logs/standalone-self-default-kernel-resources.log')
        return result

    def independent_kernel():
        print('standalone-independent-nanoda', flush=True)
        resources = work/'logs/single-nanoda-resources.log'
        result = base.run_logged(args, ['/usr/bin/time', '-v', '-o', str(resources),
                                     str(nanoda), str(config)], work/'logs/single-nanoda.log', stdin=export)
        text = Path(result['log']).read_text()
        count = re.search(r'Checked (\d+) declarations with no errors', text)
        assert count
        observed = [n.split('.{')[0] for n in re.findall(r'^axiom ([^\s]+)', text, re.M)]
        assert set(observed) <= set(base.ALLOWED)
        result.update(checked_declarations=int(count[1]), observed_axioms=observed,
                      resources_sha256=base.sha(resources))
        return result

    try:
        mem = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
        available_kib = int(mem['MemAvailable'].split()[0])
        receipt['self_replay_parallel_available_kib'] = available_kib
        if available_kib >= 10*1024*1024:
            with ThreadPoolExecutor(max_workers=2) as executor:
                default = executor.submit(default_kernel)
                independent = executor.submit(independent_kernel)
                receipt['standalone_self_comparator_default_kernel'] = default.result()
                receipt['single_nanoda'] = independent.result()
        else:
            receipt['standalone_self_comparator_default_kernel'] = default_kernel()
            receipt['single_nanoda'] = independent_kernel()
        assert bound == {n: base.sha(Path(n)) for n in bound}, 'A bound proof, tool, source or export changed'
        receipt.update(passed=True, stage='complete', inputs_unchanged=True,
            standalone_self_statement_comparison_passed=True,
            standalone_transitive_axioms_checked=True, standalone_default_kernel_passed=True,
            standalone_independent_nanoda_passed=True,
            result_kind='conditional_modular_plus_standalone_self_replay_comparison_failed')
        print(json.dumps({k: receipt[k] for k in ['scope', 'passed', 'result_kind',
            'standalone_modular_statement_comparison_passed', 'website_statement_verified']}), flush=True)
    except Exception as error:
        receipt.update(passed=False, error_type=type(error).__name__, error=str(error))
        raise
    finally:
        receipt['bound_input_sha256'] = bound
        base.write_json(receipt_path, receipt)
        for folder in ['', 'logs', 'tools/logs']:
            for path in (work/folder).glob('*'):
                if path.is_file() and path.suffix in ['.json', '.log']:
                    target = out/folder/path.name
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, target)


if __name__ == '__main__':
    main()
