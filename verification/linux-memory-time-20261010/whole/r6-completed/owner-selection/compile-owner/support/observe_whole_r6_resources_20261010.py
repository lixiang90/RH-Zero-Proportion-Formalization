"""Read-only r6 ownership-verified cgroup snapshot; no artifact/cache reads."""
from pathlib import Path
import json, sys, time
run = sys.argv[1]
assert run in ('whole-globalfalse-tools-r6', 'whole-globalfalse-contract-r6', 'whole-globalfalse-compile-r6')
base = Path('/sys/fs/cgroup/memory/rh-proportion-memory-20261010') / run
log = Path('/tmp/rh-proportion-memory-20261010/resource-runs') / run / 'process.log'
row = {'observed_unix': time.time(), 'run_id': run, 'cgroup_exists': base.exists()}
if base.exists():
    for key in ('memory.usage_in_bytes', 'memory.max_usage_in_bytes', 'memory.failcnt', 'memory.oom_control'):
        row[key] = (base / key).read_text().strip()
    processes = []
    for value in (base / 'cgroup.procs').read_text().split():
        path = Path('/proc') / value
        try:
            assert run in (path / 'cgroup').read_text(), 'PID namespace differs'
            fields = dict(x.split(':', 1) for x in (path / 'smaps_rollup').read_text().splitlines() if ':' in x)
            processes.append({'pid': int(value), 'pss_bytes': int(fields['Pss'].split()[0])*1024,
                'rss_bytes': int(fields['Rss'].split()[0])*1024, 'swap_bytes': int(fields['Swap'].split()[0])*1024})
        except (AssertionError, FileNotFoundError, ProcessLookupError) as error:
            row.setdefault('unresolved_pid_scope', []).append({'pid': value, 'reason': str(error)})
    row['processes'] = processes
    row['current_sampled_tree_pss_bytes'] = sum(x['pss_bytes'] for x in processes)
    row['current_sampled_tree_rss_bytes'] = sum(x['rss_bytes'] for x in processes)
cpu = Path('/sys/fs/cgroup/cpuacct/rh-proportion-memory-20261010') / run / 'cpuacct.usage'
if cpu.exists():
    row['cgroup_cpuacct_usage_nanoseconds'] = int(cpu.read_text())
supervisor = Path('/tmp/rh-proportion-memory-20261010/whole-native-20261010-r6/phase-ledgers/compile-supervisor.log')
if run == 'whole-globalfalse-compile-r6' and supervisor.exists():
    for line in reversed(supervisor.read_text().splitlines()):
        try:
            item = json.loads(line)
            if item.get('running') == run:
                row['latest_harness_proof_elapsed_seconds'] = item['seconds']
                break
        except json.JSONDecodeError:
            pass
if log.exists():
    output = log.read_text()
    row['observed_barriers_lower_bound'] = output.count('AM_BARRIER ')
    row['barrier_scope'] = 'Buffered stdout count is only a lower bound, not evidence of a stalled proof.'
    row['log_tail'] = output[-1200:]
print(json.dumps(row, indent=2))
