from pathlib import Path
import hashlib
import subprocess
import time

root = Path(r'E:\codex-build\RH-Weil\tmp\linux-memory-runtime-20261010')
root.mkdir(exist_ok=True)
archive = root/'lean-4.33.0-rc2-linux.tar.zst'
expected = '48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c'
def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(8*1024*1024),b''):
            h.update(b)
    return h.hexdigest()
if not archive.exists():
    print('Downloading exact Linux Lean release v4.33.0-rc2.', flush=True)
    subprocess.run(['gh','release','download','v4.33.0-rc2','--repo','leanprover/lean4',
                    '--pattern',archive.name,'--dir',str(root)],check=True)
assert archive.stat().st_size == 574905502
assert digest(archive) == expected
print('Pinned Linux archive SHA256 PASS.', flush=True)
linux_root = '/tmp/rh-proportion-memory-20261010'
subprocess.run(['wsl','-d','Ubuntu','--','python3','-c',
    "from pathlib import Path; p=Path('/tmp/rh-proportion-memory-20261010'); p.mkdir(exist_ok=True); print('Private Linux scratch ready.')"],check=True)
linux_archive = '/mnt/e/codex-build/RH-Weil/tmp/linux-memory-runtime-20261010/'+archive.name
linux_lean = linux_root+'/lean-4.33.0-rc2-linux/bin/lean'
exists = subprocess.run(['wsl','-d','Ubuntu','--','test','-x',linux_lean]).returncode == 0
if not exists:
    print('Extracting pinned Linux runtime into private scratch.',flush=True)
    subprocess.run(['wsl','-d','Ubuntu','--','tar','--use-compress-program=zstd','-xf',
                    linux_archive,'-C',linux_root],check=True)
subprocess.run(['wsl','-d','Ubuntu','--',linux_lean,'--version'],check=True)
print('Linux runtime setup complete; no proof/resource result claimed.',flush=True)
