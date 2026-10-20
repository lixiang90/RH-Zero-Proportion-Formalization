"""Linux-side read-only ELF loader metadata capture, not a kernel invocation.

Run with ordinary Linux Python inside the specified WSL distro. Only the
system interpreter's --list mode is called; nanoda/main and helper mains are
not executed. No compiler/export/kernel/proof/installer is invoked.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--nanoda-file',required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    if args.output.exists():raise RuntimeError('Exclusive output already exists')
    loader='/lib64/ld-linux-x86-64.so.2'
    paths=[args.nanoda_file,loader,'/usr/bin/setsid','/bin/sh','/bin/kill','/usr/bin/readlink','/usr/bin/env']
    rows=[];files={}
    def add(name):
        path=Path(name);real=path.resolve();data=real.read_bytes()
        files[str(real)]={'path':str(path),'resolved_path':str(real),'bytes':len(data),
                         'sha256':hashlib.sha256(data).hexdigest()}
    for name in paths:
        add(name)
        proc=subprocess.run([loader,'--list',str(Path(name).resolve())],
            env={'PATH':'/usr/bin:/bin'},stdout=subprocess.PIPE,stderr=subprocess.PIPE,
            timeout=15,check=False)
        stdout=proc.stdout.decode()
        rows.append({'executable_file_inspected':name,'loader_list_exit_code':proc.returncode,
                     'stdout':stdout,'stderr':proc.stderr.decode(),'main_executed':False})
        if proc.returncode:raise RuntimeError('ELF loader metadata resolution failed: '+name)
        for lib in re.findall(r'(?:=>\s+|^\s*)(/[^\s]+)\s+\(',stdout,re.M):add(lib)
    add('/etc/ld.so.cache')
    result={'scope':'ELF loader --list only; no target main/compiler/export/kernel replay',
            'inspections':rows,'files':list(files.values()),'complete_runtime_approved':False}
    with args.output.open('x',encoding='utf-8') as stream:
        json.dump(result,stream,indent=2);stream.write('\n')


if __name__=='__main__':main()
