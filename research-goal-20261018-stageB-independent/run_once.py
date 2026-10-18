"""Run one independent review child with external time/output caps; never retry."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent


def save(name, value):
    with (HERE / name).open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
        stream.flush(); os.fsync(stream.fileno())


def main():
    assert __debug__ and sys.argv[1:] == ["--launch-fixed-independent-review"]
    assert not (HERE / "launch.json").exists()
    command = [sys.executable, str(HERE / "replay_classification.py"), "--execute-fixed-independent-review"]
    save("launch.json", {"argv": command, "cwd": str(HERE.parent), "parent_pid": os.getpid(),
        "implementation_sha256": hashlib.sha256((HERE / "replay_classification.py").read_bytes()).hexdigest(),
        "launcher_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "maximum_child_launches": 1, "seconds_limit": 180, "output_bytes_limit": 32000000})
    start = time.monotonic(); reason = None
    with (HERE / "stdout.log").open("xb") as out, (HERE / "stderr.log").open("xb") as err:
        child = subprocess.Popen(command, cwd=HERE.parent, stdout=out, stderr=err)
        save("child.json", {"pid": child.pid, "parent_pid": os.getpid(), "child_launches": 1})
        print(json.dumps({"child_pid": child.pid, "stage": "independent_fixed_B_running"}), flush=True)
        while child.poll() is None:
            elapsed = time.monotonic() - start
            written = sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
            if elapsed > 180 or written > 32000000:
                reason = "elapsed_limit" if elapsed > 180 else "output_limit"
                child.terminate()
                break
            time.sleep(.25)
        exit_code = child.wait()
    terminal = {"child_pid": child.pid, "exit_code": exit_code, "seconds": time.monotonic()-start,
        "limit_stop": reason, "child_launches": 1, "automatic_retry": False,
        "review_present": (HERE / "independent-review.json").exists(),
        "failure_present": (HERE / "independent-failure.json").exists(),
        "closed_output_bytes": sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())}
    save("terminal.json", terminal)
    print(json.dumps(terminal), flush=True)
    if exit_code or reason: raise SystemExit(1)


if __name__ == "__main__":
    main()
