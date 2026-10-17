"""Freeze the actual global gap-swap competitor core after ordinary Lean.

Only current source/hash-bound receipts with fully qualified allowed axioms
are accepted. No numerical envelope or local exclusion is supplied here.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
MODULE = "StructuralGoal20261016.WindowGlobalCompetitor"
PREFIX = MODULE + "."
ROOTS = ["swapGap_apply", "swapGap_feasible", "swap_energy_le", "swap_change_nonneg",
         "envelope_difference_nonneg", "upper_change_nonneg", "weighted_changes_nonneg",
         "weighted_envelopes_nonneg", "exclude_by_upper_change",
         "exclude_by_weighted_envelopes", "exclude_cell_of_envelopes"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def entry(path):
    raw = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def frozen_write(path, value):
    raw = (json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n").encode("utf8")
    if path.exists():
        assert path.read_bytes() == raw, "Frozen file differs; use a new path."
    else:
        path.write_bytes(raw)


def main():
    canonical = json.loads((HERE / "lean_verification.json").read_bytes())
    records = {r["module"]: r for r in canonical["modules"]}
    record = records[MODULE]
    source = ROOT / (MODULE.replace(".", "/") + ".lean")
    log = HERE / record["log"]
    assert record["passed"] and record["exit_code"] == 0 and record["source_unchanged"]
    assert entry(source)["sha256"] == record["source_sha256"]
    assert entry(log)["sha256"] == record["log_sha256"]
    text = log.read_text(encoding="utf8", errors="replace")
    assert "sorryAx" not in text and "error:" not in text
    audits = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
        audits[match.group(1)] = [a.strip() for a in match.group(2).split(",") if a.strip()]
    for match in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        audits[match.group(1)] = []
    roots = []
    for name in ROOTS:
        full = PREFIX + name
        assert full in audits, full
        assert set(audits[full]) <= ALLOWED, (full, audits[full])
        roots.append({"name": full, "axioms": audits[full]})
    dependency = "StructuralGoal20261016.WindowMinimizerCover"
    dep_source = ROOT / (dependency.replace(".", "/") + ".lean")
    dep = records[dependency]
    assert dep["passed"] and dep["source_sha256"] == entry(dep_source)["sha256"]
    index = {
        "scope": __doc__, "module": MODULE, "source": entry(source), "log": entry(log),
        "receipt_record": record, "compiler_sha256": canonical["compiler_sha256"],
        "canonical_receipt": "research-goal-20261016/lean_verification.json",
        "roots": roots, "ordinary_Lean_passed": True,
        "fully_qualified_axiom_audit_passed": True,
        "direct_import_source": entry(dep_source),
        "direct_import_ordinary_pass_log_sha256": dep["log_sha256"],
        "script_sha256": entry(Path(__file__))["sha256"],
        "semantic_scope": [
            "swapGap g i j is the actual vector g composed with Equiv.swap i j.",
            "A gap swap preserves the same separated orthant.",
            "Relevant's entire-orthant global minimum clause compares actual Fw24 energies.",
            "The competitor does not have to satisfy the orientation g(0) <= g(8).",
            "Actual lower/current and upper/competitor energy bounds remain explicit hypotheses.",
            "Finite nonnegative combinations preserve nonnegative energy-difference cuts.",
            "A uniform strict negative envelope difference excludes a relevant cell only after those numerical hypotheses are supplied."],
        "new_numerical_tables": 0, "new_actual_local_exclusions": 0,
        "complete_global_cover": False, "new_zero_proportion_proven": False,
        "independent_Nanoda_replayed": False}
    index_path = HERE / "window_global_competitor_formal_index.json"
    frozen_write(index_path, index)
    files = [entry(p) for p in [source, log, Path(__file__), index_path]]
    sync_path = HERE / "window_global_competitor_sync_files.json"
    frozen_write(sync_path, {"scope": "One actual global-gap-competitor core; numerical hypotheses remain visible.",
                             "files": files, "formal_index_sha256": entry(index_path)["sha256"],
                             "ordinary_Lean_passed": True, "new_actual_local_exclusions": 0,
                             "complete_global_cover": False, "new_zero_proportion_proven": False,
                             "independent_Nanoda_replayed": False})
    print(json.dumps({"index": entry(index_path), "sync": entry(sync_path),
                      "source": entry(source), "log": entry(log), "roots": len(roots),
                      "whole_process_seconds": record["whole_process_seconds"]}))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Assertions must remain enabled")
    main()
