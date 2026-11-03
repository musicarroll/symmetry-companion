#!/usr/bin/env python3
"""Enumerate small binary operations and write symmetry diagnostics."""

from __future__ import annotations

import csv
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "results" / "data"

MODULE_PATH = ROOT / "src" / "finite_algebraic_structures.py"
SPEC = importlib.util.spec_from_file_location("finite_algebraic_structures", MODULE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"Could not load {MODULE_PATH}")
finite_algebraic_structures = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = finite_algebraic_structures
SPEC.loader.exec_module(finite_algebraic_structures)

automorphisms = finite_algebraic_structures.automorphisms
cyclic_group_operation = finite_algebraic_structures.cyclic_group_operation
diagnose_operation = finite_algebraic_structures.diagnose_operation
summarize_operations = finite_algebraic_structures.summarize_operations


def main() -> None:
    DATA.mkdir(parents=True, exist_ok=True)

    summaries = [summarize_operations(n) for n in (2, 3)]

    summary_path = DATA / "finite_algebraic_operation_summary.json"
    summary_path.write_text(json.dumps(summaries, indent=2), encoding="utf-8")

    csv_path = DATA / "finite_algebraic_operation_summary.csv"
    with csv_path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "n",
                "total_operations",
                "rigid",
                "associative",
                "commutative",
                "has_identity",
                "is_group",
                "aut_distribution",
            ]
        )
        for summary in summaries:
            counts = summary["property_counts"]
            writer.writerow(
                [
                    summary["n"],
                    summary["total_operations"],
                    counts["rigid"],
                    counts["associative"],
                    counts["commutative"],
                    counts["has_identity"],
                    counts["is_group"],
                    json.dumps(summary["aut_distribution"], sort_keys=True),
                ]
            )

    c3 = cyclic_group_operation(3)
    c3_diag = diagnose_operation(c3, 3)
    c3_path = DATA / "cyclic_group_c3_diagnostics.json"
    c3_path.write_text(
        json.dumps(
            {
                "n": 3,
                "operation": list(c3),
                "automorphisms": [list(p) for p in automorphisms(c3, 3)],
                "aut_size": c3_diag.aut_size,
                "multiplicity": c3_diag.multiplicity,
                "symmetry_deficit": c3_diag.symmetry_deficit,
                "associative": c3_diag.associative,
                "commutative": c3_diag.commutative,
                "has_identity": c3_diag.has_identity,
                "is_group": c3_diag.is_group,
            },
            indent=2,
        ),
        encoding="utf-8",
    )

    print(f"Wrote {summary_path}")
    print(f"Wrote {csv_path}")
    print(f"Wrote {c3_path}")


if __name__ == "__main__":
    main()
