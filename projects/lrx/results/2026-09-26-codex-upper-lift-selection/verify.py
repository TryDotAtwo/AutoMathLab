#!/usr/bin/env python3
"""Verify package hashes; optionally replay the exact Lean source."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", action="store_true", help="also run Lean in the pinned Lake project")
args = parser.parse_args()
manifest = json.loads((ROOT / "MANIFEST.json").read_text())
for name, expected in manifest["files"].items():
    path = ROOT / name
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"Missing or symlink input: {name}")
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"SHA-256 mismatch: {name}")
print(f"Hashes PASS: {len(manifest['files'])} files. This is not a Lean check.")
if args.lean:
    run = subprocess.run(["lake", "env", "lean", "UpperLiftSelection.lean"], cwd=ROOT,
                         text=True, capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    if run.returncode:
        raise SystemExit(run.returncode)
    expected = {"initial_lift", "exists_energy_minimizer", "shift_energy", "exists_majorized_short_lift"}
    reports = re.findall(r"'LRX\.UpperLiftSelection\.([^']+)' depends on axioms: \[([^]]*)\]", output)
    found = {}
    for name, axioms in reports:
        found[name] = {part.strip() for part in axioms.split(",") if part.strip()}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if not expected.issubset(found) or any(found[n] - allowed for n in expected):
        raise SystemExit("Missing expected axiom report or unexpected dependency")
    print("Lean source replay PASS; four named axiom reports checked. No claim about full LRX.")
