#!/usr/bin/env python3
"""Run the `quint verify` command at the top of every specification."""

import shlex
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent


def command_for(path: Path) -> tuple[list[str], bool]:
    lines = iter(path.read_text().splitlines())
    parts = []

    while True:
        line = next(lines, "")
        if not line.startswith("// "):
            raise ValueError("missing or incomplete leading // quint verify command")
        part = line[3:].strip()
        continued = part.endswith("\\")
        parts.append(part[:-1].strip() if continued else part)
        if not continued:
            break

    command = shlex.split(" ".join(parts))
    if command[:3] != ["quint", "verify", path.name]:
        raise ValueError("expected a command starting with quint verify " + path.name)

    expectation = next(lines, "")
    if expectation.startswith("// expect: ") and expectation != "// expect: counterexample":
        raise ValueError("unsupported expectation: " + expectation)
    return command, expectation == "// expect: counterexample"


def main() -> int:
    paths = sorted((ROOT / "specifications").rglob("*.qnt"))
    if not paths:
        print("No Quint specifications found", file=sys.stderr)
        return 1

    failures = []
    for path in paths:
        relative = path.relative_to(ROOT)
        try:
            command, expect_counterexample = command_for(path)
        except (ValueError, OSError) as error:
            print(f"{relative}: {error}", file=sys.stderr)
            failures.append(relative)
            continue

        print(f"\n==> {relative}: {shlex.join(command)}", flush=True)
        result = subprocess.run(
            command,
            cwd=path.parent,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
        )
        print(result.stdout, end="", flush=True)
        found_counterexample = "error: found a counterexample" in result.stdout
        passed = (
            result.returncode != 0 and found_counterexample
            if expect_counterexample
            else result.returncode == 0
        )
        if not passed:
            failures.append(relative)
        elif expect_counterexample:
            print("Expected counterexample found.", flush=True)

    if failures:
        print("\nVerification failed for:", file=sys.stderr)
        for path in failures:
            print(f"  {path}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
