#!/usr/bin/env python3
import argparse
import os
import subprocess
from pathlib import Path
from typing import Dict, List, Tuple


def parse_glob_file(path: Path) -> Tuple[str, List[Tuple[str, str]]]:
    module = None
    proofs: List[Tuple[str, str]] = []
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        if line.startswith("F") and " " not in line:
            # e.g. FSN.add
            module = line[1:]
        if line.startswith("prf "):
            parts = line.split()
            if len(parts) >= 4:
                qualifier_parts = parts[2:-1]
                if qualifier_parts == ["<>"]:
                    qualifier = ""
                else:
                    qualifier = ".".join(qualifier_parts)
                proofs.append((qualifier, parts[-1]))
    if module is None:
        raise ValueError(f"missing module header in {path}")
    return module, proofs


def ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def build_coq_commands(
    module: str, proofs: List[Tuple[str, str]], out_dir: Path
) -> List[str]:
    leaf = module.split(".")[-1]
    cmds = [f"From SN Require Import {leaf}."]
    for qualifier, name in proofs:
        full_name = f"{module}.{qualifier}.{name}" if qualifier else f"{module}.{name}"
        safe_name = full_name.replace(".", "_")
        out_file = out_dir / f"{safe_name}.txt"
        cmds.append(
            f"Redirect \"{out_file.as_posix()}\" Print Assumptions {full_name}."
        )
    cmds.append("Quit.")
    return cmds


def run_coqtop(coqtop_cmd: str, cmds: List[str]) -> None:
    script = "\n".join(cmds) + "\n"
    result = subprocess.run(
        coqtop_cmd,
        input=script,
        text=True,
        shell=True,
        capture_output=True,
    )
    if result.returncode != 0:
        raise RuntimeError(
            "coqtop failed\nstdout:\n" + result.stdout + "\nstderr:\n" + result.stderr
        )


def extract_axioms(text: str) -> List[str]:
    lines = [l.rstrip() for l in text.splitlines()]
    if "Axioms:" in lines:
        idx = lines.index("Axioms:")
        axioms = [l.strip() for l in lines[idx + 1 :] if l.strip()]
        return axioms or ["(none)"]
    if any("Closed under the global context" in l for l in lines):
        return ["(none)"]
    trimmed = [l.strip() for l in lines if l.strip()]
    return trimmed or ["(none)"]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Collect Print Assumptions for prf entries in .glob files"
    )
    parser.add_argument(
        "--root",
        default=str(Path.cwd()),
        help="project root (default: current directory)",
    )
    parser.add_argument(
        "--out",
        default="assumptions",
        help="output directory for raw Print Assumptions files",
    )
    parser.add_argument(
        "--coqtop",
        default=os.environ.get("COQTOP", "rocq repl -q"),
        help="coqtop command (default: env COQTOP or 'rocq repl -q')",
    )
    args = parser.parse_args()

    root = Path(args.root)
    out_dir = root / args.out
    ensure_dir(out_dir)

    module_to_proofs: Dict[str, List[Tuple[str, str]]] = {}
    for glob_path in root.rglob("*.glob"):
        if glob_path.name.startswith("."):
            continue
        module, proofs = parse_glob_file(glob_path)
        if proofs:
            module_to_proofs.setdefault(module, []).extend(proofs)

    for module, proofs in module_to_proofs.items():
        cmds = build_coq_commands(module, proofs, out_dir)
        run_coqtop(args.coqtop, cmds)

    for module, proofs in module_to_proofs.items():
        for qualifier, name in proofs:
            full_name = f"{module}.{qualifier}.{name}" if qualifier else f"{module}.{name}"
            out_file = out_dir / f"{full_name}.txt"
            if not out_file.exists():
                continue
            axioms = extract_axioms(out_file.read_text(encoding="utf-8", errors="ignore"))
            print(f"{full_name}:")
            for ax in axioms:
                print(f"  - {ax}")


if __name__ == "__main__":
    main()
