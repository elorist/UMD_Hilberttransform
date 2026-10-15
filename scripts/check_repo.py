#!/usr/bin/env python3
"""Audit the files Git would publish. Requires Python 3.10+ and Git."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
LEAN_PIN = "leanprover/lean4:v4.35.0"
MATHLIB_PIN = "56a005855ea17e0b0958f73ec801ae140b0a1679"
COMPARATOR_THEOREM = "HilbertUMD.Comparison.theorem_1_1"
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
PAPER_PDF = "paper/Hilbert-and-UMD-arxiv-v1.pdf"
PAPER_SHA256 = "180433f03776ad6a930c38a51a167c693aa2892a41ce86a1046ea75ce7772cb9"
PRIVATE_DIRS = {".git", ".lake", ".tools", "output", "tmp", "scratch", "__pycache__"}
GENERATED = {".zip", ".gz", ".aux", ".bbl", ".blg", ".log", ".out", ".olean", ".ilean", ".trace", ".pyc"}
SENSITIVE = {
    "private key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "access token": re.compile(r"\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{40,}|sk-proj-[A-Za-z0-9_-]{30,})"),
    "private share link": re.compile(r"https?://(?:surfdrive\.surf\.nl|[^/]+\.sharepoint\.com)/\S+", re.I),
    "machine-local path": re.compile(r"(?:[A-Z]:[\\/]+Users[\\/]|/Users/|/home/)[A-Za-z0-9_.-]+[\\/]"),
}


def git_files(root: Path) -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=root, check=True, capture_output=True,
    )
    return sorted(set(result.stdout.decode("utf-8").rstrip("\0").split("\0")) - {""})


def lean_code(text: str) -> str:
    """Blank nested Lean comments and strings while preserving line numbers."""
    out = list(text)
    i, depth, quoted = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif quoted:
            if text[i] == "\\" and i + 1 < len(text):
                out[i:i + 2] = "  "
                i += 2
            else:
                quoted = text[i] != '"'
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            quoted = True
            out[i] = " "
            i += 1
        else:
            i += 1
    return "".join(out)


def challenge_sorry_position(text: str) -> int | None:
    """Locate only the reference theorem's one terminal admission.

    This source check complements (and does not replace) Comparator's checks
    of the elaborated declarations in separate environments.
    """
    code = lean_code(text)
    admissions = list(re.finditer(r"\bsorry\b", code))
    if len(admissions) != 1:
        return None
    position = admissions[0].start()
    declarations = list(re.finditer(
        r"^\s*(?:public\s+)?(theorem|lemma|def|abbrev|structure|inductive|opaque|instance)\s+([\w.]+)",
        code[:position], re.M))
    if not declarations or declarations[-1].group(1) != "theorem":
        return None
    if declarations[-1].group(2) not in {COMPARATOR_THEOREM, "Comparison.theorem_1_1", "theorem_1_1"}:
        return None
    if not re.search(r":=\s*(?:by\s+)?sorry\s*(?:end(?:[ \t]+[\w.]+)?\s*)*\Z",
                     code[declarations[-1].start():]):
        return None
    return position


def content_issues(name: str, text: str) -> list[str]:
    issues = []
    for label, pattern in SENSITIVE.items():
        for match in pattern.finditer(text):
            line = text.count("\n", 0, match.start()) + 1
            issues.append(f"{name}:{line}: {label} (value withheld)")
    if name.endswith(".lean"):
        allowed_sorry = challenge_sorry_position(text) if name == "Challenge.lean" else None
        for match in re.finditer(r"\b(?:sorry|admit|axiom|native_decide|implemented_by|extern)\b", lean_code(text)):
            if match.group(0) == "sorry" and match.start() == allowed_sorry:
                continue
            line = text.count("\n", 0, match.start()) + 1
            issues.append(f"{name}:{line}: unproved declaration or proof escape")
    if re.search(r"^(?:<{7}|={7}|>{7})(?: |$)", text, re.M):
        issues.append(f"{name}: merge-conflict marker")
    return issues


def link_issues(root: Path, name: str, text: str, files: set[str]) -> list[str]:
    issues = []
    for match in re.finditer(r"\[[^\]\n]+\]\((<[^>]+>|[^\s)]+)\)", text):
        target = match.group(1).strip("<>")
        parts = urlsplit(target)
        if parts.scheme or not parts.path:
            continue
        path = ((root / name).parent / unquote(parts.path)).resolve()
        try:
            relative = path.relative_to(root.resolve()).as_posix()
        except ValueError:
            issues.append(f"{name}: link leaves the repository: {target}")
            continue
        if relative not in files and not any(f.startswith(relative + "/") for f in files):
            issues.append(f"{name}: link target is not published (or has wrong case): {target}")
    return issues


def imports(text: str) -> list[str]:
    """Read ordinary and module-system imports, excluding comments/strings."""
    return [module for line in lean_code(text).splitlines()
            if (match := re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)$", line))
            for module in match.group(1).split()]


def lean_source_issues(sources: dict[str, str]) -> list[str]:
    issues = []
    for name, text in sources.items():
        if not name.endswith(".lean"):
            continue
        code = lean_code(text)
        if Path(name).name != "lakefile.lean" and not re.match(r"\A\s*module\s*(?:\n|$)", code):
            issues.append(f"{name}: missing module header")
        lines = text.count("\n") + int(bool(text) and not text.endswith("\n"))
        if lines > 10_000:
            issues.append(f"{name}: exceeds the 10,000-line source limit")
        if name != "Challenge.lean" and any(m == "Challenge" or m.startswith("Challenge.") for m in imports(text)):
            issues.append(f"{name}: proof-side source imports the admitted Challenge")
    return issues


def mathlib_cache_imports(sources: dict[str, str]) -> list[str]:
    modules = sorted({module for name, text in sources.items() if name.endswith(".lean")
                      for module in imports(text) if module == "Mathlib" or module.startswith("Mathlib.")})
    if not modules or "Mathlib" in modules:
        raise ValueError("Cache imports must name specific Mathlib modules, not the whole library")
    return modules


def comparator_issues(sources: dict[str, str]) -> list[str]:
    issues = []
    try:
        config = json.loads(sources.get("comparator.json", "{}"))
    except ValueError:
        return ["comparator.json: invalid JSON"]
    if not isinstance(config, dict):
        return ["comparator.json: expected an object"]
    allowed_fields = {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms"}
    for field in sorted(config.keys() - allowed_fields):
        issues.append(f"comparator.json: unsupported field {field}")
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        issues.append("comparator.json: expected separate Challenge and Solution modules")
    if config.get("theorem_names") != [COMPARATOR_THEOREM]:
        issues.append("comparator.json: the certification target must be exactly Theorem 1.1")
    if config.get("definition_names", []) != []:
        issues.append("comparator.json: unexpected separate definition targets")
    axioms = config.get("permitted_axioms")
    if not isinstance(axioms, list) or len(axioms) != 3 or any(not isinstance(a, str) for a in axioms) or set(axioms) != PERMITTED_AXIOMS:
        issues.append("comparator.json: only the three standard axioms are permitted")
    challenge = sources.get("Challenge.lean", "")
    if challenge_sorry_position(challenge) is None:
        issues.append("Challenge.lean: expected exactly one terminal sorry for Theorem 1.1")
    if len(challenge.encode("utf-8")) > 100 * 1024 or len(challenge.splitlines()) > 1000:
        issues.append("Challenge.lean: exceeds the 1,000-line or 100-KiB limit")
    challenge_imports = imports(challenge)
    if not challenge_imports or any(m.split(".")[0] not in {"Mathlib", "Lean", "Init"} for m in challenge_imports):
        issues.append("Challenge.lean: imports must resolve only to Lean core or Mathlib")
    return issues


def module_issues(sources: dict[str, str]) -> list[str]:
    modules = {name[:-5].replace("/", "."): lean_code(text)
               for name, text in sources.items()
               if name == "HilbertUMD.lean" or name.startswith("HilbertUMD/") and name.endswith(".lean")}
    seen, pending, issues = set(), ["HilbertUMD"], []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        if module not in modules:
            issues.append(f"Missing imported module: {module}")
            continue
        pending.extend(m for m in imports(modules[module]) if m == "HilbertUMD" or m.startswith("HilbertUMD."))
    issues.extend(f"Module outside the public import: {m}" for m in sorted(modules.keys() - seen))
    return issues


def paper_pdf_issues(data: bytes) -> list[str]:
    """Allow the exact arXiv v1 manuscript while retaining the binary-file release gate."""
    issues = []
    if not data.startswith(b"%PDF-"):
        issues.append(f"Invalid PDF header: {PAPER_PDF}")
    if hashlib.sha256(data).hexdigest() != PAPER_SHA256:
        issues.append(f"Paper PDF differs from the approved arXiv v1 manuscript: {PAPER_PDF}")
    return issues


def audit(root: Path) -> tuple[list[str], dict]:
    files = git_files(root)
    issues, sources, hashes = [], {}, {}
    required = {"README.md", "LICENSE", "paper/LICENSE",
                "CITATION.cff", "lean-toolchain",
                "lakefile.toml", "lake-manifest.json", ".github/workflows/verify.yml",
                "Challenge.lean", "Solution.lean", "comparator.json", "formalization.yaml",
                "scripts/verify-comparator.sh",
                "tests/MainTheorem.lean", "tests/Definitions.lean", "tests/AxiomAudit.lean", PAPER_PDF}
    issues.extend(f"Missing release file: {name}" for name in sorted(required - set(files)))
    folded = {}
    for name in files:
        path = root / name
        if name.casefold() in folded:
            issues.append(f"Case-colliding paths: {folded[name.casefold()]} and {name}")
        folded[name.casefold()] = name
        if PRIVATE_DIRS.intersection(Path(name).parts) or path.suffix in GENERATED:
            issues.append(f"Generated or private artifact would be published: {name}")
        if path.name.startswith(".env") or path.suffix in {".key", ".pem"}:
            issues.append(f"Credential file would be published: {name}")
        if path.is_symlink() or not path.is_file():
            issues.append(f"Missing file or symbolic link: {name}")
            continue
        data = path.read_bytes()
        hashes[name] = hashlib.sha256(data).hexdigest()
        if len(data) > 2_000_000:
            issues.append(f"Unexpectedly large release file: {name}")
        if name == PAPER_PDF:
            issues.extend(paper_pdf_issues(data))
            continue
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            issues.append(f"Non-UTF-8 or binary release file: {name}")
            continue
        if "\0" in text or text.startswith("\ufeff"):
            issues.append(f"NUL byte or byte-order mark: {name}")
        sources[name] = text
        issues.extend(content_issues(name, text))
        if name.endswith(".md"):
            issues.extend(link_issues(root, name, text, set(files)))
    issues.extend(module_issues(sources))
    issues.extend(lean_source_issues(sources))
    issues.extend(comparator_issues(sources))
    if sources.get("lean-toolchain", "").strip() != LEAN_PIN:
        issues.append("Lean pin changed; review the dependency update")
    manifest = json.loads(sources.get("lake-manifest.json", "{}"))
    packages = manifest.get("packages", [])
    mathlib = [p for p in packages if p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != MATHLIB_PIN:
        issues.append("Mathlib manifest pin changed")
    if not re.search(r'rev\s*=\s*"' + MATHLIB_PIN + r'"', sources.get("lakefile.toml", "")):
        issues.append("Lake configuration and manifest pins differ")
    for package in packages:
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            issues.append(f"Unpinned dependency: {package.get('name')}")
    return issues, {"releaseFiles": len(files), "lean": LEAN_PIN, "mathlib": MATHLIB_PIN,
                    "issues": issues, "sourceSha256": hashes}


def main() -> int:
    if sys.argv[1:] == ["--cache-imports"]:
        sources = {name: (ROOT / name).read_text(encoding="utf-8")
                   for name in git_files(ROOT) if name.endswith(".lean")}
        print("\n".join(mathlib_cache_imports(sources)))
        return 0
    if sys.argv[1:]:
        print("Usage: check_repo.py [--cache-imports]", file=sys.stderr)
        return 2
    issues, report = audit(ROOT)
    destination = ROOT / ".lake/verification/repository.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if issues:
        print("Repository audit failed:\n" + "\n".join(issues))
        return 1
    print(f"PASS: {report['releaseFiles']} release files; links, pins, source reachability, and content checks passed.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Repository audit could not complete: {type(error).__name__}", file=sys.stderr)
        sys.exit(1)
