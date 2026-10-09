"""Audit, after csd-lean4's lexical guards: doc promises, placeholders, import hygiene, format.

Run from the repository root, or pass the root as the first argument. Exits 1 if it finds any
problem, so it can gate CI.
"""
import glob
import os
import re
import sys

root = sys.argv[1] if len(sys.argv) > 1 else "."
files = sorted(glob.glob(os.path.join(root, "AME62", "*.lean"))) + [os.path.join(root, "AME62.lean")]
fc_path = os.path.join(root, ".lake/packages/formal_conjectures/FormalConjectures",
                       "OpenQuantumProblems/35.lean")
fc = open(fc_path, encoding="utf-8").read()
# Read bytes, so CRLF line endings are seen rather than silently converted.
raw = {f: open(f, "rb").read() for f in files}
src = {f: b.decode("utf-8") for f, b in raw.items()}
decl_re = (r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
           r"(?:def|lemma|theorem|abbrev|structure)\s+(\S+)")
declared = set(re.findall(decl_re, "\n".join(src.values()), re.M))
declared |= set(re.findall(decl_re, fc, re.M))
problems = []
# audit/Vacuity.lean skips these suffixes as Lean-generated, so no hand-written name may use them.
for f, s in src.items():
    for name in re.findall(decl_re, s, re.M):
        last = name.split(".")[-1]
        if re.fullmatch(r"eq_\d+|eq_def|eq_unfold|congr_simp", last):
            problems.append(f"{f}: `{name}` uses a suffix reserved for Lean-generated lemmas")
for f, t in src.items():
    for doc in re.findall(r"/-[-!](.*?)-/", t, re.S):
        for name in re.findall(r"`([A-Za-z_][A-Za-z0-9_'.]*)`", doc):
            short = name.split(".")[-1]
            wordlike = "_" in short or short[:1].islower()
            if len(short) > 2 and short != "sorry" and wordlike and short not in declared:
                problems.append(f"{f}: docstring names `{name}`, not declared here or in FC 35")
    code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", t, flags=re.S))
    if re.search(r":=\s*True\b|\bsorry\b|\badmit\b|native_decide", code):
        problems.append(f"{f}: placeholder, sorry, admit or native_decide")
    for imp in re.findall(r"^import\s+(\S+)", t, re.M):
        if not (imp.startswith("AME62") or imp == "FormalConjectures.OpenQuantumProblems.«35»"):
            problems.append(f"{f}: imports {imp}")
    for i, line in enumerate(t.replace("\r\n", "\n").split("\n"), 1):
        if len(line) > 100:
            problems.append(f"{f}:{i}: {len(line)} characters")
        if line != line.rstrip():
            problems.append(f"{f}:{i}: trailing whitespace")
    if b"\r" in raw[f]:
        problems.append(f"{f}: CRLF line endings")
if problems:
    print("\n".join(problems))
    sys.exit(1)
print(f"lexical audit clean over {len(files)} files")
