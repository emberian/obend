#!/usr/bin/env bash
# Reproducible end-to-end Rust MIR -> Charon (.llbc) -> Aeneas (Lean 4.35) -> Lake verification script
# for `crates/obend-keccak`.
# Run on a Linux verification host with Charon, Aeneas, Rust, Lean 4.35, and Python 3 installed.
# Optionally set AENEAS_TOOLS_DIR to the directory containing `charon` and `aeneas`.
set -euo pipefail

if [[ "$(uname -s)" != Linux ]]; then
  echo "ERROR: extraction and verification must run on a Linux build host (hbox / bb2)." >&2
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
CRATE_DIR="${REPO_ROOT}/crates/obend-keccak"
LEAN_DIR="${SCRIPT_DIR}/lean"
LLBC_FILE="${SCRIPT_DIR}/obend_keccak.llbc"

if [[ -d "${HOME}/.cargo/bin" ]]; then
  export PATH="${HOME}/.cargo/bin:${PATH}"
fi
if [[ -d "${HOME}/.elan/bin" ]]; then
  export PATH="${HOME}/.elan/bin:${PATH}"
fi
if [[ -n "${AENEAS_TOOLS_DIR:-}" && -d "${AENEAS_TOOLS_DIR}" ]]; then
  export PATH="${AENEAS_TOOLS_DIR}:${PATH}"
elif [[ -d "${HOME}/.cache/aeneas-tools/aeneas-dist" ]]; then
  export PATH="${HOME}/.cache/aeneas-tools/aeneas-dist:${PATH}"
fi

for tool in charon aeneas cargo lake python3; do
  if ! command -v "${tool}" >/dev/null 2>&1; then
    echo "ERROR: ${tool} is missing; install it on PATH or set AENEAS_TOOLS_DIR." >&2
    exit 1
  fi
done

echo "[1/4] Running Rust FIPS 202 / SP 800-185 conformance and unit tests on crates/obend-keccak..."
(
  cd "${REPO_ROOT}"
  cargo test -p obend-keccak
)

echo "[2/4] Extracting crates/obend-keccak MIR to LLBC via Charon..."
(
  cd "${CRATE_DIR}"
  charon cargo --preset=aeneas --dest-file "${LLBC_FILE}" -- --lib
)

echo "[3/4] Translating LLBC to pure Lean 4.35 via Aeneas..."
rm -f "${LEAN_DIR}/ObendKeccak/FunsExternal.lean" \
      "${LEAN_DIR}/ObendKeccak/FunsExternal_Template.lean" \
      "${LEAN_DIR}/ObendKeccak/TypesExternal.lean" \
      "${LEAN_DIR}/ObendKeccak/TypesExternal_Template.lean"
(
  cd "${SCRIPT_DIR}"
  aeneas -sequential -backend lean -split-files -dest "${LEAN_DIR}" -subdir ObendKeccak -no-progress-bar "${LLBC_FILE}"
)

for external in \
  "${LEAN_DIR}/ObendKeccak/FunsExternal.lean" \
  "${LEAN_DIR}/ObendKeccak/FunsExternal_Template.lean" \
  "${LEAN_DIR}/ObendKeccak/TypesExternal.lean" \
  "${LEAN_DIR}/ObendKeccak/TypesExternal_Template.lean"; do
  if [[ -e "${external}" ]]; then
    echo "ERROR: extraction produced an external-model dependency: ${external}" >&2
    exit 1
  fi
done

# LAW-M1 header post-processing: Aeneas emits `module`, `public import`s, and a file-wide
# `@[expose] public section`. Narrow the header to `public section` and expose only the four
# newtype aliases in `Types.lean` (`<= 12` `@[expose]` cap, zero file-wide expose). Idempotent.
python3 - "${LEAN_DIR}/ObendKeccak" <<'PY_HEADERS'
from pathlib import Path
import re
import sys

for name in ("Types.lean", "Funs.lean"):
    path = Path(sys.argv[1]) / name
    lines = path.read_text().splitlines(keepends=True)
    boundary = next(
        (i for i, line in enumerate(lines)
         if line.startswith(("open ", "namespace ", "set_option "))),
        None,
    )
    if boundary is None:
        raise SystemExit(f"Cannot identify generated header in {path}")
    header, body = lines[:boundary], lines[boundary:]
    imports = []
    comments = []
    for line in header:
        stripped = line.strip()
        match = re.fullmatch(r"(?:public\s+)?import\s+(.+)", stripped)
        if match:
            if match[1] not in imports:
                imports.append(match[1])
        elif stripped in ("module", "@[expose] public section", "public section"):
            continue
        elif not stripped or stripped.startswith("--"):
            comments.append(line)
        else:
            raise SystemExit(f"Unexpected generated header in {path}: {stripped}")
    if not imports:
        raise SystemExit(f"Missing generated imports in {path}")
    body_text = "".join(body)
    if name == "Types.lean":
        for alias in ("Shake128", "Shake256", "Cshake256", "Kmac256"):
            raw = f"@[reducible]\ndef {alias} :="
            exposed = f"@[reducible, expose]\ndef {alias} :="
            if body_text.count(raw) + body_text.count(exposed) != 1:
                raise SystemExit(f"Expected exactly one type alias {alias} in {path}")
            body_text = body_text.replace(raw, exposed)
    path.write_text(
        "".join(comments)
        + "module\n"
        + "".join(f"public import {module}\n" for module in imports)
        + "public section\n"
        + body_text
    )
PY_HEADERS

echo "[4/4] Verifying Aeneas prelude, extracted ObendKeccak MIR, proofs, and Obend.Digest spec weld via Lake..."
(
  cd "${LEAN_DIR}"
  lake build --wfail Aeneas ObendKeccak ObendKeccakMirProofs ObendKeccakSpecWeld AuditMirAxioms
  lake exe audit-mir-axioms
  test -s lake-manifest.json
)

echo "SUCCESS: Charon + Aeneas extraction and Lean 4.35 MIR proofs verified cleanly."
