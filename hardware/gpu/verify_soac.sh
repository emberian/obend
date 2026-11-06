#!/usr/bin/env bash
# Array reductions/scans: regenerated artifacts, device values, an actual wrong-answer
# tooth, and an optional independent NumPy baseline/check (SOAC_PYTHON interpreter).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${HERE}/../.." && pwd)"
EMIT="${OBEND_EMIT_GPU:-${ROOT}/lean/.lake/build/bin/obend-emit-gpu}"
RUN="${OBEND_GPU_RUN:-${HERE}/runner/target/release/obend-gpu-run}"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/verify_soac.XXXXXX")"
trap 'rm -rf "${WORK}"' EXIT
if [[ "$(uname -s)" == Linux && -r /usr/share/vulkan/icd.d/radeon_icd.x86_64.json && "${GPU_ICD:-radv}" != any ]]; then
  export VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json
fi
if command -v sha256sum >/dev/null 2>&1; then SHA=(sha256sum); else SHA=(shasum -a 256); fi
ADAPTER=()
[[ -z "${GPU_ADAPTER:-}" ]] || ADAPTER=(--adapter "${GPU_ADAPTER}")
GRAPHS=(soac-boundaries soac-empty soac-no-segments soac-single-65536 soac-segments-64x1024)
for g in "${GRAPHS[@]}"; do
  "${EMIT}" "${g}" --out "${WORK}/${g}"
  if [[ -d "${HERE}/graphs/${g}" ]]; then
    diff -r "${HERE}/graphs/${g}" "${WORK}/${g}"
  else
    (cd "${WORK}/${g}" && "${SHA[@]}" -c "${HERE}/graphs/${g}.sha256")
  fi
  "${RUN}" "${WORK}/${g}" "${ADAPTER[@]}" | tee -a "${WORK}/gpu.log"
done
"${EMIT}" soac-boundaries --out "${WORK}/planted" --plant addAsSub
if "${RUN}" "${WORK}/planted" "${ADAPTER[@]}" >"${WORK}/plant.out" 2>"${WORK}/plant.err"; then
  echo '[FAIL] planted addAsSub was not caught' >&2
  exit 1
fi
# A shader validation failure or crash does not count as detecting wrong arithmetic.
if grep -Eq '\[wgpu error\]|Validation Error|panicked' "${WORK}/plant.err"; then
  cat "${WORK}/plant.err" >&2
  echo '[FAIL] planted run reported an infrastructure failure' >&2
  exit 1
fi
if ! grep -Eq 'vector [0-9]+: gpu=.* expected=' "${WORK}/plant.out"; then
  cat "${WORK}/plant.err" >&2
  echo '[FAIL] planted run failed without an output mismatch' >&2
  exit 1
fi
echo '[PASS] planted reduction/scan addAsSub produced an output mismatch'
if [[ -n "${SOAC_PYTHON:-}" ]]; then
  REPORT_ARGS=()
  [[ -z "${SOAC_REPORT:-}" ]] || REPORT_ARGS=(--out "${SOAC_REPORT}")
  "${SOAC_PYTHON}" "${HERE}/soac_numpy.py" "${WORK}" --gpu-log "${WORK}/gpu.log" "${REPORT_ARGS[@]}"
fi
echo '[PASS] SOAC arrays: artifacts, independent expected values, device, wrong-answer tooth'
