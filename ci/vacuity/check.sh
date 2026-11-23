#!/usr/bin/env bash
# Run from lean/ with lake env. Keep the solver outside the proof build so a
# slow theorem cannot hold up compilation. The module name is data for Lean.
set -euo pipefail

if (( $# )); then
    module=$1
    if [[ $module != VacuityFixture ]]; then
        python3 ../ci/lean_cache.py fill-private . "$module"
    fi
    jq -n --arg module "$module" '
      def imp($name; $all; $meta): {module: $name, importAll: $all, isMeta: $meta, isExported: false};
      {name: "VacuityAudit", isModule: true, importArts: {}, dynlibs: [], plugins: [], options: {},
       imports: [imp("Lean"; false; true), imp($module; true; false)]}' > "$VG_VACUITY_TMP/setup.json"
    exec lean --setup "$VG_VACUITY_TMP/setup.json" ../ci/vacuity/VacuityAudit.lean
fi

VG_VACUITY_TMP=$(mktemp -d)
export VG_VACUITY_TMP
trap 'rm -rf -- "$VG_VACUITY_TMP"' EXIT
export LEAN_PATH="$VG_VACUITY_TMP${LEAN_PATH:+:$LEAN_PATH}"
export VG_VACUITY_FINDINGS="$VG_VACUITY_TMP/findings"
touch "$VG_VACUITY_FINDINGS"
lean -R ../ci/vacuity -o "$VG_VACUITY_TMP/VacuityFixture.olean" ../ci/vacuity/VacuityFixture.lean
timeout -k 2 30 bash "$0" VacuityFixture

git diff --relative --name-only --no-renames -z HEAD^1 HEAD -- . |
    python3 ../ci/check_lean_vacuity.py > "$VG_VACUITY_TMP/modules"
SECONDS=0
incomplete=0
total=0
while IFS= read -r -d '' module; do
    total=$((total + 1))
    budget=$((300 - SECONDS))
    if (( budget > 60 )); then budget=60; fi
    if (( budget <= 0 )); then
        incomplete=$((incomplete + 1))
    elif ! timeout -k 2 "$budget" bash "$0" "$module"; then
        printf 'Incomplete proof hypothesis audit for %q\n' "$module"
        incomplete=$((incomplete + 1))
    fi
done < "$VG_VACUITY_TMP/modules"

printf 'Proof hypothesis audit: %d of %d selected modules incomplete.\n' "$incomplete" "$total"
if [[ -n ${GITHUB_STEP_SUMMARY:-} ]]; then
    {
        printf '### Proof hypothesis audit\n\nFindings: %d. Modules incomplete: %d of %d.\n\n' \
            "$(wc -l < "$VG_VACUITY_FINDINGS")" "$incomplete" "$total"
        cat "$VG_VACUITY_FINDINGS"
    } >> "$GITHUB_STEP_SUMMARY"
fi
