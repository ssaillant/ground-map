#!/usr/bin/env bash
# Fails if any theory reported as done contains sorry, oops or axiomatization.
set -euo pipefail
dir="${1:-isabelle}"
if grep -nE '\b(sorry|oops|axiomatization)\b' "$dir"/*.thy; then
  echo "Found sorry/oops/axiomatization in $dir" >&2
  exit 1
fi
echo "No sorry, oops or axiomatization in $dir/*.thy"
