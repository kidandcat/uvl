#!/usr/bin/env bash
# The Lake package version must match the newest Keep a Changelog entry.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lake=$(sed -n 's/.*version := v!"\([0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\)".*/\1/p' "$root/lakefile.lean" | head -n 1)
cl=$(sed -n 's/^## \[\([0-9][0-9]*\.[0-9][0-9]*\.[0-9][0-9]*\)\].*/\1/p' "$root/CHANGELOG.md" | head -n 1)
if [ -z "${lake}" ] || [ -z "${cl}" ] || [ "${lake}" != "${cl}" ]; then
  echo "version check failed: lakefile='${lake:-missing}' changelog='${cl:-missing}'" >&2
  exit 1
fi
echo "version ${lake} matches CHANGELOG.md"
