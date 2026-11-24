#!/usr/bin/env bash
set -euo pipefail
pkg=lean-4.36.0-linux.tar.zst
cd "$RUNNER_TEMP"
curl -fLsS --retry 3 -o "$pkg" "https://github.com/leanprover/lean4/releases/download/v4.36.0/$pkg"
echo "2b7ab1ed8b92d2e6abfaf41344823b510064dbc9c0260cac73eb496ab2dea6eb  $pkg" | sha256sum --check
tar --zstd -xf "$pkg" --wildcards 'lean-4.36.0-linux/bin/*' 'lean-4.36.0-linux/lib/*'
echo "$RUNNER_TEMP/lean-4.36.0-linux/bin" >> "$GITHUB_PATH"
