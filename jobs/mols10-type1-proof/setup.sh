#!/usr/bin/env bash
set -euo pipefail
d=$(mktemp -d)
git clone -q https://github.com/arminbiere/cadical.git "$d/cadical"
git -C "$d/cadical" checkout -q 6b3d70b9ce00ecbce3f829bab76d185f0e92618c
(cd "$d/cadical"; ./configure; make -j4)
sudo install "$d/cadical/build/cadical" /usr/local/bin/cadical
git clone -q https://github.com/marijnheule/drat-trim.git "$d/drat-trim"
git -C "$d/drat-trim" checkout -q 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
(cd "$d/drat-trim"; make drat-trim)
sudo install "$d/drat-trim/drat-trim" /usr/local/bin/drat-trim
cadical --version
rm -rf "$d"
