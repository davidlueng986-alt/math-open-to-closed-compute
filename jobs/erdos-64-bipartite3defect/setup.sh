#!/usr/bin/env bash
set -euo pipefail
bash jobs/erdos-64-sms-direct/setup.sh
python3 -m pip install --disable-pip-version-check 'networkx>=3.3,<4'
