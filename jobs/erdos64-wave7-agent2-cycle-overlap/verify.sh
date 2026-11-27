#!/usr/bin/env bash
set -euo pipefail
echo "===BEGIN_B64==="
gzip -9 -c jobs/erdos64-wave7-agent2-cycle-overlap/Wave7Agent2CycleOverlap.lean | base64 -w 120
echo "===END_B64==="
exit 1
