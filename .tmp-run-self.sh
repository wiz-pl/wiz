#!/bin/bash
set -e
cd /workspace/wt/lin-result
export LAKE_JOBS=2
lake build tests
./.lake/build/bin/tests '=selfhost'
