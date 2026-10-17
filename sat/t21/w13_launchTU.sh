#!/bin/bash
# Wave 13 resume after a sandbox restart (current set, 05:31 UTC): sub-chains T (CPU 0) and U (CPU 1). S is paused.
cd "$(dirname "$0")"; ./w13_runT.sh; ./w13_runU.sh
