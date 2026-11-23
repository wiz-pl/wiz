# `scry cs` with only excluded files

The only `.cs` file is under `bin/`, which the built-in exclusion rule drops. The walk
therefore finds nothing to analyse and `scry cs` exits **3** (nothing analysed), not 0.
