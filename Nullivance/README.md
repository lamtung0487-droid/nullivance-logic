# Nullivance Lean library

This directory is the machine-checked component of Nullivance Logic release
candidate 0.7.0.

```powershell
lake exe cache get
lake build
```

The environment is pinned to Lean 4.32.1 and mathlib v4.32.1. The default target
imports all project modules through `Nullivance.lean`. For the evidence map,
proof-hole policy, manuscript build, and complete release gate, see the repository
root `ARTIFACT.md` and `scripts/Verify-Release.ps1`.
