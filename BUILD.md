# Build and verification

The package pins mathlib commit `5c0c94b3f563ed756b48b9439788c53b0d56a897` and its dependency revisions in `lake-manifest.json`. Install elan and the toolchain specified in `lean-toolchain`, fetch dependencies, then run `lake exe cache get` for mathlib's cache if available and `lake build`.

The toolchain label `leanprover/lean4:v4.20.1` corresponds to compiler commit `b02228b03f655c0cd051d82280ad5758359ec8ba`; the compiler's version string says Lean 4.20.0. This label/version difference is intentional and the reporting script checks the commit, not just the displayed version.

Run each audit listed in `audit-config.json` using `lake env lean PATH/TO/Audit.lean`. On Windows or another platform with PowerShell 7 and matching Lean available, `./Check-Project.ps1` performs the build, import coverage checks, admission inventory/signature checks and recursive audits. The default build is a library build, not execution of a huge finite enumeration.

An optional `-DependencyPackages PATH` accepts a directory containing existing dependency Git checkouts. Their exact revisions and tracked-file cleanliness are checked before local Lake overrides are generated under `.lake/`. These overrides are machine-local and excluded from the published sources. The wrapper is primarily tested on Windows; no cross-platform wrapper validation is claimed.

`verification/report.json` records the check time, compiler/dependency identities, source hashes, declaration counts and admissions. `verification/final-axioms.txt` contains actual audit output. This release's validation may reuse pinned dependency caches and unchanged project compiled artifacts. It is not a claim of an empty-cache clean-clone build. Rebuilding source and running the audits is the reproducibility path.

The source release excludes `.lake/`, compiled outputs and temporary logs. Required small certificates are Lean source files; no external large enumeration certificate is supplied. A successful build with an explicitly admitted proof is not proof of the admitted statement.
