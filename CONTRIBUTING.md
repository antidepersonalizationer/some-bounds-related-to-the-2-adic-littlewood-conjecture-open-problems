# Contributing to this research snapshot

Useful contributions include independent checking of the formal statements, reproducible build reports, localized proof improvements, verification of the Problem 5 finite obligation and a proof of the EL root-invariance core. Read [PROOF_STATUS.md](PROOF_STATUS.md) before changing a theorem or describing a result.

For a proposed change:

1. State the mathematical claim or concrete problem being addressed, including the exact Lean declaration and any source reference.
2. Preserve the existing mathematical definitions and theorem hypotheses unless the proposed change explains why they must change. Do not weaken a result merely to make the proof compile.
3. Compile the affected modules, then run `lake build` and `lake env lean VV/Audit.lean` on the proposed final checkout. Report the exact compiler identity and tests actually run. On Windows, `Check-VV.ps1` also generates verification records.
4. Keep the two current admissions explicit. Do not introduce additional `sorry`, custom axioms or opaque assumption interfaces. A claimed removal must be supported by a kernel-checked proof of the actual declaration.
5. Keep generated caches, credentials, private conversations, machine-specific paths and temporary logs out of commits. Retain third-party source headers, notices and licenses.

A finite computation must be tied to the exact graph and Boolean property used by `VV.P5FiniteCheck.rank_check_10_14`. A reported run of a different implementation, without a proved connection, does not discharge that obligation. Large runs should document resource requirements and provide a reproducible certificate or verification procedure.

If a report or source hash manifest was generated before a change, label it as historical or regenerate it. Never replace an actual failed or unperformed check with a success claim. Disclose material AI assistance and distinguish internal review from external mathematical review.

The original project contributions do not yet have a project-wide license. Third-party files retain their existing Apache-2.0 terms. A contributor should make the intended permission for their own contribution explicit; this document does not itself grant or impose a contribution license.
