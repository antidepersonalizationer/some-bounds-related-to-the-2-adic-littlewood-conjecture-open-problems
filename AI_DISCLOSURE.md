# AI-assisted development disclosure

OpenAI ChatGPT and Codex were used in the development of this research snapshot, including mathematical exploration, Lean proof programming, debugging, documentation and auxiliary review. Automated subagents also assisted with bounded implementation and review tasks. The use of multiple agents does not constitute independent human peer review.

Lean checks proof terms against the statements and definitions actually encoded. It does not by itself establish that a formal statement expresses the intended informal result, nor does it prove statements filled by `sorry`. The two admitted obligations and the audit boundary are documented in [PROOF_STATUS.md](PROOF_STATUS.md).

Claims about verification refer to the recorded compiler runs and their stated scope. The small bound-2 Problem 5 certificate was checked by the Lean kernel; the bound-10, depth-14 computation remains unexecuted and independently unverified. The EL core remains unproved. The new local project build reused pinned dependency caches and is not a clean-clone build. The original contributions should be treated as a research artifact inviting mathematical and formal review.

The publication contains selected source code and public documentation. Private conversations, account information, machine paths and working archives are not part of the intended release. Public paper references and third-party code provenance are recorded separately in [THIRD_PARTY.md](THIRD_PARTY.md) and the source notices.
