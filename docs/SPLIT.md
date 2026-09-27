# Repository split, 2026-09-27

Source: [https://github.com/antidepersonalizationer/some-bounds-related-to-the-2-adic-littlewood-conjecture-open-problems](https://github.com/antidepersonalizationer/some-bounds-related-to-the-2-adic-littlewood-conjecture-open-problems), commit `73cafd67d867ba4c0b4a4e8397f24f2bd538f1ce`.

The original project had 337 modules under `VV/`, plus `VV.lean`.
The retained application set is the import closure of all original non-BBEK/non-Entropy application modules (excluding the audit), together with `VV.BBEKPositiveFullDiagonal`. It contains 154 inherited modules. The final assembly and audit are rewritten, and `VV.BBEKCompactEntropyCore` supplies the narrowed explicit admission.

The 180 remaining original source modules, excluding the replaced final assembly, audit and old admitted core, are preserved in the independent theory repository. Their dependency closure contains 282 inherited modules, including 102 shared snapshots. The old admitted core is preserved under `Research/ELRootAlternative.lean` with its original theorem type and namespace. The old final assembly and audit remain available in Git history and the local pre-split backup.

The split uses **source-module import closure**, a conservative dependency criterion. It does not attempt to delete individual unused declarations inside a retained file. Thus no theorem used by a retained file is removed merely because a text search did not find its name.

The 180 isolated modules are absent from the application's source tree and import graph. Some remain relevant to future work on EL; “outside this build” is not “mathematically unnecessary.” No stronger claim of minimality is made.

The compact entropy exclusion is still unproved. Moving the admission to that consequence changes the trust boundary; it is not proof progress. The application's two admissions and the theory repository's one optional research admission are separately audited. The two repositories do not import each other.

Original source paths and namespaces are retained where possible; topical entry modules provide navigation in the theory repository. Byte-for-byte source provenance is in `docs/source-provenance.json`. Shared snapshots must be synchronized deliberately; there is no automatic cross-repository update.

The main application is [https://github.com/antidepersonalizationer/some-bounds-related-to-the-2-adic-littlewood-conjecture-open-problems](https://github.com/antidepersonalizationer/some-bounds-related-to-the-2-adic-littlewood-conjecture-open-problems). The theory project is [https://github.com/antidepersonalizationer/s-arithmetic-dynamics-lean](https://github.com/antidepersonalizationer/s-arithmetic-dynamics-lean). Historical source and full Git history remain preserved. No large finite computation was run as part of this organization task.
