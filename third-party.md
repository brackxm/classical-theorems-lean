# Supporting libraries and attribution

Only the imported source closure is bundled. No supporting dependency is claimed as new work of this project.

- **foundation**: [https://github.com/FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation), `7906b595899b0823922baf03a942b7126b52e759`, Apache-2.0. Preserved attribution: [LICENSE](vendor/foundation/LICENSE). [Port provenance](vendor/foundation/upstream.json).
- **unico**: [https://github.com/Solarys431/unico-lean-proofs](https://github.com/Solarys431/unico-lean-proofs), `794568d279e377c34e3ab93a5e0626467f7d9e0d`, Apache-2.0. Preserved attribution: [LICENSE](vendor/unico/LICENSE), [CITATION.cff](vendor/unico/CITATION.cff). [Port provenance](vendor/unico/upstream.json).
- **moving-sofa**: [https://github.com/deancureton/MovingSofa](https://github.com/deancureton/MovingSofa), `4d5569131940815f47a9ccf3e90a4c5043c56127`, Apache-2.0. Preserved attribution: [LICENSE](vendor/moving-sofa/LICENSE). [Port provenance](vendor/moving-sofa/upstream.json).
- **jordan-pick**: [https://github.com/rkirov/jordan_pick](https://github.com/rkirov/jordan_pick), `b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, Apache-2.0. Preserved attribution: [LICENSE](vendor/jordan-pick/LICENSE). [Port provenance](vendor/jordan-pick/upstream.json).
- **schoenflies**: [https://github.com/alonamaloh/schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean), `05a43d29cde026618777db3d4e4316204ccca237`, Apache-2.0. Preserved attribution: [LICENSE](vendor/schoenflies/LICENSE). [Port provenance](vendor/schoenflies/upstream.json).

Original compatibility modifications for the shared Lean/mathlib version retain their modification notices. Project names in local adaptation notices are standardized; mathematical proof bodies and upstream copyright notices are preserved. The retained patches.diff files describe the original full port and may mention modules outside this selected import closure.

HOL Light’s independence model strategy is attributed to John Harrison and the HOL Light contributors; source provenance is recorded in [proofs.md](proofs.md#independence-of-the-parallel-postulate), and the [BSD-2-Clause license](vendor/hol-light-port/LICENSE) is preserved. The proof outlines credit the external Lean infrastructure used by each development.

## Pascal and Desargues translations

[HOLLightPort](vendor/hol-light-port/upstream.json) manually adapts John Harrison and contributors’ HOL Light coordinate/bracket proofs at revision `cba9198db76e9dfb89cbd653df9412d01f65b22a`. The [BSD-2-Clause license](vendor/hol-light-port/LICENSE), byte-identical original sources in `upstream`, compatibility patch and Lean adaptation notices are preserved. These are Lean proofs of mathematical translations; no foreign proof objects or axioms are imported. See [proofs.md](proofs.md#pascals-hexagon-theorem).
