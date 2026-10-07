# Classical Theorems in Lean

Lean proofs of eight classical theorems, with reusable mathematics for geometry, analysis and logic.

These theorems appear in Freek Wiedijk’s [Formalizing 100 Theorems](https://www.cs.ru.nl/~freek/100/), an online catalog tracking formalizations of classical theorems across proof assistants.

- **Incompleteness for Robinson arithmetic:** every satisfiable recursively enumerable extension of Robinson arithmetic Q has an independent sentence.
- **Independence of the parallel postulate:** the Euclidean plane and Klein disk satisfy Tarski neutral geometry and Dedekind continuity. The Euclidean plane satisfies the parallel postulate; the Klein disk refutes it.
- **Euler’s polyhedron formula:** V − E + F = 2 for every full-dimensional convex polytope in real three-space, counting its geometric vertices, edges and facets.
- **Green’s theorem:** for a positively oriented boundary, the line integral equals the integral of curl over a planar Jordan domain. The library includes versions for either orientation, local C¹ regularity, changes of parameter, arbitrary compact parameter intervals and piecewise C¹ boundaries.
- **Isoperimetric theorem:** the sharp area–perimeter inequality for continuous rectifiable Jordan curves, with equality exactly for circles.
- **Heron’s formula for triangle area:** the Lebesgue area of a nondegenerate Euclidean triangle equals the square root of the semiperimeter product.
- **Pascal’s hexagon theorem:** collinearity of the opposite-side intersections for six points on a conic, including a nonsingular conic formulation.
- **Desargues’s theorem:** concurrency of the lines through corresponding vertices implies collinearity of the corresponding side intersections. Includes a converse for noncollinear triangles.

The eight theorems are represented by **ten audited Lean declarations**; Pascal and Desargues each have two main declarations. Their precise hypotheses and supporting results are described in [theorems.md](theorems.md) and the [proof outlines](proofs.md). Pascal and Desargues are translations of HOL Light arguments, proved anew in Lean. Foundation provides the incompleteness infrastructure. Mathlib already provides a trigonometric form of Heron’s formula; this library proves its geometric area interpretation.

**AI-use disclosure:** OpenAI Codex was used extensively, under human direction, to develop proof strategies, write and refactor this project’s Lean code, and prepare documentation. Lean’s kernel checks the resulting formal proof terms, and the build audits their axioms as described below.

Use Lean **4.34.1**, Python **3.11 or newer**, and the pinned mathlib revision in `lake-manifest.json`:

```sh
lake exe cache get
python3 scripts/release.py
```

The verification command checks source integrity, builds the library and audits proof axioms.

Use `import ClassicalTheorems` for the full library, or import an individual theorem module such as `ClassicalTheorems.Euler`. [theorems.md](theorems.md) links to all eight theorem modules. `ClassicalTheorems.Translations` imports Pascal and Desargues together. Public theorem names include `ClassicalTheorems.euler_polyhedron`; the translated proofs use the `HOLLightPort.Pascal` and `HOLLightPort.Desargues` namespaces.

Reusable sign lemmas are in `ClassicalTheorems.Progress.Orientation`. `ClassicalTheorems.Progress.HeronAlgebra` proves the determinant and side-length identity independently of Jordan area and Green’s theorem. Euler’s general cycle-filling proof is independent of pyramid face counting.

The build checks the axioms used by all ten main theorem declarations, including those reached through dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are accepted; `sorryAx` and other axioms cause the audit to fail. Supporting results are also audited. Project proofs contain no unfinished placeholders.

Licensed supporting sources from Foundation, Unico, MovingSofa, Jordan Pick, Schönflies and HOL Light are bundled. Their upstream revisions, licenses, modification notices and hashes are preserved in [third-party.md](third-party.md), [NOTICE](NOTICE) and `vendor/*/upstream.json`.

Package dependencies use relative paths within the project or pinned Git revisions. Source archives must omit every `.lake` directory; Lake retrieves the pinned external packages and their caches during setup.

Run the verification command above before sharing changed sources.

Original project code and documentation are licensed under [Apache-2.0](LICENSE). Files with explicit BSD-2-Clause notices and bundled third-party sources retain their respective licenses; see [NOTICE](NOTICE) and [third-party.md](third-party.md).

Citation metadata for version 0.0.2 is in [CITATION.cff](CITATION.cff). The published version 0.0.1 can be cited as:

Brackx, M. (2026). *Classical Theorems in Lean* (Version 0.0.1) [Software]. Zenodo. [https://doi.org/10.5281/zenodo.23144255](https://doi.org/10.5281/zenodo.23144255).

Zenodo releases use a source ZIP of the corresponding Git release tag. It contains the committed source files. Run the verification command above before creating the release tag.
