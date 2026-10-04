# Proof outlines

This document explains the arguments and the main supporting modules. Precise theorem statements and public declaration names are in [theorems.md](theorems.md); dependency revisions, licenses and compatibility changes are recorded in [third-party.md](third-party.md) and `vendor/*/upstream.json`.

The Lean modules contain the executable axiom audits. The default build checks the ten main declarations in `ClassicalTheorems.IndexAudit` and supporting declarations in their own modules. These explanations introduce no additional hypotheses or trusted proof objects.

## Incompleteness for Robinson arithmetic

The proof uses computably inseparable program outcomes: the predicates saying that program n, on input n, returns 0 or returns 1. Both are recursively enumerable and disjoint. A computable separator would allow a program to return the opposite of its own classification, contradicting diagonalization.

The seven Robinson axioms suffice to interpret standard numerals correctly and identify every element below a standard numeral with one of finitely many numerals. Bounded formulas therefore agree at numeral inputs in every Robinson model and in the natural numbers. Foundation's representation of enumerable predicates supplies bounded witness matrices. A translation into the original arithmetic language preserves their semantics and variable support. A Rosser comparison of positive and negative witnesses produces actual sentences separating the two program outcomes, including when a proposed witness is nonstandard.

To apply inseparability to an arbitrary enumerable extension of Q, the proof must enumerate its consequences in the original encoding. An auxiliary Foundation language has exactly the original arithmetic symbols and a logical equality relation. Translation preserves truth and provability; equality-model quotients recover ordinary equality. A primitive-recursive partial inverse recovers the original serialized syntax, so the translated axiom image is enumerable. Foundation's proof calculus, Craig construction, soundness and completeness then enumerate the positive and negative consequences of the Rosser sentence family. Semantic completeness would yield a computable separator by Post's theorem, giving the contradiction.

The main supporting modules are:

- [RobinsonNumerals](ClassicalTheorems/Progress/RobinsonNumerals.lean), [RobinsonBounded](ClassicalTheorems/Progress/RobinsonBounded.lean) and [RobinsonRepresentation](ClassicalTheorems/Progress/RobinsonRepresentation.lean): numeral arithmetic, bounded truth and Rosser witness comparison.
- [ProgramWitnessMatrices](ClassicalTheorems/Progress/ProgramWitnessMatrices.lean), [FoundationArithmeticTranslation](ClassicalTheorems/Progress/FoundationArithmeticTranslation.lean) and [RobinsonProgramWitnesses](ClassicalTheorems/Progress/RobinsonProgramWitnesses.lean): bounded representation of enumerable program outcomes.
- [ArithmeticProofLanguage](ClassicalTheorems/Progress/ArithmeticProofLanguage.lean), [ArithmeticProofTranslation](ClassicalTheorems/Progress/ArithmeticProofTranslation.lean), [ArithmeticProofDecoder](ClassicalTheorems/Progress/ArithmeticProofDecoder.lean), [ArithmeticProofTokenCoding](ClassicalTheorems/Progress/ArithmeticProofTokenCoding.lean), [ArithmeticProofFormulaCoding](ClassicalTheorems/Progress/ArithmeticProofFormulaCoding.lean) and [ArithmeticProofAxioms](ClassicalTheorems/Progress/ArithmeticProofAxioms.lean): the exact language and effective axiom translation.
- [FoundationEffectiveConsequences](ClassicalTheorems/Progress/FoundationEffectiveConsequences.lean), [InseparablePrograms](ClassicalTheorems/Progress/InseparablePrograms.lean) and [ArithmeticIncompleteness](ClassicalTheorems/Progress/ArithmeticIncompleteness.lean): enumeration of consequences and the final contradiction.

[ArithmeticModels](ClassicalTheorems/Progress/ArithmeticModels.lean) also constructs natural and nonstandard models of the exact axioms; [ArithmeticEncoding](ClassicalTheorems/Progress/ArithmeticEncoding.lean) proves Q itself is enumerable. These give concrete independent extensions and finite-extension corollaries. The general theorem adds neither induction nor a Church's-thesis axiom. Foundation supplies representation and proof infrastructure; its stronger arithmetic incompleteness theorem is not used as a substitute for the Q statement.

## Independence of the parallel postulate

Two coordinate models establish independence. The Euclidean plane uses affine betweenness and metric congruence. The Klein model uses the open unit disk with affine betweenness and congruence defined by equality of normalized Lorentz inner products. Each satisfies Tarski neutral geometry and full Dedekind continuity. The Euclidean plane satisfies the parallel postulate; an explicit configuration in the Klein disk refutes it.

Affine segment intersection proves inner Pasch. Compactness and a maximal-distance point in the closure of the lower set prove continuity. In the Klein model, a hemisphere sum-of-squares identity gives the congruence laws, and equidistant loci are affine lines. For the five-segment axiom, the two adjacent cosine distances determine the extension coefficients uniquely. Segment construction takes place on the unit Lorentz hyperboloid and is projected back to the disk. The negative parallel configuration uses the origin, east and north half-axis points, a quarter-diagonal intersection and a three-fifths diagonal tip.

The model construction is organized in [ParallelAffine](ClassicalTheorems/Progress/ParallelAffine.lean), [ParallelEuclidean](ClassicalTheorems/Progress/ParallelEuclidean.lean), [ParallelKlein](ClassicalTheorems/Progress/ParallelKlein.lean), [ParallelKleinMetric](ClassicalTheorems/Progress/ParallelKleinMetric.lean), [ParallelKleinFiveSegment](ClassicalTheorems/Progress/ParallelKleinFiveSegment.lean), [ParallelKleinSegment](ClassicalTheorems/Progress/ParallelKleinSegment.lean) and [ParallelKleinModel](ClassicalTheorems/Progress/ParallelKleinModel.lean).

The model strategy is adapted from John Harrison and contributors' HOL Light sources at revision `cba9198db76e9dfb89cbd653df9412d01f65b22a`: [Tarski geometry](https://github.com/jrh13/hol-light/blob/cba9198db76e9dfb89cbd653df9412d01f65b22a/Multivariate/tarski.ml) and [independence](https://github.com/jrh13/hol-light/blob/cba9198db76e9dfb89cbd653df9412d01f65b22a/100/independence.ml). The Lean development replaces the Möbius/isometry machinery with direct Lorentz-coordinate arguments. Its BSD-2-Clause notices and the original copyright and license are retained in source headers, [NOTICE](NOTICE) and [vendor/hol-light-port/LICENSE](vendor/hol-light-port/LICENSE).

SHA-256 hashes of the inspected original sources:

| Source | SHA-256 |
|---|---|
| `Multivariate/tarski.ml` | `b64c2168dcf8ba44f3532701d8ff92808c50d98da5dd3c41be8ac1ad0ed2e5d5` |
| `100/independence.ml` | `83ce6195031b469bea18714841659b67a43a87942d8c7aec1997b58369bb3dc0` |

## Euler's polyhedron formula

The proof counts genuine exposed faces of the convex hull. Unico supplies the geometric face theory, local incidences, vertex sections and graph connectivity. Local code identifies the finite vertex, edge and facet types and proves their incidence identities.

Over 𝔽₂, the edge–vertex and edge–facet incidence matrices have ranks V − 1 and F − 1. Polygon incidences show that the boundary of a facet boundary is zero. Rank-nullity reduces Euler equality to the assertion that every geometric edge cycle is a sum of facet boundaries.

A generic linear height distinguishes the vertices. Descending edges at a vertex are connected through suitable facets, so their even chains can be filled locally. Adding those facet boundaries cancels the highest vertex of a cycle without introducing a vertex of equal or greater height. Finite induction fills the whole cycle. The incidence ranks yield V − E + F = 2, and facet double counting yields E ≤ 3V − 6.

The geometry and rank calculation are in [PolytopeFaces](ClassicalTheorems/Progress/PolytopeFaces.lean), [PolytopeIncidence](ClassicalTheorems/Progress/PolytopeIncidence.lean) and [PolytopeEulerBound](ClassicalTheorems/Progress/PolytopeEulerBound.lean). The filling argument runs through [DescendingVertexFigure](ClassicalTheorems/Progress/DescendingVertexFigure.lean), [IncidenceFilling](ClassicalTheorems/Progress/IncidenceFilling.lean), [DescendingCycleFilling](ClassicalTheorems/Progress/DescendingCycleFilling.lean), [CycleElimination](ClassicalTheorems/Progress/CycleElimination.lean) and [PolyhedronEuler](ClassicalTheorems/Progress/PolyhedronEuler.lean).

[SimplexEuler](ClassicalTheorems/Progress/SimplexEuler.lean) gives binomial face counts for simplices, and [PyramidEuler](ClassicalTheorems/Progress/PyramidEuler.lean) gives the full pyramid f-vector. The general proof does not rely on these special cases or assume planarity or Euler equality. It is not a direct translation of the [HOL Light polyhedron development](https://github.com/jrh13/hol-light/blob/cba9198db76e9dfb89cbd653df9412d01f65b22a/100/polyhedron.ml).

## Green's theorem

MovingSofa's Jordan signed-area identity is the starting point. The proof identifies its Stieltjes integrals with ordinary derivative integrals for a C¹ boundary. A smooth cutoff extends a coefficient defined near the domain to a globally C¹ compactly supported field, preserving its values and derivatives near the closure.

For a direction v and sufficiently small positive ε, the rank-one shear T(z) = z + εP(z)v is a homeomorphism by a contraction argument. Its Jacobian determinant is 1 + εdP(v), which stays positive, and the shear preserves winding. The signed boundary area changes by a linear combination of the coefficient-weighted line integrals; the quadratic term vanishes on a closed curve. Change of variables computes the domain-area change as ε times the integral of the directional derivative. Cancelling ε gives the directional Green identity. Two coordinate directions give the curl formula.

The core argument is in [GreenClassicalArea](ClassicalTheorems/Progress/GreenClassicalArea.lean), [GreenExtension](ClassicalTheorems/Progress/GreenExtension.lean), [GreenShear](ClassicalTheorems/Progress/GreenShear.lean) and [GreenFull](ClassicalTheorems/Progress/GreenFull.lean). Orientation results allow either sign, determine it from one positive winding check, or remove it by taking absolute values. The sign depends on the boundary and works for every coefficient pair.

Affine substitution handles arbitrary compact parameter intervals. A local compact-support extension removes global C¹ assumptions on curves. Interval-integral substitution handles nonlinear clocks, including pauses and retraced arcs. For finite piecewise boundaries, the clock 3t² − 2t³ flattens endpoint derivatives; the pieces can then be joined into a C¹ curve while preserving their line integrals. Schönflies' polygon separation theorem supplies the geometry for certified polygons, including collinear subdivision vertices.

These extensions are in [GreenOrientation](ClassicalTheorems/Progress/GreenOrientation.lean), [GreenInterval](ClassicalTheorems/Progress/GreenInterval.lean), [GreenLocalCurve](ClassicalTheorems/Progress/GreenLocalCurve.lean), [GreenReparametrization](ClassicalTheorems/Progress/GreenReparametrization.lean), [GreenPiecewise](ClassicalTheorems/Progress/GreenPiecewise.lean), [GreenPiecewiseLocal](ClassicalTheorems/Progress/GreenPiecewiseLocal.lean) and [GreenPolygon](ClassicalTheorems/Progress/GreenPolygon.lean). The proof uses the signed-area/shear argument rather than directly translating HOL Light's Cauchy–Pompeiu development.

## Isoperimetry and circle equality

Mathlib's Fourier theory gives the sharp periodic Wirtinger inequality. Subtracting the mean and completing squares bounds signed area by energy divided by 4π. The Jordan signed-area identity converts this to a geometric area bound. Smooth reparametrization by a positive density gives the C¹ perimeter inequality, including stationary points by approximation.

The argument extends to absolutely continuous coordinates using integration by parts against Fourier tests and the Stieltjes derivative-density identity. Accumulated variation gives ordered Lipschitz representatives of rectifiable curves. Representatives with Lipschitz constant at most perimeter + ε give the inequality as ε tends to zero; simplicity also permits exact reparametrization by accumulated length.

Equality forces the completed-square defects to vanish almost everywhere in the exact representative. The resulting rotation ODE has an absolutely continuous integrating factor with zero derivative almost everywhere. It is therefore constant, and the boundary is a circle. Simplicity excludes radius zero. Conversely, angular lifting bounds a simple circular parametrization's perimeter by its circumference, while disk volume gives the area bound. The sharp inequality forces both bounds to be equalities.

The final theorem determines orientation from Jordan geometry. Schönflies supplies an ambient homeomorphism between the unit circle and the boundary. Every loop avoiding a point deforms to an integer traversal of a circle. Pulling this deformation through the homeomorphism, using homotopy invariance and the integer-traversal winding formula, forces interior winding to be ±1. Local constancy gives one orientation throughout the interior; parameter reversal handles either sign. Affine normalization gives arbitrary compact intervals.

The main analytic modules are [Wirtinger](ClassicalTheorems/Progress/Wirtinger.lean), [IsoperimetricClassical](ClassicalTheorems/Progress/IsoperimetricClassical.lean), [IsoperimetricAC](ClassicalTheorems/Progress/IsoperimetricAC.lean), [IsoperimetricACArea](ClassicalTheorems/Progress/IsoperimetricACArea.lean), [RectifiableExactParameter](ClassicalTheorems/Progress/RectifiableExactParameter.lean) and [IsoperimetricACEquality](ClassicalTheorems/Progress/IsoperimetricACEquality.lean). [IsoperimetricCircleIff](ClassicalTheorems/Progress/IsoperimetricCircleIff.lean) and [IsoperimetricInterval](ClassicalTheorems/Progress/IsoperimetricInterval.lean) assemble the sharp equality characterization and interval forms.

Reusable topology is in [WindingPerturbation](ClassicalTheorems/Progress/WindingPerturbation.lean), [LoopCircleDeformation](ClassicalTheorems/Progress/LoopCircleDeformation.lean), [PeriodicWinding](ClassicalTheorems/Progress/PeriodicWinding.lean), [SchoenfliesBridge](ClassicalTheorems/Progress/SchoenfliesBridge.lean) and [SchoenfliesWinding](ClassicalTheorems/Progress/SchoenfliesWinding.lean). [CircleWinding](ClassicalTheorems/Progress/CircleWinding.lean) gives exact circle area and perimeter, while [RadialWinding](ClassicalTheorems/Progress/RadialWinding.lean), [SingleRayWinding](ClassicalTheorems/Progress/SingleRayWinding.lean) and [JordanCyclicCut](ClassicalTheorems/Progress/JordanCyclicCut.lean) provide specialized geometric orientation criteria. Those criteria are not hypotheses of the final theorem.

## Heron's formula

Polygon Green with the real coordinate as coefficient gives the triangle's area as half the absolute determinant. A polynomial identity in squared side lengths relates the determinant to the semiperimeter product. A linear isometry transfers Lebesgue volume between complex and real-plane coordinates, producing the geometric area formula.

[HeronAlgebra](ClassicalTheorems/Progress/HeronAlgebra.lean) proves the determinant identity independently of Jordan area and Green's theorem. [Heron](ClassicalTheorems/Heron.lean) assembles the geometric result. Mathlib already proves a trigonometric form of Heron's formula; this development supplies its interpretation as the Lebesgue area enclosed by the three sides.

## Pascal's hexagon theorem

Six homogeneous conic equations make a Veronese matrix singular. A polynomial determinant identity then proves collinearity of the opposite-side intersections. The nonsingular symmetric-matrix conic formulation implies the nonzero quadratic-form version. The homogeneous statement requires no distinctness assumption.

The Lean proof in [HOLLightPort.Pascal](vendor/hol-light-port/HOLLightPort/Pascal.lean) manually adapts John Harrison and contributors' [HOL Light Pascal argument](https://github.com/jrh13/hol-light/blob/cba9198db76e9dfb89cbd653df9412d01f65b22a/100/pascal.ml). The original source is retained byte-for-byte in [pascal.ml.txt](vendor/hol-light-port/upstream/pascal.ml.txt).

## Desargues's theorem

Homogeneous coordinates over an arbitrary field and a determinant identity turn concurrency of corresponding vertex lines into a nonzero common line through the corresponding side intersections. A second argument proves the converse for noncollinear triangles. Nonzero representatives and intersections give the usual interpretation in projective points.

[HOLLightPort.Desargues](vendor/hol-light-port/HOLLightPort/Desargues.lean) manually adapts John Harrison and contributors' [HOL Light Desargues argument](https://github.com/jrh13/hol-light/blob/cba9198db76e9dfb89cbd653df9412d01f65b22a/100/desargues.ml). The original source is retained byte-for-byte in [desargues.ml.txt](vendor/hol-light-port/upstream/desargues.ml.txt).

Both translations use HOL Light revision `cba9198db76e9dfb89cbd653df9412d01f65b22a`. The BSD-2-Clause copyright and license are preserved in [vendor/hol-light-port/LICENSE](vendor/hol-light-port/LICENSE) and source headers; [upstream.json](vendor/hol-light-port/upstream.json) records provenance and hashes. Lean checks the determinant identities and proof terms anew. No HOL proof objects are imported, and there is no general automatic translator.
