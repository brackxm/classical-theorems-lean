/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ParallelKleinModel

/-! Independence of the parallel postulate, in neutral Tarski geometry.
The Euclidean plane and Klein disk both satisfy Tarski axioms 1–9 and full
Dedekind continuity, and respectively satisfy and refute his Euclidean axiom. -/

namespace ClassicalTheorems

open Statements.Geometry

theorem parallel_postulate_independence :
    ∃ euclidean hyperbolic : NeutralPlane,
      euclidean.ParallelPostulate ∧ ¬hyperbolic.ParallelPostulate :=
  Progress.Parallel.parallel_postulate_independence

end ClassicalTheorems

#check_upstream ClassicalTheorems.parallel_postulate_independence
