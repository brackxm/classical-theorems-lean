import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.FanVertice

/-!
FASE 3A — SCARICO DI `EdgeInAtMostTwoFacets` (18 lug 2026).

Il predicato locale assunto dal gemello KG-3A2 vale INCONDIZIONATAMENTE:
è esattamente la forma quantificata del diamante.
-/

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **Il lemma locale del fan è un teorema**: in ogni politopo di ℝ³, per
ogni punto `v`, uno spigolo sta in al più due faccette. -/
theorem edgeInAtMostTwoFacets_vale (P : ConvexPolytope 3) (v : E 3) :
    ConvexPolytope.EdgeInAtMostTwoFacets P v := by
  intro A B C hA hdA hB hdB hC hdC hAB hvA hvB hvC x hx hxv hxC
  exact spigolo_in_due_faccette P v hA hdA hB hdB hC hdC hAB hvA hvB hvC
    hx hxv hxC

end LeanEval.Geometry.PlatonicClassification
