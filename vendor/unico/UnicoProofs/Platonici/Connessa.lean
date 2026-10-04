import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FacceConnesse
import UnicoProofs.Platonici.Coincidenza
import UnicoProofs.Platonici.Balinski

/-!
RIGIDITÀ — LA FALLA 10 È CHIUSA (19 lug 2026).

Con `balinski_light` (sol, fascicolo 23) le ipotesi di connettività dei
grafi dei vertici si scaricano: la connettività GLOBALE delle faccette
diventa incondizionata, e la coincidenza per propagazione pende dalla
sola CHIUSURA PER ADIACENZA (gate 4-5). È la riparazione completa della
falla che avevo io stesso introdotto nel fascicolo del vaglio, dando per
certificata una connettività che era solo locale.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **CONNETTIVITÀ GLOBALE DELLE FACCETTE, INCONDIZIONATA**. -/
theorem faccette_connesse (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {A B : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2) :
    Relation.ReflTransGen (FaccetteAdiacenti P) A B :=
  faccette_connesse_globale P hfull (balinski_light P hfull) hA hdA hB hdB

/-- **COINCIDENZA PER PROPAGAZIONE**: ora pende dalla sola chiusura per
adiacenza delle faccette comuni (gate 4-5 del vaglio). -/
theorem coincidenza_da_chiusura (P Q : ConvexPolytope 3)
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    (hchiusoP : ∀ A, FaccettaComune P Q A →
      ∀ B, FaccetteAdiacenti P A B → FaccettaComune P Q B)
    (hchiusoQ : ∀ A, FaccettaComune P Q A →
      ∀ B, FaccetteAdiacenti Q A B → FaccettaComune P Q B)
    (A₀ : Set (E 3)) (hA₀ : FaccettaComune P Q A₀) :
    P.toSet = Q.toSet :=
  coincidenza_condizionale P Q hfullP hfullQ
    (balinski_light P hfullP) (balinski_light Q hfullQ)
    hchiusoP hchiusoQ A₀ hA₀

end LeanEval.Geometry.PlatonicClassification
