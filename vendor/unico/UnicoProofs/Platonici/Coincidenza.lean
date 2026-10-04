import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FacceConnesse
import UnicoProofs.Platonici.VerticiFaccette

/-!
RIGIDITÀ — LO SCHELETRO DELL'INDUZIONE PER COINCIDENZA (R′4 + R′5).

Il teorema di montaggio del piano R′: se due politopi full-dimensional
hanno una faccetta in comune, e l'insieme delle faccette comuni è chiuso
per adiacenza nei DUE grafi (il passo del diamante, gate 4-5), e i due
grafi dei vertici sono connessi (Balinski-light), allora i due politopi
COINCIDONO come insiemi. La chiusura simmetrica del vaglio è qui: il
cammino si fa sia nel grafo di P sia in quello di Q, così le faccette di
ciascuno risultano faccette dell'altro, e `toSet_eq_of_faccette_eq`
conclude. Le tre ipotesi condizionali (Balinski per i due lati e il passo
di chiusura) sono i gate che il resto della campagna scarica.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Una faccetta comune ai due politopi. -/
def FaccettaComune (P Q : ConvexPolytope 3) (A : Set (E 3)) : Prop :=
  (P.IsFace A ∧ faceDim A = 2) ∧ (Q.IsFace A ∧ faceDim A = 2)

/-- **COINCIDENZA PER PROPAGAZIONE**: faccetta comune di partenza,
chiusura per adiacenza nei due versi, Balinski nei due grafi ⟹ i due
politopi sono lo stesso insieme. -/
theorem coincidenza_condizionale (P Q : ConvexPolytope 3)
    (hfullP : P.IsFullDim) (hfullQ : Q.IsFullDim)
    (hbalP : ∀ u ∈ P.vertices, ∀ w ∈ P.vertices,
      Relation.ReflTransGen (AdiacentiVertici P) u w)
    (hbalQ : ∀ u ∈ Q.vertices, ∀ w ∈ Q.vertices,
      Relation.ReflTransGen (AdiacentiVertici Q) u w)
    (hchiusoP : ∀ A, FaccettaComune P Q A →
      ∀ B, FaccetteAdiacenti P A B → FaccettaComune P Q B)
    (hchiusoQ : ∀ A, FaccettaComune P Q A →
      ∀ B, FaccetteAdiacenti Q A B → FaccettaComune P Q B)
    (A₀ : Set (E 3)) (hA₀ : FaccettaComune P Q A₀) :
    P.toSet = Q.toSet := by
  apply toSet_eq_of_faccette_eq P Q hfullP hfullQ
  intro A
  constructor
  · rintro ⟨hA, hdA⟩
    have hpath := faccette_connesse_globale P hfullP hbalP
      hA₀.1.1 hA₀.1.2 hA hdA
    have hmem : A ∈ {X : Set (E 3) | FaccettaComune P Q X} :=
      induzione_coincidenza (S := {X | FaccettaComune P Q X})
        (fun X hX B hXB => hchiusoP X hX B hXB) hA₀ hpath
    exact hmem.2
  · rintro ⟨hA, hdA⟩
    have hpath := faccette_connesse_globale Q hfullQ hbalQ
      hA₀.2.1 hA₀.2.2 hA hdA
    have hmem : A ∈ {X : Set (E 3) | FaccettaComune P Q X} :=
      induzione_coincidenza (S := {X | FaccettaComune P Q X})
        (fun X hX B hXB => hchiusoQ X hX B hXB) hA₀ hpath
    exact hmem.1

end LeanEval.Geometry.PlatonicClassification
