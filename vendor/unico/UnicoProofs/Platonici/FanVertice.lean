import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.Fondamenta
import UnicoProofs.Platonici.PerturbazioneFinita

/-!
# KG-3A2: il fan al vertice dalla flag-transitivita

Versione condizionale ammessa dal fascicolo 14.  La simmetria `σ` non e'
postulata: viene estratta da `IsRegular` applicata alle bandiere `F` e `G`.
Le faccette vengono poi *definite* come l'orbita della faccetta di `F`.

Restano espliciti due input del cantiere delle facce:

* `FanOrbitCertificate`: l'orbita scelta chiude esattamente dopo `q` passi,
  e' semplice, e comprende tutte le faccette per `v`;
* `EdgeInAtMostTwoFacets`: il lemma geometrico locale che un punto interno a
  uno spigolo di due faccette non appartiene a una terza faccetta.

Le bandiere `L` e `R` certificano che le prime due faccette dell'orbita
condividono davvero uno spigolo per `v`.  L'esistenza di queste bandiere e dei
certificati e' precisamente il cantiere Q1; Q0 e' importato dal modulo
kernel-certificato `PerturbazioneFinita`.
-/

open Set
open scoped Topology RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification
namespace ConvexPolytope

/-- Il contratto benchmark visto come il politopo astratto usato dal predicato
locale.  I campi coincidono definizionalmente. -/
def asFinite {n : ℕ} (P : ConvexPolytope n) : FiniteConvexPolytope (E n) where
  vertices := P.vertices
  nonempty := P.vertices_nonempty
  vertices_eq_extremePoints := P.vertices_eq_extremePoints

@[simp] theorem asFinite_toSet {n : ℕ} (P : ConvexPolytope n) :
    P.asFinite.toSet = P.toSet := rfl

@[simp] theorem asFinite_isFacet_iff (P : ConvexPolytope 3) (A : Set (E 3)) :
    P.asFinite.IsFacet A ↔ P.IsFace A ∧ faceDim A = 2 := Iff.rfl

/-- La `k`-esima immagine di una faccetta di bandiera. -/
def iteratedFacet {P : ConvexPolytope 3} (σ : Isom 3) (F : P.Flag) (k : ℕ) :
    Set (E 3) :=
  ((σ : E 3 → E 3)^[k]) '' F.face 2

/-- L'orbita finita, indicizzata da `Fin q`, della faccetta di `F`. -/
def facetOrbit {P : ConvexPolytope 3} {q : ℕ} (σ : Isom 3) (F : P.Flag)
    (i : Fin q) : Set (E 3) :=
  iteratedFacet σ F i.val

@[simp] theorem iteratedFacet_zero {P : ConvexPolytope 3} (σ : Isom 3)
    (F : P.Flag) : iteratedFacet σ F 0 = F.face 2 := by
  simp [iteratedFacet]

theorem image_iteratedFacet {P : ConvexPolytope 3} (σ : Isom 3) (F : P.Flag)
    (k : ℕ) :
    (σ : E 3 → E 3) '' iteratedFacet σ F k = iteratedFacet σ F (k + 1) := by
  rw [iteratedFacet, iteratedFacet, Set.image_image]
  congr 1
  funext x
  exact (Function.iterate_succ_apply' (σ : E 3 → E 3) k x).symm

/-- Dati finiti/combinatori dell'orbita.  La legge di rotazione non e' un
campo: verra' dedotta dagli iterati e da `period`. -/
structure FanOrbitCertificate (P : ConvexPolytope 3) (v : E 3) (q : ℕ)
    (F : P.Flag) (σ : Isom 3) : Prop where
  period : iteratedFacet σ F q = F.face 2
  isFacet : ∀ i : Fin q,
    P.IsFace (facetOrbit σ F i) ∧ faceDim (facetOrbit σ F i) = 2
  injective : Function.Injective (fun i : Fin q => facetOrbit σ F i)
  complete : ∀ A : Set (E 3), P.IsFace A → faceDim A = 2 → v ∈ A →
    ∃ i : Fin q, A = facetOrbit σ F i

/-- Forma generale del solo lemma di intersezione ammesso dal fascicolo:
una terza faccetta per `v` che contiene un punto non terminale dello spigolo
comune di `A` e `B` coincide con `A` oppure con `B`. -/
def EdgeInAtMostTwoFacets (P : ConvexPolytope 3) (v : E 3) : Prop :=
  ∀ ⦃A B C : Set (E 3)⦄,
    P.IsFace A → faceDim A = 2 →
    P.IsFace B → faceDim B = 2 →
    P.IsFace C → faceDim C = 2 →
    A ≠ B → v ∈ A → v ∈ B → v ∈ C →
    ∀ ⦃x : E 3⦄, x ∈ A ∩ B → x ≠ v → x ∈ C → C = A ∨ C = B

theorem finRotate_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finRotate q i ≠ i := by
  cases q with
  | zero => omega
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        intro h
        have hv := congrArg Fin.val h
        simp only [finRotate_last, Fin.val_zero, Fin.val_last] at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        rw [coe_finRotate_of_ne_last hi] at hv
        omega

/-- Un'orbita chiusa al passo `q` e' ruotata da `σ` secondo `finRotate`. -/
theorem facetOrbit_ruota {P : ConvexPolytope 3} {q : ℕ} (hq : 1 ≤ q)
    (σ : Isom 3) (F : P.Flag) (hperiod : iteratedFacet σ F q = F.face 2)
    (i : Fin q) :
    (σ : E 3 → E 3) '' facetOrbit σ F i =
      facetOrbit σ F (finRotate q i) := by
  cases q with
  | zero => omega
  | succ n =>
      by_cases hi : i = Fin.last n
      · subst i
        rw [facetOrbit, facetOrbit, finRotate_last, Fin.val_last, Fin.val_zero]
        rw [image_iteratedFacet]
        simpa using hperiod
      · rw [facetOrbit, facetOrbit, image_iteratedFacet]
        congr 1
        exact (coe_finRotate_of_ne_last hi).symm

/-!
`horbit` e' deliberatamente quantificato su ogni trasportatore di bandiere:
`IsRegular` sceglie esistenzialmente `σ`, e il certificato Q1 deve potersi
applicare alla scelta prodotta dal kernel senza un operatore di scelta esterno.
-/

/-- **KG-3A2, versione condizionale.** Dalla flag-transitivita', da due
bandiere che selezionano il passo del fan, dalle bandiere dello spigolo base e
dai due lemmi locali Q1, si ottengono esattamente i dati del predicato
`CyclicVertexData`, incluso `spigolo_due`. -/
theorem fan_vertice_condizionale (P : ConvexPolytope 3) (h : P.IsRegular)
    {v : E 3} {q : ℕ} (hq : 3 ≤ q)
    (F G L R : P.Flag)
    (hF0 : F.face 0 = {v}) (hG0 : G.face 0 = {v})
    (hL0 : L.face 0 = {v})
    (hLF : L.face 2 = F.face 2) (hRG : R.face 2 = G.face 2)
    (hLR : L.face 1 = R.face 1)
    (horbit : ∀ σ : Isom 3, P.isSymmetry σ →
      (∀ k : Fin 3, (σ : E 3 → E 3) '' F.face k = G.face k) →
      FanOrbitCertificate P v q F σ)
    (hedge_two : EdgeInAtMostTwoFacets P v) :
    Nonempty (P.asFinite.CyclicVertexData v q) := by
  obtain ⟨σ, hσP, hσflag⟩ := h.2 F G
  have C : FanOrbitCertificate P v q F σ := horbit σ hσP hσflag

  have hσv : σ v = v := by
    have hv : σ v ∈ (σ : E 3 → E 3) '' F.face 0 := by
      exact ⟨v, by simp [hF0], rfl⟩
    rw [hσflag 0, hG0] at hv
    simpa using hv

  have hvF : v ∈ F.face 2 := by
    apply (F.strict_mono 0 2 (by decide)).1
    simp [hF0]

  have hmem : ∀ i : Fin q, v ∈ facetOrbit σ F i := by
    intro i
    refine ⟨v, hvF, ?_⟩
    exact (show Function.IsFixedPt (σ : E 3 → E 3) v from hσv).iterate i.val

  have hruota : ∀ i : Fin q,
      (σ : E 3 → E 3) '' facetOrbit σ F i =
        facetOrbit σ F (finRotate q i) :=
    facetOrbit_ruota (by omega) σ F C.period

  have hbase : ∃ x : E 3,
      x ≠ v ∧ x ∈ F.face 2 ∩ G.face 2 := by
    have hss : L.face 0 ⊂ L.face 1 := L.strict_mono 0 1 (by decide)
    obtain ⟨x, hxL1, hxL0⟩ := Set.exists_of_ssubset hss
    have hxne : x ≠ v := by
      intro hxv
      apply hxL0
      simp [hL0, hxv]
    have hxF : x ∈ F.face 2 := by
      rw [← hLF]
      exact (L.strict_mono 1 2 (by decide)).1 hxL1
    have hxR1 : x ∈ R.face 1 := by
      rw [← hLR]
      exact hxL1
    have hxG : x ∈ G.face 2 := by
      rw [← hRG]
      exact (R.strict_mono 1 2 (by decide)).1 hxR1
    exact ⟨x, hxne, hxF, hxG⟩
  obtain ⟨x₀, hx₀v, hx₀F, hx₀G⟩ := hbase

  refine ⟨{
    faccetta := facetOrbit σ F
    isFacet := ?_
    mem_v := hmem
    distinte := C.injective
    complete := ?_
    σ := σ
    fissa_v := hσv
    preserva := ?_
    ruota := hruota
    spigolo := ?_
    spigolo_due := ?_
  }⟩
  · intro i
    exact (asFinite_isFacet_iff P _).2 (C.isFacet i)
  · intro A hA hvA
    exact C.complete A hA.1 hA.2 hvA
  · simpa [ConvexPolytope.isSymmetry] using hσP
  · intro i
    let xᵢ : E 3 := ((σ : E 3 → E 3)^[i.val]) x₀
    have hxᵢ_this : xᵢ ∈ facetOrbit σ F i := by
      exact ⟨x₀, hx₀F, rfl⟩
    have hx₀image : x₀ ∈ (σ : E 3 → E 3) '' F.face 2 := by
      rw [hσflag 2]
      exact hx₀G
    obtain ⟨y, hyF, hσy⟩ := hx₀image
    have hxᵢ_image : xᵢ ∈ (σ : E 3 → E 3) '' facetOrbit σ F i := by
      refine ⟨((σ : E 3 → E 3)^[i.val]) y, ⟨y, hyF, rfl⟩, ?_⟩
      dsimp [xᵢ]
      rw [← hσy]
      exact (Function.iterate_succ_apply' (σ : E 3 → E 3) i.val y).symm.trans
        (Function.iterate_succ_apply (σ : E 3 → E 3) i.val y)
    have hxᵢ_next : xᵢ ∈ facetOrbit σ F (finRotate q i) := by
      rw [← hruota i]
      exact hxᵢ_image
    have hxᵢv : xᵢ ≠ v := by
      intro heq
      apply hx₀v
      apply (σ.injective.iterate i.val)
      rw [(show Function.IsFixedPt (σ : E 3 → E 3) v from hσv).iterate i.val]
      exact heq
    exact ⟨xᵢ, hxᵢv, hxᵢ_this, hxᵢ_next⟩
  · intro i j x hxedge hxv hxj
    have hne : facetOrbit σ F i ≠ facetOrbit σ F (finRotate q i) := by
      intro heq
      have := C.injective heq
      exact (finRotate_ne_self (by omega) i) this.symm
    rcases hedge_two (C.isFacet i).1 (C.isFacet i).2
        (C.isFacet (finRotate q i)).1 (C.isFacet (finRotate q i)).2
        (C.isFacet j).1 (C.isFacet j).2 hne (hmem i)
        (hmem (finRotate q i)) (hmem j) hxedge hxv hxj with hj | hj
    · exact Or.inl (C.injective hj)
    · exact Or.inr (C.injective hj)

end ConvexPolytope
end LeanEval.Geometry.PlatonicClassification

/-!
CONSEGNA

File: `FanVertice.lean`
Teorema:
`LeanEval.Geometry.PlatonicClassification.ConvexPolytope.fan_vertice_condizionale`

Forma: KG-3A2 condizionale.  Ipotesi residue dichiarate:

1. quattro bandiere `F,G,L,R`; `F -> G` seleziona il passo della simmetria,
   mentre `L,R` attraversano lo spigolo comune delle prime due faccette;
2. `FanOrbitCertificate`: periodo esatto indicizzato, faccette dell'orbita,
   iniettivita' e completezza al vertice;
3. `EdgeInAtMostTwoFacets`: il lemma generale d'intersezione di tre faccette
   esplicitamente autorizzato dal fascicolo.

Non sono assunte ne' una simmetria `σ`, ne' la legge `ruota`, ne' i testimoni
`spigolo`, ne' `spigolo_due` nella forma indicizzata del risultato.  `σ` viene
da `IsRegular`; `ruota` dagli iterati e dal periodo; `spigolo` dalle bandiere;
`spigolo_due` dal lemma generale e dall'iniettivita' dell'orbita.

Certificazione: dimostrazione kernel pura; nessun `sorry`, `axiom` o
`native_decide`.
SHA-256 del contenuto Lean (righe 1-245, fino a
`end LeanEval.Geometry.PlatonicClassification` incluso):
`218eaee67fcd61e740d59afbc04800c1737a57554e4a7d65b3c6d72e71510236`.
Compilazione dalla radice di `/Volumes/DATIAI/UNICO_LEAN/unico`:
`lake env lean /Users/solarys/.claude/jobs/b3950245/tmp/sol_workdir14/FanVertice.lean`,
exit code 0, nessun errore e nessun warning (Lean 4.32.0-rc1).
-/
