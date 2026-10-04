import Mathlib

/-!
CAMPAGNA #50 — MODULO DEFINIZIONI (disegno del gate cieco, 17 lug 2026).

Le nozioni su cui vive il teorema `cyclicallyRegular_schlafli`:

* `FiniteConvexPolytope A` — hull convesso di un insieme finito i cui vertici
  dichiarati sono ESATTAMENTE i punti estremi (lo stesso patto del benchmark
  lean-eval, ma su spazio astratto A: si vincola l'oggetto, non l'ambiente).
* `IsFace` / `IsFacet` — facce esposte non vuote; faccette = facce di span 2D.
* `IsRegularFacet` — poligono regolare PER ORBITA di una rotazione: niente
  liste di angoli postulategli dentro (la riparazione anti-trappola del gate).
  La congruenza dei lati consecutivi è GRATIS dall'isometria.
* `CyclicVertexData` / `IsCyclicVertex` — il fan di q faccette attorno a un
  vertice, permutato ciclicamente da un'isometria che fissa il vertice e
  preserva il politopo.
* `IsCyclicallyRegularOfType` — il predicato del teorema di classificazione.

La disuguaglianza angolare NON compare in alcuna definizione: è il TEOREMA
(kill-gate `spike_somma_sotto_due_pi`, già kernel-certificato al giorno zero).
-/

open Set Metric
open scoped RealInnerProductSpace

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Un politopo convesso su uno spazio con prodotto interno reale: hull convesso
di un insieme finito non vuoto di punti, i cui vertici dichiarati sono
esattamente i punti estremi dell'hull. -/
structure FiniteConvexPolytope (A : Type*) [NormedAddCommGroup A]
    [InnerProductSpace ℝ A] where
  vertices : Finset A
  nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set A) = (convexHull ℝ (vertices : Set A)).extremePoints ℝ

namespace FiniteConvexPolytope

variable (P : FiniteConvexPolytope A)

/-- Il corpo convesso del politopo. -/
def toSet : Set A := convexHull ℝ (P.vertices : Set A)

/-- Una faccia: sottoinsieme esposto e non vuoto del corpo. -/
def IsFace (F : Set A) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- Una faccetta: faccia il cui span direzionale è un piano. -/
def IsFacet (F : Set A) : Prop :=
  P.IsFace F ∧ Module.finrank ℝ (vectorSpan ℝ F) = 2

/-- Faccetta p-gonale REGOLARE, definita per orbita: esiste un'isometria affine
ρ che manda la faccetta in sé, il cui ciclo su un vertice di partenza ha
esattamente p punti distinti, chiude dopo p passi, genera la faccetta come hull
convesso, e ha passo di lunghezza ℓ. La congruenza di TUTTI i lati consecutivi
segue gratis dall'isometria; nessun angolo è postulato. -/
def IsRegularFacet (F : Set A) (p : ℕ) (ℓ : ℝ) : Prop :=
  P.IsFacet F ∧ 0 < ℓ ∧ 3 ≤ p ∧
  ∃ (ρ : A ≃ᵃⁱ[ℝ] A) (x₀ : A),
    x₀ ∈ F ∧
    (⇑ρ) '' F = F ∧
    Function.Injective (fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) ∧
    (⇑ρ)^[p] x₀ = x₀ ∧
    F = convexHull ℝ (Set.range fun i : Fin p => (⇑ρ)^[(i : ℕ)] x₀) ∧
    dist x₀ (ρ x₀) = ℓ

/-- I dati di un vertice q-ciclico: le faccette incidenti a v enumerate da
`Fin q`, un'isometria σ che fissa v, preserva il politopo e ruota il fan di un
passo, e la completezza locale del fan (faccette consecutive condividono uno
spigolo per v: il loro incontro contiene v e un punto ulteriore). -/
structure CyclicVertexData (v : A) (q : ℕ) where
  /-- l'enumerazione ciclica delle faccette incidenti a v -/
  faccetta : Fin q → Set A
  isFacet : ∀ i, P.IsFacet (faccetta i)
  mem_v : ∀ i, v ∈ faccetta i
  distinte : Function.Injective faccetta
  complete : ∀ F : Set A, P.IsFacet F → v ∈ F → ∃ i, F = faccetta i
  /-- la simmetria ciclica locale -/
  σ : A ≃ᵃⁱ[ℝ] A
  fissa_v : σ v = v
  preserva : (⇑σ) '' P.toSet = P.toSet
  ruota : ∀ i : Fin q, (⇑σ) '' faccetta i = faccetta (finRotate q i)
  /-- faccette consecutive si toccano in uno spigolo per v, non solo in v -/
  spigolo : ∀ i : Fin q,
    ∃ x, x ≠ v ∧ x ∈ faccetta i ∩ faccetta (finRotate q i)
  /-- struttura di fan (pseudovarietà): un punto di spigolo diverso da v
  appartiene SOLO alle due faccette che quello spigolo condividono. Nessun
  angolo, nessun conteggio: è la proprietà «ogni spigolo ha due facce». -/
  spigolo_due : ∀ i j : Fin q, ∀ x,
    x ∈ faccetta i ∩ faccetta (finRotate q i) → x ≠ v →
    x ∈ faccetta j → j = i ∨ j = finRotate q i

/-- Vertice q-ciclico (forma proposizionale). -/
def IsCyclicVertex (v : A) (q : ℕ) : Prop :=
  Nonempty (P.CyclicVertexData v q)

/-- Il predicato del teorema di classificazione: politopo 3-dimensionale con
faccette p-gonali regolari di lato comune ℓ e ogni vertice q-ciclico. -/
def IsCyclicallyRegularOfType (p q : ℕ) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ (P.vertices : Set A)) = 3 ∧
  3 ≤ p ∧ 3 ≤ q ∧
  ∃ ℓ > 0,
    (∀ F, P.IsFacet F → P.IsRegularFacet F p ℓ) ∧
    (∀ v ∈ P.vertices, P.IsCyclicVertex v q)

end FiniteConvexPolytope

/-- Due faccette distinte passanti per un punto estremo si incontrano, da quel
punto, lungo un'unica semiretta: due loro punti non estremi hanno vettori
radiali positivamente proporzionali. -/
theorem intersezione_spigolo_semiretta (P : FiniteConvexPolytope A)
    {F G : Set A} (hF : P.IsFacet F) (hG : P.IsFacet G) (hFG : F ≠ G)
    {v : A} (hvF : v ∈ F) (hvG : v ∈ G)
    (hvex : v ∈ P.toSet.extremePoints ℝ)
    {x y : A} (hx : x ∈ F ∩ G) (hy : y ∈ F ∩ G) (hxv : x ≠ v) (hyv : y ≠ v) :
    ∃ c : ℝ, 0 < c ∧ y - v = c • (x - v) := by
  have hvI : v ∈ F ∩ G := ⟨hvF, hvG⟩
  have hxsub : x - v ≠ 0 := sub_ne_zero.mpr hxv
  have hdep : ¬LinearIndependent ℝ ![x - v, y - v] := by
    intro hli
    let S : Submodule ℝ A := vectorSpan ℝ (F ∩ G)
    have hSF : S ≤ vectorSpan ℝ F := vectorSpan_mono ℝ inter_subset_left
    have hxS : x - v ∈ S := vsub_mem_vectorSpan ℝ hx hvI
    have hyS : y - v ∈ S := vsub_mem_vectorSpan ℝ hy hvI
    have hSfin : FiniteDimensional ℝ S := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ F) :=
        FiniteDimensional.of_finrank_pos (by rw [hF.2]; norm_num)
      exact FiniteDimensional.of_injective (Submodule.inclusion hSF)
        (Submodule.inclusion_injective hSF)
    letI : FiniteDimensional ℝ S := hSfin
    let b : Fin 2 → S := ![⟨x - v, hxS⟩, ⟨y - v, hyS⟩]
    have hlib : LinearIndependent ℝ b := by
      apply LinearIndependent.of_comp S.subtype
      have hb : S.subtype ∘ b = ![x - v, y - v] := by
        funext k
        fin_cases k <;> rfl
      rw [hb]
      exact hli
    have hSge : 2 ≤ Module.finrank ℝ S := by
      simpa using hlib.fintype_card_le_finrank
    have hSle : Module.finrank ℝ S ≤ 2 := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ F) :=
        FiniteDimensional.of_finrank_pos (by rw [hF.2]; norm_num)
      simpa [hF.2] using Submodule.finrank_mono hSF
    have hSrank : Module.finrank ℝ S = 2 := le_antisymm hSle hSge
    have hspanF : vectorSpan ℝ (F ∩ G) = vectorSpan ℝ F := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ F) :=
        FiniteDimensional.of_finrank_pos (by rw [hF.2]; norm_num)
      exact Submodule.eq_of_le_of_finrank_eq hSF (hSrank.trans hF.2.symm)
    have hSG : S ≤ vectorSpan ℝ G := vectorSpan_mono ℝ inter_subset_right
    have hspanG : vectorSpan ℝ (F ∩ G) = vectorSpan ℝ G := by
      letI : FiniteDimensional ℝ (vectorSpan ℝ G) :=
        FiniteDimensional.of_finrank_pos (by rw [hG.2]; norm_num)
      exact Submodule.eq_of_le_of_finrank_eq hSG (hSrank.trans hG.2.symm)
    have haffF : affineSpan ℝ (F ∩ G) = affineSpan ℝ F := by
      apply AffineSubspace.ext_of_direction_eq
      · simpa only [direction_affineSpan] using hspanF
      · exact ⟨v, mem_affineSpan ℝ hvI, mem_affineSpan ℝ hvF⟩
    have haffG : affineSpan ℝ (F ∩ G) = affineSpan ℝ G := by
      apply AffineSubspace.ext_of_direction_eq
      · simpa only [direction_affineSpan] using hspanG
      · exact ⟨v, mem_affineSpan ℝ hvI, mem_affineSpan ℝ hvG⟩
    have hFGsub : F ⊆ G := by
      obtain ⟨l, hGl⟩ := hG.1.1 ⟨v, hvG⟩
      have hvmax := hvG
      rw [hGl] at hvmax
      let H : AffineSubspace ℝ A := AffineSubspace.mk' v l.ker
      have hIH : affineSpan ℝ (F ∩ G) ≤ H := by
        apply affineSpan_le.2
        intro z hz
        have hzmax := hz.2
        rw [hGl] at hzmax
        have hlz : l z = l v := le_antisymm (hvmax.2 z hzmax.1) (hzmax.2 v hvmax.1)
        change z - v ∈ l.ker
        change l (z - v) = 0
        rw [map_sub, hlz, sub_self]
      intro z hzF
      have hzH : z ∈ H := hIH (haffF.symm ▸ mem_affineSpan ℝ hzF)
      have hlz : l z = l v := by
        change z - v ∈ l.ker at hzH
        change l (z - v) = 0 at hzH
        rwa [map_sub, sub_eq_zero] at hzH
      rw [hGl]
      exact ⟨hF.1.1.subset hzF, fun w hw => (hvmax.2 w hw).trans_eq hlz.symm⟩
    have hGFsub : G ⊆ F := by
      obtain ⟨l, hFl⟩ := hF.1.1 ⟨v, hvF⟩
      have hvmax := hvF
      rw [hFl] at hvmax
      let H : AffineSubspace ℝ A := AffineSubspace.mk' v l.ker
      have hIH : affineSpan ℝ (F ∩ G) ≤ H := by
        apply affineSpan_le.2
        intro z hz
        have hzmax := hz.1
        rw [hFl] at hzmax
        have hlz : l z = l v := le_antisymm (hvmax.2 z hzmax.1) (hzmax.2 v hvmax.1)
        change z - v ∈ l.ker
        change l (z - v) = 0
        rw [map_sub, hlz, sub_self]
      intro z hzG
      have hzH : z ∈ H := hIH (haffG.symm ▸ mem_affineSpan ℝ hzG)
      have hlz : l z = l v := by
        change z - v ∈ l.ker at hzH
        change l (z - v) = 0 at hzH
        rwa [map_sub, sub_eq_zero] at hzH
      rw [hFl]
      exact ⟨hG.1.1.subset hzG, fun w hw => (hvmax.2 w hw).trans_eq hlz.symm⟩
    exact hFG (Set.Subset.antisymm hFGsub hGFsub)
  rw [LinearIndependent.pair_iff' hxsub] at hdep
  push Not at hdep
  obtain ⟨c, hc⟩ := hdep
  have hrel : y - v = c • (x - v) := hc.symm
  have hc0 : c ≠ 0 := by
    intro hczero
    apply hyv
    apply sub_eq_zero.mp
    rw [hrel, hczero, zero_smul]
  have hc_nonneg : 0 ≤ c := by
    by_contra hcn
    have hcneg : c < 0 := lt_of_not_ge hcn
    have hden : 1 - c ≠ 0 := by linarith
    have htpos : 0 < (1 - c)⁻¹ := inv_pos.mpr (by linarith)
    have htlt : (1 - c)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    have hscalar : (1 - c)⁻¹ * (c - 1) + 1 = 0 := by
      field_simp [hden]
      ring
    have hline : AffineMap.lineMap x y ((1 - c)⁻¹ : ℝ) = v := by
      apply sub_eq_zero.mp
      calc
        AffineMap.lineMap x y ((1 - c)⁻¹ : ℝ) - v =
            (1 - c)⁻¹ • (y - x) + x - v := by rw [AffineMap.lineMap_apply_module']
        _ = (1 - c)⁻¹ • ((y - v) - (x - v)) + (x - v) := by module
        _ = (1 - c)⁻¹ • (c • (x - v) - (x - v)) + (x - v) := by rw [hrel]
        _ = ((1 - c)⁻¹ * (c - 1) + 1) • (x - v) := by module
        _ = 0 := by rw [hscalar, zero_smul]
    have hvopen : v ∈ openSegment ℝ x y := by
      rw [← hline]
      exact lineMap_mem_openSegment ℝ x y ⟨htpos, htlt⟩
    have hxP : x ∈ P.toSet := hF.1.1.subset hx.1
    have hyP : y ∈ P.toSet := hF.1.1.subset hy.1
    exact hxv ((mem_extremePoints.mp hvex).2 x hxP y hyP hvopen).1
  exact ⟨c, lt_of_le_of_ne hc_nonneg (Ne.symm hc0), hrel⟩

/-- La simmetria ciclica manda lo spigolo fra due faccette consecutive nello
spigolo successivo del fan. -/
theorem spigolo_trasportato (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    (⇑D.σ) '' (D.faccetta i ∩ D.faccetta (finRotate q i)) =
      D.faccetta (finRotate q i) ∩ D.faccetta (finRotate q (finRotate q i)) := by
  rw [Set.image_inter D.σ.injective, D.ruota i, D.ruota (finRotate q i)]

/-- Il trasporto ciclico di un punto non vertice dello spigolo resta sullo
spigolo successivo, resta distinto dal vertice e conserva la distanza da esso. -/
theorem punto_spigolo_trasportato (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) {x : A} :
    x ∈ D.faccetta i ∩ D.faccetta (finRotate q i) → x ≠ v →
      D.σ x ∈ D.faccetta (finRotate q i) ∩
          D.faccetta (finRotate q (finRotate q i)) ∧
        D.σ x ≠ v ∧ ‖D.σ x - v‖ = ‖x - v‖ := by
  intro hx hxv
  have hmem : D.σ x ∈ (⇑D.σ) ''
      (D.faccetta i ∩ D.faccetta (finRotate q i)) := ⟨x, hx, rfl⟩
  rw [spigolo_trasportato P D i] at hmem
  refine ⟨hmem, ?_, ?_⟩
  · simpa [D.fissa_v] using D.σ.injective.ne hxv
  · calc
      ‖D.σ x - v‖ = dist (D.σ x) v := (dist_eq_norm _ _).symm
      _ = dist (D.σ x) (D.σ v) := by rw [D.fissa_v]
      _ = dist x v := D.σ.dist_map x v
      _ = ‖x - v‖ := dist_eq_norm _ _

/-- Una faccetta ammette un funzionale di supporto costante su di essa e
strettamente minore su ogni punto non vertice degli spigoli che non le
appartengono. L'esclusione è scritta come `j ≠ i` e `finRotate q j ≠ i`, cioè
nega precisamente i due modi in cui lo spigolo `j` può appartenere alla
faccetta `i`. -/
theorem funzionale_faccetta (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    ∃ l : A →L[ℝ] ℝ,
      (∀ x ∈ D.faccetta i, l x = l v) ∧
      (∀ j : Fin q, j ≠ i → finRotate q j ≠ i →
        ∀ x, x ∈ D.faccetta j ∩ D.faccetta (finRotate q j) → x ≠ v →
          l x < l v) := by
  obtain ⟨l, hil⟩ := (D.isFacet i).1.1 ⟨v, D.mem_v i⟩
  have hvmax := D.mem_v i
  rw [hil] at hvmax
  refine ⟨l, ?_, ?_⟩
  · intro x hxi
    have hxmax := hxi
    rw [hil] at hxmax
    exact le_antisymm (hvmax.2 x hxmax.1) (hxmax.2 v hvmax.1)
  · intro j hji hrji x hxedge hxv
    have hxnoti : x ∉ D.faccetta i := by
      intro hxi
      rcases D.spigolo_due j i x hxedge hxv hxi with h | h
      · exact hji h.symm
      · exact hrji h.symm
    have hxP : x ∈ P.toSet := (D.isFacet j).1.1.subset hxedge.1
    have hxnotmax : ¬∀ w ∈ P.toSet, l w ≤ l x := by
      intro hxmax
      apply hxnoti
      rw [hil]
      exact ⟨hxP, hxmax⟩
    push Not at hxnotmax
    obtain ⟨w, hwP, hxw⟩ := hxnotmax
    exact hxw.trans_le (hvmax.2 w hwP)

/-!
## Riepilogo dei raccordi consegnati

* `intersezione_spigolo_semiretta`: l'intersezione di due faccette distinte da
  un vertice estremo è radialmente una semiretta.
* `spigolo_trasportato`: la simmetria del fan manda ogni spigolo consecutivo
  nello spigolo consecutivo successivo.
* `punto_spigolo_trasportato`: il punto trasportato resta non vertice e conserva
  la sua distanza dal vertice fisso.
* `funzionale_faccetta`: il supporto esposto è costante sulla faccetta e
  strettamente più basso sugli spigoli che non le appartengono.
-/

/-!
A9 — IL FAN NELLO SPAZIO (campagna #50, assemblaggio).

Dal `CyclicVertexData` alle direzioni unitarie degli spigoli: scelta dei
punti, passo isometrico L uᵢ = uᵢ₊₁ (via A1+A2), e INIETTIVITÀ delle
direzioni. La scoperta che semplifica: l'iniettività non richiede
propagazione — se due spigoli condividono la semiretta, il punto più vicino
a v giace per convessità in una faccetta estranea all'altro spigolo, e
`spigolo_due` chiude direttamente, per ogni coppia, con q ≥ 3.
-/

section FanNelloSpazio

open FiniteConvexPolytope

/-- finRotate non ha punti fissi (q ≥ 2). -/
theorem finRotate_ne_self {q : ℕ} (hq : 2 ≤ q) (i : Fin q) :
    finRotate q i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  rw [finRotate_apply]
  intro h
  have hone : (1 : Fin (m + 2)) = 0 := by
    calc (1 : Fin (m + 2)) = i + 1 - i := by abel
      _ = i - i := by rw [h]
      _ = 0 := by abel
  have := congrArg Fin.val hone
  simp at this

/-- finRotate applicato due volte non torna (q ≥ 3). -/
theorem finRotate_due_ne {q : ℕ} (hq : 3 ≤ q) (i : Fin q) :
    finRotate q (finRotate q i) ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 3 := ⟨q - 3, by omega⟩
  rw [finRotate_apply, finRotate_apply]
  intro h
  have hdue : (2 : Fin (m + 3)) = 0 := by
    calc (2 : Fin (m + 3)) = i + 1 + 1 - i := by abel
      _ = i - i := by rw [h]
      _ = 0 := by abel
  have hval := congrArg Fin.val hdue
  have hmod : ((2 : Fin (m + 3)) : ℕ) = 2 := by
    have : (2 : ℕ) % (m + 3) = 2 := Nat.mod_eq_of_lt (by omega)
    simpa [Fin.coe_ofNat_eq_mod] using this
  rw [hmod, Fin.val_zero] at hval
  omega

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]

/-- Il punto di spigolo scelto tra la faccetta i e la successiva. -/
noncomputable def punto (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : A :=
  (D.spigolo i).choose

theorem punto_spec (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) :
    punto P v D i ≠ v ∧
      punto P v D i ∈ D.faccetta i ∩ D.faccetta (finRotate q i) :=
  (D.spigolo i).choose_spec

/-- La direzione unitaria dello spigolo i. -/
noncomputable def dir (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : A :=
  ‖punto P v D i - v‖⁻¹ • (punto P v D i - v)

theorem dir_unitaria (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : ‖dir P v D i‖ = 1 := by
  have h := (punto_spec P v D i).1
  have hne : ‖punto P v D i - v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  rw [dir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]

/-- Le faccette sono convesse. -/
theorem faccetta_convessa (P : FiniteConvexPolytope A) {v : A} {q : ℕ}
    (D : P.CyclicVertexData v q) (i : Fin q) : Convex ℝ (D.faccetta i) :=
  (D.isFacet i).1.1.convex (convex_convexHull ℝ _)

/-- INIETTIVITÀ DELLE DIREZIONI: due spigoli distinti non condividono la
semiretta da v. Il punto più vicino cade nella faccetta sbagliata e
`spigolo_due` chiude. Non serve l'estremalità di v. -/
theorem dir_iniettiva (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (hq : 3 ≤ q) (D : P.CyclicVertexData v q) :
    Function.Injective (dir P v D) := by
  intro i j hij
  by_contra hne
  have hi := punto_spec P v D i
  have hj := punto_spec P v D j
  have hnormi : (0 : ℝ) < ‖punto P v D i - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hi.1)
  have hnormj : (0 : ℝ) < ‖punto P v D j - v‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hj.1)
  -- dal comune versore: punto i − v = t • (punto j − v) con t > 0
  have hrad : punto P v D i - v
      = (‖punto P v D i - v‖ / ‖punto P v D j - v‖) • (punto P v D j - v) := by
    calc punto P v D i - v
        = ‖punto P v D i - v‖ • dir P v D i := by
          rw [dir, smul_smul, mul_inv_cancel₀ (ne_of_gt hnormi), one_smul]
      _ = ‖punto P v D i - v‖ • dir P v D j := by rw [hij]
      _ = (‖punto P v D i - v‖ / ‖punto P v D j - v‖)
            • (punto P v D j - v) := by
          rw [dir, smul_smul, div_eq_mul_inv]
  rcases le_total ‖punto P v D i - v‖ ‖punto P v D j - v‖ with hle | hle
  · -- punto i ∈ [v, punto j] ⊆ faccetta j ∩ faccetta (j+1)
    have hseg : punto P v D i ∈ segment ℝ v (punto P v D j) := by
      rw [segment_eq_image']
      refine ⟨‖punto P v D i - v‖ / ‖punto P v D j - v‖,
        ⟨div_nonneg hnormi.le hnormj.le, (div_le_one hnormj).mpr hle⟩, ?_⟩
      show v + (‖punto P v D i - v‖ / ‖punto P v D j - v‖)
          • (punto P v D j - v) = punto P v D i
      rw [← hrad]
      abel
    have hmem1 : punto P v D i ∈ D.faccetta j :=
      (faccetta_convessa P D j).segment_subset (D.mem_v j) hj.2.1 hseg
    have hmem2 : punto P v D i ∈ D.faccetta (finRotate q j) :=
      (faccetta_convessa P D (finRotate q j)).segment_subset
        (D.mem_v (finRotate q j)) hj.2.2 hseg
    by_cases h2 : j = finRotate q i
    · -- j = i+1: la faccetta buona è j+1 = i+2
      have hk1 : finRotate q j ≠ i := by
        rw [h2]; exact finRotate_due_ne hq i
      have hk2 : finRotate q j ≠ finRotate q i := by
        intro h
        exact finRotate_ne_self (by omega) i (h2 ▸ (finRotate q).injective h)
      rcases D.spigolo_due i (finRotate q j) (punto P v D i) hi.2 hi.1 hmem2
        with h | h
      · exact hk1 h
      · exact hk2 h
    · -- j ∉ {i, i+1}: la faccetta buona è j
      rcases D.spigolo_due i j (punto P v D i) hi.2 hi.1 hmem1 with h | h
      · exact hne h.symm
      · exact h2 h
  · -- simmetrico: punto j ∈ [v, punto i]
    have hrad' : punto P v D j - v
        = (‖punto P v D j - v‖ / ‖punto P v D i - v‖) • (punto P v D i - v) := by
      symm
      calc (‖punto P v D j - v‖ / ‖punto P v D i - v‖) • (punto P v D i - v)
          = (‖punto P v D j - v‖ / ‖punto P v D i - v‖)
              • ((‖punto P v D i - v‖ / ‖punto P v D j - v‖)
              • (punto P v D j - v)) := by rw [← hrad]
        _ = ((‖punto P v D j - v‖ / ‖punto P v D i - v‖)
              * (‖punto P v D i - v‖ / ‖punto P v D j - v‖))
              • (punto P v D j - v) := by rw [smul_smul]
        _ = (1 : ℝ) • (punto P v D j - v) := by
            congr 1
            rw [div_mul_div_comm,
              mul_comm ‖punto P v D i - v‖ ‖punto P v D j - v‖]
            exact div_self (ne_of_gt (mul_pos hnormj hnormi))
        _ = punto P v D j - v := one_smul ℝ _
    have hseg : punto P v D j ∈ segment ℝ v (punto P v D i) := by
      rw [segment_eq_image']
      refine ⟨‖punto P v D j - v‖ / ‖punto P v D i - v‖,
        ⟨div_nonneg hnormj.le hnormi.le, (div_le_one hnormi).mpr hle⟩, ?_⟩
      show v + (‖punto P v D j - v‖ / ‖punto P v D i - v‖)
          • (punto P v D i - v) = punto P v D j
      rw [← hrad']
      abel
    have hmem1 : punto P v D j ∈ D.faccetta i :=
      (faccetta_convessa P D i).segment_subset (D.mem_v i) hi.2.1 hseg
    have hmem2 : punto P v D j ∈ D.faccetta (finRotate q i) :=
      (faccetta_convessa P D (finRotate q i)).segment_subset
        (D.mem_v (finRotate q i)) hi.2.2 hseg
    by_cases h2 : i = finRotate q j
    · have hk1 : finRotate q i ≠ j := by
        rw [h2]; exact finRotate_due_ne hq j
      have hk2 : finRotate q i ≠ finRotate q j := by
        intro h
        exact finRotate_ne_self (by omega) j (h2 ▸ (finRotate q).injective h)
      rcases D.spigolo_due j (finRotate q i) (punto P v D j) hj.2 hj.1 hmem2
        with h | h
      · exact hk1 h
      · exact hk2 h
    · rcases D.spigolo_due j i (punto P v D j) hj.2 hj.1 hmem1 with h | h
      · exact hne h
      · exact h2 h

/-- IL PASSO DEL FAN NELLO SPAZIO: la parte lineare di σ manda la direzione
dello spigolo i in quella dello spigolo i+1 (via A1 + A2). -/
theorem dir_passo (P : FiniteConvexPolytope A) (v : A) {q : ℕ}
    (hq : 3 ≤ q) (D : P.CyclicVertexData v q)
    (hvex : v ∈ P.toSet.extremePoints ℝ) (i : Fin q) :
    D.σ.linearIsometryEquiv (dir P v D i) = dir P v D (finRotate q i) := by
  have hi := punto_spec P v D i
  have htr := punto_spigolo_trasportato P D i hi.2 hi.1
  have hnext := punto_spec P v D (finRotate q i)
  have hFG : D.faccetta (finRotate q i)
      ≠ D.faccetta (finRotate q (finRotate q i)) := by
    intro h
    exact finRotate_ne_self (by omega) (finRotate q i) (D.distinte h).symm
  obtain ⟨c, hc0, hc⟩ := intersezione_spigolo_semiretta P
    (D.isFacet (finRotate q i)) (D.isFacet (finRotate q (finRotate q i)))
    hFG (D.mem_v _) (D.mem_v _) hvex htr.1 hnext.2 htr.2.1 hnext.1
  -- hc : punto (i+1) − v = c • (σ (punto i) − v)
  have hlin : D.σ.linearIsometryEquiv (punto P v D i - v)
      = D.σ (punto P v D i) - v := by
    have h := D.σ.map_vsub (punto P v D i) v
    rw [D.fissa_v] at h
    simpa using h
  have hnorm : ‖punto P v D (finRotate q i) - v‖ = c * ‖punto P v D i - v‖ := by
    rw [hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc0, htr.2.2]
  have hnormi : ‖punto P v D i - v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hi.1)
  rw [dir, dir, map_smul, hlin, hnorm, hc, smul_smul]
  congr 1
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hni : ‖punto P v D i - v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hi.1)
  rw [mul_inv]
  field_simp

end FanNelloSpazio
