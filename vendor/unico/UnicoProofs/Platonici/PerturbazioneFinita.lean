import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.FacciaArgmax

/-!
FASE 3A, Q0 — IL LEMMA DELLA PERTURBAZIONE FINITA (18 lug 2026).

«In un politopo, una faccia esposta di una faccia esposta è esposta.»
Falso per convessi generali; vero per politopi: se f = argmax di l su P
ed e = argmax di l' su f, allora e = argmax di l + ε·l' su P, con ε sotto
il gap minimo di l sui vertici fuori da f (il gap esiste: vertici FINITI).
Chiusura della direzione ⊇ con `faccia_argmax` (la concentrazione dei pesi
sui generatori argmax). Da Q0: spigoli delle faccette, bandiere complete,
la bandiera compagna di KG-3A1.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Ogni faccia (esposta, non vuota) di un politopo è l'hull dei vertici che
contiene: il pattern del tetraedro, in forma generale sul contratto. -/
theorem face_eq_hull_vertices (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    f = convexHull ℝ ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n)) := by
  classical
  let S : Finset (E n) := P.vertices.filter (· ∈ f)
  have hPcompact : IsCompact P.toSet :=
    (P.vertices.finite_toSet.isCompact_convexHull ℝ)
  have hFcompact : IsCompact f := hf.1.isCompact hPcompact
  have hFconvex : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
  have hKM := closure_convexHull_extremePoints hFcompact hFconvex
  have hext : f.extremePoints ℝ = (S : Set (E n)) := by
    rw [hf.1.isExtreme.extremePoints_eq]
    ext x
    simp only [S, Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff]
    change (x ∈ f ∧ x ∈ P.toSet.extremePoints ℝ) ↔
      x ∈ P.vertices ∧ x ∈ f
    rw [ConvexPolytope.toSet, ← P.vertices_eq_extremePoints]
    tauto
  calc
    f = closure (convexHull ℝ (f.extremePoints ℝ)) := hKM.symm
    _ = closure (convexHull ℝ (S : Set (E n))) := by rw [hext]
    _ = convexHull ℝ (S : Set (E n)) :=
      (S.finite_toSet.isClosed_convexHull ℝ).closure_eq
    _ = convexHull ℝ
        ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n)) := rfl

open Classical in
/-- Un funzionale limitato sui vertici è limitato sul corpo. -/
theorem le_su_toSet (P : ConvexPolytope n) (g : E n →L[ℝ] ℝ) {c : ℝ}
    (hv : ∀ v ∈ (P.vertices : Set (E n)), g v ≤ c) :
    ∀ x ∈ P.toSet, g x ≤ c := by
  intro x hx
  have hsub : (P.vertices : Set (E n)) ⊆ {z : E n | g z ≤ c} := hv
  exact convexHull_min hsub
    (convex_halfSpace_le (LinearMap.isLinear g.toLinearMap) c) hx

/-- Q0, IL LEMMA-CHIAVE: una faccia esposta non vuota di una faccia di un
politopo è una faccia del politopo. -/
theorem isFace_of_isExposed_isFace (P : ConvexPolytope n)
    {f e : Set (E n)} (hf : P.IsFace f) (he : IsExposed ℝ f e)
    (hene : e.Nonempty) : P.IsFace e := by
  classical
  obtain ⟨l, hl⟩ := hf.1 hf.2
  obtain ⟨l', hl'⟩ := he hene
  have hene' := hene
  obtain ⟨x₀, hx₀⟩ := hene'
  have hx₀f : x₀ ∈ f := by rw [hl'] at hx₀; exact hx₀.1
  have hx₀T : x₀ ∈ P.toSet := by rw [hl] at hx₀f; exact hx₀f.1
  -- il valore comune di l su f
  set M : ℝ := l x₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    rw [hl] at hz hx₀f
    exact le_antisymm (hx₀f.2 z hz.1) (hz.2 x₀ hx₀f.1)
  have hlmax : ∀ y ∈ P.toSet, l y ≤ M := by
    intro y hy
    rw [hl] at hx₀f
    exact hx₀f.2 y hy
  -- caso A: tutti i vertici stanno in f ⟹ f = toSet
  by_cases hA : ∀ v ∈ P.vertices, v ∈ f
  · have hTf : P.toSet ⊆ f := by
      have hsub : (P.vertices : Set (E n)) ⊆ f := fun v hv =>
        hA v (by exact_mod_cast hv)
      have hconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
      exact convexHull_min hsub hconv
    have hfT : f = P.toSet := by
      apply Set.Subset.antisymm ?_ hTf
      rw [hl]; exact fun z hz => hz.1
    refine ⟨?_, hene⟩
    intro _
    refine ⟨l', ?_⟩
    rw [hl', hfT]
  -- caso B: c'è un vertice fuori da f
  · push_neg at hA
    obtain ⟨v₀, hv₀V, hv₀f⟩ := hA
    set Vout : Finset (E n) := P.vertices.filter (· ∉ f) with hVout
    have hVoutne : Vout.Nonempty := ⟨v₀, by simp [hVout, hv₀V, hv₀f]⟩
    -- il gap δ
    set mout : ℝ := (Vout.image (fun v => l v)).max'
      (hVoutne.image _) with hmout
    have hmout_lt : mout < M := by
      have : ∀ b ∈ Vout.image (fun v => l v), b < M := by
        intro b hb
        obtain ⟨v, hvin, rfl⟩ := Finset.mem_image.mp hb
        have hvV : v ∈ P.vertices := (Finset.mem_filter.mp hvin).1
        have hvnf : v ∉ f := (Finset.mem_filter.mp hvin).2
        have hle : l v ≤ M := hlmax v (subset_convexHull ℝ _ (by exact_mod_cast hvV))
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exfalso
          apply hvnf
          rw [hl]
          exact ⟨subset_convexHull ℝ _ (by exact_mod_cast hvV),
            fun y hy => h ▸ hlmax y hy⟩
      rw [hmout]
      exact (Finset.max'_lt_iff _ (hVoutne.image _)).mpr this
    set δ : ℝ := M - mout with hδ
    have hδpos : 0 < δ := by simp [hδ]; linarith
    -- il tetto C di |l'| sui vertici
    have hVne : P.vertices.Nonempty := P.vertices_nonempty
    set C : ℝ := (P.vertices.image (fun v => |l' v|)).max'
      (hVne.image _) with hC
    have hCnneg : 0 ≤ C := by
      obtain ⟨v, hv⟩ := hVne
      have : |l' v| ∈ P.vertices.image (fun v => |l' v|) :=
        Finset.mem_image_of_mem _ hv
      rw [hC]
      exact le_trans (abs_nonneg (l' v))
        (Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|) this)
    have hl'le : ∀ x ∈ P.toSet, l' x ≤ C := by
      apply le_su_toSet
      intro v hv
      have hvV : v ∈ P.vertices := by exact_mod_cast hv
      have hCb : |l' v| ≤ C := by
        rw [hC]
        exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
          (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
      linarith [le_abs_self (l' v)]
    have hl'ge : ∀ x ∈ P.toSet, -C ≤ l' x := by
      have h2 : ∀ x ∈ P.toSet, (-l') x ≤ C := by
        apply le_su_toSet
        intro v hv
        have hvV : v ∈ P.vertices := by exact_mod_cast hv
        have h2a : |l' v| ≤ C := by
          rw [hC]
          exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
            (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
        have h2b := neg_abs_le (l' v)
        simp only [ContinuousLinearMap.neg_apply]
        linarith
      intro x hx
      have := h2 x hx
      simp only [ContinuousLinearMap.neg_apply] at this
      linarith
    -- la perturbazione
    set ε : ℝ := δ / (2 * C + 1) with hε
    have hεpos : 0 < ε := div_pos hδpos (by linarith)
    have h2C1 : (0:ℝ) < 2 * C + 1 := by linarith
    have hεδ : ε * (2 * C + 1) = δ := by
      rw [hε]
      field_simp
    have hεC : 2 * ε * C < δ := by nlinarith
    -- il funzionale perturbato
    set L : E n →L[ℝ] ℝ := l + ε • l' with hLdef
    have hLapp : ∀ x, L x = l x + ε * l' x := by
      intro x
      simp [hLdef, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    refine ⟨?_, hene⟩
    intro _
    refine ⟨L, ?_⟩
    ext x
    constructor
    · intro hx
      have hxf : x ∈ f := by rw [hl'] at hx; exact hx.1
      have hxT : x ∈ P.toSet := by rw [hl] at hxf; exact hxf.1
      refine ⟨hxT, ?_⟩
      intro y hy
      have hvert : ∀ v ∈ (P.vertices : Set (E n)), L v ≤ L x := by
        intro v hvS
        have hvV : v ∈ P.vertices := by exact_mod_cast hvS
        have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
        by_cases hvf : v ∈ f
        · have h1 : l v = M := hlf v hvf
          have h2 : l' v ≤ l' x := by
            rw [hl'] at hx
            exact hx.2 v hvf
          rw [hLapp, hLapp, h1, hlf x hxf]
          nlinarith
        · have h1 : l v ≤ mout := by
            rw [hmout]
            exact Finset.le_max' (Vout.image (fun w => l w)) (l v)
              (Finset.mem_image_of_mem (fun w => l w) (by simp [hVout, hvV, hvf]))
          have h2 : l' v ≤ C := by
            have hb : |l' v| ≤ C := by
              rw [hC]
              exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
                (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
            linarith [le_abs_self (l' v)]
          have h3 : -C ≤ l' x := hl'ge x hxT
          rw [hLapp, hLapp, hlf x hxf]
          have hmoutδ : mout = M - δ := by rw [hδ]; ring
          nlinarith
      exact le_su_toSet P L hvert y hy
    · rintro ⟨hxT, hxmax⟩
      have hxhull := PlatoniciL3.faccia_argmax P.vertices L
        (y := x) hxT (fun w hw => hxmax w hw)
      have hVL : {z ∈ (P.vertices : Set (E n)) | L z = L x} ⊆ e := by
        rintro v ⟨hvS, hvL⟩
        have hvV : v ∈ P.vertices := by exact_mod_cast hvS
        have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
        have hcomp : L x₀ ≤ L x := hxmax x₀ hx₀T
        have hLx₀ : L x₀ = M + ε * l' x₀ := by
          rw [hLapp, hM]
        have hvf : v ∈ f := by
          by_contra hvnf
          have h1 : l v ≤ mout := by
            rw [hmout]
            exact Finset.le_max' (Vout.image (fun w => l w)) (l v)
              (Finset.mem_image_of_mem (fun w => l w) (by simp [hVout, hvV, hvnf]))
          have h2 : l' v ≤ C := by
            have hb : |l' v| ≤ C := by
              rw [hC]
              exact Finset.le_max' (P.vertices.image (fun w => |l' w|)) (|l' v|)
                (Finset.mem_image_of_mem (fun w => |l' w|) hvV)
            linarith [le_abs_self (l' v)]
          have h3 : -C ≤ l' x₀ := hl'ge x₀ hx₀T
          have h5 : L v = l v + ε * l' v := hLapp v
          have hmoutδ : mout = M - δ := by rw [hδ]; ring
          rw [hvL] at h5
          nlinarith
        have hlv : l v = M := hlf v hvf
        have h7 : L x₀ ≤ L v := by rw [hvL]; exact hcomp
        rw [hLapp, hLapp, hlv, hM] at h7
        have h8 : l' x₀ ≤ l' v := by
          have h6 : ε * l' x₀ ≤ ε * l' v := by linarith
          exact le_of_mul_le_mul_left h6 hεpos
        rw [hl']
        refine ⟨hvf, ?_⟩
        intro y hyf
        have h9 : l' y ≤ l' x₀ := by
          rw [hl'] at hx₀
          exact hx₀.2 y hyf
        linarith
      have hecvx : Convex ℝ e := he.convex (hf.1.convex (convex_convexHull ℝ _))
      have hsub : convexHull ℝ {z ∈ (P.vertices : Set (E n)) | L z = L x} ⊆ e :=
        convexHull_min hVL hecvx
      exact hsub hxhull

end LeanEval.Geometry.PlatonicClassification
