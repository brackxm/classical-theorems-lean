import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita

/-!
FASE 3A, Q1 — I VERTICI SONO FACCE ESPOSTE (18 lug 2026).

Primo gradino dell'esistenza delle bandiere: per ogni vertice v di un
politopo, {v} è una faccia (esposta, non vuota). Dimostrazione: v è un punto
estremo, quindi NON sta nell'hull degli altri vertici (altrimenti l'hull
collasserebbe e v sarebbe tra i punti estremi di un hull che non lo
contiene); Hahn-Banach geometrico separa v da quell'hull compatto; l'argmax
del separatore si concentra su v (faccia_argmax).
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Un vertice non sta nell'hull degli altri vertici. -/
theorem vertex_notMem_hull_erase (P : ConvexPolytope n) {v : E n}
    (hv : v ∈ P.vertices) :
    v ∉ convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) := by
  intro hmem
  have hsub : (P.vertices : Set (E n))
      ⊆ convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; exact hmem
    · exact subset_convexHull ℝ _ (by
        exact_mod_cast Finset.mem_erase.mpr ⟨hwv, by exact_mod_cast hw⟩)
  have hhull : convexHull ℝ ((P.vertices : Finset (E n)) : Set (E n))
      = convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hsub (convex_convexHull ℝ _)
    · apply convexHull_mono
      intro w hw
      have := Finset.erase_subset (s := P.vertices) (a := v)
      exact_mod_cast this (by exact_mod_cast hw)
  have hvext : v ∈ (convexHull ℝ ((P.vertices : Finset (E n)) : Set (E n))).extremePoints ℝ := by
    rw [← P.vertices_eq_extremePoints]
    exact_mod_cast hv
  rw [hhull] at hvext
  have hin : v ∈ ((P.vertices.erase v : Finset (E n)) : Set (E n)) :=
    extremePoints_convexHull_subset hvext
  have : v ∈ P.vertices.erase v := by exact_mod_cast hin
  exact (Finset.mem_erase.mp this).1 rfl

open Classical in
/-- Q1: ogni vertice è una faccia (esposta, non vuota) del politopo. -/
theorem vertex_isFace (P : ConvexPolytope n) {v : E n}
    (hv : v ∈ P.vertices) : P.IsFace ({v} : Set (E n)) := by
  classical
  refine ⟨?_, Set.singleton_nonempty v⟩
  intro _
  by_cases hK : (P.vertices.erase v).Nonempty
  · -- separazione di Hahn-Banach dal compatto hull(altri)
    set K : Set (E n) :=
      convexHull ℝ ((P.vertices.erase v : Finset (E n)) : Set (E n)) with hKdef
    have hKconv : Convex ℝ K := convex_convexHull ℝ _
    have hKclosed : IsClosed K :=
      (P.vertices.erase v).finite_toSet.isClosed_convexHull ℝ
    have hvK : v ∉ K := vertex_notMem_hull_erase P hv
    obtain ⟨l, u, hlt, hu⟩ :=
      geometric_hahn_banach_closed_point hKconv hKclosed hvK
    refine ⟨l, ?_⟩
    ext x
    constructor
    · rintro rfl
      refine ⟨subset_convexHull ℝ _ (by exact_mod_cast hv), ?_⟩
      -- l ≤ l v su tutto il corpo, via i vertici
      intro y hy
      have hvert : ∀ w ∈ (P.vertices : Set (E n)), l w ≤ l x := by
        intro w hw
        by_cases hwv : w = x
        · subst hwv; exact le_refl _
        · have hwK : w ∈ K := subset_convexHull ℝ _ (by
            exact_mod_cast Finset.mem_erase.mpr ⟨hwv, by exact_mod_cast hw⟩)
          exact le_of_lt (lt_trans (hlt w hwK) hu)
      exact le_su_toSet P l hvert y hy
    · rintro ⟨hxT, hxmax⟩
      have hxhull := PlatoniciL3.faccia_argmax P.vertices l
        (y := x) hxT (fun w hw => hxmax w hw)
      have hset : {z ∈ (P.vertices : Set (E n)) | l z = l x} ⊆ ({v} : Set (E n)) := by
        rintro w ⟨hwS, hwl⟩
        have hwV : w ∈ P.vertices := by exact_mod_cast hwS
        by_contra hwv
        have hwv' : w ≠ v := by simpa using hwv
        have hwK : w ∈ K := subset_convexHull ℝ _ (by
          exact_mod_cast Finset.mem_erase.mpr ⟨hwv', hwV⟩)
        -- l w < u < l v ≤ l x = l w: assurdo
        have h1 : l w < u := hlt w hwK
        have h2 : u < l v := hu
        have h3 : l v ≤ l x := hxmax v (subset_convexHull ℝ _ (by exact_mod_cast hv))
        rw [hwl] at h1
        linarith
      have : convexHull ℝ {z ∈ (P.vertices : Set (E n)) | l z = l x}
          ⊆ ({v} : Set (E n)) := by
        have hconv : Convex ℝ ({v} : Set (E n)) := convex_singleton v
        exact convexHull_min hset hconv
      exact this hxhull
  · -- vertici = {v}: il corpo È {v}, esposto dal funzionale nullo
    have hverts : P.vertices = {v} := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        by_contra hwv
        have : w ∈ P.vertices.erase v :=
          Finset.mem_erase.mpr ⟨by simpa using hwv, hw⟩
        exact hK ⟨w, this⟩
      · have h1 : 1 ≤ P.vertices.card :=
          Finset.card_pos.mpr ⟨v, hv⟩
        simpa using h1
    have hT : P.toSet = ({v} : Set (E n)) := by
      show convexHull ℝ ((P.vertices : Finset (E n)) : Set (E n)) = _
      rw [hverts]
      simp
    refine ⟨0, ?_⟩
    rw [hT]
    ext x
    simp
