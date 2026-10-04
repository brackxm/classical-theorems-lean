import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.SecondoSpigolo

/-!
FASE 3A, F4a-F4b — SEGMENTO E CONO AL VERTICE (18 lug 2026).

(1) Un vertice del politopo è estremo in ogni faccia che lo contiene.
(2) Uno spigolo (faccia di rango 1) che contiene un vertice del politopo è
il segmento tra quel vertice e un secondo estremo: le coordinate lungo la
direzione dello spigolo sono confinate in [0, s_a] perché una coordinata
negativa metterebbe il vertice nell'openSegment tra due punti della faccia.
(3) Il lemma del cono nel poligono: al vertice w con spigoli [w,a] e [w,b],
tutto il poligono sta in w + s(a−w) + t(b−w) con s,t ≥ 0: il segno di t si
legge sull'espositore di e₁ (che uccide a−w e morde b−w), quello di s
sull'espositore di e₂. Corollario locale-globale: un funzionale che non
cresce verso a né verso b è massimo su tutto il poligono in w.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Un vertice del politopo è estremo in ogni faccia che lo contiene. -/
theorem vertice_estremo_in_faccia (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) {w : E n} (hwV : w ∈ P.vertices) (hwf : w ∈ f) :
    w ∈ f.extremePoints ℝ := by
  have hex : w ∈ P.toSet.extremePoints ℝ := by
    have h1 : w ∈ (P.vertices : Set (E n)) := Finset.mem_coe.mpr hwV
    rw [P.vertices_eq_extremePoints] at h1
    exact h1
  refine ⟨hwf, ?_⟩
  intro x hx y hy hseg
  exact hex.2 (face_subset_toSet P hf hx) (face_subset_toSet P hf hy) hseg

/-- Uno spigolo con un vertice del politopo è il segmento fino a un secondo
estremo. -/
theorem spigolo_segmento (P : ConvexPolytope n) {e : Set (E n)}
    (he : P.IsFace e) (hde : faceDim e = 1)
    {w : E n} (hwV : w ∈ P.vertices) (hwe : w ∈ e) :
    ∃ a : E n, a ∈ P.vertices ∧ a ∈ e ∧ a ≠ w ∧ e = segment ℝ w a := by
  classical
  obtain ⟨u, hue, huw⟩ := faccia_ha_secondo_punto hde (v := w)
  set d : E n := u - w with hd
  have hdne : d ≠ 0 := sub_ne_zero.mpr huw
  have hdd : (0:ℝ) < ⟪d, d⟫ := real_inner_self_pos.mpr hdne
  -- lo span dello spigolo è la retta di d
  have hspan : vectorSpan ℝ e = Submodule.span ℝ {d} := by
    have hle : Submodule.span ℝ {d} ≤ vectorSpan ℝ e := by
      rw [Submodule.span_le]
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact vsub_mem_vectorSpan ℝ hue hwe
    apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    rw [finrank_span_singleton hdne]
    have h1 : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
    omega
  -- coordinate lungo lo spigolo
  have hcoord : ∀ z ∈ e, ∃ s : ℝ, z = w + s • d := by
    intro z hz
    have h1 : z - w ∈ vectorSpan ℝ e := vsub_mem_vectorSpan ℝ hz hwe
    rw [hspan] at h1
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h1
    refine ⟨s, ?_⟩
    have h2 := congrArg (fun q => q + w) hs
    simp at h2
    rw [← h2]
    abel
  have hval : ∀ z : E n, ∀ s : ℝ, z = w + s • d → ⟪d, z - w⟫ = s * ⟪d, d⟫ := by
    intro z s hs
    rw [hs]
    simp [inner_smul_right]
  -- il massimo della coordinata su un vertice dello spigolo
  set V : Finset (E n) := (facePolytope P he).vertices with hV
  have hVne : V.Nonempty := (facePolytope P he).vertices_nonempty
  have hVsube : (V : Set (E n)) ⊆ e := by
    intro x hx
    have h1 : x ∈ (facePolytope P he).toSet := subset_convexHull ℝ _ hx
    rwa [facePolytope_toSet P he] at h1
  obtain ⟨a, haV, hamax⟩ := V.exists_max_image (fun z => ⟪d, z⟫) hVne
  have hae : a ∈ e := hVsube haV
  have hmax : ∀ z ∈ e, ⟪d, z⟫ ≤ ⟪d, a⟫ := by
    intro z hz
    have hz' : z ∈ convexHull ℝ (V : Set (E n)) := by
      have h1 := face_eq_hull_vertices P he
      rw [h1] at hz
      exact hz
    have hconv : Convex ℝ {y : E n | ⟪d, y⟫ ≤ ⟪d, a⟫} := by
      apply convex_halfSpace_le
      exact (innerSL ℝ d).toLinearMap.isLinear
    have hsub : (V : Set (E n)) ⊆ {y : E n | ⟪d, y⟫ ≤ ⟪d, a⟫} := by
      intro x hx
      exact hamax x (Finset.mem_coe.mp hx)
    exact convexHull_min hsub hconv hz'
  obtain ⟨sa, hsa⟩ := hcoord a hae
  have hsage : 1 ≤ sa := by
    have h1 : ⟪d, u⟫ ≤ ⟪d, a⟫ := hmax u hue
    have h2 : ⟪d, u - w⟫ ≤ ⟪d, a - w⟫ := by
      rw [inner_sub_right, inner_sub_right]
      linarith
    have h3 : ⟪d, u - w⟫ = ⟪d, d⟫ := by rw [hd]
    have h4 := hval a sa hsa
    nlinarith
  have hsapos : 0 < sa := by linarith
  -- w è l'estremo inferiore: nessuna coordinata negativa
  have hwex : w ∈ e.extremePoints ℝ := vertice_estremo_in_faccia P he hwV hwe
  have hmin : ∀ z ∈ e, ∀ s : ℝ, z = w + s • d → 0 ≤ s := by
    intro z hz sz hsz
    by_contra hneg
    push_neg at hneg
    have hτ : (0:ℝ) < sa - sz := by linarith
    have hne : sa - sz ≠ 0 := ne_of_gt hτ
    have hcomb : w ∈ openSegment ℝ z a := by
      refine ⟨sa / (sa - sz), -sz / (sa - sz), ?_, ?_, ?_, ?_⟩
      · exact div_pos hsapos hτ
      · exact div_pos (by linarith) hτ
      · have h5 : sa / (sa - sz) + -sz / (sa - sz) = (sa + -sz) / (sa - sz) :=
          (add_div sa (-sz) (sa - sz)).symm
        rw [h5]
        have h6 : sa + -sz = sa - sz := by ring
        rw [h6]
        exact div_self hne
      · rw [hsz, hsa]
        match_scalars <;> field_simp <;> ring
    have hzw : z = w := hwex.2 hz hae hcomb
    rw [hzw] at hsz
    have h0 : sz • d = 0 := by
      have := congrArg (fun q => q - w) hsz
      simpa using this.symm
    rcases smul_eq_zero.mp h0 with h | h
    · linarith
    · exact hdne h
  have haPV : a ∈ P.vertices := by
    have h1 := haV
    rw [hV] at h1
    exact (Finset.mem_filter.mp h1).1
  refine ⟨a, haPV, hae, ?_, ?_⟩
  · intro h
    rw [h] at hsa
    have h0 : sa • d = 0 := by
      have := congrArg (fun q => q - w) hsa
      simpa using this.symm
    rcases smul_eq_zero.mp h0 with h1 | h1
    · linarith
    · exact hdne h1
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨s, hs⟩ := hcoord z hz
      have hs0 : 0 ≤ s := hmin z hz s hs
      have hssa : s ≤ sa := by
        have h1 : ⟪d, z⟫ ≤ ⟪d, a⟫ := hmax z hz
        have h2 : ⟪d, z - w⟫ ≤ ⟪d, a - w⟫ := by
          rw [inner_sub_right, inner_sub_right]
          linarith
        have h3 := hval z s hs
        have h4 := hval a sa hsa
        nlinarith
      refine ⟨1 - s / sa, s / sa, ?_, ?_, by ring, ?_⟩
      · have h1 : s / sa ≤ 1 := by
          rw [div_le_one hsapos]
          exact hssa
        linarith
      · exact div_nonneg hs0 (le_of_lt hsapos)
      · rw [hs, hsa]
        match_scalars <;> field_simp <;> ring
    · have hconv : Convex ℝ e := he.1.convex (convex_convexHull ℝ _)
      exact hconv.segment_subset hwe hae

/-- **IL CONO AL VERTICE DEL POLIGONO**: al vertice w con spigoli [w,a] e
[w,b] distinti, ogni punto del poligono è w + s(a−w) + t(b−w) con s,t ≥ 0. -/
theorem cono_al_vertice (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {w : E n} (hwV : w ∈ Q.vertices)
    {e₁ e₂ : Set (E n)} (he₁ : Q.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (he₂ : Q.IsFace e₂) (hde₂ : faceDim e₂ = 1) (hne : e₁ ≠ e₂)
    {a b : E n} (hae : a ∈ e₁) (haw : a ≠ w) (hseg₁ : e₁ = segment ℝ w a)
    (hbe : b ∈ e₂) (hbw : b ≠ w) (hseg₂ : e₂ = segment ℝ w b)
    (hwe₁ : w ∈ e₁) (hwe₂ : w ∈ e₂) :
    ∀ z ∈ Q.toSet, ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
      z = w + s • (a - w) + t • (b - w) := by
  classical
  -- gli espositori dei due spigoli
  obtain ⟨l₁, hl₁⟩ := he₁.1 he₁.2
  obtain ⟨l₂, hl₂⟩ := he₂.1 he₂.2
  have hmax₁ : ∀ y ∈ Q.toSet, l₁ y ≤ l₁ w := by
    have h1 := hwe₁
    rw [hl₁] at h1
    exact h1.2
  have hmax₂ : ∀ y ∈ Q.toSet, l₂ y ≤ l₂ w := by
    have h1 := hwe₂
    rw [hl₂] at h1
    exact h1.2
  have hchar₁ : ∀ q ∈ Q.toSet, l₁ q = l₁ w → q ∈ e₁ := by
    intro q hq hlq
    rw [hl₁]
    exact ⟨hq, fun y hy => le_trans (hmax₁ y hy) (le_of_eq hlq.symm)⟩
  have hchar₂ : ∀ q ∈ Q.toSet, l₂ q = l₂ w → q ∈ e₂ := by
    intro q hq hlq
    rw [hl₂]
    exact ⟨hq, fun y hy => le_trans (hmax₂ y hy) (le_of_eq hlq.symm)⟩
  -- valori: l₁ uccide a, morde b; l₂ uccide b, morde a
  have hl₁a : l₁ a = l₁ w := by
    have h1 := hae
    rw [hl₁] at h1
    exact le_antisymm (hmax₁ a (face_subset_toSet Q he₁ hae))
      (h1.2 w (face_subset_toSet Q he₁ hwe₁))
  have hl₂b : l₂ b = l₂ w := by
    have h1 := hbe
    rw [hl₂] at h1
    exact le_antisymm (hmax₂ b (face_subset_toSet Q he₂ hbe))
      (h1.2 w (face_subset_toSet Q he₂ hwe₂))
  -- b ∉ e₁ (due punti comuni forzerebbero rango ≥ 1 dell'intersezione)
  have hfuori : ∀ {p : E n}, p ∈ e₂ → p ≠ w → p ∉ e₁ := by
    intro p hpe₂ hpw hpe₁
    have hint : Q.IsFace (e₁ ∩ e₂) := ⟨he₁.1.inter he₂.1, ⟨w, hwe₁, hwe₂⟩⟩
    have hssub : e₁ ∩ e₂ ⊂ e₁ := by
      refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
      have h12 : e₁ ⊆ e₂ := fun z hz => (hsup hz).2
      have hss : e₁ ⊂ e₂ := ⟨h12, fun h => hne (Set.Subset.antisymm h12 h)⟩
      have := faceDim_lt_of_ssubset Q he₁ he₂ hss
      omega
    have hlt := faceDim_lt_of_ssubset Q hint he₁ hssub
    have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) :=
      finrank_pos_di_due ⟨hwe₁, hwe₂⟩ ⟨hpe₁, hpe₂⟩ hpw
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) < 1 := by
      have h1 : Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) <
          Module.finrank ℝ (vectorSpan ℝ e₁) := hlt
      have h2 : Module.finrank ℝ (vectorSpan ℝ e₁) = 1 := hde₁
      omega
    omega
  have hfuori' : ∀ {p : E n}, p ∈ e₁ → p ≠ w → p ∉ e₂ := by
    intro p hpe₁ hpw hpe₂
    exact hfuori hpe₂ hpw hpe₁
  have hl₁b : l₁ b < l₁ w := by
    rcases lt_or_eq_of_le (hmax₁ b (face_subset_toSet Q he₂ hbe)) with h | h
    · exact h
    · exact absurd (hchar₁ b (face_subset_toSet Q he₂ hbe) h) (hfuori hbe hbw)
  have hl₂a : l₂ a < l₂ w := by
    rcases lt_or_eq_of_le (hmax₂ a (face_subset_toSet Q he₁ hae)) with h | h
    · exact h
    · exact absurd (hchar₂ a (face_subset_toSet Q he₁ hae) h) (hfuori' hae haw)
  -- le due direzioni sono indipendenti e generano lo span del poligono
  have hLI : LinearIndependent ℝ ![a - w, b - w] := by
    rw [linearIndependent_fin2]
    constructor
    · show b - w ≠ 0
      exact sub_ne_zero.mpr hbw
    · intro c
      show c • (b - w) ≠ a - w
      intro heq
      -- a sarebbe sulla retta di e₂: l₂ costante ⟹ a ∈ e₂: assurdo
      have ha' : a = c • (b - w) + w := by
        have h2 := congrArg (fun q => q + w) heq
        simp at h2
        exact h2.symm
      have hval : l₂ a = c * (l₂ b - l₂ w) + l₂ w := by
        rw [ha']
        simp [map_add, map_smul, map_sub, smul_eq_mul]
      rw [hl₂b] at hval
      simp at hval
      exact absurd (hchar₂ a (face_subset_toSet Q he₁ hae) hval)
        (hfuori' hae haw)
  have hspan2 : Submodule.span ℝ (Set.range ![a - w, b - w]) =
      vectorSpan ℝ Q.toSet := by
    have hle : Submodule.span ℝ (Set.range ![a - w, b - w]) ≤
        vectorSpan ℝ Q.toSet := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with ⟨iv, hi⟩
      interval_cases iv
      · show (![a - w, b - w] : Fin 2 → E n) 0 ∈ vectorSpan ℝ Q.toSet
        show a - w ∈ vectorSpan ℝ Q.toSet
        exact vsub_mem_vectorSpan ℝ (face_subset_toSet Q he₁ hae)
          (face_subset_toSet Q he₁ hwe₁)
      · show (![a - w, b - w] : Fin 2 → E n) 1 ∈ vectorSpan ℝ Q.toSet
        show b - w ∈ vectorSpan ℝ Q.toSet
        exact vsub_mem_vectorSpan ℝ (face_subset_toSet Q he₂ hbe)
          (face_subset_toSet Q he₂ hwe₂)
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_span_eq_card hLI]
    simp [hdim]
  -- la scrittura in coordinate e i segni
  intro z hz
  have hzmem : z - w ∈ Submodule.span ℝ (Set.range ![a - w, b - w]) := by
    rw [hspan2]
    exact vsub_mem_vectorSpan ℝ hz (face_subset_toSet Q he₁ hwe₁)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hzmem
  rw [Fin.sum_univ_two] at hc
  have hc' : c 0 • (a - w) + c 1 • (b - w) = z - w := hc
  have hzval : z = w + c 0 • (a - w) + c 1 • (b - w) := by
    have := congrArg (fun q => q + w) hc'
    simp at this
    rw [← this]
    abel
  -- l₁ dà il segno di c 1
  have hs1 : l₁ z = l₁ w + c 1 * (l₁ b - l₁ w) := by
    rw [hzval]
    simp [map_add, map_smul, map_sub, smul_eq_mul, hl₁a]
  have ht : 0 ≤ c 1 := by
    have h1 := hmax₁ z hz
    rw [hs1] at h1
    by_contra hneg
    push_neg at hneg
    nlinarith
  -- l₂ dà il segno di c 0
  have hs2 : l₂ z = l₂ w + c 0 * (l₂ a - l₂ w) := by
    rw [hzval]
    simp [map_add, map_smul, map_sub, smul_eq_mul, hl₂b]
  have hs : 0 ≤ c 0 := by
    have h1 := hmax₂ z hz
    rw [hs2] at h1
    by_contra hneg
    push_neg at hneg
    nlinarith
  exact ⟨c 0, c 1, hs, ht, hzval⟩

/-- **LOCALE-GLOBALE**: un funzionale che al vertice w non cresce verso i
due estremi vicini è massimo su tutto il poligono in w. -/
theorem locale_globale (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {w : E n} (hwV : w ∈ Q.vertices)
    {e₁ e₂ : Set (E n)} (he₁ : Q.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (he₂ : Q.IsFace e₂) (hde₂ : faceDim e₂ = 1) (hne : e₁ ≠ e₂)
    {a b : E n} (hae : a ∈ e₁) (haw : a ≠ w) (hseg₁ : e₁ = segment ℝ w a)
    (hbe : b ∈ e₂) (hbw : b ≠ w) (hseg₂ : e₂ = segment ℝ w b)
    (hwe₁ : w ∈ e₁) (hwe₂ : w ∈ e₂)
    (h : E n →L[ℝ] ℝ) (hha : h a ≤ h w) (hhb : h b ≤ h w) :
    ∀ z ∈ Q.toSet, h z ≤ h w := by
  intro z hz
  obtain ⟨s, t, hs, ht, hzval⟩ := cono_al_vertice Q hdim hwV he₁ hde₁ he₂ hde₂
    hne hae haw hseg₁ hbe hbw hseg₂ hwe₁ hwe₂ z hz
  have hval : h z = h w + s * (h a - h w) + t * (h b - h w) := by
    rw [hzval]
    simp [map_add, map_smul, map_sub, smul_eq_mul]
  nlinarith [mul_nonneg hs (by linarith : (0:ℝ) ≤ h w - h a),
    mul_nonneg ht (by linarith : (0:ℝ) ≤ h w - h b)]

end LeanEval.Geometry.PlatonicClassification
