import Mathlib

/-!
FASE 3A, F4c — LA CAMMINATA DEL SIMPLESSO, FORMA ASTRATTA (18 lug 2026).

Su un insieme finito con una relazione di adiacenza, un potenziale che
soddisfa il principio locale-globale (chi non cresce verso i vicini è
massimo globale) e ha un massimo unico x⋆ costringe ogni punto a essere
connesso a x⋆: la componente di partenza contiene il proprio argmax, che
non può essere un massimo locale diverso da x⋆.
-/

namespace LeanEval.Geometry.PlatonicClassification

/-- **LA CAMMINATA DEL SIMPLESSO**: con il principio locale-globale e un
massimo unico, ogni nodo è connesso al massimo. -/
theorem camminata_del_simplesso {α : Type*} [DecidableEq α]
    (X : Finset α) (adj : α → α → Prop) (φ : α → ℝ)
    (hlg : ∀ x ∈ X, (∀ y ∈ X, adj x y → φ y ≤ φ x) →
      ∀ z ∈ X, φ z ≤ φ x)
    {xs : α} (hxs : xs ∈ X)
    (hunico : ∀ z ∈ X, z ≠ xs → φ z < φ xs)
    {x₀ : α} (hx₀ : x₀ ∈ X) :
    Relation.ReflTransGen (fun p q => q ∈ X ∧ adj p q) x₀ xs := by
  classical
  set raggiunto : α → Prop :=
    fun q => Relation.ReflTransGen (fun p q => q ∈ X ∧ adj p q) x₀ q
    with hragg
  set R : Finset α := X.filter (fun q => raggiunto q) with hR
  have hx₀R : x₀ ∈ R := Finset.mem_filter.mpr ⟨hx₀, Relation.ReflTransGen.refl⟩
  have hRne : R.Nonempty := ⟨x₀, hx₀R⟩
  obtain ⟨m, hmR, hmmax⟩ := R.exists_max_image φ hRne
  have hmX : m ∈ X := (Finset.mem_filter.mp hmR).1
  have hmragg : raggiunto m := (Finset.mem_filter.mp hmR).2
  by_cases hms : m = xs
  · rw [hms] at hmragg
    exact hmragg
  · exfalso
    -- m non è massimo globale, quindi ha un vicino migliore
    have hnotmax : ¬ (∀ y ∈ X, adj m y → φ y ≤ φ m) := by
      intro hloc
      have h1 := hlg m hmX hloc xs hxs
      have h2 := hunico m hmX hms
      linarith
    push_neg at hnotmax
    obtain ⟨y, hyX, hadj, hlt⟩ := hnotmax
    -- il vicino è raggiunto, quindi sta in R: contraddice l'argmax
    have hyragg : raggiunto y := hmragg.tail ⟨hyX, hadj⟩
    have hyR : y ∈ R := Finset.mem_filter.mpr ⟨hyX, hyragg⟩
    have := hmmax y hyR
    linarith

end LeanEval.Geometry.PlatonicClassification
