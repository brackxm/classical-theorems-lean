/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.Green
import MovingSofa.Curve.Jordan.Interior
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Verified domain and curve bridges for Green’s theorem, used by the complete proof
in `ClassicalTheorems.Progress.GreenFull`. -/

noncomputable section
open Set MovingSofa
namespace ClassicalTheorems.Progress.Green

/-- An open connected domain is exactly a component of its frontier's complement. -/
theorem domain_component {X : Type*} [TopologicalSpace X] (D : Set X)
    (hOpen : IsOpen D) (hConnected : IsConnected D) {p : X} (hp : p ∈ D) :
    connectedComponentIn (frontier D)ᶜ p = D := by
  have hD : D ⊆ (frontier D)ᶜ := by
    intro x hx hxf
    exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hOpen)) hxf hx
  apply Set.Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hOpen
    · exact ⟨p, mem_connectedComponentIn (hD hp), hp⟩
    · rintro x ⟨hxc, hxcomp⟩
      have hxf := connectedComponentIn_subset (frontier D)ᶜ p hxcomp
      by_contra hxd
      apply hxf
      exact ⟨hxc, by simpa only [hOpen.interior_eq] using hxd⟩
  · exact hConnected.isPreconnected.subset_connectedComponentIn hp hD

/-- A simple closed interval curve gives a Jordan curve in the circle model. -/
theorem isJordanCurve_of_simple_closed (γ : ℝ → Point)
    (hc : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hinj : InjOn γ (Ico 0 1)) : IsJordanCurve (γ '' Icc 0 1) := by
  let f : AddCircle (1 : ℝ) → Point := AddCircle.liftIco 1 0 γ
  have hfc : Continuous f := AddCircle.liftIco_zero_continuous hclosed hc
  have hfi : Function.Injective f := by
    intro x y hxy
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    apply hinj
    · simpa using (AddCircle.equivIco (1 : ℝ) 0 x).property
    · simpa using (AddCircle.equivIco (1 : ℝ) 0 y).property
    · exact hxy
  have hrange : range f = γ '' Icc 0 1 := by
    apply Subset.antisymm
    · rintro p ⟨z, rfl⟩
      refine ⟨AddCircle.equivIco (1 : ℝ) 0 z, ?_, rfl⟩
      have ht := (AddCircle.equivIco (1 : ℝ) 0 z).property
      exact ⟨ht.1, by simpa using ht.2.le⟩
    · rintro p ⟨t, ht, rfl⟩
      by_cases hlt : t < 1
      · refine ⟨(t : AddCircle (1 : ℝ)), ?_⟩
        exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, hlt⟩
      · have ht1 : t = 1 := le_antisymm ht.2 (le_of_not_gt hlt)
        subst t
        refine ⟨(0 : AddCircle (1 : ℝ)), ?_⟩
        exact (AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 1)).trans hclosed
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  refine ⟨f ∘ e.symm, hfc.comp e.symm.continuous, hfi.comp e.symm.injective, ?_⟩
  rw [range_comp, e.symm.surjective.range_eq, image_univ, hrange]

/-- A bounded open connected domain with a Jordan frontier is its Jordan interior. -/
theorem domain_eq_jordanInterior (D : Set Point) (hOpen : IsOpen D)
    (hConnected : IsConnected D) (hBounded : Bornology.IsBounded D)
    (hJordan : IsJordanCurve (frontier D)) : D = jordanInterior (frontier D) := by
  obtain ⟨U, V, _, _, _, _, hUbounded, hVunbounded, _, hcover, _, _, hUcomp, hVcomp⟩ :=
    jordan_separation hJordan
  obtain ⟨p, hp⟩ := hConnected.nonempty
  have hcomponent := domain_component D hOpen hConnected hp
  have hpfront : p ∈ (frontier D)ᶜ := by
    exact connectedComponentIn_subset (frontier D)ᶜ p
      (hcomponent.symm ▸ hp)
  have hpUV : p ∈ U ∪ V := by rwa [hcover]
  have hD : D = U := by
    rcases hpUV with hpU | hpV
    · exact hcomponent.symm.trans (hUcomp p hpU)
    · exact False.elim (hVunbounded ((hcomponent.symm.trans (hVcomp p hpV)) ▸ hBounded))
  ext q
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · exact connectedComponentIn_subset (frontier D)ᶜ p (hcomponent.symm ▸ hq)
    · rw [hUcomp q (hD ▸ hq)]
      exact hUbounded
  · rintro ⟨hqfront, hqbounded⟩
    have hqUV : q ∈ U ∪ V := by rwa [hcover]
    rcases hqUV with hqU | hqV
    · exact hD.symm ▸ hqU
    · rw [hVcomp q hqV] at hqbounded
      exact False.elim (hVunbounded hqbounded)

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.domain_component
#check_upstream ClassicalTheorems.Progress.Green.isJordanCurve_of_simple_closed
#check_upstream ClassicalTheorems.Progress.Green.domain_eq_jordanInterior
