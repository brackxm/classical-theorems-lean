/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import UnicoProofs.Platonici.BandieraVertice

/-! Finite counts of genuine exposed faces of convex polytopes.
The imported polytope is a finite convex hull whose vertices are its extreme
points. No Euler identity or combinatorial embedding is assumed. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope

namespace ClassicalTheorems.Progress.Euler

/-- Nonempty geometric faces of affine dimension `k`. -/
def facesOfDim {n : ℕ} (P : ConvexPolytope n) (k : ℕ) : Set (Set (E n)) :=
  {F | P.IsFace F ∧ faceDim F = k}

/-- The number of distinct geometric faces of dimension `k`. -/
def faceCount {n : ℕ} (P : ConvexPolytope n) (k : ℕ) : ℕ :=
  (facesOfDim P k).ncard

theorem facesOfDim_finite {n : ℕ} (P : ConvexPolytope n) (k : ℕ) :
    (facesOfDim P k).Finite := (facce_finite P).subset (fun _ h => h.1)

/-- A face is determined by precisely the vertices it contains. -/
theorem face_vertices_injective {n : ℕ} (P : ConvexPolytope n) :
    InjOn (fun F : Set (E n) => P.vertices.filter (· ∈ F)) {F | P.IsFace F} := by
  classical
  intro F hF G hG h
  exact (face_eq_hull_vertices P hF).trans
    ((congrArg (fun s : Finset (E n) => convexHull ℝ (s : Set (E n))) h).trans
      (face_eq_hull_vertices P hG).symm)

/-- Zero-dimensional geometric faces are exactly the vertex singletons. -/
theorem facesOfDim_zero {n : ℕ} (P : ConvexPolytope n) :
    facesOfDim P 0 = (fun v : E n => ({v} : Set (E n))) '' (P.vertices : Set (E n)) := by
  ext F
  constructor
  · rintro ⟨hF, hd⟩
    obtain ⟨v, rfl⟩ := faccia_dim0_singoletto hF.2 hd
    have hv : v ∈ P.toSet.extremePoints ℝ := hF.1.isExtreme.mem_extremePoints
    have hvV : v ∈ P.vertices := by
      simpa only [ConvexPolytope.toSet, ← P.vertices_eq_extremePoints, Finset.mem_coe] using hv
    exact ⟨v, hvV, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨vertex_isFace P hv, by simp [faceDim]⟩

theorem faceCount_zero {n : ℕ} (P : ConvexPolytope n) :
    faceCount P 0 = P.vertices.card := by
  unfold faceCount
  rw [facesOfDim_zero, (show Function.Injective (fun v : E n => ({v} : Set (E n))) from
    fun _ _ h => singleton_injective h).injOn.ncard_image]
  simp

/-- The whole body is the unique face of the polytope's dimension. -/
theorem facesOfDim_top {n : ℕ} (P : ConvexPolytope n) :
    facesOfDim P P.dim = {P.toSet} := by
  ext F
  constructor
  · rintro ⟨hF, hd⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hne⟩)
    change faceDim F < P.dim at hlt
    omega
  · rintro rfl
    exact ⟨toSet_isFace P, rfl⟩

theorem faceCount_top {n : ℕ} (P : ConvexPolytope n) : faceCount P P.dim = 1 := by
  simp [faceCount, facesOfDim_top]

/-- The geometric Euler expression for a solid three-dimensional polytope. -/
def boundaryEuler (P : ConvexPolytope 3) : ℤ :=
  (faceCount P 0 : ℤ) - (faceCount P 1 : ℤ) + (faceCount P 2 : ℤ)

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.face_vertices_injective
#check_upstream ClassicalTheorems.Progress.Euler.faceCount_zero
#check_upstream ClassicalTheorems.Progress.Euler.faceCount_top
