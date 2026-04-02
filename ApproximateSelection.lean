/-
Copyright (c) 2026 Riccardo Formenti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Formenti
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.PartitionOfUnity
import ProjectRiccardoFormenti.Correspondences

/-!
# Approximate Selection Theorem

This file proves the approximate selection theorem for lower hemicontinuous
correspondences with nonempty convex values into a normed space.

## Main results

- `approximate_selection`: Given a lower hemicontinuous correspondence `F : X → Set Y`
  with nonempty convex values, for any `ε > 0` there exists a continuous function
  `φ : X → Y` such that `infDist (φ x) (F x) < ε` for all `x`.
-/




set_option linter.style.emptyLine false
open Metric Correspondence


variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [ParacompactSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]





theorem approximate_selection (F : X → Set Y)
    (hF_nonempty : ∀ x, (F x).Nonempty)
    (hF_lowerHemicontinuous : Correspondence.LowerHemicontinuous F)
    (hF_convex : ∀ x, Convex ℝ (F x)) :
    ∀ (ε : ℝ), ε > 0 → ∃ φ : C(X, Y), ∀ x : X, infDist (φ x) (F x) < ε := by
  intro ε hε_pos


-- Define the open cover indexed by the image of F
  let O : (image F) → Set X := fun i => {x : X | infDist (i : Y) (F x) < ε/2}


-- Each O(i) is open (via lower hemicontinuity)
  have hO_open : ∀ (i :(image F)), IsOpen (O i) := by
    intro i
-- Characterize openness via neighborhoods (filter definition).
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨y, hyF, hyd⟩ := (infDist_lt_iff (hF_nonempty x)).1 hx
    have hδ_pos : 0 < ε / 2 - dist (i : Y) y := by linarith
    filter_upwards [hF_lowerHemicontinuous x _ Metric.isOpen_ball
     ⟨y, hyF, Metric.mem_ball_self hδ_pos⟩] with a ⟨z, hzF, hzball⟩

    calc infDist (i : Y) (F a)
        ≤ dist (i : Y) z := infDist_le_dist_of_mem hzF
      _ ≤ dist (i : Y) y + dist y z := dist_triangle _ _ _
      _ < ε / 2 := by rw [dist_comm y z]; linarith [Metric.mem_ball.mp hzball]


-- The family O covers X
  have hO_covering : (Set.univ : Set X) = ⋃ (i : (image F)), O i := by
    symm
    refine Set.eq_univ_of_forall (fun x ↦ ?_)
    obtain ⟨y, hy⟩ := hF_nonempty x
    refine Set.mem_iUnion_of_mem ⟨y, Set.mem_iUnion_of_mem x hy⟩ ?_
    dsimp [O]
    rw [Metric.infDist_zero_of_mem hy]
    linarith


-- Define a partition of unity subordinate to the open cover O.
  obtain ⟨ρ, hρ_subordinate⟩ := PartitionOfUnity.exists_isSubordinate
    (isClosed_univ) (O) (hO_open) (Eq.subset hO_covering)


-- Define the function φ and prove that it is continuous.
  let φ : C(X, Y) := {
  toFun := fun x => ∑ᶠ i, ρ i x • (i : Y)
  continuous_toFun := continuous_finsum
    (fun i => (ρ i).continuous.smul continuous_const)
    (ρ.locallyFinite.subset fun i => Function.support_smul_subset_left _ _)
  }


-- Conclude the proof by using φ.
  use φ
  intro x
  have h_near : ∀ i, ρ i x ≠ 0 → infDist (↑i) (F x) < ε / 2 := fun i hi ↦
    hρ_subordinate i (subset_tsupport _ hi)
  choose! y hy_mem hy_dist using fun i (hi : ρ i x ≠ 0) ↦
    (infDist_lt_iff (hF_nonempty x)).mp (h_near i hi)


-- Finite support at x
  have hfin : (Function.support (fun i => ρ i x)).Finite := ρ.locallyFinite.point_finite x
  let S := hfin.toFinset


-- The convex combination witness
  have hz_mem : ∑ᶠ i, (ρ i x) • y i ∈ F x := by
    have hsup : Function.support (fun i => (ρ i) x • y i) ⊆ ↑S := fun i hi => by
      simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
      exact hfin.mem_toFinset.mpr hi.1
    rw [finsum_eq_sum_of_support_subset _ hsup]
    apply Convex.sum_mem (hF_convex x)
    · intro i _
      exact (ρ).nonneg' i x
    · rw [← finsum_eq_sum _ hfin]
      exact ρ.sum_eq_one (Set.mem_univ x)
    · intro i hi
      exact hy_mem i (hfin.mem_toFinset.mp hi)


-- Distance estimate
  calc infDist (φ x) (F x)
      ≤ dist (φ x) (∑ᶠ i, (ρ i x) • y i) := infDist_le_dist_of_mem hz_mem
    _ = ‖∑ᶠ i, (ρ i) x • ↑i - ∑ᶠ i, (ρ i) x • y i‖ := by
      simp only [φ, dist_eq_norm, ContinuousMap.coe_mk]
    _ = ‖∑ᶠ i, (ρ i x) • (i - y i)‖ := by
      congr
      rw [← finsum_sub_distrib]
      · congr 1 with i
        simp only [smul_sub]
      · exact hfin.subset (Function.support_smul_subset_left _ _)
      · exact hfin.subset (Function.support_smul_subset_left _ _)
    _ = ‖∑ i ∈ S, (ρ i) x • (↑i - y i)‖ := by
      congr 1
      exact finsum_eq_sum_of_support_subset _ fun i hi =>
          hfin.mem_toFinset.mpr (by simp_all [Function.mem_support, smul_eq_zero])
    _ ≤ ∑ i ∈ S, ‖(ρ i) x • (↑i - y i)‖ := norm_sum_le S _
    _ = ∑ i ∈ S, ρ i x * ‖↑i - y i‖ := by
      congr 1; ext i
      rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg i x)]
    _ ≤ ∑ i ∈ S, ρ i x * (ε / 2) := by
      gcongr with i hi
      · exact ρ.nonneg' i x
      · rw [← dist_eq_norm]
        exact (hy_dist i (hfin.mem_toFinset.mp hi)).le
    _ = (∑ i ∈ S, ρ i x) * (ε / 2) := by
      exact Eq.symm (Finset.sum_mul S (fun i ↦ (ρ i) x) (ε / 2))
    _ = ε / 2 := by
      have : (∑ i ∈ S, ρ i x) = ∑ᶠ i, (ρ i x) := by
       symm
       exact finsum_eq_sum (fun i => ρ i x) hfin
      rw [this, ρ.sum_eq_one, one_mul]
      exact Set.mem_univ x
    _ < ε := by linarith
