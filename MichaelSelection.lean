/-
Copyright (c) 2026 Riccardo Formenti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Formenti
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Basic
import ProjectRiccardoFormenti.ApproximateSelection

/-!
# Michael Selection Theorem

In this file we prove the Michael selection theorem for lower hemicontinuous
correspondences with closed convex values in a normed space.

## Main results

- `michael_selection`: the main selection theorem stating that a lower hemicontinuous
  correspondence with closed convex nonempty values admits a continuous selection.

-/

set_option linter.style.emptyLine false
noncomputable section
open Filter Metric Topology Correspondence



variable {X : Type*} [TopologicalSpace X] [NormalSpace X] [ParacompactSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]




def michael_correspondence (F : X → Set Y) (ε : ℝ) (f : C(X, Y)) : X → Set Y :=
    fun x => (F x) ∩ (ball (f x) ε)




-- The Michael correspondence preserves convexity
omit [NormalSpace X] [ParacompactSpace X] [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y] in
lemma michael_correspondence_convex (F : X → Set Y)
    (hFconv : ∀ x, Convex ℝ (F x))
    (f : C(X, Y)) (ε : ℝ) :
    ∀ x, Convex ℝ ((michael_correspondence F ε f) x) := by

  intro x
  dsimp [michael_correspondence]
  apply Convex.inter
  · exact hFconv x
  · exact convex_ball _ _




-- The Michael correspondence inherits lower hemicontinuity from F.
omit [NormalSpace X] [ParacompactSpace X] [NormedSpace ℝ Y] [CompleteSpace Y]
     [TopologicalSpace.SeparableSpace Y] in
lemma michael_correspondence_lhc (F : X → Set Y)
    (hFlhc : Correspondence.LowerHemicontinuous F)
    (f : C(X, Y)) (ε : ℝ) :
    Correspondence.LowerHemicontinuous (michael_correspondence F ε f) := by

  intro x O hO ⟨y, ⟨hyF, hyball⟩, hyO⟩
  set δ := ε - dist y (f x) with hδ
  have hδpos : 0 < δ := sub_pos.mpr (mem_ball.mp hyball)
  filter_upwards [
    hFlhc x (O ∩ ball y (δ/2)) (hO.inter isOpen_ball) ⟨y, hyF, hyO, mem_ball_self (half_pos hδpos)⟩,
    Metric.tendsto_nhds.mp (f.continuous.tendsto x) (δ/2) (half_pos hδpos)]
    with a ⟨z, hzF, hzO, hzball⟩ hfa
  refine ⟨z, ⟨hzF, mem_ball.mpr ?_⟩, hzO⟩

  calc dist z (f a)
      ≤ dist z y + dist y (f a) := dist_triangle _ _ _
    _ ≤ dist z y + (dist y (f x) + dist (f x) (f a)) := by
       gcongr
       exact dist_triangle _ _ _
    _ < δ/2 + ((ε - δ) + δ/2) := by linarith [mem_ball.mp hzball, dist_comm (f x) (f a)]
    _ = ε := by ring




-- The Michael correspondence has nonempty values
omit [NormalSpace X] [ParacompactSpace X] [NormedSpace ℝ Y] [CompleteSpace Y]
     [TopologicalSpace.SeparableSpace Y] in
lemma michael_correspondence_nonempty (F : X → Set Y)
    (hFne : ∀ x, (F x).Nonempty)
    (f : C(X, Y)) (ε : ℝ)
    (hf : ∀ x : X, infDist (f x) (F x) < ε) :
    ∀ x : X, (michael_correspondence F ε f x).Nonempty := by

  intro x
  obtain ⟨y, hyF, hylt⟩ := (infDist_lt_iff (hFne x)).1 (hf x)
  change ((F x) ∩ ball (f x) ε).Nonempty
  refine ⟨y, ?_⟩
  have hylt' : dist y (f x) < ε := by
   rw [dist_comm]
   exact hylt
  exact ⟨hyF, mem_ball.mpr hylt'⟩




/-! ### Packaging the Approximate Selection

These definitions wrap the `approximate_selection` theorem to extract a witness
function and its specification separately, which is convenient for the iterative construction.
-/

def approximate_selection_witness (F : X → Set Y)
    (hFne : ∀ x, (F x).Nonempty)
    (hFlhc : Correspondence.LowerHemicontinuous F)
    (hFconv : ∀ x, Convex ℝ (F x))
    (ε : ℝ) (hε : ε > 0) : C(X, Y) := by

exact Classical.choose (approximate_selection F hFne hFlhc hFconv ε hε)




omit [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y] in
lemma approximate_selection_spec (F : X → Set Y)
    (hFne : ∀ x, (F x).Nonempty)
    (hFlhc : Correspondence.LowerHemicontinuous F)
    (hFconv : ∀ x, Convex ℝ (F x))
    (ε : ℝ) (hε : ε > 0) :
    ∀ x : X, infDist ((approximate_selection_witness F hFne hFlhc hFconv ε hε) x) (F x) < ε := by

  exact Classical.choose_spec (approximate_selection F hFne hFlhc hFconv ε hε)



/-! ### The Step Data Structure

This structure bundles all the data needed at each stage of the iterative construction:
a correspondence F with its properties (nonempty, LHC, convex values), an error bound ε,
and an approximate selection f satisfying the ε-approximation property.
-/


structure step_data (X : Type*) (Y : Type*) [TopologicalSpace X] [NormalSpace X]
    [ParacompactSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y] where
  /-- The underlying correspondence -/
  F : X → Set Y
  /-- Nonemptiness of values -/
  hF_nonempty : ∀ x, (F x).Nonempty
  /-- Lower hemicontinuity -/
  hFlhc : Correspondence.LowerHemicontinuous F
  /-- Convexity of values -/
  hF_convex : ∀ x, Convex ℝ (F x)
  /-- The approximation error bound -/
  ε : ℝ
  /-- Positivity of the error bound -/
  hε : 0 < ε
  /-- The approximate selection -/
  f : C(X, Y)
  /-- The approximation property -/
  hf : ∀ x : X, infDist (f x) (F x) < ε




/-! ### The Iteration Step

Given step data (F, ε, f), construct the next step:
1. Define F' = michael_correspondence(F, ε, f) = F ∩ ball(f, ε)
2. Set ε' = ε/2
3. Apply approximate_selection to F' with tolerance ε' to get f'

This halves the error bound while refining the correspondence.
-/


def step (d : step_data X Y) : step_data X Y := by


-- Define the refined correspondence F' = F ∩ ball(f, ε)
let F' : X → Set Y := michael_correspondence d.F d.ε d.f


-- F' has nonempty values (since f is an ε-approximate selection of F)
have hF'ne : ∀ x : X, (F' x).Nonempty :=
    michael_correspondence_nonempty d.F d.hF_nonempty d.f d.ε d.hf


-- F' inherits lower hemicontinuity from F
have hF'lhc : Correspondence.LowerHemicontinuous F' :=
    michael_correspondence_lhc d.F d.hFlhc d.f d.ε


-- F' inherits convexity from F (intersection of convex sets)
have hF'conv : ∀ x : X, Convex ℝ (F' x) := michael_correspondence_convex d.F d.hF_convex d.f d.ε


-- Halve the error tolerance
let ε' : ℝ := d.ε / 2
have hε' : ε' > 0 := by
   change d.ε / 2 > 0
   exact div_pos d.hε (by norm_num)


-- Apply the approximate selection theorem to F' with the new tolerance ε'
let f' : C(X,Y) :=
    approximate_selection_witness F' hF'ne hF'lhc hF'conv ε' hε'


-- f' is an ε'-approximate selection of F'
let hf' : ∀ x : X, infDist (f' x) (F' x) < ε' :=
    approximate_selection_spec F' hF'ne hF'lhc hF'conv ε' hε'

exact
    { F      := F'
      hF_nonempty   := hF'ne
      hFlhc  := hF'lhc
      hF_convex := hF'conv
      ε      := ε'
      hε     := hε'
      f      := f'
      hf     := hf' }




theorem michael_selection (F : X → Set Y)
    (hFne : ∀ x, (F x).Nonempty)
    (hFlhc : Correspondence.LowerHemicontinuous F)
    (hFconv : ∀ x, Convex ℝ (F x))
    (hFcl : ∀ x, IsClosed (F x)) :
    ∃ φ : C(X, Y), ∀ x : X, φ x ∈ (F x):= by


-- Define the sequence of step data by recursion:
  let data : ℕ → step_data X Y :=
    Nat.rec
      {F := F
       hF_nonempty := hFne
       hFlhc := hFlhc
       hF_convex := hFconv
       ε := (1 : ℝ)
       hε := by positivity
       f := approximate_selection_witness F hFne hFlhc hFconv 1 (by positivity)
       hf := approximate_selection_spec F hFne hFlhc hFconv 1 (by positivity)
      }
      (fun n d => step (X := X) (Y := Y) d)


-- Extract the sequence of continuous functions
  let f (n : ℕ) : C(X, Y) := (data n).f


-- The error bound at step m is exactly 1/2^m (halving at each step)
  have h_data_eps (m : ℕ) : (data m).ε = (1 : ℝ) / 2 ^ m := by
    induction m with
    | zero => simp only [Nat.rec_zero, pow_zero, ne_eq, one_ne_zero, not_false_eq_true, div_self,
    data]
    |  succ m ih =>
      calc
        (data m.succ).ε = (data m).ε / 2 := by
              simp only [step, Nat.succ_eq_add_one, data]
        _   = ((1 : ℝ) / (2 : ℝ)^m) / 2 := by
              simp only [ih, one_div]
        _   = (1 : ℝ) / (2 : ℝ)^(m.succ) := by
              rw [Nat.succ_eq_add_one]
              grind only [cases Or]


-- Key estimate: consecutive iterates satisfy
  have h_dist_succ_bound (m : ℕ) (x : X) :
    dist ((f (m+1)) x) ((f (m)) x) < (3/(2^(m+1)) : ℝ) := by

    have h_inf := (data (m+1)).hf x
    rw [Metric.infDist_lt_iff ((data (m+1)).hF_nonempty x)] at h_inf
    rcases h_inf with ⟨y, hy_Fm, hy_dist_fm⟩
    rw [dist_comm] at hy_dist_fm


    have hy_dist_fm' : dist y ((data m).f x) < (data m).ε := by
      dsimp only [data, step, michael_correspondence] at hy_Fm
      rcases hy_Fm with ⟨_, hy_in_ball⟩
      rw [Metric.mem_ball] at hy_in_ball
      exact hy_in_ball


-- Triangle inequality
    calc dist ((f (m + 1)) x) ((f m) x)
    _ ≤ dist ((f (m + 1)) x) y + dist y ((f m) x) := dist_triangle _ _ _
    _ = dist y ((f (m + 1)) x) + dist y ((f m) x) := by rw [dist_comm]
    _ < (data (m + 1)).ε + (data m).ε             := add_lt_add hy_dist_fm hy_dist_fm'
    _ = 1 / 2 ^ (m + 1) + 1 / 2 ^ m                := by simp only [h_data_eps, one_div]
    _ = 1 / 2 ^ (m + 1) + 2 / 2 ^ (m + 1)          := by ring -- or explicit field_simp
    _ = 3 / 2 ^ (m + 1)                            := by ring



-- The bounding sequence 3/2^{n+1} is summable (geometric series with ratio 1/2)
  let bound_seq (n : ℕ) : ℝ := 3 / 2 ^ (n + 1)
  have h_summable : Summable bound_seq := by
     have h := summable_geometric_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num)
     exact (h.mul_left (3/2)).congr fun n => by
       simp [bound_seq, pow_succ']
       ring


-- The sequence (fₙ) is uniformly Cauchy on X
  have h_cauchy : UniformCauchySeqOn (fun n x ↦ f n x) Filter.atTop Set.univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (3 : ℝ) / 2 ^ N < ε := by
      have : Tendsto (fun n => (3 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
        exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
      exact (this.eventually (gt_mem_nhds hε)).exists

    refine ⟨N, fun m hm n hn x _ => ?_⟩
    wlog hmn : m ≤ n generalizing m n
    · rw [dist_comm]
      exact this n hn m hm (le_of_not_ge hmn)
    · calc
        dist ((f m) x) ((f n) x) ≤ ∑ k ∈ Finset.Ico m n, dist ((f k) x) ((f (k + 1)) x) := by
          exact dist_le_Ico_sum_dist (α := Y) (fun n => f n x) hmn
      _ ≤ ∑ k ∈ Finset.Ico m n, 3 / 2 ^ (k + 1) := by
          gcongr with k _
          rw [dist_comm]
          exact le_of_lt (h_dist_succ_bound k x)
      _ = (3 / 2) * (∑ k ∈ Finset.Ico m n, (1 / 2 : ℝ) ^ k):= by
          rw [Finset.mul_sum]
          congr 1
          ext k
          rw [pow_succ, one_div_pow, div_mul_div_comm, mul_one, mul_comm]
      _ ≤ (3 / 2) * ((1 / 2 : ℝ) ^ m / (1 - 1 / 2)) := by
          have h := geom_sum_Ico_le_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
            (by norm_num : (1/2 : ℝ) < 1)
            (m := m) (n := n)
          apply mul_le_mul_of_nonneg_left h
          norm_num
      _ = 3 * (1 / 2 : ℝ) ^ m := by ring
      _ ≤ 3 * (1 / 2 : ℝ) ^ N := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 3 / 2 ^ N := by
          field_simp
          simp only [one_div, inv_pow, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
            not_false_eq_true, inv_mul_cancel₀]
      _ < ε := by exact hN




-- Uniform Cauchy implies pointwise Cauchy
  have h_ptwise_cauchy : ∀ x, CauchySeq (fun n ↦ (f n) x) := fun x ↦
    h_cauchy.cauchySeq (Set.mem_univ x)


-- Completeness of Y gives pointwise convergence to some limit
  have h_ptwise : ∀ x, ∃ y, Tendsto (fun n ↦ (f n) x) atTop (𝓝 y) := fun x ↦
    cauchySeq_tendsto_of_complete (h_ptwise_cauchy x)


-- Package the pointwise limits into a function φ
  choose φ hφ using h_ptwise


-- Uniform Cauchy + pointwise convergence implies uniform convergence
  have h_unif : TendstoUniformlyOn (fun n x ↦ f n x) φ atTop Set.univ :=
    h_cauchy.tendstoUniformlyOn_of_tendsto (fun x _ ↦ hφ x)

  rw [tendstoUniformlyOn_univ] at h_unif


-- Uniform limit of continuous functions is continuous
  have hφ_cont : Continuous φ := TendstoUniformly.continuous (h_unif) (Frequently.of_forall (by
   intro n
   exact (f n).continuous))

-- Package φ as a continuous map
  use ⟨φ, hφ_cont⟩


-- Now prove that φ(x) ∈ F(x) for all x
  intro x
  simp only [ContinuousMap.coe_mk]


-- The error bounds εₙ = 1/2ⁿ → 0 as n → ∞
  have hε_tendsto_zero : Tendsto (fun m : ℕ => (data m).ε) atTop (𝓝 (0 : ℝ)) := by
    have hgeom : Tendsto (fun m : ℕ => ((1 / 2 : ℝ) ^ m)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hε_eq : (fun m : ℕ => (data m).ε) = fun m => ((1 / 2 : ℝ) ^ m) := by
      funext m
      calc
        (data m).ε = (1 : ℝ) / 2 ^ m := h_data_eps m
        _ = ((1 / 2 : ℝ) ^ m) := by simp only [one_div, inv_pow]
    simpa only [hε_eq, one_div, inv_pow] using hgeom


-- For each m, find a witness yₘ ∈ Fₘ(x) with dist(fₘ(x), yₘ) < εₘ
  have hy'_ex : ∀ m : ℕ, ∃ y ∈ (data m).F x, dist ((f m) x) y < (data m).ε := by
    intro m
    rcases (Metric.infDist_lt_iff ((data m).hF_nonempty x)).1 ((data m).hf x) with ⟨y, hyF, hydist⟩
    exact ⟨y, hyF, hydist⟩

  choose y hy_mem hy_dist using hy'_ex


-- fₙ(x) → φ(x) pointwise
  have h_φx_pointwise : Tendsto (fun n => (f n) x) atTop (𝓝 (φ x)) := by
    exact hφ x


-- The witness sequence yₙ also converges to φ(x)
  have h_y_lim : Tendsto y atTop (𝓝 (φ x)) := by
    have hdist_y_fx : Tendsto (fun m => dist (y m) ((f m) x)) atTop (𝓝 (0 : ℝ)) := by
      refine squeeze_zero (fun _ => dist_nonneg) ?_ hε_tendsto_zero
      intro m
      rw[dist_comm]
      exact le_of_lt (hy_dist m)

    have hdist_fx : Tendsto (fun m => dist ((f m) x) (φ x)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_iff_dist_tendsto_zero).1 h_φx_pointwise


    have hsum : Tendsto (fun m => dist (y m) ((f m) x) + dist ((f m) x) (φ x)) atTop (𝓝 0) := by
      simpa only [add_zero] using hdist_y_fx.add hdist_fx


    refine (tendsto_iff_dist_tendsto_zero).2 ?_

    refine squeeze_zero (g := fun m => dist (y m) ((f m) x) + dist ((f m) x) (φ x)) ?_ ?_ ?_

    · simp only [dist_nonneg, implies_true]
    · simp only [dist_triangle, implies_true]
    · exact hsum


-- F(x) is closed and yₙ → φ(x), so φ(x) ∈ F(x) if yₙ ∈ F(x) eventually
  apply (hFcl x).mem_of_tendsto h_y_lim


-- Each Fₙ(x) ⊆ F(x) (the Michael correspondence only refines, never enlarges)
  have data_F_subset_original (n : ℕ) (x : X) : (data n).F x ⊆ F x := by
    induction n with
    | zero => exact Set.Subset.refl _
    | succ n ih => exact Set.Subset.trans (fun _ h => h.1) ih


-- Therefore yₘ ∈ Fₘ(x) ⊆ F(x) for all m
  have hy_mem_F : ∀ m, y m ∈ F x := fun m => data_F_subset_original m x (hy_mem m)


  exact Eventually.of_forall hy_mem_F
