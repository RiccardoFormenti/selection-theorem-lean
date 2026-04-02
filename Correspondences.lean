/-
Copyright (c) 2026 Riccardo Formenti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Formenti
-/
import Mathlib.Topology.Defs.Filter

/-
# Correspondences and Hemicontinuity

This file defines set-valued maps (correspondences) and their hemicontinuity properties.

## Main definitions

`Correspondence.image`: The image (range) of a correspondence.
`LowerHemicontinuousAt`: Lower hemicontinuity of a correspondence at a point.
`LowerHemicontinuous`: Lower hemicontinuity of a correspondence on the whole space.
-/

open Filter Topology Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace Correspondence

/-- The image (or range) of a correspondence `F`, i.e., `⋃ x, F x`. -/
def image (F : X → Set Y) : Set Y :=
  ⋃ x, F x

/-- A correspondence `F` is lower hemicontinuous at `x` if for every open set `O`
that intersects `F x`, eventually (in a neighborhood of `x`) the correspondence
intersects `O`. -/
def LowerHemicontinuousAt (F : X → Set Y) (x : X) : Prop :=
  ∀ O : Set Y, IsOpen O → (F x ∩ O).Nonempty →
  ∀ᶠ a in 𝓝 x, (F a ∩ O).Nonempty

/-- A correspondence `F` is lower hemicontinuous if it is lower hemicontinuous at
every point `x`. -/
def LowerHemicontinuous (F : X → Set Y) : Prop :=
  ∀ x : X, LowerHemicontinuousAt F x

end Correspondence
